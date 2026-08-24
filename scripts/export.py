#!/usr/bin/env python3
"""Build the static Station V2 archive from explicitly allowlisted sources.

All agent dialogue content is exported with provider transport and host-tool
metadata removed. Public Station indexes, capsule records, and public-facing
research-submission results are also exported.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import re
import shutil
from pathlib import Path
import yaml


ROOT = Path(__file__).resolve().parents[1]
SPOTLIGHT_ARCHIVES = json.loads((ROOT / "config" / "spotlight_archives.json").read_text(encoding="utf-8"))
DATA_ROOT = ROOT / "data"
PAGE_DOCUMENT_LIMIT = 20
PAGE_BYTE_TARGET = 512 * 1024

SECRET_PATTERNS = {
    "OpenAI-style key": re.compile(rb"\bsk-[A-Za-z0-9_-]{20,}\b"),
    "GitHub token": re.compile(rb"\bgh[pousr]_[A-Za-z0-9]{30,}\b"),
    "AWS access key": re.compile(rb"\bAKIA[0-9A-Z]{16}\b"),
    "Google API key": re.compile(rb"\bAIza[0-9A-Za-z_-]{30,}\b"),
    "Slack token": re.compile(rb"\bxox[baprs]-[0-9A-Za-z-]{20,}\b"),
    "Bearer token": re.compile(rb"(?i)\bBearer\s+[A-Za-z0-9._~+/=-]{20,}"),
    "API endpoint URL": re.compile(
        rb"(?i)https?://[^\s<>\"'`\\)\]]*/v1/(?:chat/completions|messages|responses)\b"
    ),
}
ARCHIVE_REFERENCE_GROUP = re.compile(
    r"(?i)\barchives?\b(?:\s+(?:papers?|capsules?|IDs?))?\s*[:#]?\s*"
    r"((?:#?\d+)(?:(?:\s*(?:,\s*(?:(?:\band\b|&)\s*)?|;|/|&|\band\b)\s*|\s*(?:-|–|—|\bto\b|\bthrough\b)\s*)#?\d+)*)"
)
ARCHIVE_SLUG_REFERENCE = re.compile(r"(?i)\barchive_(\d+)\b")
ARCHIVE_RANGE = re.compile(r"(?i)(\d+)\s*(?:-|–|—|\bto\b|\bthrough\b)\s*#?(\d+)")
ENVIRONMENT_THINKING_REFERENCE = re.compile(
    rb"(?i)\b(?:openai\s+codex|claude\s+code|anthropic|codex_home|"
    rb"codex\s+(?:cli|shell|coding\s+agent|tool|tools|tool\s+calls))\b|\.codex(?:/|\\)"
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def filesystem_key(name: str) -> str:
    """Return an opaque URL-safe key that is also the literal directory name."""
    slug = re.sub(r"[^A-Za-z0-9._~-]+", "-", name).strip("-.")[:48] or "record"
    suffix = hashlib.sha1(name.encode("utf-8")).hexdigest()[:10]
    return f"{slug}-{suffix}"


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def write_gzip(path: Path, data: bytes) -> dict[str, object]:
    path.parent.mkdir(parents=True, exist_ok=True)
    compressed = gzip.compress(data, compresslevel=6, mtime=0)
    path.write_bytes(compressed)
    return {
        "bytes": len(data),
        "compressed_bytes": len(compressed),
        "sha256": sha256(data),
    }


def scan_secrets(path: Path, data: bytes, findings: list[dict[str, str]]) -> None:
    for label, pattern in SECRET_PATTERNS.items():
        if pattern.search(data):
            findings.append({"type": label, "source": str(path)})


def safe_yaml(data: bytes) -> dict[str, object]:
    try:
        parsed = yaml.safe_load(data.decode("utf-8"))
        return parsed if isinstance(parsed, dict) else {}
    except Exception:
        return {}


def evaluation_result(metadata: dict[str, object]) -> str:
    """Return the public result text displayed by the archive frontend."""
    notification = metadata.get("notification") if isinstance(metadata.get("notification"), dict) else {}
    message = notification.get("message")
    if isinstance(message, str) and message.strip():
        return message
    final = metadata.get("final") if isinstance(metadata.get("final"), dict) else {}
    details = final.get("evaluation_details")
    if isinstance(details, str):
        return details
    if details not in (None, {}, []):
        rendered = yaml.safe_dump(details, sort_keys=False, allow_unicode=True).rstrip()
        return f"```yaml\n{rendered}\n```"
    return ""


def project_evaluation(metadata: dict[str, object]) -> bytes:
    """Keep only the instruction and user-facing result needed by the frontend."""
    public_record = {
        "instruction": metadata.get("instruction") or "",
        "result": evaluation_result(metadata),
    }
    return yaml.safe_dump(public_record, sort_keys=False, allow_unicode=True).encode("utf-8")


def archive_citation_text(metadata: dict[str, object]) -> str:
    """Return paper-authored text, excluding review and third-party replies."""
    parts = [str(metadata.get("abstract") or ""), str(metadata.get("content") or "")]
    primary_author = str(metadata.get("author_name") or "").casefold()
    primary_lineage = str(metadata.get("author_lineage") or metadata.get("lineage") or "").casefold()
    messages = metadata.get("messages") if isinstance(metadata.get("messages"), list) else []
    for message in messages:
        if not isinstance(message, dict) or message.get("is_deleted"):
            continue
        author = str(message.get("author_name") or "").casefold()
        lineage = str(message.get("author_lineage") or "").casefold()
        if "review" in author or "reviewer" in str(message.get("role") or "").casefold():
            continue
        if (primary_author and author == primary_author) or (not primary_author and primary_lineage and lineage == primary_lineage):
            parts.append(str(message.get("content") or ""))
    return "\n".join(part for part in parts if part)


def extract_archive_citations(metadata: dict[str, object], source_id: str) -> list[str]:
    """Extract explicit local Archive references in first-appearance order."""
    text = archive_citation_text(metadata)
    numbers: list[int] = []
    for match in ARCHIVE_REFERENCE_GROUP.finditer(text):
        group = match.group(1)
        numbers.extend(int(value) for value in re.findall(r"\d+", group))
        for range_match in ARCHIVE_RANGE.finditer(group):
            first, last = map(int, range_match.groups())
            if first <= last and last - first <= 500:
                numbers.extend(range(first, last + 1))
    numbers.extend(int(match.group(1)) for match in ARCHIVE_SLUG_REFERENCE.finditer(text))
    seen: set[str] = set()
    citations = []
    for number in numbers:
        citation = f"archive_{number}"
        if citation != source_id.casefold() and citation not in seen:
            seen.add(citation)
            citations.append(citation)
    return citations


def active_messages(metadata: dict[str, object]) -> list[dict[str, object]]:
    messages = metadata.get("messages") if isinstance(metadata.get("messages"), list) else []
    return [message for message in messages if isinstance(message, dict) and not message.get("is_deleted")]


def capsule_reply_count(metadata: dict[str, object]) -> int:
    return max(0, len(active_messages(metadata)) - 1)


def mail_recipients(metadata: dict[str, object]) -> list[str]:
    recipients = metadata.get("recipients")
    if isinstance(recipients, list):
        return [str(recipient) for recipient in recipients if str(recipient).strip()]
    if isinstance(recipients, str) and recipients.strip():
        return [recipients.strip()]
    return []


def archive_reviewer_score(metadata: dict[str, object]) -> float | None:
    for message in reversed(active_messages(metadata)):
        content = str(message.get("content") or "")
        if "Reviewer Evaluation" not in content:
            continue
        match = re.search(r"\*\*Score:\*\*\s*([0-9]+(?:\.[0-9]+)?)\s*/\s*10", content)
        if match:
            return float(match.group(1))
    return None


def question_status(metadata: dict[str, object]) -> str:
    status = str(metadata.get("question_status") or "pending").strip().lower()
    return status if status in {"pending", "open", "redacted", "solved", "retired"} else "pending"


def split_history(raw: bytes) -> list[bytes]:
    """Split a YAMLL byte stream at document boundaries without changing bytes."""
    starts = [0]
    starts.extend(match.start() + 1 for match in re.finditer(rb"\n---[ \t]*\r?\n", raw))
    starts.append(len(raw))
    pages: list[bytes] = []
    page_start = starts[0]
    document_count = 0
    for index in range(len(starts) - 1):
        document_count += 1
        document_end = starts[index + 1]
        page_size = document_end - page_start
        last_document = index == len(starts) - 2
        if document_count >= PAGE_DOCUMENT_LIMIT or page_size >= PAGE_BYTE_TARGET or last_document:
            pages.append(raw[page_start:document_end])
            page_start = document_end
            document_count = 0
    assert b"".join(pages) == raw
    return pages


def export_dialogue(raw: bytes) -> bytes:
    """Return the full agent dialogue with transport and host-tool metadata removed."""
    output: list[bytes] = []
    skipping_api_metadata = False
    for line in raw.splitlines(keepends=True):
        if not skipping_api_metadata and re.match(rb"^api_metadata:[ \t]*(?:\r?\n)?$", line):
            skipping_api_metadata = True
            continue
        if skipping_api_metadata:
            if line.startswith((b" ", b"\t")) or not line.strip():
                continue
            skipping_api_metadata = False
        output.append(line)
    projected, _ = redact_environment_thinking(b"".join(output))
    projected, _ = redact_environment_model_documents(projected)
    return projected


def is_environment_thinking(block: bytes) -> bool:
    normalized = re.sub(rb"\s+", b" ", block)
    if ENVIRONMENT_THINKING_REFERENCE.search(normalized):
        return True
    lowered = normalized.lower()
    return b"codex format" in lowered and b"tool calls" in lowered


def redact_environment_thinking(raw: bytes) -> tuple[bytes, int]:
    """Drop a complete top-level thinking_content field when it reveals host tooling."""
    lines = raw.splitlines(keepends=True)
    output: list[bytes] = []
    removed = 0
    index = 0
    while index < len(lines):
        if not lines[index].startswith(b"thinking_content:"):
            output.append(lines[index])
            index += 1
            continue
        end = index + 1
        while end < len(lines) and (lines[end].startswith((b" ", b"\t")) or not lines[end].strip()):
            end += 1
        block = b"".join(lines[index:end])
        if is_environment_thinking(block):
            removed += 1
        else:
            output.extend(lines[index:end])
        index = end
    return b"".join(output), removed


def redact_environment_model_documents(raw: bytes) -> tuple[bytes, int]:
    """Drop complete model documents that reveal host tooling outside thinking_content."""
    starts = [0]
    starts.extend(match.start() + 1 for match in re.finditer(rb"\n---[ \t]*\r?\n", raw))
    starts.append(len(raw))
    output: list[bytes] = []
    removed = 0
    for index in range(len(starts) - 1):
        document = raw[starts[index]:starts[index + 1]]
        is_model = re.search(rb"(?m)^role:[ \t]*model[ \t]*$", document) is not None
        if is_model and is_environment_thinking(document):
            removed += 1
            continue
        output.append(document)
    return b"".join(output), removed


def history_summary(raw: bytes) -> dict[str, object]:
    ticks = [int(value) for value in re.findall(rb"(?m)^tick:[ \t]*(\d+)[ \t]*$", raw)]
    roles = [value.decode("ascii", "replace") for value in re.findall(rb"(?m)^role:[ \t]*([^\r\n]+)", raw)]
    return {
        "documents": max(len(roles), len(ticks)),
        "first_tick": min(ticks) if ticks else None,
        "last_tick": max(ticks) if ticks else None,
        "roles": sorted(set(roles)),
    }


def export_history(source: Path, destination: Path, findings: list[dict[str, str]]) -> dict[str, object]:
    raw = source.read_bytes()
    dialogue = export_dialogue(raw)
    scan_secrets(source, dialogue, findings)
    pages = split_history(dialogue)
    page_records = []
    for index, page in enumerate(pages, start=1):
        filename = f"page-{index:04d}.yamll.gz"
        record = {"file": filename, **history_summary(page), **write_gzip(destination / filename, page)}
        page_records.append(record)
    manifest = {
        "format": "dialogue-yamll-v2",
        "removed_metadata": [
            "provider transport metadata",
            "host-tool metadata",
        ],
        "source_name": source.name,
        "source_bytes": len(raw),
        "source_sha256": sha256(raw),
        "exported_bytes": len(dialogue),
        "exported_sha256": sha256(dialogue),
        "pages": page_records,
    }
    write_json(destination / "index.json", manifest)
    return manifest


def export_station(
    item: dict[str, object],
    station_source_root: Path,
    findings: list[dict[str, str]],
) -> dict[str, object]:
    station_id = str(item["id"])
    source = station_source_root / station_id
    destination = DATA_ROOT / station_id
    destination.mkdir(parents=True, exist_ok=True)
    if not source.is_dir():
        raise FileNotFoundError(source)

    config_source = source / "station_config.yaml"
    config_raw = config_source.read_bytes() if config_source.is_file() else b""
    config_data = safe_yaml(config_raw)

    agent_records = []
    agents_source = source / "agents"
    for history_source in sorted(agents_source.glob("*/llm_chat_history.yamll")):
        name = history_source.parent.name
        key = filesystem_key(name)
        metadata_source = agents_source / f"{name}.yaml"
        metadata_raw = metadata_source.read_bytes() if metadata_source.is_file() else b""
        metadata = safe_yaml(metadata_raw)
        history = export_history(history_source, destination / "agents" / key / "dialogue", findings)
        agent_records.append(
            {
                "name": name,
                "key": key,
                "display_name": metadata.get("agent_name") or name,
                "model": metadata.get("model_name") or "Unknown",
                "status": metadata.get("status") or "Unknown",
                "lineage": metadata.get("lineage") or "",
                "generation": metadata.get("generation"),
                "description": metadata.get("description") or "",
                "tick_birth": metadata.get("tick_birth"),
                "tick_exit": metadata.get("tick_exit"),
                "history": {
                    "pages": len(history["pages"]),
                    "documents": sum(int(page["documents"]) for page in history["pages"]),
                    "first_tick": next((page["first_tick"] for page in history["pages"] if page["first_tick"] is not None), None),
                    "last_tick": next((page["last_tick"] for page in reversed(history["pages"]) if page["last_tick"] is not None), None),
                },
            }
        )
    write_json(destination / "agents" / "index.json", {"agents": agent_records})

    capsule_records = []
    capsules_source = source / "capsules"
    if capsules_source.is_dir():
        for capsule_source in sorted(capsules_source.rglob("*")):
            if not capsule_source.is_file() or capsule_source.name.endswith(".lock") or capsule_source.name == "_index.json":
                continue
            relative = capsule_source.relative_to(capsules_source)
            capsule_type = relative.parts[0] if len(relative.parts) > 1 else "other"
            raw = capsule_source.read_bytes()
            scan_secrets(capsule_source, raw, findings)
            metadata = safe_yaml(raw)
            capsule_id = str(metadata.get("capsule_id") or capsule_source.stem)
            record_key = hashlib.sha1(str(relative).encode("utf-8")).hexdigest()[:16]
            output = destination / "capsules" / "records" / capsule_type / f"{record_key}{capsule_source.suffix}.gz"
            integrity = write_gzip(output, raw)
            capsule_records.append(
                {
                    "id": capsule_id,
                    "key": record_key,
                    "type": capsule_type,
                    "title": metadata.get("title") or capsule_source.stem,
                    "author": metadata.get("author_name") or "Unknown",
                    "lineage": metadata.get("author_lineage") or metadata.get("lineage") or "",
                    "created_tick": metadata.get("created_at_tick"),
                    "updated_tick": metadata.get("last_updated_at_tick"),
                    "word_count": metadata.get("word_count_total"),
                    "tags": metadata.get("tags") if isinstance(metadata.get("tags"), list) else [],
                    "deleted": bool(metadata.get("is_deleted", False)),
                    "source_path": str(relative).replace("\\", "/"),
                    "file": str(output.relative_to(destination)).replace("\\", "/"),
                    **({"citations": extract_archive_citations(metadata, capsule_id)} if capsule_type == "archive" else {}),
                    **({"reviewer_score": archive_reviewer_score(metadata)} if capsule_type == "archive" else {}),
                    **({"reply_count": capsule_reply_count(metadata)} if capsule_type in {"public", "private", "mail", "question"} else {}),
                    **({"recipients": mail_recipients(metadata)} if capsule_type == "mail" else {}),
                    **({
                        "question_status": question_status(metadata),
                        "question_net_upvote": int(metadata.get("question_net_upvote") or 0),
                        "question_solved_by_message_id": metadata.get("question_solved_by_message_id"),
                    } if capsule_type == "question" else {}),
                    **integrity,
                }
            )
    archive_ids = {str(record["id"]).casefold() for record in capsule_records if record["type"] == "archive"}
    spotlight_ids = {f"archive_{number}" for number in SPOTLIGHT_ARCHIVES.get(station_id, [])}
    missing_spotlights = spotlight_ids - archive_ids
    if missing_spotlights:
        raise ValueError(f"Missing spotlight Archive papers for {station_id}: {sorted(missing_spotlights)}")
    for record in capsule_records:
        if record["type"] == "archive":
            record["citations"] = [citation for citation in record.get("citations", []) if citation in archive_ids]
            record["spotlight"] = str(record["id"]).casefold() in spotlight_ids
    capsule_records.sort(key=lambda record: (str(record["type"]), record["created_tick"] or 0, str(record["id"])))
    capsule_types = sorted({str(record["type"]) for record in capsule_records})
    write_json(destination / "capsules" / "index.json", {"capsules": capsule_records, "types": capsule_types})

    evaluation_records = []
    evaluations_source = source / "rooms" / "research" / "evaluations"
    if evaluations_source.is_dir():
        for evaluation_source in sorted(evaluations_source.glob("*.yaml")):
            if evaluation_source.name.endswith(".lock"):
                continue
            source_raw = evaluation_source.read_bytes()
            metadata = safe_yaml(source_raw)
            public_raw = project_evaluation(metadata)
            scan_secrets(evaluation_source, public_raw, findings)
            evaluation_id = str(metadata.get("id") or evaluation_source.stem)
            record_key = filesystem_key(evaluation_id)
            output = destination / "evaluations" / "records" / f"{record_key}.yaml.gz"
            final = metadata.get("final") if isinstance(metadata.get("final"), dict) else {}
            coder = metadata.get("coder") if isinstance(metadata.get("coder"), dict) else {}
            evaluation_records.append(
                {
                    "id": evaluation_id,
                    "key": record_key,
                    "title": metadata.get("title") or f"Research submission {evaluation_id}",
                    "author": metadata.get("author") or "Unknown",
                    "lineage": metadata.get("lineage") or "",
                    "model": coder.get("model_name") or coder.get("backend") or "Unknown",
                    "submitted_tick": metadata.get("submitted_tick"),
                    "status": final.get("status") or metadata.get("status") or "Unknown",
                    "score": final.get("primary_score", "n.a."),
                    "tags": metadata.get("tags") if isinstance(metadata.get("tags"), list) else [],
                    "abstract": metadata.get("abstract") or "",
                    "file": str(output.relative_to(destination)).replace("\\", "/"),
                    **write_gzip(output, public_raw),
                }
            )
    evaluation_records.sort(key=lambda record: (record["submitted_tick"] or 0, str(record["id"])))
    write_json(destination / "evaluations" / "index.json", {"evaluations": evaluation_records})

    manifest = {
        "id": station_id,
        "title": item["title"],
        "station_name": item["title"],
        "version": config_data.get("station_version") or config_data.get("version") or "V2",
        "tick": config_data.get("current_tick"),
        "status": config_data.get("status") or "Archived",
        "counts": {
            "agents": len(agent_records),
            "capsules": len(capsule_records),
            "evaluations": len(evaluation_records),
        },
        "capsule_types": capsule_types,
    }
    write_json(destination / "manifest.json", manifest)
    return manifest


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Rebuild the public archive from an explicit Station data directory."
    )
    parser.add_argument(
        "--station-source-root",
        required=True,
        type=Path,
        help="Directory containing the allowlisted Station instance folders.",
    )
    args = parser.parse_args()
    station_source_root = args.station_source_root.expanduser().resolve()
    catalog_path = ROOT / "catalog.json"
    if not catalog_path.is_file() or not (ROOT / "artifacts").is_dir():
        raise FileNotFoundError("Canonical catalog or artifact directory is missing")
    canonical_catalog = json.loads(catalog_path.read_text(encoding="utf-8"))
    station_config = [
        {"id": item["id"], "title": item["title"]}
        for item in canonical_catalog.get("stations", [])
    ]
    if not station_config:
        raise ValueError("Canonical Station catalog is empty")
    artifact_manifests = canonical_catalog.get("artifacts", [])
    if not artifact_manifests:
        raise ValueError("Canonical artifact catalog is empty")
    missing_sources = [
        station_source_root / str(item["id"])
        for item in station_config
        if not (station_source_root / str(item["id"])).is_dir()
    ]
    if missing_sources:
        raise FileNotFoundError(
            "Missing Station source directories: "
            + ", ".join(str(path) for path in missing_sources)
        )

    # A rebuild is a complete snapshot, never an overlay: stale records must not
    # survive after an allowlist or source change. Verification artifacts are
    # canonical repository content and are deliberately preserved.
    if DATA_ROOT.exists():
        shutil.rmtree(DATA_ROOT)
    for generated_file in (ROOT / "catalog.json", ROOT / "security_findings.json"):
        if generated_file.exists():
            generated_file.unlink()
    DATA_ROOT.mkdir(parents=True, exist_ok=True)
    findings: list[dict[str, str]] = []
    station_manifests = []
    for item in station_config:
        print(f"Exporting Station {item['id']}...", flush=True)
        station_manifests.append(export_station(item, station_source_root, findings))

    if findings:
        write_json(ROOT / "security_findings.json", {"findings": findings})
        print(f"WARNING: {len(findings)} possible high-confidence secrets; see security_findings.json", flush=True)
    else:
        findings_path = ROOT / "security_findings.json"
        if findings_path.exists():
            findings_path.unlink()

    catalog = {
        "schema": "station-data-v2-static-archive-2",
        "stations": station_manifests,
        "artifacts": artifact_manifests,
        "scope": {
            "included": "Station metadata, agent dialogue histories, capsule records, and public research-submission evaluations",
            "excluded": "Room/service dialogue, research-center storage, coder sessions, multistart, temporal state, runtime locks, and unused Station instances",
        },
    }
    write_json(ROOT / "catalog.json", catalog)
    print(f"Exported {len(station_manifests)} Stations and preserved {len(artifact_manifests)} canonical artifact packages.", flush=True)


if __name__ == "__main__":
    main()
