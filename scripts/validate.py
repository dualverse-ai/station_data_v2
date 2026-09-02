#!/usr/bin/env python3
"""Validate archive integrity, public scope, and static-site dependencies."""

from __future__ import annotations

import gzip
import hashlib
import json
import re
from pathlib import Path
from urllib.parse import quote, unquote
import yaml


ROOT = Path(__file__).resolve().parents[1]
SPOTLIGHT_ARCHIVES = json.loads((ROOT / "config" / "spotlight_archives.json").read_text(encoding="utf-8"))
FORBIDDEN_PARTS = {
    "storage",
    "multistart",
    "temporal_chat",
    "backup",
    "_temp",
    "coder_sessions",
    "evaluators",
    "tmp",
}
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
ENVIRONMENT_THINKING_REFERENCE = re.compile(
    rb"(?i)\b(?:openai\s+codex|claude\s+code|(?-i:Anthropic)|codex_home|"
    rb"codex\s+(?:cli|shell|coding\s+agent|tool|tools|tool\s+calls))\b|\.codex(?:/|\\)"
)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def assert_no_secret(data: bytes, path: Path) -> None:
    for label, pattern in SECRET_PATTERNS.items():
        assert not pattern.search(data), f"possible {label} in {path}"


def active_messages(metadata: dict[str, object]) -> list[dict[str, object]]:
    messages = metadata.get("messages") if isinstance(metadata.get("messages"), list) else []
    return [message for message in messages if isinstance(message, dict) and not message.get("is_deleted")]


def contains_environment_thinking(raw: bytes) -> bool:
    lines = raw.splitlines(keepends=True)
    index = 0
    while index < len(lines):
        if not lines[index].startswith(b"thinking_content:"):
            index += 1
            continue
        end = index + 1
        while end < len(lines) and (lines[end].startswith((b" ", b"\t")) or not lines[end].strip()):
            end += 1
        normalized = re.sub(rb"\s+", b" ", b"".join(lines[index:end]))
        lowered = normalized.lower()
        if ENVIRONMENT_THINKING_REFERENCE.search(normalized) or (b"codex format" in lowered and b"tool calls" in lowered):
            return True
        index = end
    return False


def contains_environment_reference(raw: bytes) -> bool:
    normalized = re.sub(rb"\s+", b" ", raw)
    lowered = normalized.lower()
    return bool(
        ENVIRONMENT_THINKING_REFERENCE.search(normalized)
        or (b"codex format" in lowered and b"tool calls" in lowered)
    )


def expected_mail_recipients(metadata: dict[str, object]) -> list[str]:
    recipients = metadata.get("recipients")
    if isinstance(recipients, list):
        return [str(recipient) for recipient in recipients if str(recipient).strip()]
    if isinstance(recipients, str) and recipients.strip():
        return [recipients.strip()]
    return []


def expected_reviewer_score(metadata: dict[str, object]) -> float | None:
    for message in reversed(active_messages(metadata)):
        content = str(message.get("content") or "")
        if "Reviewer Evaluation" not in content:
            continue
        match = re.search(r"\*\*Score:\*\*\s*([0-9]+(?:\.[0-9]+)?)\s*/\s*10", content)
        if match:
            return float(match.group(1))
    return None


def main() -> None:
    catalog = json.loads((ROOT / "catalog.json").read_text(encoding="utf-8"))
    assert catalog["schema"] == "station-data-v2-static-archive-2"
    assert len(catalog["stations"]) == 16
    assert len(catalog["artifacts"]) == 14
    assert [item["id"] for item in catalog["artifacts"] if item.get("hidden")] == ["misc"]

    exported_paths = [path for path in (ROOT / "data").rglob("*") if path.is_file()]
    expected_data_paths: set[Path] = set()
    exported_bytes = 0
    for path in exported_paths:
        relative_parts = set(path.relative_to(ROOT / "data").parts)
        assert not (relative_parts & FORBIDDEN_PARTS), path
        assert not path.name.endswith(".lock"), path
        size = path.stat().st_size
        exported_bytes += size
        assert size < 100_000_000, f"file exceeds GitHub's 100 MB threshold: {path}"

    history_count = 0
    capsule_count = 0
    evaluation_count = 0
    for station in catalog["stations"]:
        print(f"Validating Station {station['id']}...", flush=True)
        station_root = ROOT / "data" / station["id"]
        expected_data_paths.add(station_root / "manifest.json")
        manifest = json.loads((station_root / "manifest.json").read_text(encoding="utf-8"))
        assert manifest == station

        expected_data_paths.add(station_root / "agents" / "index.json")
        agent_index = json.loads((station_root / "agents" / "index.json").read_text(encoding="utf-8"))
        assert len(agent_index["agents"]) == station["counts"]["agents"]
        for agent in agent_index["agents"]:
            key = agent["key"]
            assert unquote(key) == key, f"browser-decoded agent key differs: {key}"
            assert quote(key, safe="-._~") == key, f"agent key is not URL-path safe: {key}"
            agent_root = station_root / "agents" / key
            expected_data_paths.add(agent_root / "dialogue" / "index.json")
            assert (agent_root / "dialogue" / "index.json").is_file(), agent_root

        for history_index in station_root.glob("agents/*/dialogue/index.json"):
            expected_data_paths.update(history_index.parent / page["file"] for page in json.loads(history_index.read_text(encoding="utf-8"))["pages"])
            history_count += 1
            record = json.loads(history_index.read_text(encoding="utf-8"))
            reconstructed = b"".join(
                gzip.decompress((history_index.parent / page["file"]).read_bytes())
                for page in record["pages"]
            )
            assert len(reconstructed) == record["exported_bytes"]
            assert digest(reconstructed) == record["exported_sha256"]
            assert_no_secret(reconstructed, history_index)
            assert record["format"] == "dialogue-yamll-v2"
            assert record["removed_metadata"] == ["provider transport metadata", "host-tool metadata"]
            assert not contains_environment_thinking(reconstructed), history_index
            assert not contains_environment_reference(reconstructed), history_index

        expected_data_paths.add(station_root / "capsules" / "index.json")
        capsule_index = json.loads((station_root / "capsules" / "index.json").read_text(encoding="utf-8"))
        assert len(capsule_index["capsules"]) == station["counts"]["capsules"]
        capsule_count += len(capsule_index["capsules"])
        capsule_keys = set()
        archive_ids = {str(item["id"]).casefold() for item in capsule_index["capsules"] if item["type"] == "archive"}
        expected_spotlights = {f"archive_{number}" for number in SPOTLIGHT_ARCHIVES.get(station["id"], [])}
        actual_spotlights = {
            str(item["id"]).casefold()
            for item in capsule_index["capsules"]
            if item["type"] == "archive" and item.get("spotlight")
        }
        assert actual_spotlights == expected_spotlights, (station["id"], actual_spotlights, expected_spotlights)
        for capsule in capsule_index["capsules"]:
            assert capsule["key"] not in capsule_keys, f"duplicate capsule key: {capsule['key']}"
            capsule_keys.add(capsule["key"])
            expected_data_paths.add(station_root / capsule["file"])
            raw = gzip.decompress((station_root / capsule["file"]).read_bytes())
            assert len(raw) == capsule["bytes"]
            assert digest(raw) == capsule["sha256"]
            assert_no_secret(raw, station_root / capsule["file"])
            metadata = yaml.safe_load(raw.decode("utf-8")) or {}
            if capsule["type"] in {"public", "private", "mail", "question"}:
                assert capsule.get("reply_count") == max(0, len(active_messages(metadata)) - 1)
            if capsule["type"] == "mail":
                assert capsule.get("recipients") == expected_mail_recipients(metadata)
            if capsule["type"] == "archive":
                assert capsule.get("reviewer_score") == expected_reviewer_score(metadata)
                assert isinstance(capsule.get("spotlight"), bool)
                citations = capsule.get("citations")
                assert isinstance(citations, list) and len(citations) == len(set(citations))
                assert str(capsule["id"]).casefold() not in citations
                assert all(citation in archive_ids for citation in citations), (capsule["id"], citations)
            if capsule["type"] == "question":
                status = str(metadata.get("question_status") or "pending").strip().lower()
                expected_status = status if status in {"pending", "open", "redacted", "solved", "retired"} else "pending"
                assert capsule.get("question_status") == expected_status
                assert capsule.get("question_net_upvote") == int(metadata.get("question_net_upvote") or 0)
                assert capsule.get("question_solved_by_message_id") == metadata.get("question_solved_by_message_id")

        expected_data_paths.add(station_root / "evaluations" / "index.json")
        evaluation_index = json.loads((station_root / "evaluations" / "index.json").read_text(encoding="utf-8"))
        assert len(evaluation_index["evaluations"]) == station["counts"]["evaluations"]
        evaluation_count += len(evaluation_index["evaluations"])
        evaluation_keys = set()
        for evaluation in evaluation_index["evaluations"]:
            key = evaluation["key"]
            assert key not in evaluation_keys, f"duplicate evaluation key: {key}"
            evaluation_keys.add(key)
            assert unquote(key) == key and quote(key, safe="-._~") == key
            path = station_root / evaluation["file"]
            expected_data_paths.add(path)
            raw = gzip.decompress(path.read_bytes())
            assert len(raw) == evaluation["bytes"]
            assert digest(raw) == evaluation["sha256"]
            assert_no_secret(raw, path)
            public_record = yaml.safe_load(raw.decode("utf-8")) or {}
            assert set(public_record) == {"instruction", "result"}, path
            assert all(isinstance(public_record[key], str) for key in ("instruction", "result")), path

    assert set(exported_paths) == expected_data_paths, "unreferenced or missing Station export files"

    artifact_files = 0
    artifact_bytes = 0
    expected_artifact_paths: set[Path] = set()
    for artifact in catalog["artifacts"]:
        print(f"Validating artifact {artifact['id']}...", flush=True)
        for record in artifact["files"]:
            path = ROOT / "artifacts" / artifact["id"] / record["path"]
            expected_artifact_paths.add(path)
            assert path.is_file(), path
            assert path.stat().st_size < 100_000_000, f"artifact exceeds GitHub's 100 MB threshold: {path}"
            assert path.stat().st_size == record["bytes"]
            artifact_bytes += path.stat().st_size
            artifact_data = path.read_bytes()
            assert digest(artifact_data) == record["sha256"]
            assert_no_secret(artifact_data, path)
            artifact_files += 1
    actual_artifact_paths = {path for path in (ROOT / "artifacts").rglob("*") if path.is_file()}
    assert actual_artifact_paths == expected_artifact_paths, "unreferenced or missing artifact files"

    required = [
        "index.html",
        "assets/app.css",
        "assets/app.js",
        "assets/knowledge-graph.js",
        "assets/vendor/marked.umd.js",
        "assets/vendor/js-yaml.min.js",
        "assets/vendor/purify.min.js",
        "assets/vendor/katex/katex.min.js",
        "assets/vendor/katex/katex.min.css",
        "assets/vendor/marked-katex.umd.js",
    ]
    for relative in required:
        assert (ROOT / relative).is_file(), relative

    pages_files = [ROOT / relative for relative in (
        "index.html", "README.md", "LICENSE", "NOTICE", "THIRD_PARTY_NOTICES.md", ".nojekyll"
    )]
    pages_files.extend(path for directory in (ROOT / "assets", ROOT / "images") for path in directory.rglob("*") if path.is_file())
    support_files = pages_files + [
        path for directory in (ROOT / "scripts", ROOT / "config", ROOT / ".github")
        for path in directory.rglob("*") if path.is_file() and "__pycache__" not in path.parts
    ]
    for path in support_files:
        assert path.stat().st_size < 100_000_000, f"repository file exceeds GitHub's 100 MB threshold: {path}"
    pages_bytes = sum(path.stat().st_size for path in pages_files if path.is_file())
    assert pages_bytes < 1_000_000_000, "GitHub Pages frontend exceeds the 1 GB published-site ceiling"

    assert not (ROOT / "security_findings.json").exists(), "possible secrets require review"
    repository_bytes = (
        exported_bytes
        + artifact_bytes
        + sum(path.stat().st_size for path in set(support_files))
    )
    print(
        f"PASS: 16 Stations, {history_count} agent histories, {capsule_count} capsules, "
        f"{evaluation_count} research submissions, and {artifact_files} artifact files verified"
    )
    print("PASS: no forbidden research-storage or runtime paths were exported")
    print(f"PASS: lightweight Pages deployment is {pages_bytes / (1024 ** 2):.2f} MiB")
    print(f"Archive payload: {repository_bytes / (1024 ** 3):.2f} GiB")
    if repository_bytes >= 1_000_000_000:
        print("NOTICE: source repository exceeds GitHub's recommended 1 GB size; Pages deploys only the lightweight frontend")


if __name__ == "__main__":
    main()
