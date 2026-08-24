#!/usr/bin/env python3
"""Build the GitHub Pages frontend and verification bundles.

The full archive remains in the repository and is fetched from GitHub's raw-file
endpoint. Artifact folders are included only as downloadable ZIP bundles.
"""

from __future__ import annotations

import json
import shutil
import zipfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "_site"
FILES = ("index.html", "README.md", "LICENSE", "NOTICE", "THIRD_PARTY_NOTICES.md", ".nojekyll")
DIRECTORIES = ("assets", "images")


def build_bundles() -> tuple[int, int]:
    catalog = json.loads((ROOT / "catalog.json").read_text(encoding="utf-8"))
    bundle_root = OUTPUT / "bundles"
    bundle_root.mkdir()
    count = 0
    total = 0
    for artifact in catalog["artifacts"]:
        if artifact.get("hidden") or not artifact.get("notebooks"):
            continue
        artifact_id = artifact["id"]
        destination = bundle_root / f"{artifact_id}.zip"
        with zipfile.ZipFile(destination, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
            for record in artifact["files"]:
                relative = Path(record["path"])
                if relative.is_absolute() or ".." in relative.parts:
                    raise ValueError(f"Unsafe artifact path: {relative}")
                source = ROOT / "artifacts" / artifact_id / relative
                if not source.is_file():
                    raise FileNotFoundError(source)
                info = zipfile.ZipInfo((Path(artifact_id) / relative).as_posix(), date_time=(1980, 1, 1, 0, 0, 0))
                info.compress_type = zipfile.ZIP_DEFLATED
                info.external_attr = 0o100644 << 16
                archive.writestr(info, source.read_bytes(), compresslevel=9)
        count += 1
        total += destination.stat().st_size
    return count, total


def main() -> None:
    if OUTPUT.exists():
        shutil.rmtree(OUTPUT)
    OUTPUT.mkdir()
    for relative in FILES:
        source = ROOT / relative
        if source.is_file():
            shutil.copy2(source, OUTPUT / relative)
    for relative in DIRECTORIES:
        ignore = shutil.ignore_patterns("*.map") if relative == "assets" else None
        shutil.copytree(ROOT / relative, OUTPUT / relative, ignore=ignore)
    bundle_count, bundle_bytes = build_bundles()
    size = sum(path.stat().st_size for path in OUTPUT.rglob("*") if path.is_file())
    print(f"Built GitHub Pages frontend: {size / (1024 ** 2):.2f} MiB")
    print(f"Built {bundle_count} verification bundles: {bundle_bytes / (1024 ** 2):.2f} MiB")


if __name__ == "__main__":
    main()
