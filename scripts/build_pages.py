#!/usr/bin/env python3
"""Build the lightweight GitHub Pages frontend.

The full archive remains in the repository and is fetched from GitHub's raw-file
endpoint.  Keeping data/ and artifacts/ out of the Pages artifact avoids the
published-site size ceiling while retaining one canonical repository.
"""

from __future__ import annotations

import shutil
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "_site"
FILES = ("index.html", "README.md", "LICENSE", "NOTICE", "THIRD_PARTY_NOTICES.md", ".nojekyll")
DIRECTORIES = ("assets", "images")


def main() -> None:
    if OUTPUT.exists():
        shutil.rmtree(OUTPUT)
    OUTPUT.mkdir()
    for relative in FILES:
        source = ROOT / relative
        if source.is_file():
            shutil.copy2(source, OUTPUT / relative)
    for relative in DIRECTORIES:
        shutil.copytree(ROOT / relative, OUTPUT / relative)
    size = sum(path.stat().st_size for path in OUTPUT.rglob("*") if path.is_file())
    print(f"Built GitHub Pages frontend: {size / (1024 ** 2):.2f} MiB")


if __name__ == "__main__":
    main()
