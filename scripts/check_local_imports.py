#!/usr/bin/env python3
"""Verify that every project-local Lean import resolves to a checked-in file."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

IMPORT_RE = re.compile(r"(?m)^import\s+([^\s]+)")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("repo", type=Path)
    parser.add_argument("namespace")
    args = parser.parse_args()

    missing: list[tuple[Path, str, Path]] = []
    files = sorted(
        file for file in args.repo.rglob("*.lean") if ".lake" not in file.parts
    )
    prefix = args.namespace + "."
    for file in files:
        text = file.read_text(encoding="utf-8")
        for module in IMPORT_RE.findall(text):
            if module == args.namespace or module.startswith(prefix):
                expected = args.repo / (module.replace(".", "/") + ".lean")
                if not expected.is_file():
                    missing.append((file, module, expected))
    if missing:
        for file, module, expected in missing:
            print(f"{file}: unresolved local import {module} (expected {expected})")
        return 1
    print(f"OK: {len(files)} Lean files; all {args.namespace} imports resolve locally.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
