#!/usr/bin/env python3
"""Check `#print axioms` output against the repository trust boundary."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

REPORT_RE = re.compile(r"depends on axioms:\s*\[(.*?)\]", re.DOTALL)
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("report", type=Path)
    args = parser.parse_args()
    text = args.report.read_text(encoding="utf-8", errors="replace")
    if "sorryAx" in text:
        print("ERROR: axiom report contains sorryAx")
        return 1
    matches = REPORT_RE.findall(text)
    if not matches:
        print("ERROR: no '#print axioms' dependency report was found")
        return 1
    bad = False
    for index, payload in enumerate(matches, start=1):
        deps = {item.strip() for item in payload.replace("\n", " ").split(",") if item.strip()}
        extras = deps - ALLOWED
        print(f"Report {index}: {sorted(deps)}")
        if extras:
            bad = True
            print(f"ERROR: unexpected dependency or project axiom: {sorted(extras)}")
    if bad:
        return 1
    print("OK: every printed dependency is one of propext, Classical.choice, Quot.sound.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
