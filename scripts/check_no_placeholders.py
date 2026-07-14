#!/usr/bin/env python3
"""Comment-aware static audit of Lean source.

The scanner removes nested block comments, line comments, strings, and
character literals before reporting active `sorry`, `admit`, top-level `axiom`,
top-level `constant`, or `opaque` declarations. It is a source audit; `lake build` and
`#print axioms` remain the kernel-level checks.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path


def strip_noncode(src: str) -> str:
    out: list[str] = []
    i = 0
    n = len(src)
    block_depth = 0
    state = "code"
    while i < n:
        c = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if block_depth:
            if c == "/" and nxt == "-":
                block_depth += 1
                out.extend("  ")
                i += 2
            elif c == "-" and nxt == "/":
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue
        if state == "string":
            if c == "\\":
                out.append(" ")
                if i + 1 < n:
                    out.append("\n" if src[i + 1] == "\n" else " ")
                i += 2
            elif c == '"':
                out.append(" ")
                state = "code"
                i += 1
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue
        if state == "char":
            if c == "\\":
                out.append(" ")
                if i + 1 < n:
                    out.append(" ")
                i += 2
            elif c == "'":
                out.append(" ")
                state = "code"
                i += 1
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue
        if c == "-" and nxt == "-":
            out.extend("  ")
            i += 2
            while i < n and src[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if c == "/" and nxt == "-":
            block_depth = 1
            out.extend("  ")
            i += 2
            continue
        if c == '"':
            state = "string"
            out.append(" ")
            i += 1
            continue
        # A conservative character-literal test. Apostrophes inside Lean
        # identifiers are left alone.
        prev = src[i - 1] if i else " "
        if c == "'" and (prev.isspace() or prev in "([{,:="):
            state = "char"
            out.append(" ")
            i += 1
            continue
        out.append(c)
        i += 1
    if block_depth:
        raise ValueError("unterminated block comment")
    if state != "code":
        raise ValueError(f"unterminated {state} literal")
    return "".join(out)


PLACEHOLDER_RE = re.compile(r"\b(?:sorry|admit)\b")
AXIOM_RE = re.compile(r"(?m)^(?:(?:private|protected)\s+)?axioms?\b")
# `constant` can also introduce an assumption. Restrict to column zero so a
# structure field named `constant` is not misclassified.
CONSTANT_RE = re.compile(r"(?m)^(?:(?:private|protected)\s+)?constants?\s+[A-Za-z_«]")
OPAQUE_RE = re.compile(r"(?m)^(?:(?:private|protected)\s+)?opaque\s+[A-Za-z_«]")


def locations(text: str, regex: re.Pattern[str], kind: str, path: Path) -> list[dict]:
    found = []
    for match in regex.finditer(text):
        line = text.count("\n", 0, match.start()) + 1
        last_nl = text.rfind("\n", 0, match.start())
        column = match.start() - last_nl
        found.append({"kind": kind, "file": str(path), "line": line, "column": column})
    return found


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("paths", nargs="+", type=Path)
    parser.add_argument("--json", dest="json_path", type=Path)
    args = parser.parse_args()

    files: list[Path] = []
    for path in args.paths:
        if path.is_file() and path.suffix == ".lean":
            files.append(path)
        elif path.is_dir():
            files.extend(path.rglob("*.lean"))
    files = sorted(set(files))

    findings: list[dict] = []
    parse_errors: list[dict] = []
    for path in files:
        src = path.read_text(encoding="utf-8")
        try:
            code = strip_noncode(src)
        except ValueError as exc:
            parse_errors.append({"file": str(path), "error": str(exc)})
            continue
        findings.extend(locations(code, PLACEHOLDER_RE, "placeholder", path))
        findings.extend(locations(code, AXIOM_RE, "axiom", path))
        findings.extend(locations(code, CONSTANT_RE, "constant", path))
        findings.extend(locations(code, OPAQUE_RE, "opaque", path))

    counts = {
        "sorry_or_admit": sum(item["kind"] == "placeholder" for item in findings),
        "axiom_declarations": sum(item["kind"] == "axiom" for item in findings),
        "constant_declarations": sum(item["kind"] == "constant" for item in findings),
        "opaque_declarations": sum(item["kind"] == "opaque" for item in findings),
        "parse_errors": len(parse_errors),
    }
    report = {
        "files_scanned": len(files),
        "counts": counts,
        "findings": findings,
        "parse_errors": parse_errors,
    }
    if args.json_path:
        args.json_path.parent.mkdir(parents=True, exist_ok=True)
        args.json_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    print(f"Scanned {len(files)} Lean files.")
    print("Counts: " + ", ".join(f"{key}={value}" for key, value in counts.items()))
    for item in findings:
        print(f"{item['file']}:{item['line']}:{item['column']}: active {item['kind']}")
    for item in parse_errors:
        print(f"{item['file']}: {item['error']}")
    return 1 if findings or parse_errors else 0


if __name__ == "__main__":
    sys.exit(main())
