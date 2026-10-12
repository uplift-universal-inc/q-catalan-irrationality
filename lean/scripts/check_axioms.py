#!/usr/bin/env python3
"""Check fresh Lean axiom output and scan this project's delivered Lean sources.

The lexical source check ignores nested comments and string/character literals.
It is an additional gate; the transitive kernel axiom report is authoritative.
Downloaded dependencies under .lake are excluded from the source check, but
their axioms are included transitively in the public theorem reports.
"""

from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path
import os
import re
import sys


LEAN_ROOT = Path(__file__).resolve().parents[1]
AUDIT_SOURCE = LEAN_ROOT / "QCatalan" / "Audit.lean"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
REQUIRED_DECLARATIONS = {
    "QCatalan.irrational_xi",
    "QCatalan.irrational_qCatalan",
    "QCatalan.irrational_qBeta_two",
}
FORBIDDEN = re.compile(r"\b(?:sorry|sorryAx|admit|axiom|native_decide|unsafe)\b")
CHAR_LITERAL = re.compile(r"'(?:\\(?:u[0-9a-fA-F]{4}|x[0-9a-fA-F]{2}|.)|[^'\\\n])'")
RAW_STRING = re.compile(r'r(#+)?"')


def code_only(source: str) -> str:
    """Mask comments and literals, preserving offsets and line numbers."""
    result = list(source)

    def mask(start: int, end: int) -> None:
        for j in range(start, end):
            if result[j] != "\n":
                result[j] = " "

    i = 0
    while i < len(source):
        start = i
        if source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end == -1 else end
        elif source.startswith("/-", i):
            depth = 1
            i += 2
            while i < len(source) and depth:
                if source.startswith("/-", i):
                    depth += 1
                    i += 2
                elif source.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("unterminated block comment")
        else:
            # Apostrophes in Lean identifiers are not character delimiters.
            char = CHAR_LITERAL.match(source, i)
            raw = RAW_STRING.match(source, i)
            if char:
                i = char.end()
            elif raw and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] in "_'")):
                delimiter = '"' + (raw.group(1) or "")
                end = source.find(delimiter, raw.end())
                if end == -1:
                    raise ValueError("unterminated raw string")
                i = end + len(delimiter)
            elif source[i] == '"':
                i += 1
                while i < len(source):
                    if source[i] == "\\":
                        i += 2
                    elif source[i] == '"':
                        i += 1
                        break
                    else:
                        i += 1
                else:
                    raise ValueError("unterminated string")
            else:
                i += 1
                continue
        mask(start, min(i, len(source)))
    return "".join(result)


def scan_sources(root: Path = LEAN_ROOT) -> list[str]:
    errors = []
    paths = []
    for directory, children, files in os.walk(root):
        children[:] = [child for child in children if child not in {".lake", ".git"}]
        paths.extend(Path(directory) / name for name in files if name.endswith(".lean"))
    paths.sort()
    if not paths:
        return ["no project Lean sources found"]
    for path in paths:
        relative = path.relative_to(root)
        try:
            code = code_only(path.read_text(encoding="utf-8"))
        except ValueError as error:
            errors.append(f"{relative}: {error}")
            continue
        for match in FORBIDDEN.finditer(code):
            line = code.count("\n", 0, match.start()) + 1
            errors.append(f"{relative}:{line}: forbidden code token {match.group()!r}")
    if not errors:
        print(f"Source audit passed: {len(paths)} Lean files, no forbidden proof tokens.")
    return errors


def check_report(text: str, source: str) -> list[str]:
    expected = re.findall(r"^#print\s+axioms\s+(\S+)\s*$", code_only(source), re.MULTILINE)
    errors = []
    if not REQUIRED_DECLARATIONS <= set(expected):
        errors.append("audit source omits a required public irrationality theorem")
    if len(expected) != len(set(expected)):
        errors.append("audit source repeats an axiom query")
    if "sorryAx" in text:
        errors.append("the axiom output contains sorryAx")
    if re.search(r"\berror\s*:", text, re.IGNORECASE):
        errors.append("the axiom output contains a Lean error")

    rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
    rows += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", text)]
    counts = Counter(name for name, _ in rows)
    missing = set(expected) - counts.keys()
    unexpected = counts.keys() - set(expected)
    repeated = {name for name, count in counts.items() if count != 1}
    if missing:
        errors.append(f"missing axiom reports: {', '.join(sorted(missing))}")
    if unexpected:
        errors.append(f"unexpected axiom reports: {', '.join(sorted(unexpected))}")
    if repeated:
        errors.append(f"repeated axiom reports: {', '.join(sorted(repeated))}")
    for name, raw_axioms in rows:
        axioms = {item.strip() for item in raw_axioms.split(",") if item.strip()}
        extra = axioms - ALLOWED_AXIOMS
        if extra:
            errors.append(f"{name}: disallowed axioms: {', '.join(sorted(extra))}")
    if not errors:
        print(f"Kernel audit passed: {len(expected)} declarations; only "
              "propext, Classical.choice, and Quot.sound are permitted.")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", nargs="?", type=Path, help="fresh output of lean QCatalan/Audit.lean")
    parser.add_argument("--scan-only", action="store_true", help="run only the source-token gate")
    args = parser.parse_args()
    if args.scan_only == (args.log is not None):
        parser.error("provide either --scan-only or the fresh axiom log")
    errors = scan_sources()
    if args.log is not None:
        errors.extend(check_report(args.log.read_text(encoding="utf-8"),
                                   AUDIT_SOURCE.read_text(encoding="utf-8")))
    for error in errors:
        print(f"AUDIT FAILED: {error}", file=sys.stderr)
    return int(bool(errors))


if __name__ == "__main__":
    raise SystemExit(main())
