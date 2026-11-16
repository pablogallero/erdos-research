#!/usr/bin/env python3
"""Cheap source checks run in CI before `lake build` (stdlib only).

Palomar's source requirements (PalomarRegistry/PalomarSubmission, "Lean source requirements"):
* every regular `.lean` file outside `.git` and `.lake` starts with the `module` header
  (ordinary `--` and `/- -/` comments may precede it);
* at most 10,000 physical lines per file;
* no `.lean` symbolic links.

Project rules: no `sorry`, `native_decide` or `axiom` in the proofs (everything except
`Challenge.lean`, whose holes are deliberate and filled by `Solution.lean`).

Usage: python3 scripts/check-lean-sources.py [ROOT]
"""

import os
import re
import sys
from pathlib import Path

MAX_LINES = 10_000
SORRY_ALLOWED = {"Challenge.lean"}
FORBIDDEN = re.compile(r"\b(sorry|native_decide|axiom)\b")


def strip_comments(text: str) -> str:
    """Remove `--` line comments and (nested) `/- -/` block comments, including doc comments."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def has_module_header(text: str) -> bool:
    i = 0
    while i < len(text):
        if text[i] in " \r\n":
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j + 1
        elif text.startswith("/-", i) and not text.startswith(("/--", "/-!"), i):
            depth, i = 1, i + 2
            while depth and i < len(text):
                if text.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            if depth:
                return False
        else:
            return re.match(r"module(?![A-Za-z0-9_'!?.])", text[i:]) is not None
    return False


def physical_lines(text: str) -> int:
    if not text:
        return 0
    n = text.count("\n")
    return n if text.endswith("\n") else n + 1


def main() -> int:
    root = Path(sys.argv[1] if len(sys.argv) > 1 else ".").resolve()
    errors = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in (".git", ".lake")]
        for name in filenames:
            if not name.endswith(".lean"):
                continue
            path = Path(dirpath) / name
            rel = path.relative_to(root).as_posix()
            if path.is_symlink():
                errors.append(f"{rel}: symbolic link")
                continue
            text = path.read_text(encoding="utf-8")
            if rel != "lakefile.lean" and not has_module_header(text):
                errors.append(f"{rel}: missing `module` header")
            lines = physical_lines(text)
            if lines > MAX_LINES:
                errors.append(f"{rel}: {lines} lines > {MAX_LINES}")
            if rel not in SORRY_ALLOWED:
                for m in FORBIDDEN.finditer(strip_comments(text)):
                    errors.append(f"{rel}: forbidden `{m.group(1)}`")
    for e in errors:
        print(f"error: {e}")
    if not errors:
        print("Lean sources OK")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
