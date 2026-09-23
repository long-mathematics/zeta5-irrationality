#!/usr/bin/env python3
"""Reject proof placeholders and explicit axioms in project-owned Lean source.

This is a lexical source guard, not a kernel axiom audit. The endpoint still
requires an explicit `#print axioms` audit once it exists.
"""

import re
import subprocess
from pathlib import Path

FORBIDDEN = {"sorry", "admit", "axiom"}
IDENTIFIER = re.compile(r"[\w\u2080-\u209f][\w\u2080-\u209f'.]*", re.UNICODE)
CHARACTER = re.compile(r"'(?:[^'\\\n]|\\(?:u[0-9a-fA-F]{4}|x[0-9a-fA-F]{2}|.))'")
RAW_STRING = re.compile(r'r(#+)?"')


def violations(source):
    i = 0
    while i < len(source):
        if source.startswith("--", i):
            end = source.find("\n", i + 2)
            i = len(source) if end < 0 else end
        elif source.startswith("/-", i):
            start, depth = i, 1
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
                raise ValueError(f"line {source.count(chr(10), 0, start) + 1}: unclosed comment")
        elif source[i] == "«":
            end = source.find("»", i + 1)
            if end < 0:
                raise ValueError("unclosed escaped identifier")
            i = end + 1
        elif raw := RAW_STRING.match(source, i):
            terminator = '"' + (raw.group(1) or "")
            end = source.find(terminator, raw.end())
            if end < 0:
                raise ValueError("unclosed raw string")
            i = end + len(terminator)
        elif source[i] == '"':
            interpolated = i > 0 and source[i - 1] == "!"
            start = i + 1
            i += 1
            while i < len(source) and source[i] != '"':
                i += 2 if source[i] == "\\" else 1
            if i >= len(source):
                raise ValueError("unclosed string")
            if interpolated:
                for token in IDENTIFIER.finditer(source, start, i):
                    if token.group() in FORBIDDEN:
                        yield source.count("\n", 0, token.start()) + 1, token.group()
            i += 1
        elif char := CHARACTER.match(source, i):
            i = char.end()
        elif token := IDENTIFIER.match(source, i):
            if token.group() in FORBIDDEN:
                yield source.count("\n", 0, i) + 1, token.group()
            i = token.end()
        else:
            i += 1


def project_sources(root):
    result = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z", "--", "*.lean"],
        cwd=root,
    )
    return sorted({Path(name.decode()) for name in result.split(b"\0") if name
                   and not {".lake", ".git"}.intersection(Path(name.decode()).parts)})


def main():
    root = Path(subprocess.check_output(
        ["git", "rev-parse", "--show-toplevel"], text=True).strip())
    paths = project_sources(root)
    if not paths:
        raise SystemExit("Lean source audit failed: no project-owned Lean files found")
    errors = []
    for path in paths:
        try:
            errors.extend(f"{path}:{line}: forbidden Lean token '{token}'"
                          for line, token in violations((root / path).read_text(encoding="utf-8")))
        except (OSError, ValueError) as error:
            errors.append(f"{path}: {error}")
    if errors:
        raise SystemExit("Lean source audit failed:\n" + "\n".join(errors))
    print(f"Lean source audit passed: {len(paths)} files; no sorry, admit, or axiom declarations.")


if __name__ == "__main__":
    main()
