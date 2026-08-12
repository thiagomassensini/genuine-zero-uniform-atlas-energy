#!/usr/bin/env python3
"""Reject Markdown constructs that GitHub can misparse around LaTeX blocks."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SKIPPED_PARTS = {".git", ".lake"}
FENCE = re.compile(r"^ {0,3}(`{3,}|~{3,})(.*)$")
BAD_HEADING = re.compile(r"^#{1,6}[^ #]")
RAW_LATEX = re.compile(r"\\[A-Za-z]+")
DISALLOWED_MATH_MACRO = re.compile(r"\\operatorname\b")


def fail(path: Path, line_number: int, message: str) -> None:
    relative = path.relative_to(ROOT)
    raise SystemExit(
        f"GitHub Markdown check failed: {relative}:{line_number}: {message}"
    )


markdown_files = sorted(
    path
    for path in ROOT.rglob("*.md")
    if not SKIPPED_PARTS.intersection(path.relative_to(ROOT).parts)
)

math_blocks = 0

for path in markdown_files:
    open_fence_char: str | None = None
    open_fence_size = 0
    open_fence_line = 0
    open_fence_language = ""
    math_has_content = False

    for line_number, line in enumerate(path.read_text().splitlines(), start=1):
        fence = FENCE.match(line)

        if open_fence_char is not None:
            if fence is not None:
                marker, suffix = fence.groups()
                if (
                    marker[0] == open_fence_char
                    and len(marker) >= open_fence_size
                    and not suffix.strip()
                ):
                    if open_fence_language == "math" and not math_has_content:
                        fail(path, open_fence_line, "empty fenced math block")
                    open_fence_char = None
                    open_fence_size = 0
                    open_fence_line = 0
                    open_fence_language = ""
                    math_has_content = False
                    continue

            if open_fence_language == "math":
                if DISALLOWED_MATH_MACRO.search(line):
                    fail(
                        path,
                        line_number,
                        "GitHub rejects \\operatorname; use \\mathrm instead",
                    )
                if line.strip():
                    math_has_content = True
            continue

        if fence is not None:
            marker, suffix = fence.groups()
            open_fence_char = marker[0]
            open_fence_size = len(marker)
            open_fence_line = line_number
            open_fence_language = suffix.strip().split(maxsplit=1)[0]
            if open_fence_language == "math":
                math_blocks += 1
            continue

        if "$$" in line or "\\[" in line or "\\]" in line:
            fail(path, line_number, "use a fenced ```math block for display math")
        if "\\(" in line or "\\)" in line:
            fail(path, line_number, "use backticks for inline mathematical notation")
        if RAW_LATEX.search(line):
            fail(path, line_number, "LaTeX command appears outside a fenced math block")
        if re.fullmatch(r"=+", line.strip()):
            fail(path, line_number, "bare '=' can turn the preceding formula into a heading")
        if BAD_HEADING.match(line):
            fail(path, line_number, "ATX heading requires a space after '#'")

    if open_fence_char is not None:
        fail(path, open_fence_line, "unclosed fenced block")

if not markdown_files:
    raise SystemExit("GitHub Markdown check failed: no Markdown files found")
if math_blocks == 0:
    raise SystemExit("GitHub Markdown check failed: no fenced math blocks found")

print(
    f"GitHub Markdown check passed: {len(markdown_files)} files, "
    f"{math_blocks} fenced math blocks"
)
