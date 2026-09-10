#!/usr/bin/env python3
r"""Generate blueprint/lean_decls directly from \lean{...} commands.

This avoids the plasTeX/HTML build. Run from the repository root.
"""

from pathlib import Path
import re


def strip_tex_comments(text: str) -> str:
    lines: list[str] = []
    for line in text.splitlines():
        cut = len(line)
        for index, char in enumerate(line):
            if char != "%":
                continue
            backslashes = 0
            cursor = index - 1
            while cursor >= 0 and line[cursor] == "\\":
                backslashes += 1
                cursor -= 1
            if backslashes % 2 == 0:
                cut = index
                break
        lines.append(line[:cut])
    return "\n".join(lines)


def declarations(text: str, path: Path):
    position = 0
    while True:
        match = re.search(r"\\lean\s*\{", text[position:])
        if match is None:
            return
        start = position + match.end()
        depth = 1
        cursor = start
        while cursor < len(text) and depth:
            if text[cursor] == "{":
                depth += 1
            elif text[cursor] == "}":
                depth -= 1
            cursor += 1
        if depth:
            raise SystemExit(f"Unclosed \\lean{{...}} in {path}")
        body = text[start : cursor - 1]
        for raw_name in body.split(","):
            name = "".join(raw_name.split())
            if not name:
                continue
            if any(char in name for char in "\\{}"):
                raise SystemExit(f"Suspicious declaration in {path}: {name}")
            yield name
        position = cursor


root = Path.cwd()
source = root / "blueprint" / "src"
if not source.is_dir():
    raise SystemExit("Run this script from the epsilon_FML repository root")

all_names: list[str] = []
distinct_names: list[str] = []
seen: set[str] = set()

for tex_path in sorted(source.rglob("*.tex")):
    text = tex_path.read_text(encoding="utf-8")
    for name in declarations(strip_tex_comments(text), tex_path):
        all_names.append(name)
        if name not in seen:
            seen.add(name)
            distinct_names.append(name)

if not distinct_names:
    raise SystemExit("No \\lean{...} declaration references were found")

output = root / "blueprint" / "lean_decls"
output.write_text("\n".join(distinct_names) + "\n", encoding="utf-8")

print(
    f"Generated {len(distinct_names)} distinct declaration references "
    f"from {len(all_names)} occurrences in {output}"
)
