#!/usr/bin/env python3
import csv
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
rows = list(csv.DictReader((ROOT / "NODE_SPEC.csv").open(encoding="utf-8")))
errors = []
green = 0
LEAN_FILE_RE = re.compile(r"\\LeanFile\{([^{}]+)\}")


def implementation_files(row, tex):
    """Return the implementation unit explicitly declared by its TeX node."""
    entries = [entry.strip() for entry in LEAN_FILE_RE.findall(tex)]
    primary = row["lean_file"]
    if primary not in entries:
        errors.append(
            f"primary Lean file not listed in {row['tex_node']}: {primary}"
        )
    duplicate_entries = sorted({entry for entry in entries if entries.count(entry) > 1})
    for entry in duplicate_entries:
        errors.append(f"duplicate Lean file in {row['tex_node']}: {entry}")

    paths = []
    for entry in entries:
        relative = Path(entry)
        if relative.is_absolute() or ".." in relative.parts:
            errors.append(f"invalid Lean file path in {row['tex_node']}: {entry}")
            continue
        path = ROOT / relative
        if not path.is_file():
            errors.append(f"missing Lean file listed in {row['tex_node']}: {entry}")
            continue
        paths.append(path)
    return paths


for r in rows:
    primary_path = ROOT / r["lean_file"]
    if not primary_path.is_file():
        errors.append(f"missing primary Lean file: {r['lean_file']}")
    tex_path = ROOT / r["tex_node"]
    if not tex_path.is_file():
        errors.append(f"missing TeX node: {r['tex_node']}")
        continue
    tex = tex_path.read_text(encoding="utf-8")
    implementation_paths = implementation_files(r, tex)
    is_green = "\\leanok" in tex and "\\notready" not in tex
    if is_green:
        green += 1
        for path in implementation_paths:
            lean = path.read_text(encoding="utf-8")
            body = re.sub(r'/-.+?-/', '', lean, flags=re.S)
            if re.search(r'\bsorry\b|\badmit\b|\baxiom\b|:\s*PendingTask\b', body):
                relative = path.relative_to(ROOT)
                errors.append(f"green node still pending: {r['node']} ({relative})")
if errors:
    print("GREEN CHECK FAILED")
    for e in errors: print("-", e)
    raise SystemExit(1)
print(f"GREEN CHECK PASSED: {green} green node(s); no green node contains sorry/admit/axiom/PendingTask")
