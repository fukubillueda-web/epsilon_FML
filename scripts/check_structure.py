#!/usr/bin/env python3
import csv
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
rows = list(csv.DictReader((ROOT / "NODE_SPEC.csv").open(encoding="utf-8")))
keys = {r["node"] for r in rows}
errors = []
LEAN_FILE_RE = re.compile(r"\\LeanFile\{([^{}]+)\}")


def implementation_files(row, tex_text):
    """Return the implementation unit explicitly declared by its TeX node."""
    entries = [entry.strip() for entry in LEAN_FILE_RE.findall(tex_text)]
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

if len(rows) != 113:
    errors.append(f"expected 113 nodes, found {len(rows)}")
if len(keys) != len(rows):
    errors.append("duplicate node labels in NODE_SPEC.csv")

path_to_module = {r["node"]: r["lean_file"][:-5].replace("/", ".") for r in rows}
for r in rows:
    lean = ROOT / r["lean_file"]
    tex = ROOT / r["tex_node"]
    if not lean.is_file(): errors.append(f"missing Lean file: {r['lean_file']}")
    if not tex.is_file(): errors.append(f"missing TeX node: {r['tex_node']}")
    deps = [x for x in r["dependencies"].split(";") if x]
    for d in deps:
        if d not in keys: errors.append(f"unknown dependency {d} in {r['node']}")
    if tex.is_file():
        text = tex.read_text(encoding="utf-8")
        implementation_paths = implementation_files(r, text)
        implementation_texts = [
            path.read_text(encoding="utf-8") for path in implementation_paths
        ]
        implementation_text = "\n".join(implementation_texts)
        implementation_imports = {
            line
            for source_text in implementation_texts
            for line in source_text.splitlines()
            if line.startswith("import ")
        }
        short = r["primary_declaration"].split(".")[-1]
        if short not in implementation_text:
            errors.append(
                f"primary declaration anchor missing across implementation of "
                f"{r['lean_file']}: {short}"
            )
        for d in deps:
            imp = "import " + path_to_module[d]
            if imp not in implementation_imports:
                errors.append(
                    f"missing direct import across implementation of "
                    f"{r['lean_file']}: {imp}"
                )
        if f"\\label{{{r['node']}}}" not in text:
            errors.append(f"missing label in {r['tex_node']}")
        if f"\\lean{{{r['primary_declaration']}}}" not in text:
            errors.append(f"missing Lean link in {r['tex_node']}")

aggregator = ROOT / "LanglandsFirstMainLemma.lean"
if not aggregator.is_file() or "import LanglandsFirstMainLemma.Main" not in aggregator.read_text(encoding="utf-8"):
    errors.append("root aggregator does not import LanglandsFirstMainLemma.Main")

if errors:
    print("STRUCTURE CHECK FAILED")
    for e in errors: print("-", e)
    raise SystemExit(1)
lean_files = [
    p for p in ROOT.rglob("*.lean")
    if ".lake" not in p.parts and ".git" not in p.parts
]
print(
    f"STRUCTURE CHECK PASSED: {len(rows)} nodes, "
    f"{len(lean_files)} Lean files including root aggregator and subsidiary modules"
)
