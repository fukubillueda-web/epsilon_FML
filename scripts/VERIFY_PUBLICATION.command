#!/bin/bash
set -euo pipefail
export PATH="$HOME/.elan/bin:$HOME/.local/bin:/opt/homebrew/bin:$PATH"
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
mkdir -p verification
python3 scripts/check_publication_source.py | tee verification/source-check.txt
git rev-parse HEAD > verification/source-commit.txt
cp lean-toolchain lakefile.toml lake-manifest.json verification/
bash scripts/CHECK_PROJECT_STRICT.command 2>&1 | tee verification/project-check.txt
tmp_dir=$(mktemp -d)
trap 'rm -rf "$tmp_dir"' EXIT
printf '%s\n' 'import LanglandsFirstMainLemma.Main' '#print axioms LanglandsFirstMainLemma.firstMainLemma' > "$tmp_dir/Audit.lean"
lake env lean "$tmp_dir/Audit.lean" | tee verification/axioms.txt
python3 - <<'PYCODE'
import re
from pathlib import Path
text = Path('verification/axioms.txt').read_text()
match = re.search(r"'LanglandsFirstMainLemma.firstMainLemma' depends on axioms:\s*\[([^]]*)\]", text, re.S)
if not match:
    raise SystemExit('The final theorem axiom report was not found.')
axioms = {x.strip() for x in match.group(1).split(',') if x.strip()}
if axioms - {'propext', 'Classical.choice', 'Quot.sound'}:
    raise SystemExit('The final theorem has unexpected axioms.')
print('FINAL THEOREM AXIOM AUDIT PASSED')
PYCODE
lake env leanchecker --fresh LanglandsFirstMainLemma.Main 2>&1 | tee verification/kernel-check.txt
printf '%s\n' 'KERNEL RECHECK PASSED' >> verification/kernel-check.txt
git diff --exit-code -- . ':!blueprint/lean_decls'
printf '%s\n' 'PUBLICATION VERIFICATION PASSED' | tee verification/result.txt
