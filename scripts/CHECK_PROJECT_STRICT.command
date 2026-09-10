#!/bin/bash
set -euo pipefail

export PATH="$HOME/.elan/bin:$HOME/.local/bin:/opt/homebrew/bin:$PATH"

PROJECT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$PROJECT_DIR"

lake build
python3 scripts/check_structure.py
python3 scripts/validate_graph.py
python3 scripts/check_before_green.py
python3 scripts/generate_blueprint_lean_decls.py
lake exe checkdecls blueprint/lean_decls

echo "STRICT PROJECT CHECK PASSED"
