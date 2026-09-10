#!/bin/bash
set -euo pipefail

export PATH="$HOME/.elan/bin:$HOME/.local/bin:/opt/homebrew/bin:$PATH"
PROJECT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$PROJECT_DIR"

if ! command -v lake >/dev/null 2>&1; then
  echo "ERROR: Lean/Lake is not installed or is not on PATH."
  echo "Install elan, then run this command again."
  exit 1
fi

if [ ! -f lake-manifest.json ]; then
  echo "ERROR: committed lake-manifest.json is missing."
  exit 1
fi

echo "=== epsilon_FML first setup ==="
echo "Project: $PROJECT_DIR"
echo "Toolchain: $(cat lean-toolchain)"
echo

if lake exe cache get; then
  echo "Mathlib cache downloaded."
else
  echo "Cache download was unavailable; continuing with the ordinary build."
fi

bash scripts/CHECK_PROJECT_STRICT.command

echo
echo "FIRST SETUP PASSED"
echo "The committed dependency manifest was used; lake update was not run."
