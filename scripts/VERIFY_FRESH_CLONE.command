#!/bin/bash
set -euo pipefail

export PATH="$HOME/.elan/bin:$HOME/.local/bin:/opt/homebrew/bin:$PATH"

SOURCE_REPO="${1:?usage: VERIFY_FRESH_CLONE.command SOURCE_REPO COMMIT [RESULT_ROOT]}"
COMMIT="${2:?usage: VERIFY_FRESH_CLONE.command SOURCE_REPO COMMIT [RESULT_ROOT]}"
RESULT_ROOT="${3:-$HOME/Developer/LeanProjects/_epsilon_FML_reproducibility}"

STAMP="$(date '+%Y%m%d-%H%M%S')"
SHORT="$(printf '%s' "$COMMIT" | cut -c1-12)"
RUN_DIR="$RESULT_ROOT/fresh-$SHORT-$STAMP"
CLONE="$RUN_DIR/epsilon_FML"
LOG="$RUN_DIR/fresh-reproduction.log"

mkdir -p "$RUN_DIR"

{
  echo "=== FML FRESH-CLONE REPRODUCTION ==="
  echo "time=$(date '+%Y-%m-%dT%H:%M:%S%z')"
  echo "source_repo=$SOURCE_REPO"
  echo "commit=$COMMIT"
  echo

  git clone --no-local --no-checkout "$SOURCE_REPO" "$CLONE"
  git -C "$CLONE" checkout --detach "$COMMIT"

  echo
  echo "=== EXACT CHECKOUT ==="
  git -C "$CLONE" rev-parse HEAD
  git -C "$CLONE" status --short
  echo

  cd "$CLONE"

  echo "=== TOOLCHAIN AND LOCKFILE ==="
  cat lean-toolchain
  shasum -a 256 lakefile.toml lake-manifest.json
  echo

  echo "=== OPTIONAL MATHLIB CACHE ==="
  if lake exe cache get; then
    echo "CACHE_GET_SUCCESS"
  else
    echo "CACHE_GET_SKIPPED_OR_FAILED; continuing with ordinary build"
  fi
  echo

  echo "=== STRICT PROJECT CHECK ==="
  bash scripts/CHECK_PROJECT_STRICT.command
  echo

  echo "=== FINAL CLEANLINESS ==="
  git status --short
  echo

  echo "FRESH_REPRODUCTION_SUCCESS"
} 2>&1 | tee "$LOG"

cp "$CLONE/lean-toolchain" "$RUN_DIR/"
cp "$CLONE/lakefile.toml" "$RUN_DIR/"
cp "$CLONE/lake-manifest.json" "$RUN_DIR/"
cp "$CLONE/blueprint/lean_decls" "$RUN_DIR/lean_decls"

{
  echo "commit=$COMMIT"
  echo "clone=$CLONE"
  echo "log=$LOG"
  echo
  shasum -a 256 \
    "$RUN_DIR/lean-toolchain" \
    "$RUN_DIR/lakefile.toml" \
    "$RUN_DIR/lake-manifest.json" \
    "$RUN_DIR/lean_decls" \
    "$LOG"
} > "$RUN_DIR/RESULTS.txt"

echo
echo "FRESH REPRODUCTION PASSED"
echo "Commit: $COMMIT"
echo "Results: $RUN_DIR"
echo "Log: $LOG"

if command -v open >/dev/null 2>&1; then
  open "$RUN_DIR"
fi
