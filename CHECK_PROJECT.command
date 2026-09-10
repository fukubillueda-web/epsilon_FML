#!/bin/bash
set -euo pipefail

export PATH="$HOME/.elan/bin:$HOME/.local/bin:/opt/homebrew/bin:$PATH"
PROJECT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec bash "$PROJECT_DIR/scripts/CHECK_PROJECT_STRICT.command"
