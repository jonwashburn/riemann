#!/usr/bin/env bash

set -euo pipefail

REPO_ROOT=$(git rev-parse --show-toplevel 2>/dev/null || pwd)
HOOKS_DIR="$REPO_ROOT/.git/hooks"
SRC_HOOK="$REPO_ROOT/hooks/pre-commit"
DST_HOOK="$HOOKS_DIR/pre-commit"

if [ ! -f "$SRC_HOOK" ]; then
  echo "Hook source not found: $SRC_HOOK" >&2
  exit 1
fi

mkdir -p "$HOOKS_DIR"
chmod +x "$SRC_HOOK"

if [ -e "$DST_HOOK" ] && [ ! -L "$DST_HOOK" ]; then
  echo "Backing up existing hook to $DST_HOOK.bak"
  mv "$DST_HOOK" "$DST_HOOK.bak"
fi

ln -sf "$SRC_HOOK" "$DST_HOOK"
echo "Installed pre-commit hook: $DST_HOOK → $(realpath "$SRC_HOOK" 2>/dev/null || echo "$SRC_HOOK")"

exit 0


