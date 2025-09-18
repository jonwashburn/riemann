#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")"/.. && pwd)"
cd "$ROOT_DIR"

TARGET_DIR="rh"

echo "[verify] Building project via lake..."
lake build >/dev/null

echo "[verify] Scanning for forbidden placeholders in $TARGET_DIR/*.lean"

FAIL=0
scan() {
  local pattern="$1"; local desc="$2"; local filter_comments="${3:-1}"
  local out
  if out=$(grep -RIn --include='*.lean' -E "$pattern" "$TARGET_DIR" 2>/dev/null); then
    # Optionally drop comment lines starting with '--' or '/-'
    if [[ "$filter_comments" -eq 1 ]]; then
      out=$(echo "$out" | grep -v -E "^[^:]+:[0-9]+:[[:space:]]*--|^[^:]+:[0-9]+:[[:space:]]*/-")
    fi
    if [[ -n "${out}" ]]; then
      echo "❌ Found $desc:"; echo "$out"; FAIL=1
    fi
  fi
}

# Code-only scan: strip Lean comments (line and block) before matching
scan_code() {
  local pattern="$1"; local desc="$2"
  while IFS= read -r -d '' file; do
    local out
    out=$(perl -0777 -pe 's{/-.+?-/(\s*)}{}gs; s{--.*$}{}mg' "$file" | grep -nE "$pattern" || true)
    if [[ -n "$out" ]]; then
      # Prefix with file path to mimic grep -RIn output
      echo "❌ Found $desc:"; echo "$out" | sed -e "s|^|$file:|"; FAIL=1
    fi
  done < <(find "$TARGET_DIR" -type f -name '*.lean' -print0)
}

scan_code "sorry|admit|Admitted|sorryAx" "explicit proof holes"
scan ": Prop := True" "Prop := True scaffolds"
scan_code "^[[:space:]]*(axiom|constant)\\b" "top-level axioms or constants"
scan "TODO|FIXME|ad hoc" "development markers"

# Extra strict checks for sneaky placeholders (code only)
scan_code "^[[:space:]]*abbrev[[:space:]]+\\w+[[:space:]]*:[[:space:]]*Prop[[:space:]]*:=[[:space:]]*True\\b" "abbrev : Prop := True"
scan_code "^[[:space:]]*opaque[[:space:]]+\\w+[[:space:]]*:[[:space:]]*Prop\\b" "opaque Prop declarations"
scan_code "\\bby[[:space:]]+admit\\b|\\badmitted\\b" "implicit admits via tactics"

if [[ $FAIL -eq 1 ]]; then
  echo "Verification FAILED."; exit 1
else
  echo "Verification PASSED: No forbidden placeholders or axioms found in $TARGET_DIR."
fi


