#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

TARGETS=(
  rh.academic_framework.DiagonalFredholm.Determinant
  rh.RS.Det2Outer
  rh.RS.RouteB_Final
  rh.RS.RouteBPinnedRemovable
  rh.Proof.Main
)

for target in "${TARGETS[@]}"; do
  echo "[ci_routeB] building $target"
  lake build "$target"
  echo "[ci_routeB] $target ✅"
  echo
done
