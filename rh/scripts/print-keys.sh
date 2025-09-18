#!/usr/bin/env bash
set -euo pipefail
echo "Key theorems:"
grep -n "^theorem RH\b" rh/Proof/Main.lean || true
grep -n "no_offcritical_zeros_from_schur\b" rh/RS/SchurGlobalization.lean || true
grep -n "ZetaNoZerosOnRe1FromSchur\b" rh/RS/SchurGlobalization.lean || true
grep -n "zeta_nonzero_re_eq_one\b" rh/academic_framework/EulerProductMathlib.lean || true
