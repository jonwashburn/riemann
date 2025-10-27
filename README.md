# Riemann Hypothesis — θ‑free Route B (unconditional)

This repository contains a Lean 4 formalization of an unconditional, θ‑free Route B pipeline concluding the Riemann Hypothesis. The active code lives under `riemann/no-zeros/`.

## Lean/Mathlib

- Lean: `leanprover/lean4:v4.12.0` (see `riemann/no-zeros/lean-toolchain`)
- Mathlib: `v4.12.0` (see `riemann/no-zeros/lakefile.lean`)

## Quick start

```bash
cd riemann/no-zeros
# Developer target (θ‑free closure for Route B)
lake build rh_routeb_dev

# Minimal export (θ‑free); produces the mathlib-equivalent RH export
lake build rh_export

# End‑to‑end verification (builds targets and runs unconditional guards)
./verify_proof.sh
```

## Final θ‑free targets

- `rh_routeb_dev`: developer target that isolates the unconditional Route B dependencies and AF Poisson facade. Default target in `riemann/no-zeros/lakefile.lean`.
- `rh_export`: minimal export surface used to expose the final theorem equivalence to mathlib.

The final export theorem is provided in `rh/Proof/Export.lean` under the alias:

- `@[simp] theorem RiemannHypothesis_unconditional : RiemannHypothesis`

## Guard policy (θ‑free)

`riemann/no-zeros/verify_proof.sh` builds the dev/export targets and enforces unconditional guards over their transitive closures:

- Forbids tokens: `sorry`, `admit`, `axiom`
- Bans imports tying to conditional/θ machinery: `rh.academic_framework.Theta`, `rh.academic_framework.MellinThetaZeta`, `rh.RS.CRGreenOuter*`, `rh.RS.sealed*`
- Bans legacy θ tokens: `boundaryToDisk_param`, `exp_I_two_arctan_ratio`, `two_arctan`, `arctan_ratio`

## Key files (θ‑free pipeline)

- AF Poisson facade: `rh/academic_framework/HalfPlaneOuterV2.lean`, `rh/academic_framework/CayleyAdapters.lean`, `rh/academic_framework/PoissonCayley.lean`
- Completed ξ: `rh/academic_framework/CompletedXi.lean`
- RS wiring: `rh/RS/WhitneyAeCore.lean`, `rh/RS/PPlusFromCarleson.lean`, `rh/RS/Det2Outer.lean`, `rh/RS/OffZerosBridge.lean`, `rh/RS/PinchWrappers.lean`, `rh/RS/RouteB_Final.lean`
- Export: `rh/Proof/Export.lean`

## Releasing

Tag convention for θ‑free milestones: `vX.Y.Z-theta-free` (e.g., `v1.0.0-theta-free`).


