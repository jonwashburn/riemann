## Proof Track (Active)

- Entry: `rh/Proof/Active.lean`
  - Final export: `RH.Proof.Final.RiemannHypothesis_mathlib_from_pinch_ext_assign`
  - Core steps:
    - `RH_core` symmetry
    - `GlobalizeAcrossRemovable` (Schur pinch)
    - `RiemannHypothesis_from_pinch_ext_assign`

## Unconditional Export (Route B)

- Route: `rh/RS/RouteB_Final.lean`
  - Poisson rep on off-zeros; boundary positivity (P+)
  - Isolating neighborhoods; pinned u-trick; removable update
  - Certificate build: `buildPinchCertificate`
  - Conclusion: `RiemannHypothesis_via_RouteB`

- Export: `rh/Proof/Export.lean`
  - `@[simp] theorem RiemannHypothesis_unconditional : RiemannHypothesis`

## How to verify

```bash
cd riemann/no-zeros
./verify_proof.sh
```

- Builds active track, checks axioms, scans for forbidden constructs.
- Best-effort checks unconditional export.


