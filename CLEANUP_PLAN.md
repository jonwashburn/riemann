# Riemann Route B Cleanup & Release Plan

## Goal
Ensure the public repository builds and exports the unconditional Route B proof cleanly, with documentation, CI, and layout aligned to the active track under `riemann/no-zeros`.

## Current State
- The unconditional export already builds: `cd riemann/no-zeros && ./verify_proof.sh` succeeds.
- `rh/RS/PPlusFromCarleson.lean` re-exports `RH.RS.BoundaryWedgeProof.PPlus_from_constants`, so the active proof depends on `BoundaryWedgeProof`.
- `WhitneyInterval` is defined in `rh/Cert/KxiPPlus.lean`; forward-reference errors arise only when building the legacy copy under `riemann/riemann/`.
- Legacy subtree `riemann/riemann/` still contains work-in-progress files (`BWP/*.lean`) including a `sorry`.

## Problem Summary
1. Duplicate project tree causes contributors to build the wrong codebase and see stale errors.
2. Documentation claims the dev/export track excludes `BoundaryWedgeProof`, which contradicts current imports.
3. No automated guard ensures contributors run `verify_proof.sh` before publishing changes.
4. Optional: `BoundaryWedgeProof.lean` is a monolithic file; some prefer a split for readability, but the current proof typechecks.

## Plan of Record

### 1. Align to a Single Source of Truth
- Move `riemann/riemann/` to `archive/legacy/` (or delete if history is preserved elsewhere).
- Update project README to point only to `riemann/no-zeros` as the active Lean package.

### 2. Fix Documentation
- Edit `README.md` and `riemann/no-zeros/PROOF_TRACK.md` to state that `PPlusFromCarleson` imports `BoundaryWedgeProof`.
- Remove text claiming `BoundaryWedgeProof` is excluded from the dev closure.
- Note the canonical `verify_proof.sh` guard in "Quick start" instructions.

### 3. Continuous Integration Guard
- Add a GitHub Actions workflow (e.g., `.github/workflows/verify.yml`) running:
  ```bash
  cd riemann/no-zeros
  ./verify_proof.sh
  ```
- Collect script output, fail on any `sorry/admit/axiom` or banned import detection.

### 4. Version Consistency
- Ensure only one `lean-toolchain` and `lakefile.lean` are active (the ones in `riemann/no-zeros`).
- Document Lean and mathlib versions in README (currently Lean 4.13.0, mathlib v4.13.0).

### 5. Optional Hygienic Improvements
- Consider splitting `BoundaryWedgeProof.lean` into logical submodules (`BWP/Definitions`, `BWP/AnnularEnergy`, `BWP/WedgeClosure`) once the main cleanup lands.
- Provide minimal comments near `PPlus_canonical_proved` explaining where the wedge proof lives.

### 6. Release
- After CI passes, tag the repository following the θ-free convention (e.g., `vX.Y.Z-theta-free`).
- Announce that the verified export `@[simp] theorem RiemannHypothesis_unconditional : RiemannHypothesis` is available.

## Next Actions
1. Archive or relocate the legacy subtree.
2. Update README and proof summary docs.
3. Add CI workflow invoking `verify_proof.sh`.
4. (Optional) Schedule refactor of `BoundaryWedgeProof`. 
5. Prepare release tag once guard is green.
