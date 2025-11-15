# Route B Green Build Plan

## Goal

Green build exporting the Riemann Hypothesis unconditionally, with a robust Route B pipeline and no sorrys on the final path.

## High-level strategy

- Stabilize the core analytic/Poisson pipeline at the AF/RS seam while minimizing heavy dependencies.
- Prove only what the pipeline truly needs (boundary measurability and positivity), not broader global properties.
- Keep Route B thin: AF supplies identities and measurability; RS wires canonical outer, pinned/removable, and Poisson transport.

## Phased plan

### 1. Repository hygiene and baseline
- Confirm toolchain and mathlib versions; record hashes.
- Ensure there are no import cycles; keep `PoissonCayley` and `HalfPlaneOuterV2` as stable AF exports.
- Fence off heavy modules: keep `BoundaryWedgeProof` reduced to minimal exports; defer the full proof until after the green build.

### 2. Stage 1 – Boundary measurability and continuity
- In `rh/academic_framework/DiagonalFredholm/Determinant.lean`:
  - `det2_AF_boundary_hasUniformSumOnCompacts`: uniform bound on the boundary series on compact `t`-intervals using the existing cubic-tail bound.
  - `det2_AF_boundary_continuous`: continuity of `t ↦ det2_AF (1/2 + I t)` via the Weierstrass M-test.
- In `rh/RS/Det2Outer.lean`:
  - `det2_boundary_continuous`: deduced via `det2_eq_AF`.
  - `det2_boundary_measurable`: from `det2_boundary_continuous`.
  - `measurable_O`: reuse `measurable_O_witness` with `det2_boundary_measurable` and `CompletedXi.measurable_riemannXi_ext`.
  - `O_boundary_measurable`: `HalfPlaneOuterV2.measurable_comp_boundary _ measurable_O`.
- Already present: `xi_ext_boundary_measurable` (AF, via `measurable_riemannXi_ext`).
- Acceptance: `Determinant.lean` and `Det2Outer.lean` compile; `det2_boundary_measurable`, `O_boundary_measurable`, `xi_ext_boundary_measurable` are available.

### 3. Stage 2 – Route B wiring to Poisson
- In `rh/RS/RouteB_Final.lean`:
  - `F_pinch_has_poisson_rep`: satisfy measurability inputs with the three boundary lemmas; keep `theta_free_ReEqOn_offXi` via AF `PoissonCayley`.
- In `rh/RS/PinchWrappers.lean`:
  - `canonical_hasPoissonRepOn`: supply the three measurability lemmas plus the AF identity bridge; remove any `sorry`.
- Acceptance: `RouteB_Final.lean` and `PinchWrappers.lean` compile; `canonical_hasPoissonRepOn` is closed.

### 4. Stage 3 – Pinned/removable + u-trick
- Verify `rh/RS/RouteBPinnedRemovable.lean` builds.
- Ensure helper lemmas and the u-trick proof are trimmed and stable (simp bounds small, `EqOn → eventuallyEq` glued).
- Acceptance: file compiles with no new sorrys; public API unchanged.

### 5. Stage 4 – (P+) threading and positivity
- In `rh/RS/WhitneyAeCore.lean`: confirm the `(P+)` facade and `boundary_positive` export.
- In `rh/RS/RouteB_Final.lean`: reuse `boundary_positive_AF` and transport to interior positivity on `offXi`.
- Acceptance: `(P+) → BoundaryPositive → HasPoissonRepOn → interior positivity` chain compiles.

### 6. Stage 5 – Certificate and final export
- In `rh/RS/CertificateConstruction.lean` and `rh/Proof/Main.lean`:
  - Ensure `pinch_certificate_from_canonical`, `RH_from_PPlus_canonical`, and `RH_from_pinch_certificate` wire cleanly to `RiemannHypothesis`.
  - Keep domain conversions consistent (`offXi ⊆ Ω \\ {ξ = 0}`).
- Acceptance: final `RiemannHypothesis_of_PPlus` and `RiemannHypothesis_final` compile.

### 7. Stage 6 – Boundary wedge trimming (optional after green)
- Minimize `BoundaryWedgeProof` to only exports consumed by `(P+)`.
- Remove or guard heavy subproofs.

### 8. Stage 7 – Axiom/sorry audit
- Traverse the final dependency path of `RiemannHypothesis_final`; eliminate or relocate any `sorry`.
- Document remaining non-final modules as off-path.

### 9. Stage 8 – CI/branch seal
- Tag the stable commit; add a CI job to build only AF/RS/Proof final targets; reject regressions.

## Concrete additions/edits by file

- `rh/academic_framework/DiagonalFredholm/Determinant.lean`
  - `det2_AF_boundary_hasUniformSumOnCompacts` (aux bound)
  - `det2_AF_boundary_continuous : Continuous (fun t => det2_AF ((1/2 : ℝ) + I * (t : ℂ)))`
- `rh/RS/Det2Outer.lean`
  - `det2_boundary_continuous`
  - `det2_boundary_measurable`
  - `measurable_O`
  - `O_boundary_measurable`
- `rh/RS/RouteB_Final.lean`
  - Fill `hDet_meas`, `hO_meas`, `hXi_meas` with the above lemmas
- `rh/RS/PinchWrappers.lean`
  - Use the Route B façade and the three measurability lemmas for `canonical_hasPoissonRepOn`
- `rh/RS/RouteBPinnedRemovable.lean`
  - Confirm helper/u-trick proofs are trimmed; ensure no regression
- `rh/Proof/Main.lean`
  - Keep the final export stable; ensure no `open` or namespace resolution leaks

## Risk mitigation and alternates

- If uniform-convergence packaging becomes heavy, fall back to a boundary-only version:
  - Express `det₂(boundary t)` as the limit of continuous partial products (finite products over primes ≤ N).
  - Prove uniform convergence on compact `t`-intervals using the existing prime-sum bounds.
  - Conclude continuity via `TendstoUniformlyOn.compact → continuousLimit`, avoiding global measurability lemmas.
- If `RouteB_Final` strains imports, move tiny façade lemmas to AF and keep Route B very thin.

## Acceptance criteria

- `lake env lean` succeeds for:
  - `rh/academic_framework/Determinant.lean`, `rh/RS/Det2Outer.lean`
  - `rh/RS/RouteB_Final.lean`, `rh/RS/PinchWrappers.lean`
  - `rh/RS/RouteBPinnedRemovable.lean`, `rh/Proof/Main.lean`
- `RiemannHypothesis_final` compiles with no sorrys on the final path.
