# Route B Green Build Plan

## Goal

Green build exporting the Riemann Hypothesis unconditionally, with a robust Route B pipeline and no sorrys on the final path.

## High-level strategy

- Stabilize the core analytic/Poisson pipeline at the AF/RS seam while minimizing heavy dependencies.
- Prove only what the pipeline truly needs (boundary measurability and positivity), not broader global properties.
- Keep Route B thin: AF supplies identities and measurability; RS wires canonical outer, pinned/removable, and Poisson transport.

## Phased plan

### 0. Triage and build gating (current focus)
- **Deduplicate `BoundaryWedgeProof.lean`:** remove the later `abbrev KernelDecayBudgetSucc …` block (around lines 1797–1808) and keep the earlier structure definition; drop the duplicated `C_cross_default` definition/lemma near the end of the file.
- **Centralize default constants:** move `A_default`, `B_default`, `Cdiag_default`, `C_cross_default` into an early “Defaults” section or a tiny imported file so they are defined before use throughout Route B.
- **Fence placeholder “AXIOM” lemmas:** keep the heavy CR/Green/residue placeholders in a namespace or sealed file that Stage 1 does not import. Only the minimal exports consumed by Stage 1–3 should remain on the active path.
- **Scoped CI target:** add a `lake` target (or script) that rebuilds only `rh/academic_framework/DiagonalFredholm/Determinant.lean` and `rh/RS/Det2Outer.lean` so Stage 1 can stay green while the wedge file is trimmed.
- **Commit discipline:** land Stage 1 in three tight commits: (1) determinant boundary rewrites; (2) Det2Outer measurability; (3) BoundaryWedgeProof dedupe/fencing with no other edits.

### 1. Repository hygiene and baseline
- Confirm toolchain and mathlib versions; record hashes.
- Ensure there are no import cycles; keep `PoissonCayley` and `HalfPlaneOuterV2` as stable AF exports.
- Fence off heavy modules: keep `BoundaryWedgeProof` reduced to minimal exports; defer the full proof until after the green build.

### 2. Stage 1 – Boundary measurability and continuity
- Normalize the critical-line helper lemmas to use literal `1/2` exponents and keep the supporting `rewriter` lemmas off the global simp set. Whenever the `2⁻¹` form is needed, apply the dedicated helper (`two_pow_neg_one_half_lt_one`, `prime_pow_neg_one_half_lt_one`, etc.) instead of letting `simp` bounce between the shapes. This prevents the recursion loops we were seeing in `Determinant.lean`.
- Re-run `lake build rh.academic_framework.DiagonalFredholm.Determinant` to confirm the determinant layer is green before wiring RS.
- Update `rh/RS/Det2Outer.lean` so `det2_boundary_continuous`, `det2_boundary_measurable`, `measurable_O`, and `O_boundary_measurable` are proved by the new `det2_AF_twoInv_*` wrappers, keeping all statements in the literal `(2⁻¹ + I·t)` shape.
- Defer any further `BoundaryWedgeProof` edits until after the RS layer consumes the wrappers; only reopen that file once Stage 1b is complete.
- In `rh/academic_framework/DiagonalFredholm/Determinant.lean`:
  - `det2_AF_boundary_hasUniformSumOnCompacts`: uniform bound on the boundary series on compact `t`-intervals using the existing cubic-tail bound together with the normalized rewrite helpers.
  - `det2_AF_boundary_continuous`: continuity of `t ↦ det2_AF (1/2 + I t)` via the Weierstrass M-test, reusing the helpers verbatim instead of reconstructing the algebraic bounds inline.
  - `det2_AF_twoInv_eq_exp_tsum` / `det2_AF_twoInv_continuous`: lightweight wrappers obtained from the boundary lemmas by a single `boundaryPoint_eq_two_inv` rewrite so RS can consume literal `(2⁻¹ + I·t)` statements without reopening the analytic proofs.
- In `rh/RS/Det2Outer.lean`:
  - `det2_boundary_continuous`: deduced via `det2_eq_AF`.
  - `det2_boundary_measurable`: from `det2_boundary_continuous`.
  - `measurable_O`: reuse `measurable_O_witness` with `det2_boundary_measurable` and `CompletedXi.measurable_riemannXi_ext`.
  - `O_boundary_measurable`: `HalfPlaneOuterV2.measurable_comp_boundary _ measurable_O`.
- Already present: `xi_ext_boundary_measurable` (AF, via `measurable_riemannXi_ext`).
- Acceptance: `Determinant.lean` and `Det2Outer.lean` compile; `det2_boundary_measurable`, `O_boundary_measurable`, `xi_ext_boundary_measurable` are available.

Status:
- AF determinant boundary layer is green; RS `Det2Outer` is wired to the two‑inv wrappers and builds.
- `RouteB_Final` has an internal “auto‑measurability” path for the pinch boundary trace, so callers don’t need to thread those explicitly.

Next steps (quick):
- Keep AF/RS green via the scoped targets:
  - `lake build rh.academic_framework.DiagonalFredholm.Determinant`
  - `lake build rh.RS.Det2Outer rh.RS.RouteB_Final`

### 3. Stage 2 – Route B wiring to Poisson
- In `rh/RS/RouteB_Final.lean`:
  - `F_pinch_has_poisson_rep`: satisfy measurability inputs with the three boundary lemmas; keep `theta_free_ReEqOn_offXi` via AF `PoissonCayley`.
- In `rh/RS/PinchWrappers.lean`:
  - `pinch_certificate_from_canonical` / `RH_from_PPlus_canonical`: expose the Poisson-representation witness as an explicit argument (`hRepOn`) so the Route B façade can be plugged in without re-proving measurability.
- Acceptance: `RouteB_Final.lean` and `PinchWrappers.lean` compile; the canonical wrappers accept an explicit `HasPoissonRepOn` parameter instead of relying on an implicit lemma.

Status:
- `F_pinch_has_poisson_rep` now has a convenience wrapper that internally supplies boundary measurability from AF/RS exports, leaving only the θ‑free identity and `Det2OnOmega` as inputs.
- `PinchWrappers.lean` builds with the canonical wrappers parameterized by `hRepOn`.

Next steps:
- Verify and keep green:
  - `lake build rh.RS.RouteB_Final rh.RS.PinchWrappers`
- Thread the actual `RouteB_Final.F_pinch_has_poisson_rep` export (with its `Det2OnOmega`/θ‑free identity inputs) into the canonical wrappers when those hypotheses are ready.

### 4. Stage 3 – Pinned/removable + u-trick
- Verify `rh/RS/RouteBPinnedRemovable.lean` builds.
- Ensure helper lemmas and the u-trick proof are trimmed and stable (simp bounds small, `EqOn → eventuallyEq` glued).
- Acceptance: file compiles with no new sorrys; public API unchanged.

Status:
- `rh/RS/RouteBPinnedRemovable.lean` builds (only upstream warnings remain); no new proof debt on the Route B side.

Next steps:
- Keep the target green via `lake build rh.RS.RouteBPinnedRemovable` whenever the pinned-removable lemmas change.
- Once the canonical Poisson witness is finalized, thread it through the pinned-data helpers so downstream callers don’t need to reopen Route B.

Next steps:
- Build and fix any drift:
  - `lake build rh.RS.RouteBPinnedRemovable`
- Ensure pinned data wrappers consume `RouteB_Final.canonical_hasPoissonRepOn` (no direct boundary‑measurability threading).

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
  - Keep the canonical wrappers thin by threading the Route B Poisson witness via the new `hRepOn` parameter.
- `rh/RS/RouteBPinnedRemovable.lean`
  - Confirm helper/u-trick proofs are trimmed; ensure no regression
- `rh/Proof/Main.lean`
  - Keep the final export stable; ensure no `open` or namespace resolution leaks

## Risk mitigation and alternates

- Keep Stage 1 green by gating Route B updates behind the scoped CI target until `Determinant.lean` and `Det2Outer.lean` both build locally.
- If duplicate/remnant definitions remain in `BoundaryWedgeProof.lean`, move them into `RS/sealed/` so they cannot break the main build path.
- If uniform-convergence packaging becomes heavy, fall back to a boundary-only version:
  - Express `det₂(boundary t)` as the limit of continuous partial products (finite products over primes ≤ N).
  - Prove uniform convergence on compact `t`-intervals using the existing prime-sum bounds.
  - Conclude continuity via `TendstoUniformlyOn.compact → continuousLimit`, still keeping the rewrite helper lemmas local to the boundary proof.
- If `RouteB_Final` strains imports, move tiny façade lemmas to AF and keep Route B very thin.

## Acceptance criteria

- `lake env lean` succeeds for:
  - `rh/academic_framework/Determinant.lean`, `rh/RS/Det2Outer.lean`
  - `rh/RS/RouteB_Final.lean`, `rh/RS/PinchWrappers.lean`
  - `rh/RS/RouteBPinnedRemovable.lean`, `rh/Proof/Main.lean`
- `RiemannHypothesis_final` compiles with no sorrys on the final path.
