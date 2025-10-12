<!-- 026aed4d-daad-47ce-adf4-57d3b1bf6e45 9cd79fa8-7a96-4980-9bc7-c16576a40a05 -->
# Axiom Elimination Finish Plan

## Goals

- Reach a `lake build --no-sorry` that depends only on core mathlib axioms (`Classical.choice`, `propext`, `Quot.sound`).
- Replace every project-local axiom in `no-zeros/rh/RS/` and dependent modules with bona fide Lean proofs or citations to existing mathlib lemmas.
- Deliver an auditable closeout: refreshed status documentation, regenerated axiom report, and CI artifacts demonstrating the clean build.

## Current Snapshot

- Route B composition is stable; exports compile with the current reduced axiom footprint.
- Remaining axioms group into five families: Whitney covering, Poisson transport, removability/Hardy factorization, CR-Green bounds (Carleson and phase identities), and packaging/numeric witnesses.
- `BoundaryWedgeProof.lean` now proves `interior_positive_J_canonical`, shrinking the packaging obligations.

## Critical Buckets

1. **Whitney Geometry**: `whitney_to_ae_boundary`, `whitney_decomposition_exists`, dyadic covering lemmas.
2. **Poisson Transport**: `poisson_transport_interior`, `poisson_balayage`, `critical_atoms_nonneg` wiring.
3. **Removability & Hardy**: `removable_extension_at_xi_zeros`, `outer_transfer_preserves_positivity`, Hardy factorization helpers within `CertificateConstruction` and `OffZerosBridge`.
4. **CR-Green / Carleson**: `carleson_energy_bound`, `phase_velocity_identity`, `CR_green_upper_bound`, Vinogradov–Korobov constants.
5. **Packaging & Numerics**: `outer_exists` witnesses, analytic update lemmas, numeric inequalities (`upsilon_paper_lt_half`, `pi_gt_314`).

## Execution Roadmap

### Phase 1 — Baseline & Instrumentation (1 day)
- Regenerate the axiom inventory with `scripts/axiom_report.py`; capture results in `AXIOM_CLEANUP_STATUS.md`.
- Update `AXIOM_PUNCHLIST.md`, `SORRY_INVENTORY.md`, and `STANDARD_AXIOMS_CATALOG.md` to reflect the post-`interior_positive_J_canonical` state.
- Add a CI check for `lake build --no-sorry` (expected to fail initially) to monitor progress continuously.

### Phase 2 — Packaging & Numeric Cleanup (1–2 days)
- Replace `outer_exists`, `CRGreenOuterData_exists`, and related packaging axioms with the constructive witnesses already available (`OuterHalfPlane.ofModulus_det2_over_xi_ext_proved`, canonical positivity lemmas).
- Prove remaining arithmetic helpers (`upsilon_paper_lt_half`, `arctan_two_gt_one_point_one`, `pi_gt_314`) via `norm_num`, interval arithmetic, or verified computation.
- Re-run the axiom report to ensure only analytic families remain.

### Phase 3 — Removability & Hardy Factorization (2–3 days)
- Apply mathlib removable-singularity theorems to discharge `removable_extension_at_xi_zeros`, `analyticOn_update_from_pinned`, and overlapping axioms in `OffZerosBridge`.
- Import Hardy inner/outer factorization lemmas to remove `outer_transfer_preserves_positivity`, `hardy_factorization`, and `inner_function_property`.
- Add regression lemmas/tests to keep `CertificateConstruction` wiring stable under the new proofs.

### Phase 4 — Whitney Covering & Poisson Transport (3–4 days)
- Formalize dyadic Whitney decompositions in `WhitneyGeometryDefs`; prove countability, disjointness, and covering lemmas required downstream.
- Use the new decomposition to derive the a.e. boundary upgrade (`whitney_to_ae_boundary`).
- Compose Poisson kernel results from `HalfPlaneOuterV2` to obtain `poisson_balayage` and `poisson_transport_interior`, wiring them through `PPlusFromCarleson` and `BoundaryWedgeProof`.

### Phase 5 — CR-Green Bounds & Carleson Estimates (4–6 days)
- Implement quantitative `carleson_energy_bound` using documented Vinogradov–Korobov constants and the existing wedge closure framework.
- Formalize `CR_green_upper_bound`, `phase_velocity_identity`, and `critical_atoms_nonneg` via Green’s identity and CR-Green pairing lemmas.
- Cross-check with `RS/PinchWrappers.lean` to confirm downstream modules stay axiom-free.

### Phase 6 — Final Audit & Release (1–2 days)
- Run `lake build --no-sorry` and `lake env lean --run rh/Proof/AxiomsCheckLite.lean`; confirm zero project-local axioms.
- Refresh status documentation (`AXIOM_CLEANUP_STATUS.md`, `FINAL_STATUS.md`, README summary) and archive verification artifacts.
- Prepare publication/announcement materials (mathlib PR references, CI logs, release notes).

## Tracking Checklist

- [ ] Axiom inventory regenerated; status docs updated.
- [ ] Packaging and numeric axioms eliminated.
- [ ] Removability and Hardy axioms discharged.
- [ ] Whitney covering and Poisson transport formalized.
- [ ] CR-Green/Carleson bounds proved in Lean.
- [ ] `lake build --no-sorry` passes; axiom report clean.
- [ ] Final documentation and announcement prepared.

## Risks & Mitigations

- **Whitney ↔ Poisson coupling** is the longest pole; keep Route B axiomatizations in place until the proofs land to maintain green builds.
- **VK constant extraction** may need numerical libraries; coordinate with mathlib maintainers for reusable lemmas.
- Work on a feature branch with incremental `--no-sorry` checkpoints to avoid destabilizing the main proof pipeline.

