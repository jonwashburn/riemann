<!-- 4b478d63-733f-428b-a862-ba964e981cf7 a48e9d98-60ec-44ca-872c-b35f6909dcd2 -->
# Plan for `boundary_positive_AF`

1. Reaffirm commitment: finish this proof, even if it spans weeks or months—no shelving until the axiom is gone.
2. Restate the lemma precisely inside `no-zeros/rh/RS/RouteB_Final.lean`, listing hypotheses and current gap to the desired AF boundary positivity.
3. Audit supporting lemmas (`boundary_positive_wedge`, `pplus_boundary_control`, Cayley transport facts) and note any missing prerequisites such as measurability or Poisson representations.
4. Sketch the Lean proof flow: introduce hypotheses, invoke wedge closure/PPlus results, transport to the AF boundary, and conclude positivity; flag where helper lemmas will live.
5. Cross-check analytic dependencies (`phase_velocity_identity`, `whitney_to_ae_boundary`, `pullback_hasPoissonRepOn_offXi`, etc.) to ensure they provide the needed data within the AF region, recording any additional obligations.
6. Identify the highest-risk subclaim (likely AF boundary transfer) and draft its precise statement; search for analogous lemmas to reuse rather than rebuilding theory.
7. Plan documentation and verification: once the proof is complete, update axiom reports and rerun `lake build`, noting any references to add.
8. Immediate next step: study the `PPlus` closure machinery already in `RouteB_Final.lean` to extract the exact boundary positivity statement required for the AF context.

### To-dos

- [x] Document the unwavering commitment to finish `boundary_positive_AF`, regardless of timeline. (Recorded 2025-10-13: maintain sustained focus until axiom eliminated.)
- [x] Restate `boundary_positive_AF` with all hypotheses and identify current proof gap. (Axiom currently states AF-boundary positivity of `2·J_pinch det2 O`; missing Lean proof connecting wedge closure → AF trace positivity.)
- [x] Catalog available wedge/PPlus/Cayley lemmas and mark missing prerequisites. (Have wrappers for `(P+) → BoundaryPositive` and Poisson transport; missing: `phase_velocity_identity`, `whitney_to_ae_boundary`, `pullback_hasPoissonRepOn_offXi`, measurability/analytic facts, pinned removable data.)
- [x] Outline Lean proof structure and place needed helper lemmas. (Skeleton: `BoundaryWedgeProof.PPlus_from_constants` → `PinchWrappers.boundaryPositive_of_PPlus` → `HalfPlaneOuterV2.poissonTransportOn` + `rs_boundary_eq_af`; helpers live in `RouteB_Final.lean`.)
- [x] Verify analytic prerequisites cover the AF region and list extra obligations. (Inputs identified; obligations enumerated above.)
- [x] Target the riskiest subclaim, draft its statement, and locate reusable analogues. (AF boundary transport mirrored by `PinchWrappers.boundaryPositive_of_PPlus`.)
- [x] Plan post-proof updates: axiom reports and `lake build`. (Run `lake build` from `no-zeros/`, execute `scripts/axiom_report.py`, refresh `AXIOM_PUNCHLIST.md`, `AXIOM_CLEANUP_STATUS.md`, `STANDARD_AXIOMS_CATALOG.md`.)
- [x] Read `PPlus` closure results in `RouteB_Final.lean` to prep for proof skeleton work. (Reviewed `boundary_positive` and wiring for AF boundary positivity.)
<!-- 4b478d63-733f-428b-a862-ba964e981cf7 a48e9d98-60ec-44ca-872c-b35f6909dcd2 -->
# Plan for `boundary_positive_AF`

1. Reaffirm commitment: finish this proof, even if it spans weeks or months—no shelving until the axiom is gone.
2. Restate the lemma precisely inside `no-zeros/rh/RS/RouteB_Final.lean`, listing hypotheses and current gap to the desired AF boundary positivity.
3. Audit supporting lemmas (`boundary_positive_wedge`, `pplus_boundary_control`, Cayley transport facts) and note any missing prerequisites such as measurability or Poisson representations.
4. Sketch the Lean proof flow: introduce hypotheses, invoke wedge closure/PPlus results, transport to the AF boundary, and conclude positivity; flag where helper lemmas will live.
5. Cross-check analytic dependencies (`phase_velocity_identity`, `whitney_to_ae_boundary`, `pullback_hasPoissonRepOn_offXi`, etc.) to ensure they provide the needed data within the AF region, recording any additional obligations.
6. Identify the highest-risk subclaim (likely AF boundary transfer) and draft its precise statement; search for analogous lemmas to reuse rather than rebuilding theory.
7. Plan documentation and verification: once the proof is complete, update axiom reports and rerun `lake build`, noting any references to add.
8. Immediate next step: study the `PPlus` closure machinery already in `RouteB_Final.lean` to extract the exact boundary positivity statement required for the AF context.

### To-dos

- [x] Document the unwavering commitment to finish `boundary_positive_AF`, regardless of timeline. (Recorded 2025-10-13: maintain sustained focus until axiom eliminated.)
- [x] Restate `boundary_positive_AF` with all hypotheses and identify current proof gap. (Axiom currently states AF-boundary positivity of `2·J_pinch det2 O`; missing Lean proof connecting wedge closure → AF trace positivity.)
- [ ] Catalog available wedge/PPlus/Cayley lemmas and mark missing prerequisites.
- [x] Outline Lean proof structure and place needed helper lemmas. (Lean skeleton: use `BoundaryWedgeProof.PPlus_from_constants` → `PinchWrappers.boundaryPositive_of_PPlus` → `HalfPlaneOuterV2.poissonTransportOn` and `rs_boundary_eq_af`; helper lemmas likely reside in `RouteB_Final.lean`.)
- [x] Verify analytic prerequisites cover the AF region and list extra obligations. (Needed inputs: `BoundaryWedgeProof.PPlus_from_constants`, `PinchWrappers.boundaryPositive_of_PPlus`, AF Cayley transport; outstanding obligations: prove `phase_velocity_identity`, `whitney_to_ae_boundary`, `pullback_hasPoissonRepOn_offXi`, measurability/analytic `det2`/`xi_ext`, pinned removable.)
- [x] Target the riskiest subclaim, draft its statement, and locate reusable analogues. (Critical gap: AF boundary positivity via `boundary_positive_AF` demands transporting `BoundaryWedgeProof.PPlus_from_constants` through `HalfPlaneOuterV2.boundary` equality; analogous proof skeleton in `PinchWrappers.boundaryPositive_of_PPlus`.)
- [x] Plan post-proof updates: axiom reports and `lake build`. (Post-proof tasks: run `lake build` from `no-zeros/`, execute `scripts/axiom_report.py`, refresh `AXIOM_PUNCHLIST.md`, `AXIOM_CLEANUP_STATUS.md`, `STANDARD_AXIOMS_CATALOG.md`, update `boundary.plan.md` log.)
- [x] Read `PPlus` closure results in `RouteB_Final.lean` to prep for proof skeleton work. (Reviewed `boundary_positive` theorem and related wiring to ensure transport path for AF boundary positivity.)

