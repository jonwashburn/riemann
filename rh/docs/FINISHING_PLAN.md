## Finishing Plan (Unconditional RS/EPM Route)

### Clarifications from the written proof (`rh/Riemann-lean-verified.tex`)
- The boundary wedge (P+) can be proved directly from the product certificate via CR–Green pairing + Carleson box energy, without any AI negativity selection. This is the “Whitney‑uniform wedge closure” route: phase–velocity identity → plateau lower bound → CR–Green pairing bound with outer cancellation and box‑energy bookkeeping → quantitative wedge on Whitney intervals → local‑to‑global a.e. wedge.
- Names/ingredients mirrored in RS:
  - CR–Green packaging: `CRGreen_pairing_whitney_from_green_trace`, `outer_cancellation_on_boundary`, `local_pairing_bound_*` (file `rh/rh/RS/CRGreenOuter.lean`).
  - Plateau: `poisson_plateau_c0` and lower bound (file `rh/rh/RS/PoissonPlateau.lean`).
  - Box‑energy for the paired field is exactly the ξ‑side energy after outer cancellation (cf. written lemma “outer energy bookkeeping”); in RS this is encoded via the concrete Carleson witness (Kξ) and the pairing adapters.
  - Whitney overlap and local Carleson: `carleson_local_on_shadow`, `bounded_shadow_overlap_sum` (file `rh/rh/RS/TentShadow.lean`).
  - Endgame: finite‑sum coercivity wrapper `GlobalWhitneyCoercivityPkg` → `(P+)` (file `rh/rh/RS/BoundaryWedge.lean`).

### Policy (non‑negotiable)
- **Unconditional**: mathlib‑only; no new axioms; no placeholders.
- **Scope of edits**: only RS/EPM/Cert track files explicitly listed below.
- **Build rule**: build often; fix the first error in RS; if the next error is outside RS, stop and report.
- **Commits**: small, atomic, e.g. `fix(track-rs): finish coercivity→(P+) wiring`.

### Critical path (must be proved/finished)
1) Finish coercivity → (P+) in `rh/rh/RS/BoundaryWedge.lean` (no stubs), choosing one of two unconditional constructions:
   - Option A — AI‑based (shortest change set, matches existing scaffolding):
     - Replace the fabricated `HasNegativityWindowPoisson` witness and empty family with the real chain:
       1) Negativity window from `RS.negativity_window_poisson_kappaStar_of_AI`.
       2) CZ capture to a finite, disjoint Whitney family (`RS.cz_stopping_capture_finset_of_hasSum`).
       3) Per‑shadow coercivity from CR–Green pairing + plateau (`CRGreen_pairing_whitney_from_green_trace`; `poisson_plateau_c0`) or `whitney_plateau_coercivity_from_closeness`.
       4) Local Carleson on shadows + bounded overlap (`carleson_local_on_shadow`, `bounded_shadow_overlap_sum`).
       5) Algebraic finite‑sum endgame (`GlobalWhitneyCoercivityPkg` → `(P+)`).
   - Option B — Direct Whitney‑uniform wedge closure (as in the written proof, no AI):
       1) Use outer cancellation/bookkeeping so the paired field’s box energy is the ξ‑side energy controlled by Kξ.
       2) CR–Green pairing bound + plateau lower bound on each Whitney interval.
       3) Quantitative wedge on Whitney intervals with a uniform smallness parameter `Υ(c) < 1/2` (Whitney schedule choice).
       4) Local‑to‑global a.e. wedge on the whole boundary (within `ae_nonneg_from_whitney_pairing_and_plateau`).
       5) Keep the same CZ/overlap/endgame packaging if you prefer a finite‑family presentation.
   - In either option, update callers to the finished coercivity proof (no placeholders):
     `whitney_carleson_coercivity_aepos` (base), `whitney_carleson_coercivity_aepos_AI` (AI variant),
     `ae_nonneg_from_whitney_pairing_and_plateau`, and `localWedge_from_pairing_and_uniformTest`.

2) Boundary → interior → Schur glue (must compile)
   - Keep `PPlus_of_certificate` unchanged but ensure it composes with the finished `(P+)` pipeline.
   - Poisson transport: use `HasHalfPlanePoissonTransport` and provided wrappers in `BoundaryWedge.lean` to pass `(P+)` to interior nonnegativity on `Ω`.
   - Cayley → Schur: use `schur_off_zeros_of_PPlus` (and `Theta_Schur_offXi_from_*`) to obtain a Schur bound off zeros.

3) RS globalization and EPM export (must compile)
   - In `rh/RS/SchurGlobalization.lean`, ensure these are proved and exported without `sorry`:
     - `Rect.isOpen_Ω`, `SchurOnRectangles`, `NoInteriorZeros`, `ZetaNoZerosOnRe1FromSchur`.
   - In `rh/academic_framework/EulerProductMathlib.lean`, expose
     `zeta_nonzero_re_eq_one` delegating to `RS.ZetaNoZerosOnRe1FromSchur`.

### Optional improvements (not blockers)
- `rh/rh/RS/Det2Outer.lean`: implement `det2` concretely (Euler/fredholm), wired to pinch wrappers.
- `rh/rh/RS/AdmissibleWindows.lean`: replace Poisson‑energy placeholders with the actual bound for admissible windows.
- `rh/rh/RS/H1BMOWindows.lean`: fill Fefferman–Stein constants used by the windowed phase bound.

### Execution procedure (loop each iteration)
1) Read this plan and the todo list; pick the next pending critical‑path item.
2) Decide Option A (AI) or Option B (direct wedge) for coercivity→(P+); prefer A unless you aim to mirror the written proof exactly. Mark the chosen item `in_progress`, implement the edit (RS first), and build (`lake build`).
3) Fix the first RS error; if the next error is outside RS, stop and report.
4) Update the todo list: mark completed, add follow‑ups if needed.
5) Keep changes small and self‑contained; avoid creating new interfaces unless necessary.
6) Repeat until all “Critical path” and “RS globalization/EPM” items are complete and the project builds cleanly.

### Acceptance checklist
- No new axioms; mathlib‑only; no placeholders remain in the finished coercivity step.
- `(P+)` is obtained unconditionally via the real coercivity chain (AI negativity + CZ capture + CR–Green + plateau + Carleson + overlap + endgame).
- Poisson transport and Cayley steps compile; Schur bound holds on the required sets.
- `RS.SchurGlobalization` exports are present and used by EPM; `zeta_nonzero_re_eq_one` delegates to RS.
- Full build succeeds; lints/docs adjusted for touched files.


