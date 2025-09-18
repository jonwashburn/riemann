### Agents and Roles

- **RS (Schur globalization)**
  - File: `rh/RS/SchurGlobalization.lean`
  - Prove:
    - `Rect.isOpen_Ω`
    - `SchurOnRectangles`
    - `NoInteriorZeros`
    - `ZetaNoZerosOnRe1FromSchur`
  - Policy: If a required lemma is deep/missing in mathlib, continue implementation within RS where feasible; do not create separate blocker documents.

- **DF-WP (Weierstrass/product)**
  - Files: `rh/academic_framework/DiagonalFredholm/WeierstrassProduct.lean`, `ProductLemmas.lean`
  - Use: `Mathlib/Analysis/SpecialFunctions/Complex/LogBounds`, `HasProd/Multipliable`, `HasSum.cexp`.
  - Replace deprecated `tprod_*` and nonexistent `Complex.norm_log_one_sub_le`.

- **DF-Comp (Comprehensive)**
  - File: `rh/academic_framework/DiagonalFredholm/Comprehensive.lean`
  - Fix field-notation on predicates; add `[DecidableEq ι] [Countable ι]` only if required; switch to modern lemmas.

- **EPM (Euler product and ζ wrappers)**
  - File: `rh/academic_framework/EulerProductMathlib.lean`
  - Keep mathlib-backed facts: `riemannZeta_eulerProduct_tprod`, trivial zeros, `riemannZeta_ne_zero_of_one_lt_re`.
  - For `Re=1`, delegate to `RS.ZetaNoZerosOnRe1FromSchur` (implemented; no axioms).

 - **Cert-Kξ (Certificate Kξ + P+)**
   - File: `rh/Cert/KxiPPlus.lean`
   - Prove/Define:
     - `PPlus` boundary wedge predicate on the critical line.
     - Abstract Carleson box–energy interface and `KxiBound` (analytic Kξ bound).
     - Target statement shape `PPlusFromCarleson` (no axioms; statement only).
   - Policy: If Carleson energy, Poisson/CR–Green pairing, or VK zero-density are missing in mathlib, proceed within the track where feasible; do not create blocker logs.

### Global Rules
- Edit only your track files. No new axioms. No deletions or mass renames.
- On deep missing lemma: continue implementation within RS where feasible; avoid creating blocker logs.
- Build once, fix first error in your track; if next error is outside your track, STOP and report.
- Commit small, atomic changes with `fix(track-<name>): <short>`.

### Execution Plan and Dependencies

- RS → EPM: After `RS.ZetaNoZerosOnRe1FromSchur` is implemented and exported, EPM should expose `zeta_nonzero_re_eq_one` delegating to RS (no axioms).
- H′‑Cauchy → Factors: After the uniform `H′` strip bound exists, `rh/Cert/FactorsWitness.lean` should use `FEFactors_from_Hderiv (UniformHDerivBound.of_FGammaPrime ...)` (already scaffolded) so no fallback constants remain.
- Cert‑Kξ runs in parallel; it must not introduce axioms and should only add statements/interfaces.

### Additional Guidance per Agent (deliverables and acceptance)

- RS (Schur globalization)
  - Deliverables:
    - Implement: `Rect.isOpen_Ω`, `SchurOnRectangles`, `NoInteriorZeros`, `ZetaNoZerosOnRe1FromSchur` with no `admit`/`sorry`.
    - Ensure the removable‑singularity bridge used by the pinch is present in `rh/RS/SchurGlobalization.lean` or nearby RS context files.
  - Acceptance:
    - Compiles with no new axioms; only RS track files edited.
    - `ZetaNoZerosOnRe1FromSchur` is available for EPM to import.

- EPM (Euler product and ζ wrappers)
  - Deliverables:
    - Expose `zeta_nonzero_re_eq_one (z : ℂ) (hz : z.re = 1)` delegating to `RS.ZetaNoZerosOnRe1FromSchur` once provided by RS.
    - Remove any `admit`/`sorry` in this module; keep mathlib‑only reasoning here.
  - Acceptance:
    - No axioms; mathlib imports only; builds after RS export is available.

- H′‑Cauchy (Archimedean derivative bound)
  - Files: `rh/academic_framework/GammaBounds.lean`, `rh/Cert/FactorsWitness.lean`
  - Objectives:
    - Prove a uniform bound on `‖H′(s)‖` for `H(s)=π^{-s/2}Γ(s/2)` on the closed strip `σ ∈ [σ0,1]`, `σ0>1/2`, via a Cauchy circle of radius `r = σ0/2`.
    - Produce a Prop/lemma equivalent to `BoundedFGammaPrimeOnStrip σ0` giving an explicit `C ≥ 0`.
    - Wire that constant into `UniformHDerivBound.of_FGammaPrime` so `factors_witness` uses `FEFactors_from_Hderiv`.
  - Inputs: see `gamma-bounds-gpt5.txt` for the intended argument outline; prefer mathlib facts (Cauchy estimate on circles, cpow modulus, basic Γ vertical‑strip bounds).
  - Acceptance:
    - No new axioms; compiles in this track.

- Cert‑Kξ (Certificate Kξ + P+)
  - Deliverables:
    - Define `PPlus` (boundary wedge predicate) and `KxiBound` (Carleson box–energy interface), Prop‑level is acceptable.
    - Add the statement `PPlusFromCarleson` with precise hypotheses (no axioms; statement only).
    - Update any destructuring to the current `BoundedFGammaPrimeOnStrip` nested `Exists` if referenced here.
  - Acceptance:
    - Compiles; no axioms; only this file edited.

---

### Context status (what exists now)
- RS off‑zeros bridge and assignment path are implemented (`rh/RS/OffZerosBridge.lean`, `rh/RS/SchurGlobalization.lean`) and EPM delegates `zeta_nonzero_re_eq_one` to RS.
- Pinned‑limit at ξ‑zeros is available via the u‑trick in `OffZerosBridge` (consumed by RS; no axioms).
- Γ‑derivative bound path is wired; FactorsWitness uses the H′ route.

### New agents to complete the RH boundary‑certificate route (silo’d)

- **RS‑CRGreen (CR–Green pairing + outer cancellation)**
  - File: `rh/RS/CRGreenOuter.lean`
  - Deliverables:
    - Whitney–box CR–Green pairing for analytic `J`, tested against a Poisson field; scale‑invariant remainder control.
    - Outer cancellation on the boundary: phase LHS unchanged; RHS uses `∇(U − Re log O)`.
  - Outputs (names suggested):
    - `CRGreen_pairing_whitney`
    - `outer_cancellation_on_boundary`
  - Acceptance: no `sorry`; mathlib only; compiles standalone.

- **RS‑PoissonPlateau (uniform plateau constant)**
  - File: `rh/RS/PoissonPlateau.lean`
  - Deliverables: printed even window `ψ` and proof that `c0(ψ)>0`, i.e.
    `inf_{0<b≤1, |x|≤1} (P_b * ψ)(x) ≥ c0`.
  - Output: `poisson_plateau_c0 (psi) : 0 < c0 psi`
  - Acceptance: no `sorry`; compiles.

- **RS‑AdmissibleWindows (atom‑safe windows + energy)**
  - File: `rh/RS/AdmissibleWindows.lean`
  - Deliverables: define admissible mass‑1 windows with small “holes” at atoms; prove fixed‑aperture uniform Poisson energy bound on `Q(α'I)`.
  - Outputs: `AdmissibleWindow`, `poisson_energy_bound_for_admissible`
  - Acceptance: no `sorry`; compiles.

- **RS‑H1BMO (windowed H^1–BMO/Carleson bound)**
  - File: `rh/RS/H1BMOWindows.lean`
  - Deliverables: Fefferman–Stein style inequality giving a Whitney‑uniform bound for the windowed phase functional `Mψ` from a box Carleson bound.
  - Output: `windowed_phase_bound_of_carleson`
  - Acceptance: no `sorry`; compiles.

- **Cert‑Kξ‑Interface (Prop‑level Kξ bound)**
  - File: `rh/Cert/KxiWhitney.lean`
  - Deliverables: define `KxiBound (α c) : Prop` for Whitney‑box Carleson finiteness of `Uξ := Re log ξ`; provide `C_box^{(ζ)} := K0 + Kξ` adapter consumed by RS.
  - Outputs: `KxiBound`, `Cbox_zeta_of_Kxi`
  - Acceptance: no `sorry`; statement‑level only; compiles.

- **Cert‑Kξ‑RvM (prove Kξ from RvM short‑interval counts)**
  - File: `rh/Cert/KxiWhitney_RvM.lean`
  - Deliverables: formalize short‑interval zero counts (Riemann–von Mangoldt) on Whitney length `L ≍ c/log⟨T⟩`; prove `∬_{Q(αI)} |∇Uξ|^2 σ ≤ Cξ |I|`; export `KxiBound`.
  - Outputs: `rvM_short_interval_bound`, `kxi_whitney_carleson_of_rvm : KxiBound α c`
  - Acceptance: no `sorry`; unconditional; compiles.

- **RS‑BoundaryWedge (assemble (P+) and Schur off‑zeros)**
  - File: `rh/RS/BoundaryWedge.lean`
  - Dependencies: RS‑CRGreen, RS‑PoissonPlateau, RS‑AdmissibleWindows, RS‑H1BMO, and either Cert‑Kξ‑Interface or Cert‑Kξ‑RvM.
  - Deliverables: prove (P+) from plateau lower bound + CR–Green upper bound + `C_box^{(ζ)}`; Poisson → Herglotz and Cayley → Schur on `Ω \ Z(ξ)`.
  - Outputs: `PPlus_of_certificate`, `schur_off_zeros_of_PPlus`
  - Acceptance: no `sorry`; compiles with provided deps.

- **RS‑Globalization‑Final (pinch + RH wrapper)**
  - Files: reuse `rh/RS/SchurGlobalization.lean`, `rh/Proof/Main.lean`
  - Dependencies: RS‑BoundaryWedge.
  - Deliverables: removable singularities + pinch to rule out off‑critical zeros; add top‑level RH theorem (zeros lie on `Re s = 1/2`).
  - Outputs: `no_offcritical_zeros_from_schur`, `theorem RH`
  - Acceptance: no `sorry`; compiles.

- **Lint/Docs sweep**
  - Files: touched RS/EPM/Cert files
  - Deliverables: replace unnecessary `simpa` with `simp`; remove unused variables; short docstrings for public lemmas; README snippet: invoking RS export and RH wrapper.
  - Acceptance: clean build; no semantic changes.

### Parallelization and handoffs
- Parallel starts: RS‑CRGreen, RS‑PoissonPlateau, RS‑AdmissibleWindows, RS‑H1BMO, Cert‑Kξ‑Interface.
- Cert‑Kξ‑RvM is siloed (mathlib + ζ/ξ only). RS‑BoundaryWedge depends on the RS blocks + Kξ.
- RS‑Globalization‑Final depends only on RS‑BoundaryWedge.
- Lint/Docs can run incrementally or at the end.

### Acceptance Checklist (per task)

- Builds cleanly; no new `admit`/`sorry` introduced by your edits.
- No axioms added; mathlib‑only imports.
- Public names and signatures match Objectives so downstream modules can import them.
 
