## Objective

Make the final `RH` export unconditional by internalizing the remaining analysis for the right half‑plane route and wiring it into existing pinch/Schur infrastructure.

## Current state (key artifacts)

- RS: `J_pinch`, `Θ_pinch_of`, Cayley→Schur wrappers; boundary modulus lemmas (`|J_pinch|=1` on Re=1/2; hence `|Re F_pinch|≤2` on the boundary); `J_pinch_analytic_on_offXi_choose`.
- AF: right half‑plane primitives, kernel `poissonKernel`, transport `P`, subset representation/transport; integrability lemmas; on‑subset pinch transport; wrapper for the Poisson identity (delegating to representation).
- Proof: wrappers assembling certificate → (P+) → transport → Schur → RH; a variant `RiemannHypothesis_from_certificate_rep_on` that still takes a boundary equality `re_eq`.
- Det₂: interface `Det2OnOmega`; assumed packer `det2_on_Ω_assumed` is present; concrete witness not provided.

## Remaining gaps to be unconditional

1) Self‑contained Poisson identity for the right half‑plane (`Re(F)(z)` equals Poisson integral of boundary `Re(F)`) under: `S⊆Ω`, `F` analytic on `S`, boundary `Re(F(1/2+it))` L¹_loc and globally bounded by 2.
2) Refactor `pinch_representation_on_offXi` to derive the boundary equality internally via (1) with `M=2`; drop the `re_eq` parameter.
3) Update final wrapper in `Proof/Main.lean` to call the refactored builder (no `re_eq`), set `M := 2`, and finish via existing pinch ingredients.
4) Provide (or package) `Det2OnOmega` for `det2` on `Ω`. If a proof is unavailable, use `det2_on_Ω_assumed` until the analytic/nonvanishing facts are supplied.

## File‑by‑file plan

### rh/rh/academic_framework/HalfPlaneOuter.lean
- Add a self‑contained lemma `poisson_formula_re_for_halfplane_analytic` using our kernel, integrability lemmas, and dominated convergence for `S⊆Ω`.
- Refactor `pinch_representation_on_offXi` to:
  - Use `J_pinch_analytic_on_offXi_choose` for analyticity.
  - Use `integrable_boundary_kernel_of_bounded'` (M=2) for integrability.
  - Derive `re_eq` via `poisson_formula_re_for_halfplane_analytic`.

### rh/rh/RS/Cayley.lean
- Already provides `J_pinch_analytic_on_offXi_choose` and boundary modulus lemmas; no change beyond ensuring all callers use the choose‑outer specialization.

### rh/rh/RS/Det2Outer.lean
- If available, add `det2_on_Ω_proved : Det2OnOmega`.
- Otherwise, use existing `det2_on_Ω_assumed` at call sites until a proof exists.

### rh/rh/Proof/Main.lean
- Update `RiemannHypothesis_from_certificate_rep_on` to:
  - Call the refactored `pinch_representation_on_offXi` (no `re_eq`), with `M := 2`.
  - Use `F_pinch_Plus_from_certificate` to obtain `(P+)`.
  - Use on‑subset transport → Cayley→Schur off zeros → pinch ingredients to conclude `RiemannHypothesis`.

## Milestones / DoD

- M1: Poisson identity lemma implemented and used by `pinch_representation_on_offXi` (no external `re_eq`).
- M2: Final wrapper updated, lints clean, and compiles (if build infra is present).
- M3: `RH` theorem proven using only internal hypotheses; any remaining external fact is limited to `det2_on_Ω_proved` (or temporarily `det2_on_Ω_assumed`).

## Risks / Notes

- mathlib coverage for right half‑plane Poisson theory is limited; the proof will rely on kernel properties, integrability lemmas, and dominated convergence.
- A fully rigorous `det2` witness may require diagonal Fredholm foundations; we provide a packer to keep the route wired until then.

## CI / PR steps

1) Run lints over `rh/` files after each step.
2) Commit logical units with descriptive messages.
3) Push to `feature/poisson-transport-bridge` and keep PR #1 updated.
4) Enable auto‑merge (squash) upon green.

## Clarifications from the written proof (Riemann-lean-verified.tex)

Reading the manuscript clarifies several load‑bearing facts that we can mirror directly in Lean, tightening the plan:

- Noncancellation and analyticity of `det₂` on `Ω` (N2) are proved for the diagonal operator `A(s)e_p=p^{-s}e_p` via the 2‑modified determinant product with nonzero factors and HS continuity. Actionable: implement `Det2OnOmega_proved` without assumptions.
- Right‑edge normalization (N1) is established: as `σ→+∞`, `det₂(I−A)→1`, `|ξ(σ+it)|→∞` on compact `t`‑intervals, and the outer is bounded on vertical strips, so `J→0` and hence `Θ→−1`. Actionable: add an RS‑level lemma encapsulating this normalization if needed by the pinch route.
- Poisson/Cayley globalization: from (P+), `Re F ≥ 0` on `Ω\Z(ξ)`, yielding Schur via Cayley, and removability at putative zeros forces the pinch contradiction. Actionable: our `HasHalfPlanePoissonRepresentationOn` + transport + `Θ` pinch already align; the missing piece is a self‑contained Poisson identity proof used to drop `re_eq`.
- Zeta‑normalized gauge: introducing `B(s)=(s−1)/s` removes the archimedean boundary term; boundary modulus statements then involve `|det₂/ζ|`. Actionable: optional alternative wrappers; current `ξ_ext` gauge is acceptable provided boundary modulus and bounds (e.g., `|Re F_pinch|≤2`) are in place.

## Plan updates (new actions derived from the manuscript)

1) RS/Determinant witness (unconditional):
- Add `det2_on_Ω_proved : Det2OnOmega` in `rh/rh/RS/Det2Outer.lean` using the diagonal HS operator and the explicit nonvanishing/product lemma (as in the manuscript’s “Diagonal HS determinant is analytic and nonzero”). This replaces all uses of `det2_on_Ω_assumed` in the active route.

2) Optional normalization-at-infinity lemma (only if required by the pinch wrapper):
- New `rh/rh/RS/RightEdge.lean` (or add to an existing RS file): lemma that `Θ_pinch` satisfies `Θ(σ+it)→−1` uniformly on compact `t`‑intervals as `σ→+∞`. Inputs: `det₂(I−A)→1`, outer bounded on vertical strips (Poisson–BMO bound), and `|ξ(σ+it)|→∞`.

3) AF Poisson identity (self‑contained) and refactor:
- Implement `poisson_formula_re_for_halfplane_analytic` in `academic_framework/HalfPlaneOuter.lean` (no external `re_eq`).
- Refactor `pinch_representation_on_offXi` to derive `re_eq` internally with `M=2` using boundary bounds from `RS/Cayley.lean` and existing integrability lemmas.

4) Proof wrapper alignment:
- Update `Proof/Main.lean`’s `RiemannHypothesis_from_certificate_rep_on` to the refactored representation (no `re_eq`), keep the `(P+)` path via `F_pinch_Plus_from_certificate`, and finalize via the existing pinch ingredients.

5) Optional zeta‑normalized variant (parity with manuscript):
- Provide convenience wrappers for an alternative normalization using `ζ` and the Blaschke `B(s)`. Not required for unconditional closure, but keeps the code aligned with the exposition.

## Mapping (manuscript → Lean tasks)

- “Diagonal HS determinant is analytic and nonzero” → `det2_on_Ω_proved` (RS) and supportive lemmas.
- “Normalization at infinity (N1)” → optional RS lemma `right_edge_normalization_for_Θ_pinch` (if pinch machinery needs it explicitly).
- “Poisson transport to Herglotz; Cayley to Schur; removability” → already covered by AF `HasHalfPlanePoissonRepresentationOn` + RS Cayley/Schur + `OffZerosBridge`; ensure the Poisson identity lemma removes the last external equality.
- “No Archimedean term in ζ‑normalized route” → optional alternative wrappers; existing `ξ_ext` route remains valid with boundary modulus bounds already implemented.


