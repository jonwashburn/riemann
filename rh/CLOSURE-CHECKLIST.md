### RH closure checklist (what we need vs. what the two docs provide)

- Sources reviewed
  - riemann-closure-z.txt (Lean-ready snippets and skeletons)
  - Riemann-lean-verified.tex (complete paper with labeled results)

### Lean targets needed for unconditional closure (by milestone)

- Milestone A — Outer existence on Ω (outer normalization)
  - A.1: `Outer_on_halfplane_from_boundary_modulus` (shifted half-plane outer; analytic, zero-free; a.e. boundary modulus = exp uε)
  - A.2: `outer_limit_locally_uniform` (ε → 0 outer limit on Ω; zero-free; boundary modulus exp u)
  - A.3: `OuterHalfPlane.ofModulus_det2_over_xi_ext` (outer O with boundary modulus |det₂/ξ_ext| on Re s = 1/2)

- Milestone B — Half-plane transport (P+ ⇒ interior)
  - B.1: `HasHalfPlanePoissonTransport` specialized to `F := (2 : ℂ) * J_pinch det2 O`
  - B.2: Boundary uniqueness on rectangles (a.e. Re F ≥ 0 on ∂R ⇒ Re F ≥ 0 on R)
  - B.3: Cayley step to Schur (Re F ≥ 0 ⇒ Θ Schur), used with removable singularity

- Milestone C — Kξ Whitney Carleson (zero-packing → box energy)
  - C.1: `annular_balayage_L2` (Whitney annulus Poisson L² with σ-weight)
  - C.2: VK/RvM short-interval counts translated to annulus bounds (`vk_annular_counts` shape)
  - C.3: `kxi_whitney_carleson` (box energy on Q(αI) ≤ Kξ |I|)
  - C.4: `KxiWhitney.KxiBound α c` (export Kξ ≥ 0 in certificate interface)

- Support (used by RS globalization chain)
  - S.1: `removable_of_schur_on_punctured` (bounded Schur on punctured disk ⇒ removable, Θ(ρ)=limit)
  - S.2: CR–Green pairing for boundary phase and outer cancellation
  - S.3: Carleson box triangle/subadditivity: `carleson-sum` (√C_box(U+V) ≤ √C_box(U)+√C_box(V))
  - S.4: All-interval extension from Whitney: `xi_carleson_all_I`
  - S.5: Poisson plateau lower bound c0(ψ) > 0 (fixed window)
  - S.6: Determinant/HS basics: det₂ analytic/nonzero; strip bounds for ∂σ log det₂

### What riemann-closure-z.txt provides

- Outer (A)
  - A.1: `Outer_on_halfplane_from_boundary_modulus` — Provided with no sorries/axioms via a LocalBMO wrapper.
    - Includes: `PoissonConjPoisson_extension_analytic_on_halfplane` (analyticity of U+iV on shifted half-plane) and `PoissonOuter_boundary_modulus_NT` (a.e. vertical limit of |Oε| = exp(uε)).
  - A.1 (alt skeleton): An axiomatized variant also present (ok for scratch, not for repo).
  - A.2: `outer_limit_locally_uniform` — Present as a Lean-ready skeleton; proof placeholders remain.
  - A.3: `OuterHalfPlane.ofModulus_det2_over_xi_ext` — Target name referenced; not fully wired here (covered by paper’s Prop. outer-central for the math).

- Transport (B)
  - B.2: `boundary_uniqueness_rectangle` — Stated Lean-ready; proof outline given; formal proof not supplied here.
  - B.1/B.3 helpers: A short “Poisson preserves nonnegativity” statement is sketched (no formal proof in-file). Cayley step is trivial once B.1 holds.

- Kξ Carleson (C)
  - C.1: `annular_balayage_L2` — Statement and proof idea given elsewhere; in this file the Lean head for `kxi_whitney_carleson` appears with `sorry` placeholder.
  - C.3: `kxi_whitney_carleson` — Present as Lean head with `sorry`.
  - C.4: `KxiWhitney.KxiBound` — Present as Lean head with `sorry` (and an ℝ≥0 alternative); depends on a predicate stub `ConcreteHalfPlaneCarleson`.

- Support (S)
  - S.1: `removable_of_schur_on_punctured` — Fully written classically in the doc; Lean-ready theorem statement included.
  - B.2 (again): detailed max principle/ε-shift proof included.

Status summary (riemann-closure-z.txt)
- Provided/no-axiom: A.1 and its two sub-lemmas (under `LocalBMO`).
- Skeletons/placeholders present: A.2, C.3, C.4, B.1/B.2 support lemmas.

### What Riemann-lean-verified.tex provides (paper; math-level proofs)

- Outer (A)
  - Prop: Outer normalization: existence, boundary a.e. modulus, and limit (Prop. `outer-central`). Covers A.2 and the A.3 use-case for |det₂/ξ|.
  - Lemma: Outer phase/Hilbert transform identity (`lem:outer-phase-HT`).
  - Lemma: Outer cancellation and energy bookkeeping on boxes (`lem:outer-energy-bookkeeping`).

- Transport (B)
  - Remark/Theorem set: Boundary uniqueness on rectangles (Remark `rem:boundary-uniqueness`).
  - Cor.: Poisson transport/Herglotz (`cor:poisson-herglotz`).
  - Cor.: Cayley ⇒ Schur off zeros (`cor:cayley-schur`).
  - Theorem: Limit on rectangles; Θ Schur (`thm:limit-rect`).

- Kξ Carleson (C)
  - Lemma: Annular Poisson–balayage L² bound (`lem:annular-balayage`) — with full proof.
  - Lemma: Analytic (ξ) Carleson energy on Whitney boxes (`lem:carleson-xi`) — with VK/RvM input; full proof.
  - Prop.: Whitney Carleson finiteness for Uξ (`prop:Kxi-finite`).
  - Cor.: All-interval Carleson energy (`cor:xi-carleson-all-I`).

- Support (S)
  - Lemma: Carleson sum/triangle (`lem:carleson-sum`).
  - Lemma/Cor.: CR–Green pairing for boundary phase and explicit remainder control (`lem:CR-green-phase`, `lem:outer-cancel`, remainder corollary).
  - Lemma: Poisson plateau lower bound (`lem:poisson-plateau`).
  - Lemma: Removable singularity under Schur bound (`lem:removable-schur`).
  - Determinant/HS basics: `lem:hs-diagonal`, `prop:hs-det2-continuity`, `lem:det2-unsmoothed`.
  - Globalization/pinch: `thm:globalize-main`, `thm:RH`.

Status summary (paper)
- All required mathematical ingredients (A–C, S) are present with proofs at the paper level.

### Coverage verdict

- Mathematically: the paper contains everything needed (A.1–A.3, B.1–B.3, C.1–C.4, S.*) with explicit arguments.
- Lean artifacts: A.1 is supplied in `riemann-closure-z.txt` without axioms (via `LocalBMO`). The remaining Lean targets appear as clean statements/skeletons but still need formal proofs wired (A.2, A.3 wrapper, B.1 transport lemma, C.3/C.4 Kξ statements).

### Minimal delta to finish (Lean)

- Implement (no sorries) using mathlib facts already referenced by the paper:
  - A.2: `outer_limit_locally_uniform` (Montel/Hurwitz + boundary modulus passage described).
  - A.3: `OuterHalfPlane.ofModulus_det2_over_xi_ext` (instantiate A.1/A.2 with u = log|det₂/ξ|; the paper’s Prop. outer-central).
  - B.1: `HasHalfPlanePoissonTransport` for F := 2·J_pinch (use Poisson positivity + rectangle boundary uniqueness).
  - C.3/C.4: `kxi_whitney_carleson`, `KxiWhitney.KxiBound α c` (lift from Lemma `annular-balayage`, Lemma `carleson-xi`, and Prop. `Kxi-finite`).

If you want, we can generate Lean statement stubs matching the paper labels to ensure a one-to-one mapping for implementation.


