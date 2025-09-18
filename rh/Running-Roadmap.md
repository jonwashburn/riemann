# Running Roadmap – RS/Cert Proof Closure

Status legend: `next` | `in_progress` | `blocked` | `completed`

Principles
- Define clear acceptance criteria per item.
- If blocked > 1–2 attempts, decompose into smaller lemmas with explicit dependencies.
- Track exact Lean targets (file, theorem/lemma names).
- No `sorry`/axioms; mathlib-only proofs or explicitly recorded external lemmas.
- When sub-lemmas land, roll up and check acceptance for the parent.

---

## 1) RS bridge: local wedge → boundary (P+) via CR–Green/Poisson
Status: in_progress

Goal
- From a Whitney–box Carleson budget, produce boundary wedge `(P+)` for the concrete field `F` (e.g., `F := 2·J_pinch det2 O`).

Acceptance
- `rh/RS/PPlusFromCarleson.lean` compiles without placeholders, using a genuine local→a.e. upgrade.
- Provide either:
  - `localWedge_from_WhitneyCarleson_proved` in `rh/RS/BoundaryWedge.lean`, or
  - an equivalent witness used by `PPlusFromCarleson_exists_proved` so that `(∃Kξ ≥ 0, Carleson Kξ) → PPlus F` is proven.

Lean targets (exact lemma names)
```lean
-- LINK: CR–Green control of boundary pairing by the Whitney Carleson budget
lemma CRGreen_link
  {F : ℂ → ℂ} {Kξ : ℝ}
  (hCar : RH.Cert.ConcreteHalfPlaneCarleson Kξ)
  {I : Set ℝ} (hI : RH.WhitneyInterval I)
  (a : RH.H1Atom I) :
  |∫ t in I, ((F (Complex.mk (1/2) t)).re) * a t| ≤ Cgreen * Kξ * Measure.lebesgue I

-- Poisson kernel positivity (normalized half-plane kernel)
lemma halfplane_poisson_kernel_nonneg {b x : ℝ} (hb : 0 < b) :
  0 ≤ RH.RS.poissonKernel b x

-- Poisson approximate identity (a.e.) for normalized kernel
lemma poisson_approximate_identity_ae
  {f : ℝ → ℝ} (hf : LocIntegrable f Measure.lebesgue) :
  ∀ᵐ x : ℝ, Filter.Tendsto
    (fun b : ℝ => ∫ t, RH.RS.poissonKernel b (x - t) * f t ∂Measure.lebesgue)
    (Filter.nhdsWithin 0 (Set.Ioi 0)) (Filter.nhds (f x))

-- Fixed even window with Poisson plateau lower bound (normalized)
lemma poisson_plateau_c0 :
  ∃ ψ : ℝ → ℝ, Function.Even ψ ∧ (∀ x, 0 ≤ ψ x) ∧ HasCompactSupport ψ ∧
    (∫ x, ψ x ∂Measure.lebesgue = (1 : ℝ)) ∧
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ {b x}, 0 < b → b ≤ 1 → |x| ≤ 1 →
      (∫ t, RH.RS.poissonKernel b (x - t) * ψ t ∂Measure.lebesgue) ≥ c0

-- From Whitney-local a.e. nonnegativity to global a.e. on ℝ
lemma ae_limit_from_whitney_cover
  {f : ℝ → ℝ} {I : ℕ → Set ℝ}
  (hmeas : ∀ n, MeasurableSet (I n))
  (hcover : (⋃ n, I n) = Set.univ)
  (hpair : Set.Pairwise (fun m n => Disjoint (I m) (I n)))
  (hloc : ∀ n, (∀ᵐ t ∂(Measure.restrict Measure.lebesgue (I n)), 0 ≤ f t)) :
  (∀ᵐ t ∂Measure.lebesgue, 0 ≤ f t)

-- Boundary regularity (choose one; A suffices)
lemma boundary_trace_locIntegrable (F : ℂ → ℂ) :
  LocIntegrable (fun t : ℝ => (F (Complex.mk (1/2) t)).re) Measure.lebesgue
```

Decomposition
- Link: prove `CRGreen_link` by CR–Green identity + Cauchy–Schwarz and Carleson energy.
- Plateau: provide `poisson_plateau_c0` for a fixed even window `ψ` with ∫ψ=1.
- Kernel: ensure normalized kernel and positivity; use it under integrals.
- Approximate identity: show `(P_b * f)(x) → f(x)` a.e. as `b ↓ 0`.
- Cover: upgrade local (Whitney) a.e. to global a.e.

Immediate next actions
- Implement `poisson_plateau_c0` in `rh/RS/PoissonPlateau.lean` (normalized kernel).
- Draft `CRGreen_link` statement and required bounds; if any mathlib lemma is missing, record blocker.

External facts required (if missing in mathlib)
- Approximate identity lemma for normalized Poisson kernel.
- CR–Green pairing estimate on Whitney boxes.

---

### 1a) ζ→Θ/N Schur bridge and boundary nonvanishing (Re = 1)
Status: next

Goal
- Assemble the analytic bridge ζ → Θ/N on `Ω := {Re > 1/2}` with:
  - Θ Schur on `Ω \ Z(ξ_ext)` from Cayley(F) with `F := 2·J` and `Re F ≥ 0` (from P+ and Poisson transport),
  - local removable extensions across each isolated `ξ_ext` zero with normalization `g(ρ)=1` and `g ≢ 1`.
- Deduce `ζ(z) ≠ 0` for all `z` with `Re z = 1` via the Schur–pinch globalization.

Acceptance
- `rh/RS/SchurGlobalization.lean` exposes:
  - `SchurOnRectangles` (Cayley ⇒ Schur under `0 ≤ Re F`),
  - `GlobalizeAcrossRemovable` and `no_offcritical_zeros_from_schur` (pinch globalization),
  - boundary wrappers `ZetaNoZerosOnRe1FromSchur_from_bridge` (bridge packaging).
- `rh/RS/Cayley.lean` provides the Cayley packaging for `Θ := (2·J−1)/(2·J+1)` with `schur_of_herglotz` alias.
- `rh/RS/Det2Outer.lean` provides the outer interface `OuterHalfPlane.ofModulus_det2_over_xi_ext` (statement-level is fine).

Lean targets (exact names)
```lean
-- Cayley ⇒ Schur (alias form)
lemma schur_of_herglotz {F : ℂ → ℂ} {S : Set ℂ}
  (hRe : ∀ z ∈ S, 0 ≤ (F z).re) :
  RH.RS.IsSchurOn (fun z => (F z - 1) / (F z + 1)) S

-- Boundary bridge wrapper (already present)
theorem ZetaNoZerosOnRe1FromSchur_from_bridge
  (B : RH.RS.ZetaSchurBoundaryBridge) :
  ∀ z, z.re = 1 → riemannZeta z ≠ 0
```

Decomposition
- P+ via CR–Green + window energy (Whitney): `rh/RS/CRGreenOuter.lean`, `rh/RS/H1BMOWindows.lean`.
- Poisson transport: `u ≥ 0` a.e. ⇒ interior `Re F ≥ 0`.
- Cayley→Schur: `schur_of_herglotz`.
- Removable step: local `g` across each isolated zero with `g(ρ)=1`.
- Bridge packaging: `ZetaSchurBoundaryBridge` → boundary nonvanishing.

Immediate next actions
- Add the `schur_of_herglotz` alias in `rh/RS/Cayley.lean` (reuse `SchurOnRectangles`).
- Keep `Det2Outer.lean` as interface provider (no axioms, statement-level existence ok).
- Implement CR–Green pairing and outer cancellation with uniform constants (mathlib-only); if blocked, add a one-line blocker to `BLOCKERS.md`.

Dependencies
- Uses existing `SchurGlobalization` globalization lemmas and the outer interface.

---

## 2) RS: Poisson plateau constant c0 > 0 (normalized kernel)
Status: next

Acceptance
- `rh/RS/PoissonPlateau.lean`: lemma `poisson_plateau_c0` with explicit positive `c0` for 0 < b ≤ 1 and |x| ≤ 1; uses normalized kernel
  `poissonKernel b x = (1/π) * b / (x^2 + b^2)`.

Plan
- Choose ψ ≥ 0, even, compactly supported with ∫ψ=1 (e.g. a smoothed bump ≥ c on [-1,1]).
- Show continuity of `(b,x) ↦ (P_b * ψ)(x)` on `[0,1]×[-1,1]` and positivity to get a uniform positive minimum.
  Alternatively, compute a concrete lower bound using the core integral of the kernel.

Immediate next actions
- Implement the proof with either the continuity/minimum argument or the explicit arctan bound.

---

## 3) Cert: Kξ Whitney Carleson from RvM (quantitative C-pillar)
Status: blocked (likely needs external number-theory facts)

Acceptance
- `rh/Cert/KxiWhitney_RvM.lean`:
  - Define `annularEnergy` (non-dummy) and prove `annular_balayage_L2`.
  - Formalize a short-interval zero-count bound (RvM/VK) sufficient for Whitney length.
  - Derive `kxi_whitney_carleson` with an explicit nonnegative constant.
  - Export `KxiBound α c` without placeholders.

External facts required
- Short-interval zero counts (Riemann–von Mangoldt / Vinogradov–Korobov) in a mathlib-usable form.
- Half-plane Carleson geometry for `|∇Uξ|^2 σ dt dσ` over Whitney boxes.

---

## 4) A.1/A.2 canonical route: Poisson outer + Montel–Hurwitz
Status: optional/next

Acceptance
- `rh/RS/Det2Outer.lean`: replace alias alt with a genuine A.2 locally-uniform limit along ε → 0; preserve zero-freeness (Hurwitz) and boundary modulus.
- If normal-family/Hurwitz lemmas are missing, record blocker and keep alt alias.

---

## 5) Build environment stability
Status: blocked-env

Acceptance
- `lake clean && lake build` completes green; no mathlib write errors.

Immediate next actions
- If mathlib build write errors recur, clear caches / update toolchain; otherwise proceed with RS lemmas above.

---

## 6) Practical tracking rules (applies to all items)
- Each item has acceptance criteria, Lean targets, and immediate next actions.
- If an item is blocked > 1–2 attempts, split into smaller lemmas with clear dependencies.
  
- No `sorry`/axioms. Keep proofs audit-ready and mathlib-only.
- Roll up sub-lemmas as they land and check acceptance.


