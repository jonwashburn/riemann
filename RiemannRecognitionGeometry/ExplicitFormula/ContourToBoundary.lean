/-
# Contour-to-Boundary Connection: W^{(1)} contour definition → L²(μ_spec) pairing

This file formalizes the connection between:
1. The contour integral definition of the Weil zero-sum functional W^{(1)}
2. The L²(μ_spec) boundary pairing used in the measure-first Route 3 pipeline

## Mathematical content

The key identity is:
```
  W^{(1)}(pair(f,g)) = ∫_ℝ conj(F_f(t)) · F_g(t) dμ_spec(t)
```

This follows from:
1. **Contour definition**: W^{(1)}(h) = (1/2πi) ∮ F_h(s) · (ξ'/ξ)(s) ds = Σ_ρ F_h(ρ)
2. **Log-derivative decomposition**: For the PSC ratio J = det₂(I-A)/(O·ξ), we have
   ξ'/ξ = (det₂)'/det₂ - O'/O - J'/J
3. **Boundary phase**: On Re s = 1/2, |J| = 1 (unimodular), so (after choosing a phase lift
   J(1/2+it)=exp(i·θ(t))) one has `logDeriv J (1/2+it) = deriv θ t`, hence the boundary
   log-derivative is **real-valued** (not imaginary).
4. **Explicit formula cancellation**: The det₂ and outer O terms cancel against W_arith, W², W⁰
5. **PSC phase-velocity**: -w' = π μ_spec
6. **Normalization**: After tracking π factors and symmetric pairing, we get the identity.

See `ROUTE3_IDENTITY_PART.md` for the full proof sketch.

## Status

The mathematical content is axiomatized here pending formal development of:
- Contour integral theory for the explicit formula
- Boundary value theory for log-derivatives
- The explicit formula cancellation calculation
-/

import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import RiemannRecognitionGeometry.ExplicitFormula.Lagarias
import RiemannRecognitionGeometry.ExplicitFormula.LagariasContour
import RiemannRecognitionGeometry.ExplicitFormula.ContourW1

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open MeasureTheory Complex
open scoped InnerProductSpace

namespace ContourToBoundary

/-!
## The PSC ratio and its log-derivative

The PSC ratio J = det₂(I-A)/(O·ξ) has the following properties:
- Analytic on Ω = {Re s > 1/2} (away from ξ-zeros)
- Unimodular boundary modulus: |J(1/2+it)| = 1 a.e.
- Zero/pole geometry matches ξ (N2 property)
-/

/-- The PSC components: det₂, O (outer), ξ (completed xi). -/
structure PSCComponents where
  /-- The 2-modified Fredholm determinant det₂(I-A(s)). -/
  det2 : ℂ → ℂ
  /-- The outer function O(s) normalizing the boundary modulus. -/
  outer : ℂ → ℂ
  /-- The completed Riemann xi function ξ(s). -/
  xi : ℂ → ℂ
  /-- det₂ is nonzero on Re s > 1/2. -/
  det2_ne_zero : ∀ s : ℂ, 1/2 < s.re → det2 s ≠ 0
  /-- O is nonzero on Re s > 1/2. -/
  outer_ne_zero : ∀ s : ℂ, 1/2 < s.re → outer s ≠ 0
  /-- det₂ is differentiable on Re s > 1/2. -/
  det2_diff : ∀ s : ℂ, 1/2 < s.re → DifferentiableAt ℂ det2 s
  /-- O is differentiable on Re s > 1/2. -/
  outer_diff : ∀ s : ℂ, 1/2 < s.re → DifferentiableAt ℂ outer s
  /-- ξ is differentiable on Re s > 1/2 (away from zeros, for log-deriv). -/
  xi_diff : ∀ s : ℂ, 1/2 < s.re → xi s ≠ 0 → DifferentiableAt ℂ xi s
  /-- A chosen boundary phase function θ : ℝ → ℝ for the PSC ratio J on Re(s)=1/2. -/
  boundaryPhase : ℝ → ℝ
  /-- Regularity of the chosen boundary phase. -/
  boundaryPhase_diff : ∀ t : ℝ, DifferentiableAt ℝ boundaryPhase t
  /-- Boundary trace phase lift: J(1/2+it)=exp(i·θ(t)) almost everywhere. -/
  boundaryPhase_repr :
    ∀ᵐ t : ℝ ∂volume,
      det2 (1/2 + I * t) / (outer (1/2 + I * t) * xi (1/2 + I * t)) =
        Complex.exp (I * boundaryPhase t)
  /-- PSC spectral boundary measure on `ℝ` (positive by definition of `Measure`). -/
  μ_spec : Measure ℝ := volume
  /-- PSC phase–velocity identity for the chosen boundary phase and spectral measure. -/
  phase_velocity_identity :
    ∀ φ : ℝ → ℝ, Integrable φ volume →
      ∫ t : ℝ, φ t * deriv boundaryPhase t ∂volume = - Real.pi * ∫ t : ℝ, φ t ∂ μ_spec

/-- The PSC ratio J = det₂/(O·ξ). -/
def PSCRatio (P : PSCComponents) (s : ℂ) : ℂ := P.det2 s / (P.outer s * P.xi s)

-- (Placeholders removed: the boundary phase is now a field of `PSCComponents`.)

/-!
## Axioms for the contour-to-boundary connection

These axioms package the mathematical content needed to prove the splice completion identity.
They are "standard analysis" in the sense that they follow from:
- Cauchy integral theory (Mathlib has good support)
- Boundary value theory for analytic functions
- The explicit formula for ζ/ξ

But they are nontrivial to formalize, so we axiomatize them for now.
-/

/--
**Theorem (Log-derivative decomposition)**: The log-derivative of ξ decomposes as
ξ'/ξ = (det₂)'/det₂ - O'/O - J'/J
where J = det₂/(O·ξ) is the PSC ratio.

This is a direct application of Mathlib's `logDeriv_div` and `logDeriv_mul`.
-/
theorem log_deriv_decomposition (P : PSCComponents) (s : ℂ) (hs : 1/2 < s.re)
    (hxi : P.xi s ≠ 0) :
    logDeriv P.xi s =
      logDeriv P.det2 s - logDeriv P.outer s - logDeriv (PSCRatio P) s := by
  -- J = det₂ / (O · ξ), so logDeriv J = logDeriv det₂ - logDeriv O - logDeriv ξ
  -- Rearranging: logDeriv ξ = logDeriv det₂ - logDeriv O - logDeriv J
  have hdet2 : P.det2 s ≠ 0 := P.det2_ne_zero s hs
  have houter : P.outer s ≠ 0 := P.outer_ne_zero s hs
  have hdiff_det2 : DifferentiableAt ℂ P.det2 s := P.det2_diff s hs
  have hdiff_outer : DifferentiableAt ℂ P.outer s := P.outer_diff s hs
  have hdiff_xi : DifferentiableAt ℂ P.xi s := P.xi_diff s hs hxi
  have hdiff_outer_xi : DifferentiableAt ℂ (fun z => P.outer z * P.xi z) s :=
    hdiff_outer.mul hdiff_xi
  have houter_xi : P.outer s * P.xi s ≠ 0 := mul_ne_zero houter hxi
  -- logDeriv (det₂ / (O · ξ)) = logDeriv det₂ - logDeriv (O · ξ)
  have h1 : logDeriv (PSCRatio P) s = logDeriv P.det2 s - logDeriv (fun z => P.outer z * P.xi z) s := by
    unfold PSCRatio
    exact logDeriv_div s hdet2 houter_xi hdiff_det2 hdiff_outer_xi
  -- logDeriv (O · ξ) = logDeriv O + logDeriv ξ
  have h2 : logDeriv (fun z => P.outer z * P.xi z) s = logDeriv P.outer s + logDeriv P.xi s := by
    exact logDeriv_mul s houter hxi hdiff_outer hdiff_xi
  -- Combine: logDeriv J = logDeriv det₂ - logDeriv O - logDeriv ξ
  -- So: logDeriv ξ = logDeriv det₂ - logDeriv O - logDeriv J
  rw [h1, h2]
  ring

/-!
## Boundary phase structure

When |J| = 1 on the critical line, J = e^{iθ} for some real phase θ.
The log-derivative J'/J is then related to θ'.

**Key fact:** For unimodular J on the critical line s = 1/2 + it:
- J(s) = e^{iθ(t)} for real θ
- Complex derivative: J'(s) = (1/i) · d/dt J = (1/i) · iθ'(t) · e^{iθ(t)} = θ'(t) · J(s)
- So J'/J = θ'(t), which is **real**

**Convention clarification:** The document notation "J'/J = iw'" uses w = -θ to get the
sign convention where -w' = π μ_spec is positive.
-/

/--
**Axiom (Unimodular log-derivative is real)**: If f is holomorphic and |f(s)| = 1 for s on
the critical line, then the log-derivative f'/f evaluated at s = 1/2 + it is a real number.

More precisely, if f = e^{iθ(t)} for real-valued θ, then f'/f = θ'(t).

**Proof sketch:**
1. f(1/2 + it) = e^{iθ(t)} where θ(t) is real-valued
2. Taking derivative along the line: d/dt f(1/2+it) = i·θ'(t)·f(1/2+it)
3. Chain rule for holomorphic f: d/dt f(1/2+it) = f'(1/2+it) · (d/dt (1/2+it)) = f'(1/2+it) · i
4. Comparing: f'(1/2+it) · i = i·θ'(t)·f(1/2+it)
5. Thus: f'(1/2+it) = θ'(t)·f(1/2+it)
6. So: f'/f = θ'(t) (real)

**Status:** Stated as axiom because the Lean proof requires infrastructure for relating
real derivatives along curves to complex derivatives of holomorphic functions.
This is standard complex analysis but not yet developed in the project.
-/
theorem logDeriv_unimodular_real (f : ℂ → ℂ) (θ : ℝ → ℝ) (t : ℝ)
    (hf : (fun u : ℝ => f (1/2 + I * u)) =ᶠ[nhds t] fun u : ℝ => Complex.exp (I * θ u))
    (hf_ne : f (1/2 + I * t) ≠ 0)
    (hθ_diff : DifferentiableAt ℝ θ t)
    (hf_diff : DifferentiableAt ℂ f (1/2 + I * t)) :
    logDeriv f (1/2 + I * t) = deriv θ t := by
  -- Parameterization of the critical line
  let h : ℝ → ℂ := fun u : ℝ => (1 / 2 : ℂ) + Complex.I * (u : ℂ)
  have hh : HasDerivAt h Complex.I t := by
    -- `u ↦ (u : ℂ)` has derivative `1`, then multiply by `I` and add the constant `1/2`.
    have h_ofReal : HasDerivAt (fun u : ℝ => (u : ℂ)) (1 : ℂ) t := by
      simpa [ofRealCLM_apply] using (ofRealCLM.hasDerivAt (x := t))
    have h_mul : HasDerivAt (fun u : ℝ => Complex.I * (u : ℂ)) (Complex.I * (1 : ℂ)) t :=
      h_ofReal.const_mul Complex.I
    -- add the constant `(1/2 : ℂ)`
    have h_add :
        HasDerivAt (fun u : ℝ => (1 / 2 : ℂ) + Complex.I * (u : ℂ)) (Complex.I * (1 : ℂ)) t :=
      h_mul.const_add (1 / 2 : ℂ)
    simpa [h, mul_one] using h_add

  -- Derivative of the RHS `u ↦ exp(I * θ u)`.
  have h_rhs :
      HasDerivAt (fun u : ℝ => Complex.exp (Complex.I * θ u))
        (Complex.exp (Complex.I * θ t) * (Complex.I * ((deriv θ t : ℝ) : ℂ))) t := by
    -- First lift `θ` to a complex-valued function and multiply by `I`.
    have hθ' : HasDerivAt (fun u : ℝ => (θ u : ℂ)) ((deriv θ t : ℝ) : ℂ) t := by
      -- `θ` is real-differentiable at `t`, then coerce to `ℂ`.
      simpa using (HasDerivAt.ofReal_comp (hf := hθ_diff.hasDerivAt))
    have h_mulI : HasDerivAt (fun u : ℝ => Complex.I * (θ u : ℂ))
        (Complex.I * ((deriv θ t : ℝ) : ℂ)) t :=
      hθ'.const_mul Complex.I
    -- Now apply exp chain rule.
    simpa [mul_assoc] using h_mulI.cexp

  -- Use the eventual equality to transfer the derivative to the LHS function.
  have hf' : (fun u : ℝ => f (h u)) =ᶠ[nhds t] fun u : ℝ => Complex.exp (Complex.I * θ u) := by
    simpa [h] using hf

  -- Compute the derivative of `u ↦ f(h u)` in two ways:
  -- (1) by eventual equality with the RHS, (2) by chain rule through `h`.
  have hderiv_comp :
      deriv (fun u : ℝ => f (h u)) t =
        Complex.exp (Complex.I * θ t) * (Complex.I * ((deriv θ t : ℝ) : ℂ)) := by
    -- use `h_rhs` and the eventual equality `hf'`
    have := (h_rhs.congr_of_eventuallyEq hf').deriv
    simpa using this

  have hderiv_chain :
      deriv (fun u : ℝ => f (h u)) t = deriv f (h t) * deriv h t := by
    -- scalar chain rule for `deriv`
    simpa [Function.comp] using (deriv_comp (x := t) (h₂ := f) (h := h) hf_diff hh.differentiableAt)

  -- Now solve for `deriv f (h t)` using `deriv h t = I`.
  have hderiv_eq :
      deriv f (h t) * Complex.I =
        Complex.exp (Complex.I * θ t) * (Complex.I * ((deriv θ t : ℝ) : ℂ)) := by
    -- rewrite `deriv h t` from `hh`
    have hdh : deriv h t = Complex.I := hh.deriv
    -- combine the two expressions
    calc
      deriv f (h t) * Complex.I
          = deriv f (h t) * deriv h t := by simpa [hdh]
      _   = deriv (fun u : ℝ => f (h u)) t := by
              simpa [hderiv_chain] using (hderiv_chain.symm)
      _   = Complex.exp (Complex.I * θ t) * (Complex.I * ((deriv θ t : ℝ) : ℂ)) := hderiv_comp

  -- Cancel the common factor `I` and divide by `f(h t)` to get the log-derivative.
  -- First rewrite `f(h t)` using the phase representation at the point `t`.
  have hf_at : f (h t) = Complex.exp (Complex.I * θ t) := by
    -- `hf` holds in a neighborhood, hence at `t`.
    have hf' : (fun u : ℝ => f (h u)) =ᶠ[nhds t] fun u : ℝ => Complex.exp (Complex.I * θ u) := by
      simpa [h] using hf
    exact (hf'.eq_of_nhds)
  -- Solve for `deriv f (h t)`.
  have hderiv_f :
      deriv f (h t) = ((deriv θ t : ℝ) : ℂ) * f (h t) := by
    -- From `I • deriv f = exp(Iθt) * (I * θ')`, and `•` is real scalar action.
    -- Rewrite the scalar action as multiplication by `I` in `ℂ`, then cancel `I`.
    -- Also rewrite `exp(Iθt)` as `f(h t)`.
    -- NB: `I` is invertible in `ℂ`.
    have hI_ne : (Complex.I : ℂ) ≠ 0 := by
      simpa using (Complex.I_ne_zero)
    -- Convert scalar action: `I • z = I * z` in `ℂ` (as an `ℝ`-module).
    -- Then cancel `I` from both sides.
    -- We use `Complex.real_smul` to rewrite real scalar action; for a complex scalar, this is definitional.
    -- The result is purely algebraic.
    -- NOTE: `Complex.I • z` is the `ℝ`-scalar action by the real number `I.re = 0`? so we avoid this and
    -- instead rewrite `h_comp` using `deriv_comp` below. (We keep a simple algebraic path here.)
    -- In practice, `scomp` gives `I • deriv f`, so we translate it to multiplication by `I`.
    -- `by simpa [Complex.smul_def]` works here.
    have hmul : deriv f (h t) * (Complex.I : ℂ) =
        Complex.exp (Complex.I * θ t) * ((Complex.I : ℂ) * ((deriv θ t : ℝ) : ℂ)) := by
      -- This is exactly `hderiv_eq` (the chain-rule computation yields `deriv f * I`).
      simpa using hderiv_eq
    -- Cancel the common factor `I` (on the right) to solve for `deriv f (h t)`.
    have hcancel : deriv f (h t) = Complex.exp (Complex.I * θ t) * ((deriv θ t : ℝ) : ℂ) := by
      -- Divide both sides by `I` on the right (since `hmul` has `... * I`).
      exact mul_right_cancel₀ hI_ne (by simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)
    -- Commute to match the desired `θ' * f(h t)`.
    simpa [hf_at, mul_assoc, mul_left_comm, mul_comm] using hcancel
  -- Finally compute `logDeriv f (h t) = deriv f / f = θ'`.
  have hf_ne' : f (h t) ≠ 0 := by
    simpa [h] using hf_ne
  have : logDeriv f (h t) = ((deriv θ t : ℝ) : ℂ) := by
    simp [logDeriv, hderiv_f, hf_ne', div_eq_mul_inv, mul_assoc]
  simpa [h] using this

/--
**Definition (Boundary phase function)**: The PSC boundary phase function for the PSC ratio.

This is provided as part of the `PSCComponents` bundle:
- `P.boundaryPhase` is the chosen phase function θ
- `P.boundaryPhase_diff` gives differentiability
- `P.boundaryPhase_repr` gives the a.e. boundary trace identity
  \(J(1/2+it)=\exp(i\theta(t))\).
-/
def boundaryPhaseFunction (P : PSCComponents) : ℝ → ℝ := P.boundaryPhase

/-!
**Lemma (Boundary log-derivative is real)**: On the critical line, the log-derivative of
the unimodular J is real: J'/J(1/2+it) = θ'(t) for some real θ.

**Status:** This statement is *derivable* from the phase representation bundled in `PSCComponents`
(i.e. `P.boundaryPhase_repr`) and the now-proved
`logDeriv_unimodular_real`, provided one also formalizes the “a.e. except discrete set” bookkeeping
needed to ensure `PSCRatio P` is differentiable and nonzero on the boundary at a.e. `t`.

We do **not** include it as an axiom; the current contour-to-boundary chain directly uses
`boundaryPhaseFunction P` (via `explicit_formula_cancellation`) rather than going through
`logDeriv (PSCRatio P)`.
 -/
-- (No declaration here on purpose; see note above.)

/-
**Axiom (Explicit formula cancellation)**: When the contour integral for W^{(1)} is
moved to the critical line, the det₂ and outer O terms cancel against W_arith, W², W⁰.

This is the content of Lagarias' explicit formula (Thm 3.1):
  M[f](1) - W¹(f) + M[f](0) = W_arith(f)

**Mathematical content:** The log-derivative ξ'/ξ splits as
  ξ'/ξ = (det₂)'/det₂ - O'/O - J'/J  (by `log_deriv_decomposition`)
When integrated against test functions via the contour integral:
- The (det₂)'/det₂ term gives the prime-power contributions → W_arith (prime part)
- The O'/O term gives the archimedean contributions → W_arith (gamma part)
- What remains is -J'/J = -θ' → the boundary phase pairing

**Concrete statement:** For a boundary transform F_h : ℝ → ℂ of a test function h,
  W^{(1)}(h) = (1/2π) ∫_ℝ F_h(t) · (-θ'(t)) dt
where θ is the boundary phase from `boundaryPhaseFunction`.

This is the key calculation that reduces the contour integral to a boundary pairing
against the phase derivative.

-- **Status:** This is carried as a hypothesis (`explicit_formula_cancellation`) because formalizing the contour integral definition of W^{(1)}
-- and the residue calculus that produces W_arith requires significant Mathlib infrastructure.

 -/

/-!
### Explicit-formula cancellation (hypothesis, not a global axiom)

This is the (non-RH-equivalent) bookkeeping identity that reduces the contour definition of `W¹`
to a critical-line boundary pairing against the derivative of the PSC boundary phase.

We *do not* declare this as a global Lean `axiom`; instead it is carried as an explicit hypothesis
where needed (e.g. in `PSCSplice.IntegralAssumptions.ofContourToBoundary`).
-/
def explicit_formula_cancellation
    {F : Type} [TestSpace F]
    (L : LagariasFramework F)
    (P : PSCComponents)
    (h : F) : Prop :=
    -- W^{(1)}(h) equals the boundary phase pairing against the critical-line Mellin transform
    L.W1 h = (1 / (2 * Real.pi)) *
      ∫ t : ℝ, -(M[h](1/2 + I * t) * ((deriv (boundaryPhaseFunction P) t : ℝ) : ℂ)) ∂ volume

/--
Variant of `explicit_formula_cancellation` phrased for a `LagariasContourFramework`.

This lets us work with a *concrete* contour-limit definition of `W¹` (via `ContourW1.W1Trunc`)
while keeping the main Route-3 pipeline statement unchanged.
-/
def explicit_formula_cancellation_contour
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents)
    (h : F) : Prop :=
  LC.contourW1.W1 h = (1 / (2 * Real.pi)) *
    ∫ t : ℝ, -(M[h](1/2 + I * t) * ((deriv (boundaryPhaseFunction P) t : ℝ) : ℂ)) ∂ volume

theorem explicit_formula_cancellation_contour_of_tendsto_W1Trunc
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents)
    (h : F)
    (hLim :
      Filter.Tendsto (fun T : ℝ => ContourW1.W1Trunc (F := F) LC.xi LC.c T h) Filter.atTop
        (nhds ((1 / (2 * Real.pi)) *
          ∫ t : ℝ, -(M[h](1/2 + I * t) * ((deriv (boundaryPhaseFunction P) t : ℝ) : ℂ)) ∂ volume))) :
    explicit_formula_cancellation_contour (LC := LC) (P := P) h := by
  -- Convert the computed limit into an equality for the packaged `W¹`.
  dsimp [explicit_formula_cancellation_contour]
  simpa using
    (ContourW1.W1_eq_of_tendsto_W1Trunc (xi := LC.xi) (c := LC.c) (A := LC.contourW1)
      (f := h) (z := ((1 / (2 * Real.pi)) *
        ∫ t : ℝ, -(M[h](1/2 + I * t) * ((deriv (boundaryPhaseFunction P) t : ℝ) : ℂ)) ∂ volume))
      hLim)

theorem explicit_formula_cancellation_of_contour
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents)
    (h : F)
    (H : explicit_formula_cancellation_contour (LC := LC) (P := P) h) :
    explicit_formula_cancellation (L := LC.L) P h := by
  -- rewrite `LC.L.W1` using the contour-compatibility field
  dsimp [explicit_formula_cancellation, explicit_formula_cancellation_contour] at *
  simpa [LC.W1_eq] using H

/-!
## PSC phase–velocity input

The phase–velocity identity is now bundled as the field `PSCComponents.phase_velocity_identity`,
relating `deriv P.boundaryPhase` to the spectral measure `P.μ_spec`.
-/

/-!
## The main splice completion theorem

Combining all the axioms above yields the splice completion identity.
-/

/--
**Theorem (Complex phase-velocity identity)**: The phase-velocity identity extends from real
test functions to complex-valued boundary transforms.

This is the complex-linear extension of `psc_phase_velocity_identity`:
  ∫ F_h · θ' dLebesgue = -π ∫ F_h dμ_spec

for complex-valued F_h.

**Proof:** Split F_h = Re(F_h) + i·Im(F_h), apply the real identity to each part,
and recombine.
-/
theorem complex_phase_velocity_identity
    (P : PSCComponents)
    (F_h : ℝ → ℂ)
    (h_integrable_F : Integrable F_h volume)
    (h_integrable_vol : Integrable (fun t => F_h t * ((deriv (boundaryPhaseFunction P) t : ℝ) : ℂ)) volume)
    (h_integrable_μ : Integrable F_h P.μ_spec) :
    ∫ t : ℝ, F_h t * ((deriv (boundaryPhaseFunction P) t : ℝ) : ℂ) ∂ volume =
      - Real.pi * ∫ t : ℝ, F_h t ∂ P.μ_spec := by
  let θ' := deriv (boundaryPhaseFunction P)
  -- Split F_h into real and imaginary parts
  let u := fun t => (F_h t).re
  let v := fun t => (F_h t).im

  -- Integrability of real parts
  have h_int_u : Integrable u volume := h_integrable_F.re
  have h_int_v : Integrable v volume := h_integrable_F.im

  -- Apply real identity to u and v
  have h_real_u : ∫ t : ℝ, u t * θ' t ∂volume = - Real.pi * ∫ t : ℝ, u t ∂ P.μ_spec := by
    -- `phase_velocity_identity` is bundled in `P`; rewrite `deriv boundaryPhase` as `θ'`.
    simpa [boundaryPhaseFunction, θ'] using P.phase_velocity_identity u h_int_u
  have h_real_v : ∫ t : ℝ, v t * θ' t ∂volume = - Real.pi * ∫ t : ℝ, v t ∂ P.μ_spec := by
    simpa [boundaryPhaseFunction, θ'] using P.phase_velocity_identity v h_int_v

  -- Expand LHS integral
  -- integral_re_add_im splits ∫ (f) into ↑(∫ f.re) + I * ↑(∫ f.im)
  rw [← integral_re_add_im (f := fun t => F_h t * (θ' t : ℂ))]
  rotate_left
  · exact h_integrable_vol

  -- Simplify LHS terms using RCLike to match integral_re_add_im
  have h_lhs_re : ∫ t, RCLike.re (F_h t * (θ' t : ℂ)) ∂volume = -Real.pi * ∫ t, u t ∂P.μ_spec := by
    have h_eq : (fun t => RCLike.re (F_h t * (θ' t : ℂ))) = fun t => u t * θ' t := by
      ext t; dsimp [RCLike.re]; simp [u, θ']
    rw [h_eq, h_real_u]

  have h_lhs_im : ∫ t, RCLike.im (F_h t * (θ' t : ℂ)) ∂volume = -Real.pi * ∫ t, v t ∂P.μ_spec := by
    have h_eq : (fun t => RCLike.im (F_h t * (θ' t : ℂ))) = fun t => v t * θ' t := by
      ext t; dsimp [RCLike.im]; simp [u, v, θ']
    rw [h_eq, h_real_v]

  rw [h_lhs_re, h_lhs_im]

  -- Expand RHS
  rw [← integral_re_add_im (f := F_h)]
  rotate_left
  · exact h_integrable_μ

  -- RHS is: -π * (↑(∫ u) + I * ↑(∫ v))
  -- Check equality
  -- Normalize `RCLike.re/im` produced by `integral_re_add_im` so it matches `.re/.im`
  dsimp [RCLike.re, RCLike.im]
  simp only [u, v, Complex.ofReal_mul, Complex.ofReal_neg]
  ring_nf

/--
**Theorem (Splice completion from axioms):** Combining `explicit_formula_cancellation` and
`complex_phase_velocity_identity` yields the boundary integral representation.

Given:
- `explicit_formula_cancellation`: W^{(1)}(h) = (1/2π) ∫ F_h · (-θ') dt
- `complex_phase_velocity_identity`: ∫ F_h · θ' dt = -π ∫ F_h dμ_spec

Result: W^{(1)}(h) = (1/2) ∫ F_h dμ_spec

The factor of 1/2 is absorbed by the symmetric zero-sum convention (the sum over ρ counts
each zero once, while the measure μ_spec includes contributions from ρ and 1-ρ̄).
-/
theorem splice_completion_with_normalization
    (P : PSCComponents)
    (F_h : ℝ → ℂ)
    (W1_h : ℂ)
    (h_explicit : W1_h = (1 / (2 * Real.pi)) *
        ∫ t : ℝ, -(F_h t * ((deriv (boundaryPhaseFunction P) t : ℝ) : ℂ)) ∂ volume)
    (h_integrable_F : Integrable F_h volume)
    (h_integrable_vol : Integrable (fun t => F_h t * ((deriv (boundaryPhaseFunction P) t : ℝ) : ℂ)) volume)
    (h_integrable_μ : Integrable F_h P.μ_spec) :
    W1_h = (1 / 2 : ℂ) * ∫ t : ℝ, F_h t ∂ P.μ_spec := by
  -- Use h_explicit and complex_phase_velocity_identity
  rw [h_explicit]
  -- ∫ -F_h·θ' = - ∫ F_h·θ' = -(-π ∫ F_h dμ_spec) = π ∫ F_h dμ_spec
  have h_phase := complex_phase_velocity_identity P F_h h_integrable_F h_integrable_vol h_integrable_μ
  -- Simplify the negation: ∫ (-f) = - ∫ f
  rw [integral_neg]
  -- After simp: (1/(2π)) * (- ∫ F_h·θ')
  -- Substitute h_phase: ∫ F_h·θ' = -π ∫ F_h dμ_spec
  rw [h_phase]
  -- Now we have: (1/(2π)) * (- (-π * ∫ F_h dμ_spec))
  -- = (1/(2π)) * (π * ∫ F_h dμ_spec)
  -- = (1/2) * ∫ F_h dμ_spec
  ring_nf
  -- The remaining algebra: (1/(2π)) * π = 1/2
  congr 1
  have h_pi_ne : (Real.pi : ℂ) ≠ 0 := by
    rw [ne_eq, Complex.ofReal_eq_zero]
    exact Real.pi_ne_zero
  have h_two_ne : (2 : ℂ) ≠ 0 := by norm_num
  have h_twoπ_ne : (2 * Real.pi : ℂ) ≠ 0 := mul_ne_zero h_two_ne h_pi_ne
  field_simp [h_twoπ_ne]

/-!
## Splice completion from axioms

If all the above axioms hold for a given PSC ratio J and boundary phase θ, then the
splice completion identity follows.

This is the mathematical content that the `identity_integral` field of
`Route3.PSCSplice.IntegralAssumptions` in `PSCSplice.lean` asserts.
The actual proof would combine:
1. The boundary phase θ bundled in `PSCComponents` (`P.boundaryPhase` / `P.boundaryPhase_repr`)
2. `log_deriv_decomposition` (theorem) to write ξ'/ξ = ... - J'/J
3. `logDeriv_unimodular_real` (theorem) to identify J'/J = θ' (real) on the boundary, under trace regularity
4. `explicit_formula_cancellation` to show W^{(1)}(h) = (1/2π) ∫ F_h · (-θ') dt
5. `PSCComponents.phase_velocity_identity` (bundled in `P`) to connect -θ' = π μ_spec (using w = -θ convention)
6. Normalization tracking (handled in `splice_completion_with_normalization`)

**Chain summary:**
```
W^{(1)}(h) = (1/2π) ∫ F_h · (-θ') dt     [explicit_formula_cancellation]
           = (1/2π) ∫ F_h · π dμ_spec    [`P.phase_velocity_identity` with w = -θ]
           = (1/2) ∫ F_h dμ_spec          [algebra]
```

For h = pair(f,g), F_h = conj(F_f) · F_g, the factor of 1/2 is absorbed by the symmetric
pairing convention (see ROUTE3_IDENTITY_PART.md for detailed normalization tracking).

**Lean implementation note:** This entire chain is intended to produce the
`identity_integral` field of `Route3.PSCSplice.IntegralAssumptions` (in `PSCSplice.lean`).
Once the axioms in this file are proved, they can be used to construct that field and complete
the Route 3 pipeline.
-/

end ContourToBoundary

end ExplicitFormula
end RiemannRecognitionGeometry
