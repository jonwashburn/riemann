/-
# PSC → Route 3 splice (μ_spec wrapper)

This file is intentionally lightweight: it does **not** attempt to re-prove any analytic number theory.
It just packages the boundary-certificate manuscript’s canonical positive boundary measure

`μ_spec : Measure ℝ`

as the measure feeding the existing Route 3 *measure-first* pipeline (`AssumptionsMeasure → RHμ`).

In other words: once you can identify the Route‑3 Weil pairing with an `L²(μ_spec)` inner product,
all remaining steps (quotient nulls → complete → reflection positivity → Weil gate → RH) are
mechanical and already implemented.
-/

import RiemannRecognitionGeometry.ExplicitFormula.Route3HypBundle
import RiemannRecognitionGeometry.ExplicitFormula.ContourToBoundary
import Mathlib.MeasureTheory.Integral.Bochner

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open MeasureTheory
open scoped InnerProductSpace

namespace Route3

-- Route 3 is already specialized to the concrete test-function type `Route3.F := ℝ → ℂ`
-- (see `Route3Targets.lean`). We keep only the `TestSpace` operations abstract.
variable [TestSpace F]

namespace PSCSplice

/--
PSC splice assumptions, written in Route‑3’s *measure-first* form but with the canonical name `μ_spec`.

This is definitionally the same data as `Route3.AssumptionsMeasure` (just renaming the measure field).
-/
structure Assumptions where
  /-- The Lagarias explicit-formula framework (`W¹`, etc.). -/
  L : LagariasFramework F
  /-- PSC spectral boundary measure on `ℝ` (positive by definition of `Measure`). -/
  μ_spec : Measure ℝ := volume
  /-- Route‑3 boundary transform (assumed ℂ-linear). -/
  transform : F →ₗ[ℂ] (ℝ → ℂ)
  /-- (Normalization) `transform` agrees with the critical-line Mellin transform. -/
  transform_eq_mellinOnCriticalLine :
    ∀ f : F, transform f = fun t : ℝ => mellinOnCriticalLine (F := F) f t
  /-- L² admissibility: the transformed functions lie in `L²(μ_spec)`. -/
  memL2 : ∀ f : F, MeasureTheory.Memℒp (transform f) 2 μ_spec
  /-- The measure-first sesquilinear identity (Hilbert-space form). -/
  identity :
    ∀ f g : F,
      L.W1 (pair (F := F) f g) =
        ⟪(memL2 f).toLp (transform f), (memL2 g).toLp (transform g)⟫_ℂ

/--
PSC splice assumptions in the **Bochner-integral form**:

`W¹(pair f g) = ∫ conj(F_f(t)) · F_g(t) dμ_spec`.

This is often the most natural “analysis lemma” statement; it converts automatically to the
Hilbert-space form `Assumptions` via `SesqMeasureIntegralIdentity.toSesqMeasureIdentity`.
-/
structure IntegralAssumptions where
  /-- The Lagarias explicit-formula framework (`W¹`, etc.). -/
  L : LagariasFramework F
  /-- PSC spectral boundary measure on `ℝ` (positive by definition of `Measure`). -/
  μ_spec : Measure ℝ := volume
  /-- Route‑3 boundary transform (assumed ℂ-linear). -/
  transform : F →ₗ[ℂ] (ℝ → ℂ)
  /-- (Normalization) `transform` agrees with the critical-line Mellin transform. -/
  transform_eq_mellinOnCriticalLine :
    ∀ f : F, transform f = fun t : ℝ => mellinOnCriticalLine (F := F) f t
  /-- L² admissibility: the transformed functions lie in `L²(μ_spec)`. -/
  memL2 : ∀ f : F, MeasureTheory.Memℒp (transform f) 2 μ_spec
  /-- The measure-first sesquilinear identity as an integral pairing against `μ_spec`. -/
  identity_integral :
    ∀ f g : F,
      L.W1 (pair (F := F) f g) =
        ∫ t : ℝ, (starRingEnd ℂ (transform f t)) * (transform g t) ∂ μ_spec

/-- Convert integral-form PSC assumptions into Hilbert-form PSC assumptions. -/
def IntegralAssumptions.toAssumptions (A : IntegralAssumptions) : Assumptions where
  L := A.L
  μ_spec := A.μ_spec
  transform := A.transform
  transform_eq_mellinOnCriticalLine := A.transform_eq_mellinOnCriticalLine
  memL2 := A.memL2
  identity := by
    -- Convert via the general measure-first integral-to-Hilbert lemma.
    intro f g
    let S : SesqMeasureIntegralIdentity (F := F) (L := A.L) :=
      { μ := A.μ_spec
        transform := A.transform
        memL2 := A.memL2
        identity_integral := A.identity_integral }
    simpa using (SesqMeasureIntegralIdentity.toSesqMeasureIdentity (F := F) (L := A.L) S).identity f g

/-- Convert PSC splice assumptions into the Route‑3 `AssumptionsMeasure` bundle. -/
def toRoute3AssumptionsMeasure (A : Assumptions) : AssumptionsMeasure where
  L := A.L
  μ := A.μ_spec
  transform := A.transform
  transform_eq_mellinOnCriticalLine := A.transform_eq_mellinOnCriticalLine
  memL2 := A.memL2
  identity := A.identity

/-- PSC splice: once the `L²(μ_spec)` identity holds, the Route‑3 Weil gate fires and yields RH. -/
theorem RHμ_spec (A : Assumptions) : RiemannHypothesis :=
  RHμ (A := toRoute3AssumptionsMeasure A)

/-! The same conclusion, starting from the integral-form identity. -/
theorem RHμ_spec_integral (A : IntegralAssumptions) : RiemannHypothesis :=
  RHμ_spec (A := IntegralAssumptions.toAssumptions A)

/-!
## Normalization helper: absorb a real scalar into the measure

In practice, contour-normalization conventions can produce identities of the form

`W¹(pair f g) = (c : ℂ) * ∫ conj(F_f) · F_g dμ`,

where `c` is a *real* scalar (e.g. `1/2`). Since scaling a measure by a finite constant scales the
Bochner integral, we can absorb this factor into the measure and recover the “clean” integral-form
identity against a rescaled positive measure.
-/

/--
If the Bochner identity holds with a real prefactor `c.toReal` on the RHS, then it holds *without*
that prefactor against the rescaled measure `c • μ_spec`.
-/
def IntegralAssumptions.ofRealScalarMulIntegral
    (L : LagariasFramework F)
    (μ_spec : Measure ℝ)
    (transform : F →ₗ[ℂ] (ℝ → ℂ))
    (transform_eq_mellinOnCriticalLine :
      ∀ f : F, transform f = fun t : ℝ => mellinOnCriticalLine (F := F) f t)
    (memL2 : ∀ f : F, MeasureTheory.Memℒp (transform f) 2 μ_spec)
    (c : ENNReal) (hc : c ≠ (⊤ : ENNReal))
    (identity_real_scalar :
      ∀ f g : F,
        L.W1 (pair (F := F) f g) =
          ((c.toReal : ℝ) : ℂ) *
            ∫ t : ℝ, (starRingEnd ℂ (transform f t)) * (transform g t) ∂ μ_spec) :
    IntegralAssumptions where
  L := L
  μ_spec := c • μ_spec
  transform := transform
  transform_eq_mellinOnCriticalLine := transform_eq_mellinOnCriticalLine
  memL2 := fun f => (memL2 f).smul_measure hc
  identity_integral := by
    intro f g
    -- Rewrite the target integral using `integral_smul_measure`.
    -- `∫ · ∂(c • μ) = c.toReal • ∫ · ∂μ`, then convert real-scalar action on `ℂ` to multiplication.
    have hscale :
        (∫ t : ℝ, (starRingEnd ℂ (transform f t)) * (transform g t) ∂ (c • μ_spec)) =
          (c.toReal : ℝ) •
            (∫ t : ℝ, (starRingEnd ℂ (transform f t)) * (transform g t) ∂ μ_spec) := by
      simpa using (MeasureTheory.integral_smul_measure
        (μ := μ_spec)
        (f := fun t : ℝ => (starRingEnd ℂ (transform f t)) * (transform g t))
        c)
    -- Convert `•` into multiplication by a real in `ℂ`.
    have hreal_smul :
        ((c.toReal : ℝ) •
            (∫ t : ℝ, (starRingEnd ℂ (transform f t)) * (transform g t) ∂ μ_spec)) =
          ((c.toReal : ℝ) : ℂ) *
            (∫ t : ℝ, (starRingEnd ℂ (transform f t)) * (transform g t) ∂ μ_spec) := by
      simpa [Complex.real_smul] using (rfl :
        ((c.toReal : ℝ) •
            (∫ t : ℝ, (starRingEnd ℂ (transform f t)) * (transform g t) ∂ μ_spec)) =
          ((c.toReal : ℝ) •
            (∫ t : ℝ, (starRingEnd ℂ (transform f t)) * (transform g t) ∂ μ_spec)))
    -- Put it together.
    -- Goal: L.W1(...) = ∫ ... ∂ (c•μ_spec)
    -- Use the assumed scaled identity, then rewrite the RHS integral.
    have hid := identity_real_scalar f g
    -- Replace the integral over `c•μ_spec` using `hscale` and `hreal_smul`.
    -- We rewrite the goal RHS, then close by `exact`.
    -- (We need symmetry: goal RHS = (c.toReal:ℂ) * ∫ ... ∂ μ_spec.)
    calc
      L.W1 (pair (F := F) f g)
          = ((c.toReal : ℝ) : ℂ) *
              ∫ t : ℝ, (starRingEnd ℂ (transform f t)) * (transform g t) ∂ μ_spec := hid
      _   = (∫ t : ℝ, (starRingEnd ℂ (transform f t)) * (transform g t) ∂ (c • μ_spec)) := by
            -- rewrite RHS integral
            -- hscale gives integral = c.toReal • ∫; then hreal_smul converts to multiplication.
            -- So (c.toReal:ℂ) * ∫ = integral over c•μ.
            -- We'll go in the forward direction.
            -- From hscale: integral_c = (c.toReal) • integral_μ.
            -- So integral_c = (c.toReal:ℂ) * integral_μ.
            -- Rewrite and finish by `simp`.
            have : (∫ t : ℝ, (starRingEnd ℂ (transform f t)) * (transform g t) ∂ (c • μ_spec)) =
                ((c.toReal : ℝ) : ℂ) *
                  ∫ t : ℝ, (starRingEnd ℂ (transform f t)) * (transform g t) ∂ μ_spec := by
              -- start from hscale
              -- integral_c = (c.toReal) • integral_μ
              --          = (c.toReal:ℂ) * integral_μ
              calc
                (∫ t : ℝ, (starRingEnd ℂ (transform f t)) * (transform g t) ∂ (c • μ_spec))
                    = (c.toReal : ℝ) •
                        (∫ t : ℝ, (starRingEnd ℂ (transform f t)) * (transform g t) ∂ μ_spec) := hscale
                _   = ((c.toReal : ℝ) : ℂ) *
                        (∫ t : ℝ, (starRingEnd ℂ (transform f t)) * (transform g t) ∂ μ_spec) := hreal_smul
            simpa [this] using this.symm

/--
Special case of `IntegralAssumptions.ofRealScalarMulIntegral` for the common normalization factor `1/2`.

If you can prove
`W¹(pair f g) = (1/2) * ∫ conj(F_f) · F_g dμ_spec`,
then you automatically get an `IntegralAssumptions` instance for the *rescaled* measure
`ENNReal.ofReal (1/2) • μ_spec` where the identity holds without the prefactor.
-/
def IntegralAssumptions.ofHalfScalarMulIntegral
    (L : LagariasFramework F)
    (μ_spec : Measure ℝ)
    (transform : F →ₗ[ℂ] (ℝ → ℂ))
    (transform_eq_mellinOnCriticalLine :
      ∀ f : F, transform f = fun t : ℝ => mellinOnCriticalLine (F := F) f t)
    (memL2 : ∀ f : F, MeasureTheory.Memℒp (transform f) 2 μ_spec)
    (identity_half :
      ∀ f g : F,
        L.W1 (pair (F := F) f g) =
          (1 / 2 : ℂ) * ∫ t : ℝ, (starRingEnd ℂ (transform f t)) * (transform g t) ∂ μ_spec) :
    IntegralAssumptions := by
  -- `ENNReal.ofReal (1/2)` is a finite scaling constant, so we can absorb the prefactor into the measure.
  refine IntegralAssumptions.ofRealScalarMulIntegral
    (L := L) (μ_spec := μ_spec) (transform := transform)
    (transform_eq_mellinOnCriticalLine := transform_eq_mellinOnCriticalLine)
    (memL2 := memL2)
    (c := ENNReal.ofReal (1 / 2 : ℝ)) (hc := by simpa using (ENNReal.ofReal_ne_top (1 / 2 : ℝ)))
    (identity_real_scalar := ?_)
  intro f g
  -- `ENNReal.ofReal (1/2)` has `toReal = 1/2`.
  simpa using (identity_half f g)

/-!
## Building the splice identity from `ContourToBoundary` axioms (with normalization)

`ContourToBoundary.splice_completion_with_normalization` gives the identity with a real prefactor `1/2`.
This definition packages that into a `PSCSplice.IntegralAssumptions` instance by absorbing the prefactor
into the measure (scaling by `ENNReal.ofReal (1/2)`).
-/

open ContourToBoundary

private def pairTransform (transform : F →ₗ[ℂ] (ℝ → ℂ)) (f g : F) : ℝ → ℂ :=
  fun t : ℝ => (starRingEnd ℂ (transform f t)) * (transform g t)

/--
If the contour-to-boundary axioms hold for some `P : PSCComponents`, then (given routine integrability
hypotheses) we can build a splice identity bundle. The resulting measure is scaled by `1/2` to absorb
the normalization appearing in `splice_completion_with_normalization`.
-/
def IntegralAssumptions.ofContourToBoundary
    (P : ContourToBoundary.PSCComponents)
    (L : LagariasFramework F)
    (transform : F →ₗ[ℂ] (ℝ → ℂ))
    (transform_eq_mellinOnCriticalLine :
      ∀ f : F, transform f = fun t : ℝ => mellinOnCriticalLine (F := F) f t)
    (memL2 : ∀ f : F, MeasureTheory.Memℒp (transform f) 2 P.μ_spec)
    (h_explicit :
      ∀ f g : F,
        ContourToBoundary.explicit_formula_cancellation
          (L := L) (P := P) (h := pair (F := F) f g))
    (h_integrable_F : ∀ f g : F, Integrable (pairTransform transform f g) volume)
    (h_integrable_vol :
      ∀ f g : F,
        Integrable
          (fun t : ℝ =>
            pairTransform transform f g t *
              ((deriv (ContourToBoundary.boundaryPhaseFunction P) t : ℝ) : ℂ))
          volume)
    (h_integrable_μ : ∀ f g : F, Integrable (pairTransform transform f g) P.μ_spec) :
    IntegralAssumptions :=
by
  -- First, prove the `1/2`-normalized identity for all `f,g`.
  have identity_half :
      ∀ f g : F,
        L.W1 (pair (F := F) f g) =
          (1 / 2 : ℂ) * ∫ t : ℝ, pairTransform transform f g t ∂ P.μ_spec := by
    intro f g
    -- Instantiate `splice_completion_with_normalization` at `F_h := conj(F_f) * F_g`.
    have h_explicit :
        L.W1 (pair (F := F) f g) =
          (1 / (2 * Real.pi)) *
            ∫ t : ℝ, -(pairTransform transform f g t *
                ((deriv (ContourToBoundary.boundaryPhaseFunction P) t : ℝ) : ℂ)) ∂ volume := by
      -- Start from the contour-to-boundary explicit cancellation axiom, stated in terms of `M[pair f g]`.
      have h0 :
          L.W1 (pair (F := F) f g) =
            (1 / (2 * Real.pi)) *
              ∫ t : ℝ,
                -(M[pair (F := F) f g](1/2 + Complex.I * t) *
                    ((deriv (ContourToBoundary.boundaryPhaseFunction P) t : ℝ) : ℂ)) ∂ volume := by
        -- `explicit_formula_cancellation` is now a hypothesis (`Prop`), so extract it from `h_explicit`.
        simpa [ContourToBoundary.explicit_formula_cancellation] using (h_explicit f g)
      -- Rewrite `M[pair f g](1/2+it)` as `conj(M[f](1/2+it)) * M[g](1/2+it)`, then use the supplied
      -- `transform = mellinOnCriticalLine` normalization to convert to `pairTransform`.
      have hpair_mellin :
          (fun t : ℝ => M[pair (F := F) f g](1/2 + Complex.I * t)) =
            fun t : ℝ => pairTransform transform f g t := by
        funext t
        -- Mellin of the sesquilinear test `pair` on the critical line.
        -- `simp` uses `TestSpace.mellin_conv`, `TestSpace.mellin_tilde`, `TestSpace.mellin_star`.
        -- Work at `s = 1/2 + i t`.
        set s : ℂ := (1/2 : ℂ) + Complex.I * t
        have hs_conj : starRingEnd ℂ (1 - s) = s := by
          -- `conj(1 - (1/2 + i t)) = 1/2 + i t`
          -- Expand and simplify conjugations; `norm_num` closes the remaining rational arithmetic.
          dsimp [s]
          -- `simp` handles conjugation of `I`, `t`, and rational scalars.
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
          -- Close the remaining rational identity `1 - 1/2 = 1/2`.
          have hconj2 : (starRingEnd ℂ) (2 : ℂ) = (2 : ℂ) := by
            -- `simp` doesn't always reduce `starRingEnd` on numerals, so unfold via `Complex.conj`.
            simpa [starRingEnd] using (Complex.conj_ofReal (2 : ℝ))
          -- Rewrite `conj(2)` and finish by ring normalization.
          rw [hconj2]
          ring_nf
        have hm :
            M[pair (F := F) f g](s) =
              (M[g](s)) * (starRingEnd ℂ (M[f](s))) := by
          -- Expand `pair` and rewrite using the Mellin identities, then specialize to the critical line via `hs_conj`.
          calc
            M[pair (F := F) f g](s)
                = M[g](s) * M[˜ₘ (⋆ₜ f)](s) := by
                    simp [pair]
            _ = M[g](s) * M[⋆ₜ f](1 - s) := by
                    simp
            _ = M[g](s) * starRingEnd ℂ (M[f](starRingEnd ℂ (1 - s))) := by
                    simp
            _ = M[g](s) * starRingEnd ℂ (M[f](s)) := by
                    simpa [hs_conj]
        -- Convert `M[·] s` to the chosen `transform · t`.
        have hf : transform f t = M[f](s) := by
          have := congrArg (fun Fh => Fh t) (transform_eq_mellinOnCriticalLine f)
          simpa [mellinOnCriticalLine, criticalLine, s, mul_comm, mul_left_comm, mul_assoc] using this
        have hg : transform g t = M[g](s) := by
          have := congrArg (fun Fh => Fh t) (transform_eq_mellinOnCriticalLine g)
          simpa [mellinOnCriticalLine, criticalLine, s, mul_comm, mul_left_comm, mul_assoc] using this
        -- Finish by rewriting `pairTransform` and commuting the product.
        -- (We keep the `pairTransform` convention `conj(F_f) * F_g`.)
        have hm' : M[pair (F := F) f g](s) = (starRingEnd ℂ (M[f](s))) * (M[g](s)) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hm
        simpa [pairTransform, hf, hg, s, mul_comm, mul_left_comm, mul_assoc] using hm'
      -- Use the pointwise rewrite inside the integral.
      have hpair_mellin_pt :
          ∀ t : ℝ,
            M[pair (F := F) f g]((2 : ℂ)⁻¹ + Complex.I * t) = pairTransform transform f g t := by
        intro t
        -- `1/2` in `ℂ` is definitionaly `2⁻¹`; normalize to match the form used by `simp`/pretty-printing.
        simpa [one_div] using congrArg (fun Fh => Fh t) hpair_mellin
      -- Rewrite the integrand pointwise and use `integral_congr_ae`.
      have hintegral :
          (∫ t : ℝ,
              -(M[pair (F := F) f g]((2 : ℂ)⁻¹ + Complex.I * t) *
                    ((deriv (ContourToBoundary.boundaryPhaseFunction P) t : ℝ) : ℂ)) ∂ volume) =
            ∫ t : ℝ,
              -(pairTransform transform f g t *
                    ((deriv (ContourToBoundary.boundaryPhaseFunction P) t : ℝ) : ℂ)) ∂ volume := by
        refine MeasureTheory.integral_congr_ae ?_
        refine Filter.Eventually.of_forall ?_
        intro t
        simpa using
          congrArg (fun z => -(z * ((deriv (ContourToBoundary.boundaryPhaseFunction P) t : ℝ) : ℂ)))
            (hpair_mellin_pt t)
      -- Finish.
      -- `integral_congr_ae` gives definitional equality of the integrals, so we can `simp` using `hintegral`.
      simpa [hintegral] using h0
    -- Apply the contour-to-boundary splice theorem.
    simpa [pairTransform] using
      (ContourToBoundary.splice_completion_with_normalization
        (P := P)
        (F_h := pairTransform transform f g)
        (W1_h := L.W1 (pair (F := F) f g))
        (h_explicit := h_explicit)
        (h_integrable_F := h_integrable_F f g)
        (h_integrable_vol := h_integrable_vol f g)
        (h_integrable_μ := h_integrable_μ f g))
  -- Absorb the factor `1/2` into the measure.
  exact IntegralAssumptions.ofHalfScalarMulIntegral
    (L := L)
    (μ_spec := P.μ_spec)
    (transform := transform)
    (transform_eq_mellinOnCriticalLine := transform_eq_mellinOnCriticalLine)
    (memL2 := memL2)
    (identity_half := by
      intro f g
      simpa [pairTransform] using identity_half f g)

/--
Route‑3 conclusion: if the contour-to-boundary axioms are available (and the routine integrability
hypotheses needed to apply them are supplied), then RH follows via the existing measure-first Route‑3
pipeline.
-/
theorem RH_ofContourToBoundary
    (P : ContourToBoundary.PSCComponents)
    (L : LagariasFramework F)
    (transform : F →ₗ[ℂ] (ℝ → ℂ))
    (transform_eq_mellinOnCriticalLine :
      ∀ f : F, transform f = fun t : ℝ => mellinOnCriticalLine (F := F) f t)
    (memL2 : ∀ f : F, MeasureTheory.Memℒp (transform f) 2 P.μ_spec)
    (h_explicit :
      ∀ f g : F,
        ContourToBoundary.explicit_formula_cancellation
          (L := L) (P := P) (h := pair (F := F) f g))
    (h_integrable_F : ∀ f g : F, Integrable (pairTransform transform f g) volume)
    (h_integrable_vol :
      ∀ f g : F,
        Integrable
          (fun t : ℝ =>
            pairTransform transform f g t *
              ((deriv (ContourToBoundary.boundaryPhaseFunction P) t : ℝ) : ℂ))
          volume)
    (h_integrable_μ : ∀ f g : F, Integrable (pairTransform transform f g) P.μ_spec) :
    RiemannHypothesis :=
by
  -- Build the integral-form splice assumptions and fire the existing pipeline.
  exact RHμ_spec_integral
    (A := IntegralAssumptions.ofContourToBoundary
      (P := P) (L := L) (transform := transform)
      (transform_eq_mellinOnCriticalLine := transform_eq_mellinOnCriticalLine)
      (memL2 := memL2)
      (h_explicit := h_explicit)
      (h_integrable_F := h_integrable_F)
      (h_integrable_vol := h_integrable_vol)
      (h_integrable_μ := h_integrable_μ))

/-!
## Splice Completion: the single remaining *identity lemma*

The only non-mechanical piece remaining is the **identity claim**:

> The Route‑3 Weil functional `W¹(pair f g)` equals the boundary Bochner pairing
> `∫ conj(F_f(t)) · F_g(t) dμ_spec(t)`.

In Lean, this is exactly the `identity_integral` field of `IntegralAssumptions` above.

### Why this identity holds (proof sketch from `ROUTE3_IDENTITY_PART.md`)

The PSC ratio from `Riemann-active.txt` is:
```
  J(s) = det₂(I - A(s)) / (O(s) · ξ(s))
```
where `det₂` is the 2-modified Fredholm determinant for the diagonal prime operator, `O` is an outer
function, and `ξ` is the completed Riemann xi. On the critical line `Re s = 1/2`, we have `|J| = 1`
(unimodular), so `J = exp(i·θ(t))` for a real phase `θ(t)`.

Taking log-derivatives:
```
  logDeriv ξ = logDeriv det₂ - logDeriv O - logDeriv J
```

On the boundary, `logDeriv J (1/2+it) = deriv θ t` (real-valued). Therefore:
```
  logDeriv ξ = [(logDeriv det₂) - (logDeriv O)] - deriv θ
```

The Route‑3 contour integral for `W¹` picks up `-logDeriv ξ` when moved to the critical line. The bracketed
term cancels against the arithmetic/archimedean parts (`W_arith`, `W²`, `W⁰`) via Lagarias' explicit
formula. What remains is `deriv θ`, and the PSC phase–velocity identity gives `-(deriv θ) = π μ_spec`.
After tracking normalization, this yields the target identity.

See `ExplicitFormula/ContourToBoundary.lean` for the axiomatized contour-to-boundary chain and the
proved complex-linear extension (`complex_phase_velocity_identity`).
-/

/-!
## Explicit Formula Cancellation Structure

This structure packages the claim that the arithmetic/archimedean parts of the log-derivative
cancel against `W_arith`, `W²`, `W⁰` in Lagarias' explicit formula, leaving only the boundary
phase contribution.
-/

/--
**Explicit Formula Cancellation** (sub-lemma for splice completion).

This structure packages the claim that:
1. The Lagarias explicit formula holds: `M[f](1) - W¹(f) + M[f](0) = W_arith(f)`
2. The arithmetic side `W_arith` corresponds to `(det₂)'/det₂ - O'/O` boundary contributions
3. After cancellation, `W¹` equals the boundary phase pairing

This is the "SC2" step in `ROUTE3_IDENTITY_PART.md`.
-/
structure ExplicitFormulaCancellation where
  /-- The Lagarias framework (provides W¹, W_arith, and explicit formula). -/
  L : LagariasFramework F
  /-- The PSC boundary measure. -/
  μ_spec : Measure ℝ
  /-- The boundary transform. -/
  transform : F →ₗ[ℂ] (ℝ → ℂ)
  /--
  **Cancellation claim:** after applying the explicit formula and moving the W¹ contour to the
  boundary, the det₂ and outer O contributions cancel against W_arith and boundary terms,
  leaving exactly the phase pairing against μ_spec.
  -/
  cancellation :
    ∀ f g : F,
      L.W1 (pair (F := F) f g) =
        ∫ t : ℝ, (starRingEnd ℂ (transform f t)) * (transform g t) ∂ μ_spec

/-- Convert explicit formula cancellation into IntegralAssumptions. -/
def ExplicitFormulaCancellation.toIntegralAssumptions
    (E : ExplicitFormulaCancellation)
    (transform_eq : ∀ f : F, E.transform f = fun t : ℝ => mellinOnCriticalLine (F := F) f t)
    (memL2 : ∀ f : F, MeasureTheory.Memℒp (E.transform f) 2 E.μ_spec) :
    IntegralAssumptions where
  L := E.L
  μ_spec := E.μ_spec
  transform := E.transform
  transform_eq_mellinOnCriticalLine := transform_eq
  memL2 := memL2
  identity_integral := E.cancellation

/-- Explicit formula cancellation immediately yields RH. -/
theorem RH_of_explicitFormulaCancellation
    (E : ExplicitFormulaCancellation)
    (transform_eq : ∀ f : F, E.transform f = fun t : ℝ => mellinOnCriticalLine (F := F) f t)
    (memL2 : ∀ f : F, MeasureTheory.Memℒp (E.transform f) 2 E.μ_spec) :
    RiemannHypothesis :=
  RHμ_spec_integral (E.toIntegralAssumptions transform_eq memL2)

end PSCSplice
end Route3

end ExplicitFormula
end RiemannRecognitionGeometry
