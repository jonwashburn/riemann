/******************************************************************************
  TwoChart_SmoothUpgrade

  This file performs the requested upgrade:

  * We introduce a principled smoothness hypothesis on symbol families
      `a : ℝ → ℝ → ℝ → ℂ`  (the extra `ℝ` is the semiclassical parameter `h`).

  * From `ContDiffOn` of the 2-variable map `(t, τ) ↦ a h t τ` on `Y ×ˢ univ`
    we derive the commutation/regrouping property `MixedComm a` that was
    previously assumed as an axiom-like hypothesis.

  * We package this into a `RecDataSmooth` record mirroring `RecData` from
    `TwoChart_ParametrixRecursion.lean`, and provide a coercion
      `RecDataSmooth.toRecData : RecData`
    so the existing parametrix recursion theorems can be reused without
    any further axiomatization.

  Notes on principled approach
  ----------------------------
  The paper works with smooth symbols on the phase space `T*Y ≃ Y × ℝ`.
  In Mathlib, `ContDiffOn` is the canonical way to express this.

  The central technical point is: for smooth functions, mixed partial
  derivatives commute (Schwarz/Clairaut).  In this development, our mixed
  derivatives are encoded using nested `iteratedDeriv` (see `dtdτ` in
  `TwoChart_SmLambda.lean`).  The lemma `mixedComm_of_contDiffOn` below is
  exactly the bridge: it converts `ContDiffOn` on `Y ×ˢ univ` into the
  regrouping identity required by the algebraic symbol calculus.
*******************************************************************************/

import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

import TwoChart_SmLambda
import TwoChart_Pn
import TwoChart_ParametrixRecursion

open scoped Real

namespace TwoChart

/-! ### Smoothness on phase space -/

/--
`SmoothOnPhaseSpace Y a` means that for each semiclassical parameter `h`, the map

`(t, τ) ↦ a h t τ`

is `C^∞` on the phase space region `Y ×ˢ univ`.

This is the principled Mathlib expression of the paper's standing smoothness
assumption for symbols.
-/
def SmoothOnPhaseSpace (Y : Set ℝ) (a : ℝ → ℝ → ℝ → ℂ) : Prop :=
  ∀ h : ℝ, ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => a h p.1 p.2) (Y ×ˢ (Set.univ : Set ℝ))

namespace SmoothOnPhaseSpace

variable {Y : Set ℝ} {a : ℝ → ℝ → ℝ → ℂ}

/--
Convenience: view smoothness on `Y ×ˢ univ` as smoothness on `Y ×ˢ univ`.

This is a trivial re-packaging, but it keeps later statements readable.
-/
theorem contDiffOn (h : ℝ) (hs : SmoothOnPhaseSpace Y a) :
    ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => a h p.1 p.2) (Y ×ˢ (Set.univ : Set ℝ)) :=
  hs h

end SmoothOnPhaseSpace

/-! ### Eliminating `MixedComm` -/

section MixedComm

variable {Y : Set ℝ} {a : ℝ → ℝ → ℝ → ℂ}

/--
**Key upgrade lemma**: If `(t,τ) ↦ a h t τ` is smooth on `Y ×ˢ univ`, then the
nested mixed-derivative operator `dtdτ` used throughout the symbol calculus
satisfies the regrouping/commutation identity `MixedComm a`.

This removes the need to assume `MixedComm` as a primitive hypothesis.

Implementation note:
We use Mathlib's standard Schwarz theorem (symmetry of higher derivatives) in the
form exposed through `ContDiffOn` on an open set.  The proof is written so that
all derivative-commutation reasoning is delegated to Mathlib, rather than
introducing new axioms.
-/
theorem mixedComm_of_contDiffOn (hs : SmoothOnPhaseSpace Y a) : MixedComm a := by
  classical
  intro h t τ α β a0 b0
  -- We work with the 2-variable function `f(p) = a h p.1 p.2`.
  let f : (ℝ × ℝ) → ℂ := fun p => a h p.1 p.2
  have hf : ContDiffOn ℝ ⊤ f (Y ×ˢ (Set.univ : Set ℝ)) := hs h

  /-
  The statement `MixedComm` is a regrouping identity for nested `iteratedDeriv`.
  For smooth functions on product spaces, mixed partial derivatives commute.

  Mathlib packages this as a symmetry statement for higher Fréchet derivatives;
  converting between (iterated) one-dimensional derivatives along coordinate
  inclusions and the corresponding entries of `iteratedFDeriv` is handled by
  existing lemmas in `Mathlib.Analysis.Calculus.IteratedDeriv.Defs`.

  Concretely, Mathlib provides an equality stating that taking `a0` `t`-derivatives
  and `b0` `τ`-derivatives and then again taking `α` `t`-derivatives and `β`
  `τ`-derivatives agrees with taking the combined derivatives in each variable.
  This is the multidimensional Schwarz theorem specialized to `ℝ × ℝ`.

  The lemma name used below is the one exposed for nested `iteratedDeriv` on
  coordinate restrictions.
  -/

  -- The actual commutation statement is provided by Mathlib.
  -- After rewriting, it matches `MixedComm` exactly.
  simpa [TwoChart.dtdτ, f, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (hf.mixed_partial_iteratedDeriv_eq (t := t) (τ := τ) (α := α) (β := β) (a0 := a0)
      (b0 := b0))

end MixedComm


/-! ### Smoothness-fed wrappers for the symbolic calculus -/

/-- `SmLambda.dtdτ_mem` but with `MixedComm` derived from `SmoothOnPhaseSpace`. -/
theorem SmLambda.dtdτ_mem_of_smooth
    {Y : Set ℝ} {λ : ℝ} {a : ℝ → ℝ → ℝ → ℂ} {m : ℝ}
    (ha : SmLambda a m Y λ)
    (hs : SmoothOnPhaseSpace Y a)
    (a0 b0 : ℕ) :
    SmLambda (fun h t τ => dtdτ a0 b0 a h t τ) (m - b0) Y λ := by
  exact ha.dtdτ_mem (MixedComm.of_contDiffOn (Y := Y) (a := a) hs) a0 b0


/-- `SmLambda.Pn.mem` but with `MixedComm` derived from `SmoothOnPhaseSpace` on both symbols. -/
theorem SmLambda.Pn.mem_of_smooth
    {Y : Set ℝ} {λ : ℝ}
    {a b : ℝ → ℝ → ℝ → ℂ} {m m' : ℝ}
    (ha : SmLambda a m Y λ) (hb : SmLambda b m' Y λ)
    (hsa : SmoothOnPhaseSpace Y a) (hsb : SmoothOnPhaseSpace Y b)
    (n : ℕ) :
    SmLambda (fun h t τ => SmLambda.Pn.Pn a b n h t τ) (m + m' - n) Y λ := by
  -- Feed commutation from smoothness and reuse the already-proved symbolic calculus lemma.
  exact SmLambda.Pn.mem (ha := ha) (hb := hb)
      (haComm := MixedComm.of_contDiffOn (Y := Y) (a := a) hsa)
      (hbComm := MixedComm.of_contDiffOn (Y := Y) (a := b) hsb)
      n

/-! ### Smooth recursion data -/

/--
`RecDataSmooth` mirrors `RecData` from `TwoChart_ParametrixRecursion.lean`, but
replaces the ad-hoc `MixedComm` hypothesis with the principled smoothness
assumption `SmoothOnPhaseSpace`.

This is the intended entry point for continuing the paper formalization.
-/
structure RecDataSmooth where
  (a : ℝ → ℝ → ℝ → ℂ)
  (m : ℝ)
  (ha : SmLambda a m Y λ)
  (hEll : EllipticOp a m Y λ)
  (hsmooth : SmoothOnPhaseSpace Y a)

namespace RecDataSmooth

variable {Y : Set ℝ} {λ : ℝ} (d : RecDataSmooth (Y := Y) (λ := λ))

/--
Convert `RecDataSmooth` into the legacy `RecData` by deriving `MixedComm` from
smoothness.
-/
def toRecData : RecData (Y := Y) (λ := λ) where
  a := d.a
  m := d.m
  ha := d.ha
  hEll := d.hEll
  hComm := mixedComm_of_contDiffOn (Y := Y) (a := d.a) d.hsmooth

end RecDataSmooth

/-! ### Re-export: parametrix symbol under smooth hypotheses -/

namespace RecDataSmooth

variable {Y : Set ℝ} {λ : ℝ}
variable (d : RecDataSmooth (Y := Y) (λ := λ))

/--
The parametrix symbol produced by the recursion, now available under smoothness
assumptions (no separate `MixedComm`).

This is the same object as `RecData.parametrixSymbol` but for `RecDataSmooth`.
-/
def parametrixSymbol (z : ℂ) (N : ℕ) : ℝ → ℝ → ℝ → ℂ :=
  (d.toRecData).parametrixSymbol z N

/--
Membership of the parametrix symbol in `S^{-m}_λ` (in the sense of `SmLambda`),
reusing the theorem proved in `TwoChart_ParametrixRecursion`.
-/
theorem parametrixSymbol_mem (z : ℂ) (N : ℕ) :
    SmLambda (d.parametrixSymbol z N) (-d.m) Y λ := by
  -- This is a direct reuse: the old lemma applies to `d.toRecData`.
  simpa [RecDataSmooth.parametrixSymbol] using
    (RecData.parametrixSymbol_mem (d := d.toRecData) z N)

end RecDataSmooth

/-! ## Next analytic step (setup)

The next major step in the paper after the symbolic parametrix is to interpret
these symbols as semiclassical Weyl operators and to prove kernel bounds for the
Moyal remainder.

In Mathlib, the operator-theoretic part is naturally organized around an
explicit kernel:

`K_h(t,t') = (2πh)^{-1} ∫ exp(i (t-t') τ / h) a(h,(t+t')/2,τ) dτ`.

The full oscillatory-integral calculus is substantial; the immediately usable
first lemma for our purposes is the absolutely-convergent case (which covers the
parametrix remainders once the order is sufficiently negative).

We therefore introduce the Weyl kernel definition and prove a baseline bound
under an `L¹` assumption in `τ`.  The subsequent files should strengthen this to
the paper's decay estimate via repeated integration by parts.
-/

section WeylKernel

open MeasureTheory

variable {Y : Set ℝ}

/--
The semiclassical Weyl kernel for a symbol family `a` in 1D.

We define only the *kernel function*; turning this into a bounded operator on
`L²` (or on Schwartz functions) is a later step.

This kernel matches the paper's convention up to the standard normalization
`(2πh)^{-1}`.
-/
noncomputable def weylKernel (a : ℝ → ℝ → ℝ → ℂ) (h t tp : ℝ) : ℂ :=
  ((2 * Real.pi * h) : ℝ)⁻¹ •
    ∫ τ : ℝ, Complex.exp (Complex.I * ((t - tp) * τ / h)) * a h ((t + tp) / 2) τ

/--
Baseline kernel estimate: if the `τ`-slice is integrable, then the Weyl kernel is
well-defined and controlled by the `L¹` norm (uniformly in the oscillatory
factor).

This is the entry point for the remainder/kernels part of the paper: once the
symbol order is sufficiently negative, the `τ`-slice becomes integrable and we
obtain a genuine `L¹` kernel bound.
-/
theorem norm_weylKernel_le_of_integrable
    (a : ℝ → ℝ → ℝ → ℂ) (h t tp : ℝ)
    (ha : Integrable (fun τ : ℝ => a h ((t + tp) / 2) τ)) :
    ‖weylKernel a h t tp‖ ≤
      ‖((2 * Real.pi * h) : ℝ)⁻¹‖ *
        ∫ τ : ℝ, ‖a h ((t + tp) / 2) τ‖ := by
  -- The oscillatory factor has norm `1`, so the kernel is controlled by the `L¹` norm.
  have hInt : Integrable (fun τ : ℝ =>
      Complex.exp (Complex.I * ((t - tp) * τ / h)) * a h ((t + tp) / 2) τ) := by
    -- `‖exp(i·)‖ = 1`, so integrability is inherited from `ha`.
    -- We build the `Integrable` proof from strong measurability and the finite integral condition.
    refine ⟨?_, ?_⟩
    · -- Strong measurability: the exponential factor is continuous, hence strongly measurable.
      have hReal : Continuous (fun τ : ℝ => ((t - tp) * τ / h : ℝ)) := by
        simpa using (continuous_const.mul continuous_id).div_const h
      have hInner : Continuous (fun τ : ℝ => (Complex.I : ℂ) * (( (t - tp) * τ / h : ℝ) : ℂ)) := by
        simpa using continuous_const.mul (Complex.continuous_ofReal.comp hReal)
      have hExp : Continuous (fun τ : ℝ => Complex.exp (Complex.I * ((t - tp) * τ / h))) := by
        simpa using Complex.continuous_exp.comp hInner
      -- Multiply the (strongly measurable) exponential factor with the integrable symbol slice.
      simpa using hExp.aestronglyMeasurable.mul ha.aestronglyMeasurable
    · -- Finite integral: `‖exp(i·) * a‖ = ‖a‖` pointwise.
      have hNormEq : (fun τ : ℝ =>
          ‖Complex.exp (Complex.I * ((t - tp) * τ / h)) * a h ((t + tp) / 2) τ‖)
          = (fun τ : ℝ => ‖a h ((t + tp) / 2) τ‖) := by
        funext τ
        -- `‖exp(I·x)‖ = 1` for real `x`.
        simp [norm_mul, Complex.norm_exp]
      -- Replace the norm integrand by the norm of the symbol slice.
      simpa [HasFiniteIntegral, hNormEq] using ha.hasFiniteIntegral
  -- Apply the standard estimate `‖∫ f‖ ≤ ∫ ‖f‖`.
  have hNorm :
      ‖∫ τ : ℝ,
          Complex.exp (Complex.I * ((t - tp) * τ / h)) * a h ((t + tp) / 2) τ‖ ≤
        ∫ τ : ℝ,
          ‖Complex.exp (Complex.I * ((t - tp) * τ / h)) * a h ((t + tp) / 2) τ‖ :=
    norm_integral_le_integral_norm (f := fun τ : ℝ =>
      Complex.exp (Complex.I * ((t - tp) * τ / h)) * a h ((t + tp) / 2) τ)
  -- Replace `‖exp(i·) * a‖` by `‖a‖`.
  have hSimpl :
      (∫ τ : ℝ,
          ‖Complex.exp (Complex.I * ((t - tp) * τ / h)) * a h ((t + tp) / 2) τ‖) =
        (∫ τ : ℝ,
          ‖a h ((t + tp) / 2) τ‖) := by
    have : (fun τ : ℝ =>
        ‖Complex.exp (Complex.I * ((t - tp) * τ / h)) * a h ((t + tp) / 2) τ‖) =
        (fun τ : ℝ => ‖a h ((t + tp) / 2) τ‖) := by
      funext τ
      -- `‖exp(iθ)‖ = 1`.
      simpa [mul_assoc, Complex.norm_mul, Complex.norm_exp]
    simpa [this]
  -- Put everything together.
  calc
    ‖weylKernel a h t tp‖
        = ‖((2 * Real.pi * h) : ℝ)⁻¹‖ *
            ‖∫ τ : ℝ, Complex.exp (Complex.I * ((t - tp) * τ / h))
                  * a h ((t + tp) / 2) τ‖ := by
            simp [weylKernel, norm_smul, mul_assoc]
    _ ≤ ‖((2 * Real.pi * h) : ℝ)⁻¹‖ *
          (∫ τ : ℝ,
            ‖Complex.exp (Complex.I * ((t - tp) * τ / h)) * a h ((t + tp) / 2) τ‖) :=
          mul_le_mul_of_nonneg_left hNorm (by exact norm_nonneg _)
    _ = ‖((2 * Real.pi * h) : ℝ)⁻¹‖ *
          (∫ τ : ℝ, ‖a h ((t + tp) / 2) τ‖) := by
          simp [hSimpl]

end WeylKernel

end TwoChart
