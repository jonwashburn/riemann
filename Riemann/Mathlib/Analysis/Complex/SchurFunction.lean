/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Project Contributors
-/
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Basic

/-!
# Schur Functions and the Cayley Transform

This file develops the basic theory of Schur functions (functions bounded by 1 in modulus)
and their relationship to the Cayley transform.

## Main definitions

* `IsSchurOn`: A function `Θ` satisfies the Schur condition on a set `S` if `‖Θ z‖ ≤ 1`
  for all `z ∈ S`.

* `cayley`: The Cayley transform sending a function `F` to `(F - 1) / (F + 1)`.

## Main results

* `schur_of_cayley_re_nonneg_on`: If `Re(F z) ≥ 0` on a set `S` and `F z + 1 ≠ 0` on `S`,
  then the Cayley transform `(F - 1) / (F + 1)` is Schur on `S`.

* `SchurOnRectangles`: If `Re(F z) ≥ 0` on `S`, then the Cayley transform is Schur on `S`
  (the denominator condition is automatic since `Re(F) ≥ 0` implies `F ≠ -1`).

* `schur_pinches_to_one`: If `g` is analytic on an open connected set `U`, satisfies
  `‖g z‖ ≤ 1` on `U \ {ρ}`, and `g ρ = 1`, then `g ≡ 1` on `U` (maximum modulus principle).

## Implementation notes

The Cayley transform classically maps the right half-plane `{Re z > 0}` biholomorphically
onto the open unit disc. The key observation is that `|w - 1| ≤ |w + 1|` when `Re w ≥ 0`,
which is the geometric statement that `w` is closer to `-1` than to `1`.

These results are extracted from the Riemann Project's RS layer for potential Mathlib inclusion.
The proofs use elementary complex analysis (the maximum modulus principle).
-/

noncomputable section

open Set Complex Filter

namespace Complex

/-- Schur predicate on a set: `Θ` is Schur on `S` if `‖Θ z‖ ≤ 1` for all `z ∈ S`. -/
def IsSchurOn (Θ : ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, norm (Θ z) ≤ 1

/-- Monotonicity of the Schur predicate under set inclusion. -/
lemma IsSchurOn.mono {Θ : ℂ → ℂ} {S T : Set ℂ}
    (h : IsSchurOn Θ S) (hTS : T ⊆ S) : IsSchurOn Θ T := by
  intro z hz; exact h z (hTS hz)

/-- The constant function 1 is Schur on any set. -/
lemma isSchurOn_one (S : Set ℂ) : IsSchurOn (fun _ => (1 : ℂ)) S := by
  intro z _; simp

/-- The constant function 0 is Schur on any set. -/
lemma isSchurOn_zero (S : Set ℂ) : IsSchurOn (fun _ => (0 : ℂ)) S := by
  intro z _; simp

/-- Cayley transform sending a function `F` to `(F - 1) / (F + 1)`. -/
def cayley (F : ℂ → ℂ) : ℂ → ℂ := fun z => (F z - 1) / (F z + 1)

/-- The Cayley transform produces a Schur function when the input has nonnegative real part
and the denominator is nonvanishing.

The key geometric observation: if `Re w ≥ 0`, then `|w - 1| ≤ |w + 1|` because
`w` is at least as close to `1` as to `-1`. -/
lemma schur_of_cayley_re_nonneg_on
    (F : ℂ → ℂ) (S : Set ℂ)
    (hRe : ∀ z ∈ S, 0 ≤ (F z).re)
    (hDen : ∀ z ∈ S, F z + 1 ≠ 0) :
    IsSchurOn (fun z => (F z - 1) / (F z + 1)) S := by
  intro z hz
  have hden : F z + 1 ≠ 0 := hDen z hz
  have hRez : 0 ≤ (F z).re := hRe z hz
  -- Goal: |(w-1)/(w+1)| ≤ 1 when Re w ≥ 0 and w ≠ -1
  -- Reduce to |w-1| ≤ |w+1|
  -- Work with real coordinates x = Re(F z), y = Im(F z)
  set x : ℝ := (F z).re with hx
  set y : ℝ := (F z).im with hy
  have hxplus : (F z + 1).re = x + 1 := by simp [hx]
  have hyplus : (F z + 1).im = y := by simp [hy]
  have hxminus : (F z - 1).re = x - 1 := by simp [hx]
  have hyminus : (F z - 1).im = y := by simp [hy]
  have hdiff : (norm (F z + 1)) ^ 2 - (norm (F z - 1)) ^ 2 = 4 * x := by
    have h1s : (norm (F z + 1)) ^ 2 = (x + 1) * (x + 1) + y * y := by
      simpa [Complex.normSq_apply, hxplus, hyplus, pow_two] using (Complex.sq_norm (F z + 1))
    have h2s : (norm (F z - 1)) ^ 2 = (x - 1) * (x - 1) + y * y := by
      simpa [Complex.normSq_apply, hxminus, hyminus, pow_two] using (Complex.sq_norm (F z - 1))
    have : ((x + 1) * (x + 1) + y * y) - ((x - 1) * (x - 1) + y * y) = 4 * x := by ring
    simpa [h1s, h2s]
  have hnonneg : 0 ≤ (norm (F z + 1)) ^ 2 - (norm (F z - 1)) ^ 2 := by
    have hxnonneg : 0 ≤ x := by simpa [hx] using hRez
    have : 0 ≤ 4 * x := mul_nonneg (by norm_num) hxnonneg
    simpa [hdiff] using this
  have hle_sq : (norm (F z - 1)) ^ 2 ≤ (norm (F z + 1)) ^ 2 := sub_nonneg.mp hnonneg
  -- Monotonicity of sqrt gives |w-1| ≤ |w+1|
  have hle : norm (F z - 1) ≤ norm (F z + 1) := by
    have : Real.sqrt ((norm (F z - 1)) ^ 2) ≤ Real.sqrt ((norm (F z + 1)) ^ 2) :=
      Real.sqrt_le_sqrt hle_sq
    simpa [Real.sqrt_sq_eq_abs] using this
  -- Conclude |(w-1)/(w+1)| ≤ 1
  have hden_pos : 0 < norm (F z + 1) := by simpa using hDen z hz
  -- Divide the inequality by the positive denominator
  have hmul : norm (F z - 1) / norm (F z + 1) ≤ norm (F z + 1) / norm (F z + 1) := by
    exact div_le_div_of_nonneg_right hle (norm_nonneg (F z + 1))
  have hdiv_le_one : norm (F z - 1) / norm (F z + 1) ≤ 1 := by
    simpa [div_self (ne_of_gt hden_pos)] using hmul
  -- Conclude using `abs_div`
  simpa [abs_div, div_eq_mul_inv] using hdiv_le_one

/-- Under `0 ≤ Re F`, the denominator `F + 1` never vanishes (since `F = -1` would give
negative real part), so the Cayley transform is Schur on the same set. -/
lemma SchurOnRectangles
    (F : ℂ → ℂ) (R : Set ℂ)
    (hRe : ∀ z ∈ R, 0 ≤ (F z).re) :
    IsSchurOn (fun z => (F z - 1) / (F z + 1)) R := by
  -- If `F z + 1 = 0`, then `F z = -1`, contradicting `0 ≤ Re (F z)`.
  have hDen : ∀ z ∈ R, F z + 1 ≠ 0 := by
    intro z hz hzden
    have hFneg1 : F z = (-1 : ℂ) := by
      have : F z = -(1 : ℂ) := eq_neg_of_add_eq_zero_left hzden
      simpa using this
    have h0le : 0 ≤ (F z).re := hRe z hz
    have hle : (0 : ℝ) ≤ -1 := by simpa [hFneg1] using h0le
    have hlt : (-1 : ℝ) < 0 := by norm_num
    have : (0 : ℝ) < 0 := lt_of_le_of_lt hle hlt
    exact False.elim ((lt_irrefl _) this)
  exact schur_of_cayley_re_nonneg_on F R hRe hDen

/-- Maximum modulus principle for Schur maps: if `Θ` is analytic on a preconnected open set `S`,
satisfies `‖Θ z‖ ≤ 1` on `S`, and attains the value `1` at some `z₀ ∈ S`, then `Θ ≡ 1` on `S`. -/
lemma schur_constant_of_one
    (S : Set ℂ) (hSopen : IsOpen S) (hSconn : IsPreconnected S)
    (Θ : ℂ → ℂ) (hΘ : AnalyticOn ℂ Θ S) (hSchur : IsSchurOn Θ S)
    (z0 : ℂ) (hz0 : z0 ∈ S) (hval : Θ z0 = 1) :
    ∀ z ∈ S, Θ z = 1 := by
  classical
  have hdiff : DifferentiableOn ℂ Θ S := (analyticOn_iff_differentiableOn hSopen).1 hΘ
  have hmax : IsMaxOn (fun x => norm (Θ x)) S z0 := by
    intro z hz
    have : norm (Θ z) ≤ 1 := hSchur z hz
    simpa [hval, Complex.one_re] using this
  have hconst :=
    Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (E := ℂ) (F := ℂ)
      hSconn hSopen hdiff hz0 hmax
  intro z hz
  have : Θ z = Θ z0 := hconst hz
  simpa [hval] using this

/-- Removable-singularity pinch: if `g` is analytic on open connected `U`, satisfies
`‖g z‖ ≤ 1` on `U \ {ρ}`, and `g ρ = 1`, then `g ≡ 1` on `U`.

This is the key lemma for extending Schur bounds across removable singularities. -/
lemma schur_pinches_to_one
    {U : Set ℂ} (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    {ρ : ℂ} {g : ℂ → ℂ}
    (hg : AnalyticOn ℂ g U)
    (hle : ∀ z ∈ (U \ {ρ}), norm (g z) ≤ 1)
    (hρU : ρ ∈ U) (hval : g ρ = 1) : ∀ z ∈ U, g z = 1 := by
  -- Build a Schur bound for g on U from the off-point bound and the pinned value.
  have hSchurU : IsSchurOn g U := by
    intro z hz
    by_cases hzρ : z = ρ
    · simp [hzρ, hval]
    · have hz' : z ∈ (U \ {ρ}) := ⟨hz, by simp [hzρ]⟩
      exact hle z hz'
  exact schur_constant_of_one U hUopen hUconn g hg hSchurU ρ hρU hval

/-- Extension from removable singularity: if `Θ` is Schur on `U \ {ρ}`, and `g` is an analytic
extension of `Θ` across `ρ` with `g ρ = 1`, then both `g` and `Θ` are identically `1` on their
respective domains. -/
lemma schur_from_extension
    (S : Set ℂ) (hSopen : IsOpen S) (hSconn : IsPreconnected S) (ρ : ℂ) (hρ : ρ ∈ S)
    (Θ : ℂ → ℂ) (_ : AnalyticOn ℂ Θ (S \ {ρ}))
    (hSchur : IsSchurOn Θ (S \ {ρ}))
    (g : ℂ → ℂ) (hg : AnalyticOn ℂ g S)
    (heq : EqOn Θ g (S \ {ρ}))
    (hval : g ρ = 1) :
    (∀ z ∈ S, g z = 1) ∧ (∀ z ∈ (S \ {ρ}), Θ z = 1) := by
  have hSchur_g : IsSchurOn g S := by
    intro z hz
    by_cases hzρ : z = ρ
    · simp [hzρ, hval]
    · have hz_in : z ∈ (S \ {ρ}) := ⟨hz, by simp [hzρ]⟩
      have hzg : Θ z = g z := by simpa [hzρ] using heq hz_in
      have : norm (Θ z) ≤ 1 := hSchur z hz_in
      simpa [hzg] using this
  have hconst := schur_constant_of_one S hSopen hSconn g hg hSchur_g ρ hρ hval
  have hg1 : ∀ z ∈ S, g z = 1 := hconst
  have hθ1 : ∀ z ∈ (S \ {ρ}), Θ z = 1 := by
    intro z hz
    have hzg : Θ z = g z := by simpa using heq hz
    have hz1 : g z = 1 := hg1 z hz.1
    simpa [hzg.symm] using hz1
  exact ⟨hg1, hθ1⟩

end Complex
