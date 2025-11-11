import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
Compat: Centralized imports and a place to add 4.6 ↔ 4.13 shims.

Usage: replace scattered Mathlib imports in files with `import rh.Compat`.
Add alias lemmas or small wrappers here as needed during the port.
-/

namespace RH

noncomputable section

open Classical Complex MeasureTheory
open scoped BigOperators Topology Interval

-- Add lightweight aliases or helper lemmas here if the port needs them.

-- Shims for v4.6 → v4.13 API changes:

-- inv_le_inv_of_le deprecated, use inv_anti₀
lemma inv_le_inv_of_le {α : Type*} [LinearOrderedField α] {a b : α} (ha : 0 < a) (h : a ≤ b) : b⁻¹ ≤ a⁻¹ :=
  inv_anti₀ ha h

-- sq_le_sq signature changed - now needs absolute values
namespace sq_le_sq
lemma mpr {α : Type*} [LinearOrderedRing α] {a b : α} (h : |a| ≤ |b|) : a ^ 2 ≤ b ^ 2 := by
  rw [← sq_abs a, ← sq_abs b]
  gcongr
end sq_le_sq

-- sq_pos_of_ne_zero signature changed - in v4.13 use sq_pos_iff
lemma sq_pos_of_ne_zero {α : Type*} [LinearOrderedRing α] [Nontrivial α] (a : α) (ha : a ≠ 0) : 0 < a ^ 2 :=
  sq_pos_iff.mpr ha

-- Real.rpow_eq_one_iff API changed or renamed
namespace Real

-- v4.6 compatibility: accept `1 < x` (old API) instead of `x ≠ 1`.
-- This returns `y = 0 ∨ x = 1`; with `1 < x`, only `y = 0` is possible.
lemma rpow_eq_one_iff_of_pos {x : ℝ} (hx_pos : 0 < x) (hx_gt_one : 1 < x) {y : ℝ} :
    x ^ y = 1 ↔ y = 0 ∨ x = 1 := by
  have hx_ne_one : x ≠ 1 := ne_of_gt hx_gt_one
  constructor
  · intro h
    by_cases hy : y = 0
    · left; exact hy
    · right
      -- If y ≠ 0 and x^y = 1, then log(x^y) = 0, so y*log(x) = 0, so log(x) = 0, so x = 1
      have : Real.log (x ^ y) = 0 := by rw [h]; exact Real.log_one
      rw [Real.log_rpow hx_pos] at this
      have : Real.log x = 0 := by
        by_contra h_log_ne
        have : y * Real.log x = 0 := this
        have : y = 0 := mul_eq_zero.mp this |>.resolve_right h_log_ne
        exact hy this
      have : x = 0 ∨ x = 1 ∨ x = -1 := Real.log_eq_zero.mp this
      have : x = 1 ∨ x = -1 := this.resolve_left (by linarith)
      exact this.resolve_right (by linarith)
  · intro h
    cases h with
    | inl hy => rw [hy]; exact Real.rpow_zero x
    | inr hx => exact absurd hx hx_ne_one

end Real

-- analyticAt API changed in v4.13 - exp and log are now just direct .comp calls
-- The old Complex.analyticAt_exp and Complex.analyticAt_log don't have .comp fields anymore

-- AnalyticAt.congr_of_eventuallyEq renamed to AnalyticAt.congr
lemma AnalyticAt.congr_of_eventuallyEq {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f g : E → F} {z : E}
    (hf : AnalyticAt 𝕜 f z) (hfg : f =ᶠ[𝓝 z] g) : AnalyticAt 𝕜 g z :=
  hf.congr hfg

-- Helper: if z ≠ 0 then z ∈ slitPlane (since slitPlane excludes only nonpositive reals)
lemma mem_slitPlane_of_ne_zero_of_re_pos {z : ℂ} (_hne : z ≠ 0) (h_re : 0 < z.re) : z ∈ Complex.slitPlane :=
  Or.inl h_re

lemma mem_slitPlane_of_ne_zero_of_im_ne {z : ℂ} (_hne : z ≠ 0) (h_im : z.im ≠ 0) : z ∈ Complex.slitPlane :=
  Or.inr h_im

-- arithmetic helper
lemma two_pow_two_mul_eq_four_pow (d : ℕ) : (2 : ℝ) ^ (2 * d) = (4 : ℝ) ^ d := by
  have h : (2 : ℝ) ^ (2 * d) = ((2 : ℝ) ^ 2) ^ d := pow_mul (2 : ℝ) 2 d
  have h2 : ((2 : ℝ) ^ 2) = (4 : ℝ) := by norm_num
  exact h.trans (congrArg (fun z : ℝ => z ^ d) h2)

end

end RH
