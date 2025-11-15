import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import rh.academic_framework.ZetaFunctionalEquation
import rh.RS.Domain
import Mathlib.Topology.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
Completed Riemann ξ function (ext): we use mathlib's `completedRiemannZeta` and
expose minimal interface pieces needed by RS.
-/

noncomputable section

open Complex

namespace RH.AcademicFramework.CompletedXi

/-- Completed Riemann ξ (ext), defined as mathlib's completed zeta `Λ(s)`. -/
def riemannXi_ext (s : ℂ) : ℂ := completedRiemannZeta s

/-- Open right half-plane Ω = { s | Re s > 1/2 }. -/
private lemma isOpen_Ω : IsOpen RH.RS.Ω := by
  change IsOpen { s : ℂ | (1 / 2 : ℝ) < s.re }
  exact isOpen_lt continuous_const Complex.continuous_re

/-- Differentiability of `riemannXi_ext` away from `0` and `1`. -/
lemma differentiableAt_riemannXi_ext {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
  DifferentiableAt ℂ riemannXi_ext s := by
  change DifferentiableAt ℂ completedRiemannZeta s
  exact differentiableAt_completedZeta (s := s) hs0 hs1

/-- Differentiability of `riemannXi_ext` on Ω \ {1}. -/
theorem riemannXi_ext_differentiable_on_RSΩ_minus_one :
  DifferentiableOn ℂ riemannXi_ext (RH.RS.Ω \ ({1} : Set ℂ)) := by
  intro z hz
  -- z ∈ Ω and z ≠ 1
  have hzΩ : (1 / 2 : ℝ) < z.re := by
    simpa [RH.RS.Ω, Set.mem_setOf_eq] using hz.1
  have hz0 : z ≠ 0 := by
    intro h0
    have hzRe : (0 : ℝ) < z.re := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hzΩ
    have hzre0 := congrArg Complex.re h0
    simp [Complex.zero_re] at hzre0
    have hzRe' := hzRe
    rw [hzre0] at hzRe'
    exact (lt_irrefl (0 : ℝ)) hzRe'
  have hz1 : z ≠ 1 := by
    have h := hz.2
    simp [Set.mem_singleton_iff] at h
    exact h
  exact (differentiableAt_riemannXi_ext (s := z) hz0 hz1).differentiableWithinAt

/-- Analyticity of `riemannXi_ext` on Ω \ {1}``, via open-set equivalence. -/
lemma riemannXi_ext_analytic_on_RSΩ_minus_one :
  AnalyticOn ℂ riemannXi_ext (RH.RS.Ω \ ({1} : Set ℂ)) := by
  have hOpen : IsOpen (RH.RS.Ω \ ({1} : Set ℂ)) :=
    (isOpen_Ω).sdiff isClosed_singleton
  -- use the equivalence on open sets
  have h :=
    (analyticOn_iff_differentiableOn (f := riemannXi_ext)
      (s := RH.RS.Ω \ ({1} : Set ℂ)) hOpen)
  exact h.mpr riemannXi_ext_differentiable_on_RSΩ_minus_one

/-- Measurability of the completed ξ extension on all of `ℂ`. -/
lemma measurable_riemannXi_ext : Measurable riemannXi_ext := by
  classical
  let S : Set ℂ := ({0, 1} : Set ℂ)
  let Scompl : Set ℂ := {z : ℂ | z ∉ S}
  have hFinite : S.Finite := by
    simpa [S] using (finite_singleton (1 : ℂ)).insert 0
  have hRestr : Measurable (Scompl.restrict riemannXi_ext) := by
    have hCont : Continuous fun z : Scompl => riemannXi_ext z := by
      refine continuous_iff_continuousAt.mpr ?_
      intro z
      have hzNot : (z : ℂ) ∉ S := by
        have := z.property
        dsimp [Scompl] at this
        exact this
      have hzMem :
          (z : ℂ) ≠ 0 ∧ (z : ℂ) ≠ 1 := by
        simpa [S, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hzNot
      have hz0 : (z : ℂ) ≠ 0 := hzMem.1
      have hz1 : (z : ℂ) ≠ 1 := hzMem.2
      have hDiff : DifferentiableAt ℂ riemannXi_ext (z : ℂ) :=
        differentiableAt_riemannXi_ext (s := (z : ℂ)) hz0 hz1
      have hContAt : ContinuousAt riemannXi_ext (z : ℂ) := hDiff.continuousAt
      have hIncl :
          ContinuousAt (Subtype.val : Scompl → ℂ) z :=
        continuous_subtype_val.continuousAt
      exact hContAt.comp hIncl
    simpa using hCont.measurable
  have hCompl : Scompl = Sᶜ := by
    ext z; simp [Scompl, S]
  simpa [hCompl] using measurable_of_measurable_on_compl_finite S hFinite hRestr

-- symmetry lemmas are provided in CompletedXiSymmetry to avoid duplication

/-- On Ω, zeros of `riemannXi_ext` coincide with zeros of `riemannZeta`. -/
lemma xi_ext_zeros_eq_zeta_zeros_on_Ω :
  ∀ z ∈ RH.RS.Ω, riemannXi_ext z = 0 ↔ riemannZeta z = 0 := by
  intro z hzΩ
  -- From Ω: 1/2 < Re z
  have hhalf : (1 / 2 : ℝ) < z.re := by
    simpa [RH.RS.Ω, Set.mem_setOf_eq] using hzΩ
  -- Hence Re z > 0 and Γℝ z ≠ 0
  have hpos : (0 : ℝ) < z.re := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hhalf
  have hΓnz : Complex.Gammaℝ z ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hpos
  -- Also z ≠ 0, but only Γℝ z ≠ 0 is needed below
  have hζ : riemannZeta z = completedRiemannZeta z / Complex.Gammaℝ z :=
    riemannZeta_def_of_ne_zero (s := z) (by
      intro h0
      have hnot : ¬ ((1 / 2 : ℝ) < 0) := by norm_num
      have hzre := congrArg Complex.re h0
      simp [Complex.zero_re] at hzre
      have h := hhalf
      rw [hzre] at h
      exact hnot h)
  constructor
  · intro hXi
    -- Λ z = 0 ⇒ ζ z = 0
    have hΛ0 : completedRiemannZeta z = 0 := by
      dsimp [riemannXi_ext] at hXi
      exact hXi
    -- Rewrite ζ and conclude explicitly
    calc
      riemannZeta z = completedRiemannZeta z / Complex.Gammaℝ z := hζ
      _ = completedRiemannZeta z * (Complex.Gammaℝ z)⁻¹ := by rw [div_eq_mul_inv]
      _ = 0 * (Complex.Gammaℝ z)⁻¹ := by rw [hΛ0]
      _ = 0 := by simp
  · intro hζ0
    -- ζ z = 0, and Γℝ z ≠ 0 ⇒ Λ z = 0
    have hdiv0 : completedRiemannZeta z / Complex.Gammaℝ z = 0 := by
      -- rewrite the ζ-definition into the equality
      have htmp := hζ0
      rw [hζ] at htmp
      exact htmp
    have hΛ0 : completedRiemannZeta z = 0 := by
      -- If Λ z ≠ 0 then division by nonzero Γ gives a nonzero value, contradiction
      by_contra hΛ
      have : completedRiemannZeta z / Complex.Gammaℝ z ≠ 0 :=
        div_ne_zero hΛ hΓnz
      exact this hdiv0
    -- Conclude ξ_ext z = 0
    dsimp [riemannXi_ext]
    exact hΛ0

open scoped Real Topology

private def zeta_nat_sq (n : ℕ) : ℝ := (1 : ℝ) / (n : ℝ) ^ 2

lemma riemannZeta_two_ne_zero : riemannZeta (2 : ℂ) ≠ 0 := by
  classical
  have hz :
      riemannZeta (2 : ℂ) = ∑' n : ℕ, 1 / (n : ℂ) ^ 2 :=
    zeta_nat_eq_tsum_of_gt_one (k := 2) (by decide : 1 < (2 : ℕ))
  have hf : HasSum (fun n : ℕ => zeta_nat_sq n) (π ^ 2 / 6) := hasSum_zeta_two
  have hterm :
      (fun n : ℕ => Complex.ofReal (zeta_nat_sq n)) =
      fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ 2 := by
    funext n
    simp [zeta_nat_sq, Complex.ofReal_div, Complex.ofReal_pow]
  have hsum_complex :
      HasSum (fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ 2)
        (Complex.ofReal (π ^ 2 / 6)) := by
    simpa [hterm] using (Complex.hasSum_ofReal).2 hf
  have hfinal :
      riemannZeta (2 : ℂ) = Complex.ofReal (π ^ 2 / 6) := by
    simpa [hterm] using hz.trans hsum_complex.tsum_eq
  have hval : Complex.ofReal (π ^ 2 / 6) ≠ 0 := by
    have hpos : ((π : ℝ) ^ 2 / 6) ≠ 0 := by
      refine div_ne_zero (pow_ne_zero _ Real.pi_ne_zero) ?_
      norm_num
    simpa using Complex.ofReal_ne_zero.mpr hpos
  simpa [hfinal] using hval

lemma riemannXi_ext_two_ne_zero : riemannXi_ext (2 : ℂ) ≠ 0 := by
  classical
  have h :=
    completedZeta_eq_tsum_of_one_lt_re (s := (2 : ℂ))
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)
  have hz :
      riemannZeta (2 : ℂ) = ∑' n : ℕ, 1 / (n : ℂ) ^ 2 :=
    zeta_nat_eq_tsum_of_gt_one (k := 2) (by decide : 1 < (2 : ℕ))
  have hGamma : Gamma (1 : ℂ) = 1 := by simpa using Complex.Gamma_one
  have hπ : (π : ℂ) ≠ 0 := by
    simpa using (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hΓne : Gamma (1 : ℂ) ≠ 0 := by
    simpa [hGamma] using one_ne_zero
  have hpow : (π : ℂ) ^ (-(1 : ℂ)) ≠ 0 := by
    intro hzero
    have hbase : (π : ℂ) = 0 :=
      (cpow_eq_zero_iff _ _).1 hzero |>.1
    exact hπ hbase
  have hfactor :
      (π : ℂ) ^ (-(1 : ℂ)) * Gamma (1 : ℂ) ≠ 0 :=
    mul_ne_zero hpow hΓne
  have hprod :
      ( (π : ℂ) ^ (-(1 : ℂ)) * Gamma (1 : ℂ)) * riemannZeta (2 : ℂ) ≠ 0 :=
    mul_ne_zero hfactor riemannZeta_two_ne_zero
  simpa [riemannXi_ext, h, hz, hGamma, mul_comm, mul_left_comm, mul_assoc] using hprod

end RH.AcademicFramework.CompletedXi
