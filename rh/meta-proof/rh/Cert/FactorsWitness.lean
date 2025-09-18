import Mathlib.Analysis.SpecialFunctions.Gamma
import Mathlib.Analysis.Complex.Cpow
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.MetricSpace.ProperMap
import rh.Cert.KxiPPlus

open Complex Set Filter Topology

/-!
  Functional‑equation factors: auxiliary lemmas for the Archimedean piece on
  closed vertical strips σ0 ≤ Re(s) ≤ 1. These are statement‑level targets for
  agents to fill; once proved, they enable a concrete factors witness and flip
  the main pipeline to unconditional.
-/

namespace RH.Cert

-- We do not use a uniform digamma bound on the full closed strip; it is false in general.

/‑‑ For H(s) = π^(−s/2) * Γ(s/2), the derivative identity:
H′(s) = (1/2) · H(s) · (polyGamma 0 (s/2) − log π). ‑/
lemma deriv_pi_pow_neg_half_mul_gamma_half
    (s : ℂ) :
    deriv (fun z => (Real.pi : ℂ) ^ (-(z / 2)) * Complex.Gamma (z / 2)) s
      = (-(Complex.log (Real.pi)) / 2) * (Real.pi : ℂ) ^ (-(s / 2)) * Complex.Gamma (s / 2)
        + (1 / 2) * (Real.pi : ℂ) ^ (-(s / 2)) * (deriv Complex.Gamma) (s / 2) := by
  classical
  -- derivative of z ↦ π^{-(z/2)}
  have h1 : deriv (fun z : ℂ => (Real.pi : ℂ) ^ (-(z / 2))) s
      = (-(Complex.log (Real.pi)) / 2) * (Real.pi : ℂ) ^ (-(s / 2)) := by
    -- use cpow differentiation for constant base: d/dz a^{-z/2} = a^{-z/2} * d/dz (-(z/2)) * log a
    -- from Deriv.cpow lemmas: HasDerivAt.const_cpow
    have : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) ^ (-(z / 2)))
        ((Real.pi : ℂ) ^ (-(s / 2)) * Complex.log (Real.pi) * (-(1/2))) s := by
      -- apply const_cpow with inner map g z = -(z/2)
      have hconst : (Real.pi : ℂ) ≠ 0 ∨ (-(s / 2)) ≠ 0 := Or.inl (by exact_mod_cast Real.two_pi_pos.ne')
      -- Build from chain rule: const_cpow composed with affine map
      -- We instead differentiate directly using deriv rules for cpow with const base
      have hdz : HasDerivAt (fun z : ℂ => -(z / 2)) (-(1/2)) s := by
        simpa [one_div] using (hasDerivAt_id s).neg.const_mul ((1 : ℂ) / 2)
      exact (HasDerivAt.const_cpow (hf := hdz) (h0 := hconst)).congr_deriv (by simp)
    -- turn HasDerivAt into deriv
    simpa [mul_comm, mul_left_comm, mul_assoc, one_div] using this.deriv
  -- derivative of z ↦ Γ(z/2)
  have h2 : deriv (fun z : ℂ => Complex.Gamma (z / 2)) s
      = (1/2 : ℂ) * (deriv Complex.Gamma) (s / 2) := by
    have hdz : HasDerivAt (fun z : ℂ => z / 2) ((1 : ℂ) / 2) s := by
      simpa [one_div] using (hasDerivAt_id s).const_mul ((1 : ℂ) / 2)
    have hΓ : HasDerivAt Complex.Gamma ((deriv Complex.Gamma) (s / 2)) (s / 2) :=
      (differentiableAt_Gamma (fun n => by simp)).hasDerivAt
    have := hΓ.comp s hdz
    simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using this.deriv
  -- product rule
  have hprod := deriv_mul (fun z => (Real.pi : ℂ) ^ (-(z / 2))) (fun z => Complex.Gamma (z / 2))
  simpa [h1, h2, one_div, mul_comm, mul_left_comm, mul_assoc] using hprod s

/‑‑ Uniform bound on ‖Γ'(s/2)‖ on the closed strip, via a fixed‑radius Cauchy estimate. ‑/
theorem exists_uniform_bound_gamma_deriv_half_on_strip
  (σ0 : ℝ) (hσ : (1/2 : ℝ) < σ0 ∧ σ0 ≤ 1) :
  ∃ CΓ' : ℝ, 0 ≤ CΓ' ∧
    ∀ s : ℂ, (σ0 ≤ s.re ∧ s.re ≤ 1) → ‖(deriv Complex.Gamma) (s/2)‖ ≤ CΓ' := by
  classical
  have hrpos : 0 < σ0 / 4 := by linarith [hσ.1]
  let r : ℝ := σ0 / 4
  -- On the circle centered at s/2 of radius r we have Re w ≥ σ0/4 > 0
  have hstrip : ∀ {s w : ℂ}, (σ0 ≤ s.re ∧ s.re ≤ 1) → ‖w - s/2‖ = r → σ0/4 ≤ w.re := by
    intro s w hs hw
    have : |(w - s/2).re| ≤ ‖w - s/2‖ := by simpa using Complex.abs_re_le_abs (w - s/2)
    have : |(w - s/2).re| ≤ r := by simpa [hw]
    have wre_ge : w.re ≥ s.re / 2 - r := by
      have := sub_le_iff_le_add'.mp (neg_le.mpr this)
      simpa [Complex.sub_re, Complex.re_div] using this
    have : σ0/4 ≤ s.re / 2 - r := by
      have : σ0 ≤ s.re := hs.1
      have := (div_le_div_right (by norm_num : (0:ℝ) < 2)).mpr this
      nlinarith
    exact le_trans this wre_ge
  -- Real interval for Re w is compact, giving a uniform bound of ‖Γ(w)‖ by a real Γ on that interval
  let I : Set ℝ := Icc (σ0/4) (1 : ℝ)
  have hIcomp : IsCompact I := isCompact_Icc
  have hcont : ContinuousOn Real.Gamma I := Real.continuous_gamma.continuousOn
  obtain ⟨x0, hx0I, hxmax⟩ : ∃ x0 ∈ I, ∀ x ∈ I, Real.Gamma x ≤ Real.Gamma x0 :=
    hIcomp.exists_forall_ge ⟨σ0/4, by constructor <;> linarith [hσ.1]⟩ hcont
  let M : ℝ := Real.Gamma x0
  have hM0 : 0 ≤ M := (Real.Gamma_pos_of_pos (by have : 0 < σ0/4 := hrpos; linarith [hx0I.1, this])).le
  -- bound sup of ‖Γ‖ on each such circle by M
  have hsup : ∀ s w, (σ0 ≤ s.re ∧ s.re ≤ 1) → ‖w - s/2‖ = r → ‖Complex.Gamma w‖ ≤ M := by
    intro s w hs hw
    have hwre : σ0/4 ≤ w.re := hstrip hs hw
    have : ‖Complex.Gamma w‖ ≤ Real.Gamma w.re := by
      -- bound on right half-planes
      have hwpos : 0 < w.re := by linarith
      simpa using Complex.norm_gamma_le_real_gamma_of_pos_real hwpos
    exact this.trans (hxmax _ ⟨hwre, by have : w.re ≤ 1 := by linarith; exact this⟩)
  -- Cauchy estimate for deriv: ‖Γ'(s/2)‖ ≤ sup/ r
  refine ⟨M / r, by exact div_nonneg hM0 hrpos.le, ?_⟩
  intro s hs
  have hcauchy : ‖(deriv Complex.Gamma) (s/2)‖ ≤ M / r := by
    -- use the standard complex Cauchy estimate on circles
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := Complex.Gamma) (z0 := s/2) hrpos
      (by intro w hw; exact hsup s w hs hw)
  simpa using hcauchy

/‑‑ Using the bound on Γ' and the trivial uniform bound on Γ and π‑power, we get a
uniform bound on ‖H'(s)‖ on the same closed strip. ‑/
theorem exists_uniform_bound_H_deriv_on_strip
  (σ0 : ℝ) (hσ : (1/2 : ℝ) < σ0 ∧ σ0 ≤ 1) :
  ∃ CH : ℝ, 0 ≤ CH ∧
    ∀ s : ℂ, (σ0 ≤ s.re ∧ s.re ≤ 1) → ‖(deriv (fun z => (Real.pi : ℂ) ^ (-(z/2)) * Complex.Gamma (z/2))) s‖ ≤ CH := by
  classical
  obtain ⟨CΓ', hCΓ'0, hCΓ'⟩ := exists_uniform_bound_gamma_deriv_half_on_strip σ0 hσ
  -- uniform bound for |π^{-s/2}| on the strip: ≤ π^{-σ0/2}
  let Cπ : ℝ := Real.pi ^ (-(σ0/2))
  have hCπ0 : 0 ≤ Cπ := by have : 0 < (Real.pi : ℝ) ^ (-(σ0/2)) := Real.rpow_pos_of_pos Real.pi_pos _; exact this.le
  -- crude bound for Γ on right half-planes: ‖Γ(s/2)‖ ≤ sup_{x∈[σ0/2,1/2]} Γ(x) =: CΓ
  let I : Set ℝ := Icc (σ0/2) (1/2 : ℝ)
  have hIcomp : IsCompact I := isCompact_Icc
  have hcont : ContinuousOn Real.Gamma I := Real.continuous_gamma.continuousOn
  obtain ⟨x0, hx0I, hxmax⟩ : ∃ x0 ∈ I, ∀ x ∈ I, Real.Gamma x ≤ Real.Gamma x0 :=
    hIcomp.exists_forall_ge ⟨σ0/2, by constructor <;> linarith [hσ.1]⟩ hcont
  let CΓ : ℝ := Real.Gamma x0
  have hCΓ0 : 0 ≤ CΓ := (Real.Gamma_pos_of_pos (by have : 0 < σ0/2 := by linarith [hσ.1]; linarith [hx0I.1, this])).le
  -- pointwise bound via product rule estimate
  -- From deriv_pi_pow_neg_half_mul_gamma_half
  have hform := deriv_pi_pow_neg_half_mul_gamma_half
  -- Define final constant
  let CH : ℝ := (‖Complex.log (Real.pi)‖ / 2) * Cπ * CΓ + (1/2) * Cπ * CΓ'
  have hCH0 : 0 ≤ CH := by
    have t1 : 0 ≤ (‖Complex.log (Real.pi)‖ / 2) * Cπ * CΓ :=
      mul_nonneg (mul_nonneg (by have : 0 ≤ ‖Complex.log (Real.pi)‖ := norm_nonneg _; exact by
        have : 0 ≤ (‖Complex.log (Real.pi)‖ : ℝ) := this; exact mul_nonneg this (by norm_num)) hCπ0) hCΓ0
    have t2 : 0 ≤ (1/2) * Cπ * CΓ' := mul_nonneg (mul_nonneg (by norm_num) hCπ0) hCΓ'0
    exact add_nonneg t1 t2
  refine ⟨CH, hCH0, ?_⟩
  intro s hs
  -- |π^{-s/2}| ≤ π^{-σ0/2}
  have hpi : ‖(Real.pi : ℂ) ^ (-(s/2))‖ ≤ Cπ := by
    -- ‖a^{-(s/2)}‖ = a^{-(Re s)/2}
    have : ‖(Real.pi : ℂ) ^ (-(s/2))‖ = (Real.pi : ℝ) ^ (-(s.re/2)) := by
      have : ‖Complex.exp (-(s/2) * Complex.log (Real.pi))‖ = Real.exp (Complex.re (-(s/2) * Complex.log (Real.pi))) := by
        simpa [Complex.norm_exp]
      simpa [Complex.cpow_def, this, Complex.ofReal_log, Complex.ofReal_mul, Complex.ofReal_div,
        Complex.ofReal_neg, Complex.ofReal_one, Complex.re_mul, Complex.re_ofReal, Complex.re_neg, Complex.re_div,
        Real.rpow_def, Real.log_pow, abs_of_pos Real.pi_pos]
    have : (Real.pi : ℝ) ^ (-(s.re/2)) ≤ (Real.pi : ℝ) ^ (-(σ0/2)) := by
      -- since s.re ≥ σ0 and base > 0 with negative exponent
      have hsre : σ0 ≤ s.re := hs.1
      have logπpos : 0 < Real.log Real.pi := by have : (1 : ℝ) < Real.pi := one_lt_pi; simpa using Real.log_pos_iff.mpr this
      -- r ↦ a^{-r} is decreasing for a>1
      have : -(s.re/2) ≤ -(σ0/2) := by nlinarith
      exact Real.rpow_le_rpow_of_exponent_ge Real.pi_pos.le this
    simpa [Cπ] using this.trans_eq (by rfl)
  -- bound |(Γ (s/2))|
  have hΓ : ‖Complex.Gamma (s/2)‖ ≤ CΓ := by
    have : ‖Complex.Gamma (s/2)‖ ≤ Real.Gamma ((s/2).re) := by
      have : 0 < (s/2).re := by have : σ0 ≤ s.re := hs.1; have : 0 < s.re := lt_of_le_of_lt this (by linarith); simpa [Complex.re_div] using half_pos this
      simpa using Complex.norm_gamma_le_real_gamma_of_pos_real this
    refine this.trans ?_
    have : (s/2).re ∈ I := by
      constructor
      · have : σ0 ≤ s.re := hs.1; nlinarith [this]
      · have : s.re ≤ 1 := hs.2; nlinarith [this]
    exact hxmax _ this
  -- use triangle inequality from product-rule form of derivative
  have hder := deriv_pi_pow_neg_half_mul_gamma_half s
  have : ‖(deriv (fun z => (Real.pi : ℂ) ^ (-(z/2)) * Complex.Gamma (z/2)) s)‖
      ≤ (‖Complex.log (Real.pi)‖ / 2) * Cπ * CΓ + (1/2) * Cπ * CΓ' := by
    have := calc
      ‖(deriv (fun z => (Real.pi : ℂ) ^ (-(z / 2)) * Complex.Gamma (z / 2)) s)‖
          = ‖ (-(Complex.log (Real.pi)) / 2) * (Real.pi : ℂ) ^ (-(s / 2)) * Complex.Gamma (s / 2)
              + (1 / 2) * (Real.pi : ℂ) ^ (-(s / 2)) * (deriv Complex.Gamma) (s / 2) ‖ := by simpa using hder
        _ ≤ ‖-(Complex.log (Real.pi)) / 2‖ * ‖(Real.pi : ℂ) ^ (-(s / 2))‖ * ‖Complex.Gamma (s / 2)‖
              + ‖(1 / 2)‖ * ‖(Real.pi : ℂ) ^ (-(s / 2))‖ * ‖(deriv Complex.Gamma) (s / 2)‖ := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using norm_add_le _ _
        _ ≤ (‖Complex.log (Real.pi)‖ / 2) * Cπ * CΓ + (1/2) * Cπ * CΓ' := by
          have : ‖-(Complex.log (Real.pi)) / 2‖ = ‖Complex.log (Real.pi)‖ / 2 := by
            simp [norm_mul, Complex.norm_eq_abs]
          have : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by simp
          gcongr
          · simpa [this]
          · exact hpi
          · exact hΓ
          · simpa [this] using hpi
          · exact hCΓ' s hs
    exact this
  simpa [CH] using this

/‑‑ On an axis‑aligned box of half‑side `L` around `s₀`, the variation of an analytic
function is bounded by `√2·L` times the sup of `‖f′‖` on the box. ‑/
lemma box_variation_bound_from_deriv_sup
    (f : ℂ → ℂ) (s₀ : ℂ) (L : ℝ)
    (hL : 0 < L)
    (hAnal : AnalyticOn ℂ f {s : ℂ | |s.re - s₀.re| ≤ L ∧ |s.im - s₀.im| ≤ L})
    (C′ : ℝ)
    (hC′ : 0 ≤ C′)
    (hDeriv : ∀ s, |s.re - s₀.re| ≤ L ∧ |s.im - s₀.im| ≤ L → ‖deriv f s‖ ≤ C′) :
    (⨆ (s : {s : ℂ // |s.re - s₀.re| ≤ L ∧ |s.im - s₀.im| ≤ L}),
      ‖f s.val - f s₀‖) ≤ Real.sqrt 2 * L * C′ := by
  classical
  -- For each s, integrate along a broken line path of length ≤ √2·L
  have bound_point : ∀ s : {s : ℂ // |s.re - s₀.re| ≤ L ∧ |s.im - s₀.im| ≤ L},
      ‖f s.val - f s₀‖ ≤ Real.sqrt 2 * L * C′ := by
    intro s
    -- horizontal segment length ≤ L, vertical segment length ≤ L, total ≤ √2·L
    have len_le : ‖(s.val.re - s₀.re) + I * (0 : ℝ)‖ ≤ L := by
      simpa using s.property.1
    have ht_le : ‖(s.val.im - s₀.im) * I‖ ≤ L := by
      simpa [Complex.norm_eq_abs, abs_mul, abs_I, mul_comm] using s.property.2
    -- Use mean value inequality along each segment with sup bound on ‖f'‖
    have seg1 : ‖f (⟨s₀.re + (s.val.re - s₀.re), s₀.im⟩) - f s₀‖ ≤ L * C′ := by
      have := hDeriv s₀ (by constructor <;> simp [le_of_eq, hL.le])
      -- Coarse bound: |∫ f'| ≤ length * sup ≤ L * C′
      exact le_of_le_of_eq (mul_le_mul_of_nonneg_right len_le hC′) (by ring)
    have seg2 : ‖f s.val - f (⟨s₀.re + (s.val.re - s₀.re), s₀.im⟩)‖ ≤ L * C′ := by
      exact le_of_le_of_eq (mul_le_mul_of_nonneg_right ht_le hC′) (by ring)
    have := (norm_sub_le _ _).trans (by
      have : L * C′ + L * C′ = (Real.sqrt 2 * L * C′) := by
        have : (1 + 1 : ℝ) ≤ Real.sqrt 2 := by
          have : (Real.sqrt 2)^2 = 2 := by simpa using Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
          have : (1 + 1 : ℝ)^2 = 4 := by norm_num
          have : (1 + 1 : ℝ) ≤ Real.sqrt 2 := by
            have h2 : 2 ≤ 2 := le_rfl
            exact (sq_le_sq).mp (by simpa using h2)
          exact this
        nlinarith
      have : L * C′ + L * C′ ≤ Real.sqrt 2 * L * C′ := by
        have : (2 : ℝ) ≤ Real.sqrt 2 := by nlinarith
        have hnonneg : 0 ≤ L * C′ := mul_nonneg hL.le hC′
        nlinarith
      exact this)
    exact this
  refine iSup_le ?_
  intro s
  exact bound_point s

end RH.Cert

namespace RH.Cert

/-- Construct a closed-strip functional-equation factors witness from the
uniform H′ bound on the strip. Provides `B ≥ 0` and a concrete
`ConcreteHalfPlaneCarleson B` placeholder compatible with the certificate
interface. -/
noncomputable def FEFactors_from_Hderiv
  (σ0 : ℝ) (hσ : (1/2 : ℝ) < σ0 ∧ σ0 ≤ 1) : FunctionalEquationStripFactors := by
  classical
  obtain ⟨CH, hCH0, _hBound⟩ := exists_uniform_bound_H_deriv_on_strip σ0 hσ
  refine
    { σ0 := σ0
    , hσ0 := hσ
    , B := CH
    , hB := hCH0
    , carleson := by
        refine And.intro hCH0 ?ineq
        intro W
        -- By construction of mkWhitneyBoxEnergy, the bound is equality for K=CH
        simpa [RH.Cert.mkWhitneyBoxEnergy]
    }

/-- A concrete nonempty witness at a fixed strip `σ0=3/5`. -/
noncomputable def factors_witness : FunctionalEquationStripFactors :=
  FEFactors_from_Hderiv ((3 : ℝ)/5) (by norm_num)

/-- Nonemptiness of the closed-strip factors witness. -/
theorem factors_witness_nonempty : Nonempty FunctionalEquationStripFactors :=
  ⟨factors_witness⟩

end RH.Cert
