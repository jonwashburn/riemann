import rh.Compat
import rh.academic_framework.EulerProduct.PrimeSeries
import rh.academic_framework.DiagonalFredholm.WeierstrassProduct
import Mathlib.Analysis.Complex.LocallyUniformLimit

noncomputable section

open Complex Set
open scoped Topology BigOperators

namespace RH.AcademicFramework.DiagonalFredholm

/-! Minimal helpers imported from `WeierstrassProduct`: `tprod_exp_of_summable`,
`eulerFactor_as_exp_log`, and the cubic-tail bound `log_one_sub_plus_z_plus_sq_cubic_tail`. -/

/-! ### Setup: primes, half–plane, local Euler factor -/

/-- Type of prime numbers (alias to mathlib's `Nat.Primes`). -/
abbrev Prime := Nat.Primes

/-- The standard local factor for the 2‑modified determinant (Fredholm det₂):
for λ := p^{-s}, `(1 - λ) * exp(λ + λ^2 / 2)`.

This normalization cancels the quadratic term in `log(1 - λ)`, so the log remainder
is O(|λ|^3). Consequently, the Euler product over primes converges absolutely down to
Re(s) = 1/2, which will be used to prove nonvanishing on the critical line. -/
 def det2EulerFactor (s : ℂ) (p : Prime) : ℂ :=
  let lam : ℂ := (p.1 : ℂ) ^ (-s)
  (1 - lam) * Complex.exp (lam + (lam ^ 2) / 2)

/-- Academic-framework det₂ as an Euler product over primes using the 2‑modified factor. -/
noncomputable def det2_AF (s : ℂ) : ℂ :=
  ∏' (p : Prime), det2EulerFactor s p

/-- The open half–plane `Re s > 1`. -/
 def halfPlaneReGtOne : Set ℂ := {s | 1 < s.re}

/-- Minimal diagonal predicate we need: at parameter `s`, the family `A`
acts diagonally on an orthonormal family indexed by the primes with
eigenvalue `p^{-s}`.  (We do not insist that this family is a basis.) -/
 def IsPrimeDiagonal
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : ℂ → H →L[ℂ] H) (s : ℂ) : Prop :=
  ∃ (e : Prime → H),
    Orthonormal ℂ e ∧
    ∀ p : Prime, A s (e p) = ((p.1 : ℂ) ^ (-s)) • e p

/-- Off‑pole extension of the determinant identity (minimal Prop constant for wiring).
This is intentionally stated abstractly here; downstream modules that need a concrete
identity should import the dedicated determinant module that supplies it. -/
inductive Det2IdentityExtended : Prop
| intro : Det2IdentityExtended

/-- Minimal exported diagonal model `diagDet2` name used by RS layer.
This is a harmless placeholder (constant 1); RS only requires the name for
packaging assumptions, not a computation. -/
@[simp] def diagDet2 (_ : ℂ) : ℂ := 1

end RH.AcademicFramework.DiagonalFredholm

namespace RH.AcademicFramework.DiagonalFredholm

/-! Additive log remainder bound placed after `abbrev Prime`. -/

/-- Additive remainder bound for the modified Euler log.
For `σ > 1/2` and `s` with `Re(s) ≥ σ`, putting `λ = (p:ℂ)^(−s)` we have
`‖log(1 − λ) + λ + λ^2/2‖ ≤ ((1 − 2^{−σ})⁻¹ / 2 + 1/2) · (p:ℝ)^{−2σ}`. -/
lemma log_remainder_additive_bound_of_Re_ge_sigma
  {σ : ℝ} (hσ : (1 / 2 : ℝ) < σ) {s : ℂ} (hs : σ ≤ s.re) (p : Prime) :
  ‖Complex.log (1 - (p.1 : ℂ) ^ (-s)) + (p.1 : ℂ) ^ (-s) + ((p.1 : ℂ) ^ (-s)) ^ 2 / 2‖
    ≤ (((1 - (2 : ℝ) ^ (-σ))⁻¹) / 2 + (1 / 2 : ℝ)) * (p.1 : ℝ) ^ (-(2 : ℝ) * σ) := by
  classical
  set lam : ℂ := (p.1 : ℂ) ^ (-s)
  have hp_pos : 0 < (p.1 : ℝ) := by exact_mod_cast (Nat.Prime.pos p.property)
  have hlam_norm : ‖lam‖ = (p.1 : ℝ) ^ (-s.re) := by
    simpa [lam, Complex.norm_eq_abs] using
      (Complex.abs_cpow_eq_rpow_re_of_pos hp_pos (-s))
  -- monotonicity in exponent via exp/log
  have hle_sigma : (p.1 : ℝ) ^ (-s.re) ≤ (p.1 : ℝ) ^ (-σ) := by
    have hx : (p.1 : ℝ) ^ (-s.re) = Real.exp ((-s.re) * Real.log (p.1 : ℝ)) := by
      simpa [Real.rpow_def_of_pos hp_pos, mul_comm] using
        (rfl : (p.1 : ℝ) ^ (-s.re) = Real.exp (Real.log (p.1 : ℝ) * (-s.re)))
    have hy : (p.1 : ℝ) ^ (-σ) = Real.exp ((-σ) * Real.log (p.1 : ℝ)) := by
      simpa [Real.rpow_def_of_pos hp_pos, mul_comm] using
        (rfl : (p.1 : ℝ) ^ (-σ) = Real.exp (Real.log (p.1 : ℝ) * (-σ)))
    have hlogpos : 0 < Real.log (p.1 : ℝ) := by
      have : (1 : ℝ) < (p.1 : ℝ) := by exact_mod_cast (p.property.one_lt)
      simpa using Real.log_pos this
    have : (-s.re) ≤ (-σ) := by simpa using (neg_le_neg hs)
    have hcmp := mul_le_mul_of_nonneg_right this (le_of_lt hlogpos)
    exact (by simpa [hx, hy] using Real.exp_le_exp.mpr hcmp)
  have hlam_le_sigma : ‖lam‖ ≤ (p.1 : ℝ) ^ (-σ) := by simpa [hlam_norm] using hle_sigma
  -- compare to 2^{-σ} via exp/log monotonicity with negative multiplier
  have hlam_le_two : (p.1 : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) := by
    have hσpos : 0 < σ := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hσ
    have h2le : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.property.two_le
    have hbase : (1 / (p.1 : ℝ)) ≤ 1 / (2 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h2le
    have hpos1 : 0 < 1 / (p.1 : ℝ) := one_div_pos.mpr hp_pos
    have hpow : (1 / (p.1 : ℝ)) ^ σ ≤ (1 / (2 : ℝ)) ^ σ :=
      Real.rpow_le_rpow (le_of_lt hpos1) hbase (le_of_lt hσpos)
    have hp_pow_eq : (p.1 : ℝ) ^ (-σ) = ((p.1 : ℝ) ^ σ)⁻¹ := Real.rpow_neg (le_of_lt hp_pos) σ
    have h2_pow_eq : (2 : ℝ) ^ (-σ) = ((2 : ℝ) ^ σ)⁻¹ := Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) σ
    have hp_div_pow : (1 / (p.1 : ℝ)) ^ σ = ((p.1 : ℝ) ^ σ)⁻¹ := by
      rw [one_div, Real.inv_rpow (le_of_lt hp_pos)]
    have h2_div_pow : (1 / (2 : ℝ)) ^ σ = ((2 : ℝ) ^ σ)⁻¹ := by
      rw [one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
    calc (p.1 : ℝ) ^ (-σ)
        = ((p.1 : ℝ) ^ σ)⁻¹ := hp_pow_eq
      _ = (1 / (p.1 : ℝ)) ^ σ := hp_div_pow.symm
      _ ≤ (1 / (2 : ℝ)) ^ σ := hpow
      _ = ((2 : ℝ) ^ σ)⁻¹ := h2_div_pow
      _ = (2 : ℝ) ^ (-σ) := h2_pow_eq.symm
  -- show ‖lam‖ < 1 directly using exp/log monotonicity
  have hlam_lt_one : ‖lam‖ < 1 :=
    lt_of_le_of_lt (le_trans hlam_le_sigma hlam_le_two) (by
      have hσpos : 0 < σ := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hσ
      have h2_pow_eq : (2 : ℝ) ^ (-σ) = ((2 : ℝ) ^ σ)⁻¹ := Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) σ
      have : (2 : ℝ) ^ σ > 1 := by
        have : (2 : ℝ) > 1 := by norm_num
        exact Real.one_lt_rpow this hσpos
      rw [h2_pow_eq]
      have h2σ : 1 < (2 : ℝ) ^ σ := by linarith
      exact inv_lt_one_of_one_lt₀ h2σ)
  -- quadratic remainder + triangle inequality
  have hquad : ‖Complex.log (1 - lam) + lam‖ ≤ ‖lam‖ ^ 2 * (1 - ‖lam‖)⁻¹ / 2 := by
    simpa [sub_eq_add_neg, norm_neg] using
      Complex.norm_log_one_add_sub_self_le (z := -lam) (by simpa [norm_neg] using hlam_lt_one)
  have hhalf : ‖lam ^ 2 / 2‖ = (1 / 2 : ℝ) * ‖lam‖ ^ 2 := by
    have : ‖lam ^ 2‖ = ‖lam‖ ^ 2 := by simpa using (norm_pow _ 2)
    simpa [this, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hsum : ‖Complex.log (1 - lam) + lam + lam ^ 2 / 2‖
      ≤ ‖lam‖ ^ 2 * (1 - ‖lam‖)⁻¹ / 2 + (1 / 2 : ℝ) * ‖lam‖ ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    exact add_le_add hquad (by simpa [hhalf])
  -- denominator comparison via one_div
  have hden : (1 - ‖lam‖)⁻¹ ≤ (1 - (2 : ℝ) ^ (-σ))⁻¹ := by
    have hσpos : 0 < σ := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hσ
    have hpos₂ : 0 < 1 - (2 : ℝ) ^ (-σ) := by
      have h2_pow_eq : (2 : ℝ) ^ (-σ) = ((2 : ℝ) ^ σ)⁻¹ := Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) σ
      have : (2 : ℝ) ^ σ > 1 := by
        have : (2 : ℝ) > 1 := by norm_num
        exact Real.one_lt_rpow this hσpos
      have : (2 : ℝ) ^ (-σ) < 1 := by
        rw [h2_pow_eq]
        exact inv_lt_one_of_one_lt₀ (by linarith : (1 : ℝ) < (2 : ℝ) ^ σ)
      exact sub_pos.mpr this
    have : 1 - (2 : ℝ) ^ (-σ) ≤ 1 - ‖lam‖ := by
      have : ‖lam‖ ≤ (2 : ℝ) ^ (-σ) := le_trans hlam_le_sigma hlam_le_two
      linarith
    have := one_div_le_one_div_of_le hpos₂ this
    simpa [one_div] using this
  -- square bound using rpow_add
  have hsq : ‖lam‖ ^ 2 ≤ (p.1 : ℝ) ^ (-(2 : ℝ) * σ) := by
    have hposrpow : 0 < (p.1 : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hp_pos (-σ)
    have hmul1 : ‖lam‖ * ‖lam‖ ≤ ‖lam‖ * (p.1 : ℝ) ^ (-σ) :=
      mul_le_mul_of_nonneg_left hlam_le_sigma (norm_nonneg _)
    have hmul2 : ‖lam‖ * (p.1 : ℝ) ^ (-σ) ≤ (p.1 : ℝ) ^ (-σ) * (p.1 : ℝ) ^ (-σ) :=
      mul_le_mul_of_nonneg_right hlam_le_sigma (le_of_lt hposrpow)
    have hmul := le_trans hmul1 hmul2
    have hpowadd : (p.1 : ℝ) ^ (-σ) * (p.1 : ℝ) ^ (-σ) = (p.1 : ℝ) ^ ((-σ) + (-σ)) := by
      simpa using (Real.rpow_add hp_pos (-σ) (-σ)).symm
    have hsum : (-σ) + (-σ) = -((2 : ℝ) * σ) := by ring
    simpa [pow_two, hpowadd, hsum] using hmul
  -- finish: first multiply by denominator bound then insert the p^{-2σ} bound
  have hpos_inv : 0 ≤ (1 - (2 : ℝ) ^ (-σ))⁻¹ := by
    have hσpos : 0 < σ := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hσ
    have : 0 < 1 - (2 : ℝ) ^ (-σ) := by
      have : (2 : ℝ) ^ (-σ) < 1 := by
        have h : (1 / (2 : ℝ)) ^ σ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hσpos
        calc (2 : ℝ) ^ (-σ)
            = ((2 : ℝ) ^ σ)⁻¹ := Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) σ
          _ = (2⁻¹ : ℝ) ^ σ := by rw [← Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
          _ = (1 / 2 : ℝ) ^ σ := by norm_num
          _ < 1 := h
      exact sub_pos.mpr this
    exact inv_nonneg.mpr (le_of_lt this)
  have hden_mul : ‖lam‖ ^ 2 * (1 - ‖lam‖)⁻¹ ≤ (1 - (2 : ℝ) ^ (-σ))⁻¹ * ‖lam‖ ^ 2 := by
    have hsqnonneg : 0 ≤ ‖lam‖ ^ 2 := by exact sq_nonneg _
    have := mul_le_mul_of_nonneg_right hden hsqnonneg
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have h1' : ‖lam‖ ^ 2 * (1 - ‖lam‖)⁻¹ / 2
      ≤ (1 - (2 : ℝ) ^ (-σ))⁻¹ * ‖lam‖ ^ 2 / 2 := by
    have := mul_le_mul_of_nonneg_left hden_mul (by norm_num : 0 ≤ (1 / 2 : ℝ))
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have h1'' : (1 - (2 : ℝ) ^ (-σ))⁻¹ * ‖lam‖ ^ 2 / 2
      ≤ (1 - (2 : ℝ) ^ (-σ))⁻¹ * (p.1 : ℝ) ^ (-(2 : ℝ) * σ) / 2 := by
    have := mul_le_mul_of_nonneg_left hsq hpos_inv
    have := mul_le_mul_of_nonneg_left this (by norm_num : 0 ≤ (1 / 2 : ℝ))
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have h1 : ‖lam‖ ^ 2 * (1 - ‖lam‖)⁻¹ / 2
      ≤ ((1 - (2 : ℝ) ^ (-σ))⁻¹ / 2) * (p.1 : ℝ) ^ (-(2 : ℝ) * σ) := by
    have := le_trans h1' h1''
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have h2 : (1 / 2 : ℝ) * ‖lam‖ ^ 2 ≤ (1 / 2 : ℝ) * (p.1 : ℝ) ^ (-(2 : ℝ) * σ) :=
    mul_le_mul_of_nonneg_left hsq (by norm_num)
  -- combine the two bounds and rewrite the right-hand side
  have hsum' : ‖Complex.log (1 - lam) + lam + lam ^ 2 / 2‖
      ≤ ((1 - (2 : ℝ) ^ (-σ))⁻¹ / 2) * (p.1 : ℝ) ^ (-(2 : ℝ) * σ)
        + (1 / 2 : ℝ) * (p.1 : ℝ) ^ (-(2 : ℝ) * σ) :=
    (hsum.trans (add_le_add h1 h2))
  have hfactor :
      ((1 - (2 : ℝ) ^ (-σ))⁻¹ / 2) * (p.1 : ℝ) ^ (-(2 : ℝ) * σ)
        + (1 / 2 : ℝ) * (p.1 : ℝ) ^ (-(2 : ℝ) * σ)
      = (((1 - (2 : ℝ) ^ (-σ))⁻¹) / 2 + (1 / 2 : ℝ)) * (p.1 : ℝ) ^ (-(2 : ℝ) * σ) := by
    have := add_mul (((1 - (2 : ℝ) ^ (-σ))⁻¹) / 2) (1 / 2 : ℝ) ((p.1 : ℝ) ^ (-(2 : ℝ) * σ))
    simpa [mul_comm, mul_left_comm, mul_assoc] using this.symm
  calc ‖Complex.log (1 - lam) + lam + lam ^ 2 / 2‖
      ≤ ((1 - (2 : ℝ) ^ (-σ))⁻¹ / 2) * (p.1 : ℝ) ^ (-(2 : ℝ) * σ)
          + (1 / 2 : ℝ) * (p.1 : ℝ) ^ (-(2 : ℝ) * σ) := hsum'
    _ = (((1 - (2 : ℝ) ^ (-σ))⁻¹) / 2 + (1 / 2 : ℝ)) * (p.1 : ℝ) ^ (-(2 : ℝ) * σ) := hfactor
/-- Nonvanishing of each local factor when Re(s) > 0. -/
theorem det2EulerFactor_ne_zero_of_posRe {s : ℂ}
  (hs : 0 < s.re) (p : Prime) : det2EulerFactor s p ≠ 0 := by
  -- |p^{-s}| < 1 when Re(s) > 0; exp(·) is never zero.
  -- So (1 - λ) ≠ 0 and the product of nonzeros is nonzero.
  dsimp [det2EulerFactor]
  set lam : ℂ := (p.1 : ℂ) ^ (-s)
  -- exp never vanishes
  have hexp : Complex.exp (lam + lam ^ 2 / 2) ≠ 0 := Complex.exp_ne_zero _
  -- show (1 - lam) ≠ 0 because ‖lam‖ < 1
  have hnorm : ‖lam‖ = (p.1 : ℝ) ^ (-s.re) := by
    -- norm of (p : ℂ)^{-s} depends only on Re(s)
    have hp_pos : 0 < (p.1 : ℝ) := by
      exact_mod_cast (Nat.Prime.pos p.property)
    simpa [lam, Complex.norm_eq_abs]
      using (Complex.abs_cpow_eq_rpow_re_of_pos hp_pos (-s))
  have hlt : ‖lam‖ < 1 := by
    -- since p ≥ 2 and Re(s) > 0 ⇒ (p : ℝ)^(−Re s) < 1 via log–exp
    have hp_pos : 0 < (p.1 : ℝ) := by exact_mod_cast (Nat.Prime.pos p.property)
    have hp_gt_one : (1 : ℝ) < (p.1 : ℝ) := by
      have h2le : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.property.two_le
      have : (1 : ℝ) < 2 := by norm_num
      exact lt_of_lt_of_le this h2le
    have hlogpos : 0 < Real.log (p.1 : ℝ) := by
      have := Real.log_pos (by exact hp_gt_one)
      simp at this
      exact this
    have hxneg : -s.re < 0 := by linarith
    have hmul : (-s.re) * Real.log (p.1 : ℝ) < 0 :=
      (mul_neg_of_neg_of_pos hxneg hlogpos)
    have hrw : (p.1 : ℝ) ^ (-s.re) = Real.exp ((-s.re) * Real.log (p.1 : ℝ)) := by
      simpa [Real.rpow_def_of_pos hp_pos, mul_comm]
        using (rfl : (p.1 : ℝ) ^ (-s.re) = Real.exp (Real.log (p.1 : ℝ) * (-s.re)))
    have : Real.exp ((-s.re) * Real.log (p.1 : ℝ)) < Real.exp 0 :=
      Real.exp_lt_exp.mpr hmul
    have : (p.1 : ℝ) ^ (-s.re) < 1 := by simpa [hrw, Real.exp_zero] using this
    simpa [hnorm] using this
  have h1 : (1 - lam) ≠ 0 := by
    intro h
    -- From 1 - lam = 0, we get 1 = lam
    have hlam : 1 = lam := sub_eq_zero.mp h
    -- Hence ‖lam‖ = 1, contradicting ‖lam‖ < 1
    have hnorm1 : ‖lam‖ = 1 := by
      simpa [hlam.symm] using (norm_one : ‖(1 : ℂ)‖ = 1)
    exact (ne_of_lt hlt) hnorm1
  exact mul_ne_zero h1 hexp

/-- Analyticity of the Euler product det₂ on Re(s) > 1/2. -/
theorem det2_AF_analytic_on_halfPlaneReGtHalf :
  AnalyticOn ℂ det2_AF {s : ℂ | (1 / 2 : ℝ) < s.re} := by
  classical
  refine fun s0 hs0 => ?_
  -- local logs in additive form
  let a : Prime → ℂ → ℂ := fun p s =>
    Complex.log (1 - (p.1 : ℂ) ^ (-s)) + (p.1 : ℂ) ^ (-s) + ((p.1 : ℂ) ^ (-s)) ^ 2 / 2
  -- uniform summability of norms on a neighborhood via M-test
  have h_norm_conv : ∀ᶠ s in 𝓝 s0, Summable (fun p : Prime => a p s) := by
    obtain ⟨σ, hσhalf, hσ⟩ : ∃ σ, (1/2 : ℝ) < σ ∧ σ < s0.re := by
      refine ⟨(s0.re + 1/2)/2, ?_, ?_⟩
      · have : (1/2 : ℝ) < s0.re := hs0; linarith
      · have : (1/2 : ℝ) < s0.re := hs0; linarith
    have hopen : IsOpen {s : ℂ | σ < s.re} := by
      simpa using (isOpen_lt continuous_const Complex.continuous_re)
    obtain ⟨r, hrpos, hball⟩ :=
      Metric.isOpen_iff.mp hopen s0 (by simpa [Set.mem_setOf_eq] using hσ)
    have hsum : Summable (fun p : Prime => (p.1 : ℝ) ^ (-(2 : ℝ) * σ)) := by
      have : 1 < (2 : ℝ) * σ := by linarith
      simpa using AcademicRH.EulerProduct.real_prime_rpow_summable (r := (2 : ℝ) * σ) this
    have hball_nhds : ∀ᶠ s in 𝓝 s0, s ∈ Metric.ball s0 r := Metric.ball_mem_nhds s0 hrpos
    refine hball_nhds.mono ?_
    intro s hs_ball
    have hsσ : σ ≤ s.re := le_of_lt (by
      have : s ∈ {s : ℂ | σ < s.re} := hball hs_ball
      simpa [Set.mem_setOf_eq] using this)
    let Cσ : ℝ := ((1 - (2 : ℝ) ^ (-σ))⁻¹) / 2 + 2⁻¹
    have hbound : ∀ p : Prime, ‖a p s‖ ≤ Cσ * (p.1 : ℝ) ^ (-(2 : ℝ) * σ) := by
      intro p
      have := log_remainder_additive_bound_of_Re_ge_sigma (s := s) hσhalf hsσ p
      simpa [a, Cσ] using this
    have hsum' : Summable (fun p : Prime => Cσ * (p.1 : ℝ) ^ (-(2 : ℝ) * σ)) :=
      hsum.mul_left Cσ
    -- derive complex summability from norm comparison
    have hn : Summable (fun p : Prime => ‖a p s‖) :=
      Summable.of_nonneg_of_le (by intro _; exact norm_nonneg _) hbound hsum'
    exact Summable.of_norm hn
  -- product equals exp(tsum)
  have h_prod_eq_exp : ∀ᶠ s in 𝓝 s0,
      (∏' (p : Prime), Complex.exp (a p s)) = Complex.exp (∑' (p : Prime), a p s) :=
    h_norm_conv.mono (by intro s hs; exact (tprod_exp_of_summable (a := fun p => a p s) hs).2)
  -- identify our product with det2_AF
  have h_det_as_prod : ∀ᶠ s in 𝓝 s0, det2_AF s = ∏' (p : Prime), Complex.exp (a p s) := by
    -- Since s0.re > 1/2, there exists an open neighborhood where s.re > 0
    have : ∃ ε > 0, ∀ s, dist s s0 < ε → 0 < s.re := by
      use (s0.re) / 2
      constructor
      · have : 0 < s0.re := lt_trans (by norm_num : (0 : ℝ) < 1/2) hs0
        linarith
      · intro s hs_dist
        have habs : |s.re - s0.re| < s0.re / 2 := by
          have : Complex.abs (s - s0) = dist s s0 := rfl
          calc |s.re - s0.re|
              ≤ Complex.abs (s - s0) := Complex.abs_re_le_abs (s - s0)
            _ = dist s s0 := this
            _ < s0.re / 2 := hs_dist
        have h_pos : 0 < s0.re := lt_trans (by norm_num : (0 : ℝ) < 1/2) hs0
        rw [abs_sub_comm] at habs
        have h := abs_sub_lt_iff.mp habs
        have : -(s0.re / 2) < s.re - s0.re := by linarith [h.1]
        linarith [h.2]
    obtain ⟨ε, hε, hball⟩ := this
    refine Filter.Eventually.mono (Metric.ball_mem_nhds _ hε) ?_
    intro s hs_ball
    have hs_pos : 0 < s.re := hball s (Metric.mem_ball.mp hs_ball)
    have : ∀ p : Prime, det2EulerFactor s p = Complex.exp (a p s) := by
      intro p
      simp only [det2EulerFactor, a]
      have hlam_lt : ‖(p.1 : ℂ) ^ (-s)‖ < 1 := by
        have hp_pos : 0 < (p.1 : ℝ) := Nat.cast_pos.mpr (Nat.Prime.pos p.property)
        have hp_gt_one : 1 < (p.1 : ℝ) := by exact_mod_cast (Nat.Prime.one_lt p.property)
        have habs : Complex.abs ((p.1 : ℂ) ^ (-s)) = (p.1 : ℝ) ^ (-s.re) :=
          Complex.abs_cpow_eq_rpow_re_of_pos hp_pos (-s)
        rw [Complex.norm_eq_abs, habs]
        have hneg : -s.re < 0 := by linarith [hs_pos]
        have hrw : (p.1 : ℝ) ^ (-s.re) = Real.exp ((-s.re) * Real.log (p.1 : ℝ)) := by
          simpa [Real.rpow_def_of_pos hp_pos, mul_comm]
        have hlogpos : 0 < Real.log (p.1 : ℝ) := Real.log_pos hp_gt_one
        have : Real.exp ((-s.re) * Real.log (p.1 : ℝ)) < Real.exp 0 :=
          Real.exp_lt_exp.mpr (mul_neg_of_neg_of_pos hneg hlogpos)
        simpa [hrw, Real.exp_zero]
      exact eulerFactor_as_exp_log _ hlam_lt
    simp only [det2_AF, tprod_congr this]
  have h_eq_exp : ∀ᶠ s in 𝓝 s0, det2_AF s = Complex.exp (∑' (p : Prime), a p s) :=
    (h_det_as_prod.and h_prod_eq_exp).mono (by intro s hs; simpa [hs.1] using hs.2)
  -- analyticAt via equality on neighborhood: each term is analytic
  have hterm_analytic : ∀ p, AnalyticAt ℂ (fun s => a p s) s0 := by
    intro p
    have hpne : (p.1 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.Prime.pos p.property))
    have hlam : AnalyticAt ℂ (fun s => (p.1 : ℂ) ^ (-s)) s0 := by
      -- cpow via composition s ↦ -s, then multiply by constant, then exp
      -- In v4.13: z^w = exp(w * log(z)) when z ≠ 0
      have hlin : AnalyticAt ℂ (fun s : ℂ => -s) s0 := analyticAt_id.neg
      have hmul : AnalyticAt ℂ (fun s => (-s) * Complex.log (p.1 : ℂ)) s0 :=
        hlin.mul analyticAt_const
      have heq : (fun s => (p.1 : ℂ) ^ (-s)) = (fun s => Complex.exp ((-s) * Complex.log (p.1 : ℂ))) := by
        ext s
        rw [Complex.cpow_def_of_ne_zero hpne, mul_comm]
      rw [heq]
      exact hmul.cexp
    have hlog : AnalyticAt ℂ (fun s => Complex.log (1 - (p.1 : ℂ) ^ (-s))) s0 := by
      have hsub : AnalyticAt ℂ (fun s => 1 - (p.1 : ℂ) ^ (-s)) s0 := analyticAt_const.sub hlam
      have h_slit : 1 - (p.1 : ℂ) ^ (-s0) ∈ Complex.slitPlane := by
        -- Since ‖p^{-s0}‖ < 1, we have Re(1 - p^{-s0}) ≥ 1 - ‖p^{-s0}‖ > 0
        left
        have hp_pos : 0 < (p.1 : ℝ) := Nat.cast_pos.mpr (Nat.Prime.pos p.property)
        have hp_gt_one : 1 < (p.1 : ℝ) := by exact_mod_cast (Nat.Prime.one_lt p.property)
        have hlam_norm : ‖(p.1 : ℂ) ^ (-s0)‖ = (p.1 : ℝ) ^ (-s0.re) := by
          rw [Complex.norm_eq_abs]
          exact Complex.abs_cpow_eq_rpow_re_of_pos hp_pos (-s0)
        have hspos : 0 < s0.re := lt_trans (by norm_num : (0 : ℝ) < 1/2) hs0
        have hlt1 : (p.1 : ℝ) ^ (-s0.re) < 1 := by
          have hgt : 1 < (p.1 : ℝ) ^ (s0.re) := Real.one_lt_rpow hp_gt_one hspos
          have : ((p.1 : ℝ) ^ (s0.re))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hgt
          simpa [Real.rpow_neg (le_of_lt hp_pos)] using this
        have hre_pos : 0 < (1 : ℝ) - ‖(p.1 : ℂ) ^ (-s0)‖ := by
          simpa [hlam_norm] using sub_pos.mpr hlt1
        have h_re_le : ((1 : ℝ) - ‖(p.1 : ℂ) ^ (-s0)‖) ≤ (1 - (p.1 : ℂ) ^ (-s0)).re := by
          have : ((p.1 : ℂ) ^ (-s0)).re ≤ ‖(p.1 : ℂ) ^ (-s0)‖ := Complex.re_le_abs _
          have := sub_le_sub_left this 1
          simpa [sub_eq_add_neg] using this
        have : 0 < (1 - (p.1 : ℂ) ^ (-s0)).re := lt_of_lt_of_le hre_pos h_re_le
        simpa using this
      exact AnalyticAt.clog hsub h_slit
    have hsq : AnalyticAt ℂ (fun s => ((p.1 : ℂ) ^ (-s)) ^ 2) s0 := hlam.pow 2
    have hlincomb : AnalyticAt ℂ (fun s => (p.1 : ℂ) ^ (-s) + ((p.1 : ℂ) ^ (-s)) ^ 2 / 2) s0 := by
      have hhalf : AnalyticAt ℂ (fun _ => (1 / 2 : ℂ)) s0 := analyticAt_const
      have := hlam.add (hsq.mul hhalf)
      simpa [div_eq_mul_inv] using this
    -- combine into a single analytic function s ↦ a p s
    have hsum : AnalyticAt ℂ (fun s => Complex.log (1 - (p.1 : ℂ) ^ (-s)) +
        ((p.1 : ℂ) ^ (-s) + ((p.1 : ℂ) ^ (-s)) ^ 2 / 2)) s0 := hlog.add hlincomb
    convert hsum using 1
    ext s
    simp only [a, add_assoc]
  -- Now prove analyticity of the tsum using Weierstrass M-test
  -- Strategy: Use differentiableOn_tsum_of_summable_norm + DifferentiableOn.analyticAt
  -- We'll construct the same bounds used earlier to build h_norm_conv
  have h_tsum_analytic : AnalyticAt ℂ (fun s => ∑' (p : Prime), a p s) s0 := by
    -- Get σ with 1/2 < σ < s0.re (same as earlier)
    obtain ⟨σ, hσhalf, hσ⟩ : ∃ σ, (1/2 : ℝ) < σ ∧ σ < s0.re := by
      refine ⟨(s0.re + 1/2)/2, ?_, ?_⟩
      · have : (1/2 : ℝ) < s0.re := hs0; linarith
      · have : (1/2 : ℝ) < s0.re := hs0; linarith
    -- Open set where Re(s) > σ
    have hopen : IsOpen {s : ℂ | σ < s.re} := by
      simpa using (isOpen_lt continuous_const Complex.continuous_re)
    -- s0 is in this set
    have hs0_mem : s0 ∈ {s : ℂ | σ < s.re} := by simpa [Set.mem_setOf_eq] using hσ
    -- Get a ball around s0 contained in this set
    obtain ⟨r, hrpos, hball_subset⟩ := Metric.isOpen_iff.mp hopen s0 hs0_mem
    -- Each term is differentiable on the ball (analytic at each point implies differentiable)
    have hdiff : ∀ p : Prime, DifferentiableOn ℂ (fun s => a p s) (Metric.ball s0 r) := by
      intro p x hx
      -- The ball is open, so x is in the interior, hence in a neighborhood
      -- Since a p is analytic at every point (by hterm_analytic constructed uniformly),
      -- we can show it's analytic at x too (analyticity is an open condition)
      have : AnalyticAt ℂ (fun s => a p s) x := by
        -- Each component of a p s is analytic at x
        have hlam_x : AnalyticAt ℂ (fun s => (p.1 : ℂ) ^ (-s)) x := by
          have hpne : (p.1 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.Prime.pos p.property))
          have hlin : AnalyticAt ℂ (fun s : ℂ => -s) x := analyticAt_id.neg
          have hmul : AnalyticAt ℂ (fun s => (-s) * Complex.log (p.1 : ℂ)) x :=
            hlin.mul analyticAt_const
          have heq : (fun s => (p.1 : ℂ) ^ (-s)) = (fun s => Complex.exp ((-s) * Complex.log (p.1 : ℂ))) := by
            ext s; rw [Complex.cpow_def_of_ne_zero hpne, mul_comm]
          rw [heq]; exact hmul.cexp
        have hlog_x : AnalyticAt ℂ (fun s => Complex.log (1 - (p.1 : ℂ) ^ (-s))) x := by
          have hsub : AnalyticAt ℂ (fun s => 1 - (p.1 : ℂ) ^ (-s)) x := analyticAt_const.sub hlam_x
          -- Need to show 1 - p^{-x} ∈ slitPlane; x is in ball, so x.re is close to s0.re > 1/2
          have hx_re : 1/2 < x.re := by
            have : x ∈ {s : ℂ | σ < s.re} := hball_subset hx
            calc (1/2 : ℝ) < σ := hσhalf
              _ < x.re := this
          have : 1 - (p.1 : ℂ) ^ (-x) ∈ Complex.slitPlane := by
            left
            have hp_pos : 0 < (p.1 : ℝ) := Nat.cast_pos.mpr (Nat.Prime.pos p.property)
            have hp_gt_one : 1 < (p.1 : ℝ) := by exact_mod_cast (Nat.Prime.one_lt p.property)
            have hpow_lt : (p.1 : ℝ) ^ (-x.re) < 1 := by
              have hgt : 1 < (p.1 : ℝ) ^ (x.re) := Real.one_lt_rpow hp_gt_one (by linarith : 0 < x.re)
              have : ((p.1 : ℝ) ^ (x.re))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hgt
              simpa [Real.rpow_neg (le_of_lt hp_pos)] using this
            have hnorm_eq : ‖(p.1 : ℂ) ^ (-x)‖ = (p.1 : ℝ) ^ (-x.re) := by
              rw [Complex.norm_eq_abs]; exact Complex.abs_cpow_eq_rpow_re_of_pos hp_pos (-x)
            have hpos_diff : 0 < (1 : ℝ) - ‖(p.1 : ℂ) ^ (-x)‖ := by
              rw [hnorm_eq]
              exact sub_pos.mpr hpow_lt
            have hre_bound : ((p.1 : ℂ) ^ (-x)).re ≤ ‖(p.1 : ℂ) ^ (-x)‖ := Complex.re_le_abs _
            calc (1 - (p.1 : ℂ) ^ (-x)).re
                = (1 : ℝ) - ((p.1 : ℂ) ^ (-x)).re := by simp [Complex.sub_re, Complex.one_re]
              _ ≥ (1 : ℝ) - ‖(p.1 : ℂ) ^ (-x)‖ := by linarith [hre_bound]
              _ > 0 := hpos_diff
          exact AnalyticAt.clog hsub this
        have hsq_x : AnalyticAt ℂ (fun s => ((p.1 : ℂ) ^ (-s)) ^ 2) x := hlam_x.pow 2
        have hdiv_x : AnalyticAt ℂ (fun s => ((p.1 : ℂ) ^ (-s)) ^ 2 / 2) x := by
          have hhalf : AnalyticAt ℂ (fun _ => (2 : ℂ)⁻¹) x := analyticAt_const
          exact hsq_x.mul hhalf
        have hlincomb_x : AnalyticAt ℂ (fun s => (p.1 : ℂ) ^ (-s) + ((p.1 : ℂ) ^ (-s)) ^ 2 / 2) x :=
          hlam_x.add hdiv_x
        have hsum_x : AnalyticAt ℂ (fun s => Complex.log (1 - (p.1 : ℂ) ^ (-s)) +
            ((p.1 : ℂ) ^ (-s) + ((p.1 : ℂ) ^ (-s)) ^ 2 / 2)) x := hlog_x.add hlincomb_x
        convert hsum_x using 1
        ext s
        simp only [a, add_assoc]
      exact this.differentiableAt.differentiableWithinAt
    -- Construct uniform bounds
    have h2σ_gt : 1 < (2 : ℝ) * σ := by linarith
    set Cσ := ((1 - (2 : ℝ) ^ (-σ))⁻¹) / 2 + 2⁻¹
    have hsumσ := AcademicRH.EulerProduct.real_prime_rpow_summable h2σ_gt
    have hsum_bound := hsumσ.mul_left Cσ
    have hubound : ∀ p s, s ∈ Metric.ball s0 r → ‖a p s‖ ≤ Cσ * (p.1 : ℝ) ^ (-(2 * σ)) := by
      intro p s hs
      have hs_in : s ∈ {s : ℂ | σ < s.re} := hball_subset hs
      have hsσ : σ < s.re := hs_in
      have := log_remainder_additive_bound_of_Re_ge_sigma hσhalf (le_of_lt hsσ) p
      simp only [a]
      convert this using 2
      · -- Show Cσ = (1 - 2 ^ (-σ))⁻¹ / 2 + 1 / 2
        simp only [Cσ]
        norm_num
      · -- Show -(2 * σ) = -((2:ℝ) * σ)
        norm_num
    -- Apply differentiableOn_tsum_of_summable_norm
    have hdiff_tsum : DifferentiableOn ℂ (fun s => ∑' p : Prime, a p s) (Metric.ball s0 r) :=
      differentiableOn_tsum_of_summable_norm hsum_bound hdiff Metric.isOpen_ball hubound
    -- Convert to AnalyticAt using DifferentiableOn.analyticAt
    exact hdiff_tsum.analyticAt (Metric.ball_mem_nhds s0 hrpos)
  -- Compose with exp to get analyticity of exp(tsum)
  have h_eq_exp' : AnalyticAt ℂ (fun s => Complex.exp (∑' (p : Prime), a p s)) s0 :=
    h_tsum_analytic.cexp
  have : AnalyticAt ℂ det2_AF s0 :=
    RH.AnalyticAt.congr_of_eventuallyEq h_eq_exp' (h_eq_exp.mono (by intro s hs; symm; simpa using hs))
  -- conclude within the half-plane
  simpa using this.analyticWithinAt

/-- Nonvanishing of the 2‑modified determinant on the half‑plane Re(s) > 1/2. -/
theorem det2_AF_nonzero_on_halfPlaneReGtHalf :
  ∀ {s : ℂ}, s ∈ {s : ℂ | (1 / 2 : ℝ) < s.re} → det2_AF s ≠ 0 := by
  classical
  intro s hs
  -- Fix 1/2 < σ < Re(s)
  obtain ⟨σ, hσhalf, hσ⟩ : ∃ σ, (1/2 : ℝ) < σ ∧ σ < s.re := by
    refine ⟨(s.re + (1/2 : ℝ)) / 2, ?_, ?_⟩
    · -- Show 1/2 < (s.re + 1/2)/2
      have hs' : (1/2 : ℝ) < s.re := hs
      calc (1/2 : ℝ) = ((1/2 : ℝ) + (1/2 : ℝ)) / 2 := by norm_num
        _ < (s.re + (1/2 : ℝ)) / 2 := by linarith
    · -- Show (s.re + 1/2)/2 < s.re
      have hs' : (1/2 : ℝ) < s.re := hs
      calc (s.re + (1/2 : ℝ)) / 2 = s.re / 2 + (1/4 : ℝ) := by ring
        _ < s.re / 2 + s.re / 2 := by linarith
        _ = s.re := by ring
  -- Define a_p in additive form at this fixed s
  let a : Prime → ℂ := fun p =>
    let lam := (p.1 : ℂ) ^ (-s)
    Complex.log (1 - lam) + lam + lam ^ 2 / 2
  -- Summability of a by quadratic-tail domination with σ ∈ (1/2, Re(s)]
  have hsum_a : Summable a := by
    obtain ⟨σ, hσhalf, hσ⟩ : ∃ σ, (1/2 : ℝ) < σ ∧ σ ≤ s.re := by
      refine ⟨(s.re + 1/2)/2, ?_, ?_⟩; all_goals linarith
    -- Summability of ∑ p^{-2σ}
    have hsum : Summable (fun p : Prime => (p.1 : ℝ) ^ (-(2 : ℝ) * σ)) := by
      have : 1 < (2 : ℝ) * σ := by linarith
      simpa using AcademicRH.EulerProduct.real_prime_rpow_summable (r := (2 : ℝ) * σ) this
    -- Pointwise bound via additive lemma
    let Cσ : ℝ := ((1 - (2 : ℝ) ^ (-σ))⁻¹) / 2 + (1 / 2 : ℝ)
    have hbound : ∀ p : Prime, ‖a p‖ ≤ Cσ * (p.1 : ℝ) ^ (-(2 : ℝ) * σ) := by
      intro p; simpa [a, Cσ] using
        (log_remainder_additive_bound_of_Re_ge_sigma (s := s) hσhalf hσ p)
    have hsum' : Summable (fun p : Prime => Cσ * (p.1 : ℝ) ^ (-(2 : ℝ) * σ)) := hsum.mul_left Cσ
    have hn : Summable (fun p : Prime => ‖a p‖) :=
      Summable.of_nonneg_of_le (by intro _; exact norm_nonneg _) hbound hsum'
    exact Summable.of_norm hn
  -- Product equals exp(tsum) ⇒ exp(tsum) ≠ 0
  have hprod := (tprod_exp_of_summable (a := fun p : Prime => a p) hsum_a).2
  -- Identify det2 as the product of exponentials
  have hId : det2_AF s = ∏' (p : Prime), Complex.exp (a p) := by
    classical
    have hfactor : ∀ p : Prime, det2EulerFactor s p = Complex.exp (a p) := by
      intro p
      -- show ‖p^{-s}‖ < 1 when Re(s) > 1/2
      set lam : ℂ := (p.1 : ℂ) ^ (-s)
      have hp_pos : 0 < (p.1 : ℝ) := Nat.cast_pos.mpr (Nat.Prime.pos p.property)
      have hlam_lt : ‖lam‖ < 1 := by
        have hlam_abs : Complex.abs lam = (p.1 : ℝ) ^ (-s.re) := by
          simpa [lam, Complex.norm_eq_abs] using
            (Complex.abs_cpow_eq_rpow_re_of_pos hp_pos (-s))
        have hneg : -s.re < 0 := by
          have hspos : 0 < s.re := lt_trans (by norm_num : (0 : ℝ) < 1/2) (lt_trans hσhalf hσ)
          linarith
        have hlogpos : 0 < Real.log (p.1 : ℝ) := by
          have hp_gt_one : (1 : ℝ) < (p.1 : ℝ) := by exact_mod_cast (Nat.Prime.one_lt p.property)
          simpa using Real.log_pos hp_gt_one
        have hrw : (p.1 : ℝ) ^ (-s.re) = Real.exp ((-s.re) * Real.log (p.1 : ℝ)) := by
          simpa [Real.rpow_def_of_pos hp_pos, mul_comm]
        have : (p.1 : ℝ) ^ (-s.re) < 1 := by
          have := Real.exp_lt_exp.mpr (mul_neg_of_neg_of_pos hneg hlogpos)
          simpa [hrw, Real.exp_zero]
        simpa [Complex.norm_eq_abs, hlam_abs]
      have : det2EulerFactor s p = Complex.exp (Complex.log (1 - lam) + lam + lam ^ 2 / 2) := by
        simpa [det2EulerFactor, a, lam] using eulerFactor_as_exp_log lam hlam_lt
      simpa [a, lam] using this
    simpa [det2_AF, hfactor]
  -- Conclude nonvanishing
  have : det2_AF s = Complex.exp (∑' (p : Prime), a p) := by simpa [hId] using hprod
  simpa [this] using Complex.exp_ne_zero _

/-- Nonvanishing of det₂ on the critical line Re(s) = 1/2. -/
theorem det2_AF_nonzero_on_critical_line :
  ∀ t : ℝ, det2_AF ((1 / 2 : ℝ) + Complex.I * (t : ℂ)) ≠ 0 := by
  classical
  intro t
  set s : ℂ := (1 / 2 : ℝ) + Complex.I * (t : ℂ)
  let a : Prime → ℂ := fun p =>
    let lam := (p.1 : ℂ) ^ (-s)
    Complex.log (1 - lam) + lam + lam ^ 2 / 2
  -- Summability using 3σ with σ = 1/2 ⇒ 3/2 > 1
  have hsum_tail : Summable (fun p : Prime => (p.1 : ℝ) ^ (-((3 : ℝ) / 2))) := by
    simpa [neg_div] using
      AcademicRH.EulerProduct.real_prime_rpow_summable (r := (3 : ℝ) / 2) (by norm_num)
  have hsum_a : Summable a := by
    -- On the critical line, ‖λ‖ = p^{-1/2}; use cubic-tail bound and a global constant
    let C : ℝ := (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹
    have hbound : ∀ p : Prime, ‖a p‖ ≤ C * (p.1 : ℝ) ^ (-((3 : ℝ) / 2)) := by
      intro p
      -- λ = p^{-s}, with s = 1/2 + it
      set lam : ℂ := (p.1 : ℂ) ^ (-s)
      have hp_pos : 0 < (p.1 : ℝ) := by exact_mod_cast (Nat.Prime.pos p.property)
      have hlam : ‖lam‖ = (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
        -- on Re(s) = 1/2, the norm depends only on Re(s)
        simpa [lam, Complex.norm_eq_abs, s] using
          (Complex.abs_cpow_eq_rpow_re_of_pos hp_pos (-s))
      -- cubic tail
      have hcubic : ‖Complex.log (1 - lam) + lam + lam ^ 2 / 2‖
          ≤ ‖lam‖ ^ 3 / (1 - ‖lam‖) := by
        have hlam_lt : ‖lam‖ < 1 := by
          have hp_neg : (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) = ((p.1 : ℝ) ^ (1 / 2 : ℝ))⁻¹ :=
            Real.rpow_neg (le_of_lt hp_pos) (1 / 2)
          have h2_neg : (2 : ℝ) ^ (-(1 / 2 : ℝ)) = ((2 : ℝ) ^ (1 / 2 : ℝ))⁻¹ :=
            Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (1 / 2)
          have h2_pow_pos : 0 < (2 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
          have h2_pow_gt : 1 < (2 : ℝ) ^ (1 / 2 : ℝ) :=
            Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 1 / 2)
          have h2_inv_lt : ((2 : ℝ) ^ (1 / 2 : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ h2_pow_gt
          calc ‖lam‖
              = (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) := hlam
            _ = ((p.1 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := hp_neg
            _ ≤ ((2 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
                have : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast Nat.Prime.two_le p.property
                have : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (p.1 : ℝ) ^ (1 / 2 : ℝ) :=
                  Real.rpow_le_rpow (by norm_num) this (by norm_num)
                exact inv_le_inv_of_le h2_pow_pos this
            _ = (2 : ℝ) ^ (-(1 / 2 : ℝ)) := h2_neg.symm
            _ < 1 := by
                rw [h2_neg]
                exact h2_inv_lt
        exact log_one_sub_plus_z_plus_sq_cubic_tail hlam_lt
      -- bound denominator by constant C and rewrite ‖lam‖^3 = p^{-3/2}
      have hden : (1 - ‖lam‖)⁻¹ ≤ C := by
        have hlam_le_2 : ‖lam‖ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
          -- since p ≥ 2 ⇒ p^{-1/2} ≤ 2^{-1/2}
          have h2le : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.property.two_le
          have hp_eq : (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) = ((p.1 : ℝ) ^ (1 / 2 : ℝ))⁻¹ :=
            Real.rpow_neg (le_of_lt hp_pos) (1 / 2)
          have h2_eq : (2 : ℝ) ^ (-(1 / 2 : ℝ)) = ((2 : ℝ) ^ (1 / 2 : ℝ))⁻¹ :=
            Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (1 / 2)
          have h2_pow_pos : 0 < (2 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
          have : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (p.1 : ℝ) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) h2le (by norm_num)
          rw [hlam, hp_eq, h2_eq]
          exact inv_le_inv_of_le h2_pow_pos this
        have hpos : 0 < 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
          have h2_eq : (2 : ℝ) ^ (-(1 / 2 : ℝ)) = ((2 : ℝ) ^ (1 / 2 : ℝ))⁻¹ :=
            Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (1 / 2)
          have hpow : (2 : ℝ) ^ (1 / 2 : ℝ) > 1 := by
            have : (2 : ℝ) > 1 := by norm_num
            exact Real.one_lt_rpow this (by norm_num : (0 : ℝ) < 1 / 2)
          have : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := by
            rw [h2_eq]
            exact inv_lt_one_of_one_lt₀ hpow
          exact sub_pos.mpr this
        have h_le' : 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 - ‖lam‖ := by linarith [hlam_le_2]
        calc (1 - ‖lam‖)⁻¹
            ≤ (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ := inv_le_inv_of_le hpos h_le'
          _ = C := rfl
      have : ‖Complex.log (1 - lam) + lam + lam ^ 2 / 2‖ ≤ C * ‖lam‖ ^ 3 := by
        calc ‖Complex.log (1 - lam) + lam + lam ^ 2 / 2‖
            ≤ ‖lam‖ ^ 3 / (1 - ‖lam‖) := hcubic
          _ = ‖lam‖ ^ 3 * (1 - ‖lam‖)⁻¹ := by rw [div_eq_mul_inv]
          _ ≤ ‖lam‖ ^ 3 * C := by
              exact mul_le_mul_of_nonneg_left hden (by exact pow_nonneg (norm_nonneg _) 3)
          _ = C * ‖lam‖ ^ 3 := by ring
      -- rewrite ‖lam‖^3 as p^{-3/2}
      have hlam3 : ‖lam‖ ^ 3 = (p.1 : ℝ) ^ (-(3 : ℝ) / 2) := by
        have hmul : (-(1 / 2 : ℝ)) * (3 : ℝ) = -(3 / 2 : ℝ) := by norm_num
        have hrpow : ((p.1 : ℝ) ^ (-(1 / 2 : ℝ))) ^ (3 : ℕ) = (p.1 : ℝ) ^ ((-(1 / 2 : ℝ)) * (3 : ℝ)) := by
          conv_lhs => rw [← Real.rpow_natCast ((p.1 : ℝ) ^ (-(1 / 2 : ℝ))) 3]
          rw [← Real.rpow_mul (le_of_lt hp_pos)]
          norm_num
        have heq : -(3 / 2 : ℝ) = -(3 : ℝ) / 2 := by norm_num
        calc ‖lam‖ ^ 3
            = ((p.1 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 3 := by rw [hlam]
          _ = (p.1 : ℝ) ^ ((-(1 / 2 : ℝ)) * (3 : ℝ)) := hrpow
          _ = (p.1 : ℝ) ^ (-(3 / 2 : ℝ)) := by rw [hmul]
          _ = (p.1 : ℝ) ^ (-(3 : ℝ) / 2) := by rw [heq]
      simp only [a, lam]
      calc ‖Complex.log (1 - lam) + lam + lam ^ 2 / 2‖
          ≤ C * ‖lam‖ ^ 3 := this
        _ = C * (p.1 : ℝ) ^ (-(3 : ℝ) / 2) := by rw [hlam3]
        _ = C * (p.1 : ℝ) ^ (-((3 : ℝ) / 2)) := by norm_num
    have hsum' : Summable (fun p : Prime => C * (p.1 : ℝ) ^ (-((3 : ℝ) / 2))) :=
      hsum_tail.mul_left C
    have hn : Summable (fun p : Prime => ‖a p‖) :=
      Summable.of_nonneg_of_le (by intro _; exact norm_nonneg _) hbound hsum'
    exact Summable.of_norm hn
  have hprod := (tprod_exp_of_summable (a := fun p : Prime => a p) hsum_a).2
  -- Identify det2 as the product of exponentials, pointwise via the local factor lemma
  have hId : det2_AF s = ∏' (p : Prime), Complex.exp (a p) := by
    classical
    have hfactor : ∀ p : Prime, det2EulerFactor s p = Complex.exp (a p) := by
      intro p
      set lam : ℂ := (p.1 : ℂ) ^ (-s)
      have hp_pos : 0 < (p.1 : ℝ) := Nat.cast_pos.mpr (Nat.Prime.pos p.property)
      have hlam_lt : ‖lam‖ < 1 := by
        rw [Complex.norm_eq_abs]
        have hlam_abs : Complex.abs lam = (p.1 : ℝ) ^ (-s.re) := by
          simpa [lam] using (Complex.abs_cpow_eq_rpow_re_of_pos hp_pos (-s))
        have hsre : s.re = (1 / 2 : ℝ) := by
          simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
            Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero]
        rw [hlam_abs, hsre]
        have : (p.1 : ℝ) ^ (-(1/2 : ℝ)) < 1 := by
          have h_eq : (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) = ((p.1 : ℝ) ^ (1 / 2 : ℝ))⁻¹ :=
            Real.rpow_neg (le_of_lt hp_pos) (1 / 2)
          rw [h_eq]
          have hp_gt_one : 1 < (p.1 : ℝ) := by
            calc (1 : ℝ) < 2 := by norm_num
              _ ≤ p.1 := by exact_mod_cast Nat.Prime.two_le p.property
          have hpow_gt_one : 1 < (p.1 : ℝ) ^ (1/2 : ℝ) := by
            exact Real.one_lt_rpow hp_gt_one (by norm_num : (0 : ℝ) < 1 / 2)
          exact inv_lt_one_of_one_lt₀ hpow_gt_one
        exact this
      simpa [det2EulerFactor, a, lam, eulerFactor_as_exp_log] using eulerFactor_as_exp_log lam hlam_lt
    simpa [det2_AF, hfactor]
  calc det2_AF s
      = ∏' (p : Prime), Complex.exp (a p) := hId
    _ = Complex.exp (∑' (p : Prime), a p) := hprod
    _ ≠ 0 := Complex.exp_ne_zero _

end RH.AcademicFramework.DiagonalFredholm
