import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Data.Real.StarOrdered
import Riemann.academic_framework.Compat
import Riemann.academic_framework.DiagonalFredholm.WeierstrassProduct
import Riemann.academic_framework.EulerProduct.PrimeSeries

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
    simpa [lam, Complex.norm_eq_sqrt_sq_add_sq] using
      (Complex.norm_cpow_eq_rpow_re_of_pos hp_pos (-s))
  -- monotonicity in exponent via exp/log
  have hle_sigma : (p.1 : ℝ) ^ (-s.re) ≤ (p.1 : ℝ) ^ (-σ) := by
    have hx : (p.1 : ℝ) ^ (-s.re) = Real.exp ((-s.re) * Real.log (p.1 : ℝ)) := by
      simp [Real.rpow_def_of_pos hp_pos, mul_comm]
    have hy : (p.1 : ℝ) ^ (-σ) = Real.exp ((-σ) * Real.log (p.1 : ℝ)) := by
      simp [Real.rpow_def_of_pos hp_pos, mul_comm]
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
    have hnorm_sq : ‖lam ^ 2‖ = ‖lam‖ ^ 2 := norm_pow _ 2
    simp [hnorm_sq, div_eq_mul_inv, mul_comm]
  have hsum : ‖Complex.log (1 - lam) + lam + lam ^ 2 / 2‖
      ≤ ‖lam‖ ^ 2 * (1 - ‖lam‖)⁻¹ / 2 + (1 / 2 : ℝ) * ‖lam‖ ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    exact add_le_add hquad (by aesop)
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
    simpa [lam, Complex.norm_eq_sqrt_sq_add_sq]
      using (Complex.norm_cpow_eq_rpow_re_of_pos hp_pos (-s))
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
      simp [Real.rpow_def_of_pos hp_pos, mul_comm]
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
      have h := congrArg (fun z : ℂ => ‖z‖) hlam.symm
      exact h.trans norm_one
    exact (ne_of_lt hlt) hnorm1
  exact mul_ne_zero h1 hexp

set_option maxHeartbeats 600000

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
          have : norm (s - s0) = dist s s0 := rfl
          calc |s.re - s0.re|
              ≤ norm (s - s0) := Complex.abs_re_le_norm (s - s0)
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
        have habs : norm ((p.1 : ℂ) ^ (-s)) = (p.1 : ℝ) ^ (-s.re) :=
          Complex.norm_cpow_eq_rpow_re_of_pos hp_pos (-s)
        rw [habs]
        calc (p.1 : ℝ) ^ (-s.re)
            = (p.1 : ℝ) ^ (-(s.re)) := by ring_nf
          _ < 1 := by
              refine Real.rpow_lt_one_of_one_lt_of_neg hp_gt_one ?_
              exact neg_neg_iff_pos.mpr (hball s hs_ball)
      exact eulerFactor_as_exp_log _ hlam_lt
    simp only [det2_AF, tprod_congr this]
  have h_eq_exp : ∀ᶠ s in 𝓝 s0, det2_AF s = Complex.exp (∑' (p : Prime), a p s) :=
    (h_det_as_prod.and h_prod_eq_exp).mono (by intro s hs; simpa [hs.1] using hs.2)
  -- Now prove analyticity of the tsum using Weierstrass M-test
  -- Strategy: Use differentiableOn_tsum_of_summable_norm + DifferentiableOn.analyticAt
  have h_tsum_analytic : AnalyticAt ℂ (fun s => ∑' (p : Prime), a p s) s0 := by
    -- Step 1: Find a summable bound that works uniformly on a ball around s0
    -- We use the calculation from h_norm_conv which showed the bound exists
    obtain ⟨σ, hσhalf, hσ⟩ : ∃ σ, (1/2 : ℝ) < σ ∧ σ < s0.re := by
      refine ⟨(s0.re + 1/2)/2, ?_, ?_⟩
      · have : (1/2 : ℝ) < s0.re := hs0; linarith
      · have : (1/2 : ℝ) < s0.re := hs0; linarith
    -- Choose radius small enough that all points in ball have Re > σ
    let r := min (s0.re - σ) 1
    have hrpos : 0 < r := by
      simp only [r, lt_min_iff]
      constructor
      · linarith
      · norm_num
    -- Apply differentiableOn_tsum_of_summable_norm
    -- We need: summable bound, each term differentiable, open set, bound holds
    have h2σ : 1 < (2 : ℝ) * σ := by linarith
    have hdiff_tsum : DifferentiableOn ℂ (fun s => ∑' p : Prime, a p s) (Metric.ball s0 r) := by
      apply differentiableOn_tsum_of_summable_norm
      · -- Summable bound
        exact (AcademicRH.EulerProduct.real_prime_rpow_summable h2σ).mul_left
          (((1 - (2 : ℝ) ^ (-σ))⁻¹) / 2 + 2⁻¹)
      · -- Each term differentiable
        intro p x hx
        -- a p s = log(1 - p^{-s}) + p^{-s} + (p^{-s})^2/2
        -- This is analytic at x by the same argument as for s0
        have hpne : (p.1 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.Prime.pos p.property))
        -- x is in the ball, so x.re > σ > 1/2 > 0
        have hx_re : 0 < x.re := by
          have : x ∈ Metric.ball s0 r := hx
          have : dist x s0 < r := Metric.mem_ball.mp this
          have : dist x s0 < s0.re - σ := lt_of_lt_of_le this (min_le_left _ _)
          have habs : |x.re - s0.re| ≤ dist x s0 := by
            calc |x.re - s0.re| ≤ norm (x - s0) := Complex.abs_re_le_norm (x - s0)
              _ = dist x s0 := rfl
          rw [abs_sub_comm] at habs
          linarith [abs_sub_lt_iff.mp (lt_of_le_of_lt habs this) |>.1,
                    abs_sub_lt_iff.mp (lt_of_le_of_lt habs this) |>.2, hσhalf]
        -- p^{-s} is analytic at x
        have hlam_x : AnalyticAt ℂ (fun s => (p.1 : ℂ) ^ (-s)) x := by
          have hlin : AnalyticAt ℂ (fun s : ℂ => -s) x := analyticAt_id.neg
          have hmul : AnalyticAt ℂ (fun s => (-s) * Complex.log (p.1 : ℂ)) x :=
            hlin.mul analyticAt_const
          have heq : (fun s => (p.1 : ℂ) ^ (-s)) = (fun s => Complex.exp ((-s) * Complex.log (p.1 : ℂ))) := by
            ext s; rw [Complex.cpow_def_of_ne_zero hpne, mul_comm]
          rw [heq]
          exact hmul.cexp
        -- log(1 - p^{-s}) is analytic at x (similar to s0 case)
        have hlog_x : AnalyticAt ℂ (fun s => Complex.log (1 - (p.1 : ℂ) ^ (-s))) x := by
          have hsub : AnalyticAt ℂ (fun s => 1 - (p.1 : ℂ) ^ (-s)) x := analyticAt_const.sub hlam_x
          have h_slit : 1 - (p.1 : ℂ) ^ (-x) ∈ Complex.slitPlane := by
            left
            have hp_pos : 0 < (p.1 : ℝ) := Nat.cast_pos.mpr (Nat.Prime.pos p.property)
            have hlam_abs :
                norm ((p.1 : ℂ) ^ (-x)) = (p.1 : ℝ) ^ (-x.re) := by
              -- abs of a complex power with positive real base
              simpa using (Complex.norm_cpow_eq_rpow_re_of_pos hp_pos (-x))
            have hlt1 : (p.1 : ℝ) ^ (-x.re) < 1 := by
              have hp_gt_one : 1 < (p.1 : ℝ) := by exact_mod_cast (Nat.Prime.one_lt p.property)
              have hgt : 1 < (p.1 : ℝ) ^ (x.re) := Real.one_lt_rpow hp_gt_one hx_re
              have : ((p.1 : ℝ) ^ (x.re))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hgt
              simpa [Real.rpow_neg (le_of_lt hp_pos)] using this
            have hre_pos :
                0 < (1 : ℝ) - norm ((p.1 : ℂ) ^ (-x)) := by
              simpa [hlam_abs] using sub_pos.mpr hlt1
            have h_re_le :
                ((1 : ℝ) - norm ((p.1 : ℂ) ^ (-x)))
                  ≤ (1 - (p.1 : ℂ) ^ (-x)).re := by
              have : ((p.1 : ℂ) ^ (-x)).re
                  ≤ norm ((p.1 : ℂ) ^ (-x)) := re_le_norm (↑↑p ^ (-x))
              have := sub_le_sub_left this 1
              simpa [sub_eq_add_neg] using this
            have : 0 < (1 - (p.1 : ℂ) ^ (-x)).re :=
              lt_of_lt_of_le hre_pos h_re_le
            simpa using this
          exact AnalyticAt.clog hsub h_slit
        -- Combine: log(1 - p^{-s}) + p^{-s} + (p^{-s})^2/2 = a p s
        have hsq_x : AnalyticAt ℂ (fun s => ((p.1 : ℂ) ^ (-s)) ^ 2) x := hlam_x.pow 2
        have hlincomb_x : AnalyticAt ℂ (fun s => (p.1 : ℂ) ^ (-s) + ((p.1 : ℂ) ^ (-s)) ^ 2 / 2) x := by
          have hhalf : AnalyticAt ℂ (fun _ => (1 / 2 : ℂ)) x := analyticAt_const
          have := hlam_x.add (hsq_x.mul hhalf)
          simpa [div_eq_mul_inv] using this
        have hsum_x : AnalyticAt ℂ (fun s => Complex.log (1 - (p.1 : ℂ) ^ (-s)) +
            ((p.1 : ℂ) ^ (-s) + ((p.1 : ℂ) ^ (-s)) ^ 2 / 2)) x := hlog_x.add hlincomb_x
        convert hsum_x.differentiableAt.differentiableWithinAt using 1
        ext s
        simp only [a, add_assoc]
      · -- Open set
        exact Metric.isOpen_ball
      · -- Bound holds
        intro p s hs
        have hs_re : σ ≤ s.re := by
          have hdist : dist s s0 < r := Metric.mem_ball.mp hs
          have hdist_σ : dist s s0 < s0.re - σ := lt_of_lt_of_le hdist (min_le_left _ _)
          have habs : |s.re - s0.re| ≤ dist s s0 := by
            calc
              |s.re - s0.re| ≤ norm (s - s0) := Complex.abs_re_le_norm (s - s0)
              _ = dist s s0 := rfl
          rw [abs_sub_comm] at habs
          linarith [abs_sub_lt_iff.mp (lt_of_le_of_lt habs hdist_σ) |>.1,
                    abs_sub_lt_iff.mp (lt_of_le_of_lt habs hdist_σ) |>.2]
        have hbound_calc := log_remainder_additive_bound_of_Re_ge_sigma hσhalf hs_re p
        convert hbound_calc using 1
        -- Show the constants match: 2⁻¹ = 1/2 and -(2*σ) = -2*σ
        norm_num
    -- Convert to AnalyticAt using DifferentiableOn.analyticAt (complex analysis)
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
        have hlam_abs : norm lam = (p.1 : ℝ) ^ (-s.re) := by
          simpa [lam] using (Complex.norm_cpow_eq_rpow_re_of_pos hp_pos (-s))
        have hs_re : (1 / 2 : ℝ) < s.re := by
          simpa [Set.mem_setOf_eq] using hs
        have hneg : -s.re < 0 := by linarith [hs_re]
        have hlogpos : 0 < Real.log (p.1 : ℝ) :=
          Real.log_pos (by exact_mod_cast (Nat.Prime.one_lt p.property))
        have hrw : (p.1 : ℝ) ^ (-s.re) = Real.exp ((-s.re) * Real.log (p.1 : ℝ)) := by
          simp [Real.rpow_def_of_pos hp_pos, mul_comm]
        have : (p.1 : ℝ) ^ (-s.re) < 1 := by
          have := Real.exp_lt_exp.mpr (mul_neg_of_neg_of_pos hneg hlogpos)
          simpa [hrw, Real.exp_zero]
        simpa [Complex.norm_eq_sqrt_sq_add_sq, hlam_abs] using this
      simpa [det2EulerFactor, a, lam, eulerFactor_as_exp_log] using eulerFactor_as_exp_log lam hlam_lt
    simp [det2_AF, hfactor]
  have hdet_exp : det2_AF s = Complex.exp (∑' (p : Prime), a p) := by
    calc
      det2_AF s = ∏' (p : Prime), Complex.exp (a p) := hId
      _ = Complex.exp (∑' (p : Prime), a p) := hprod
  have : det2_AF s ≠ 0 := by
    have hexp : Complex.exp (∑' (p : Prime), a p) ≠ 0 := Complex.exp_ne_zero _
    exact hdet_exp.symm ▸ hexp
  exact this

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
        simpa [lam, Complex.norm_eq_sqrt_sq_add_sq, s] using
          (Complex.norm_cpow_eq_rpow_re_of_pos hp_pos (-s))
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
      simp only [a]
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
        rw [Complex.norm_eq_sqrt_sq_add_sq]
        have hlam_abs : norm lam = (p.1 : ℝ) ^ (-s.re) := by
          simpa [lam, Complex.norm_eq_sqrt_sq_add_sq] using
            (Complex.norm_cpow_eq_rpow_re_of_pos hp_pos (-s))
        have hsre : s.re = (1 / 2 : ℝ) := by
          simp [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_im]
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
        calc √(lam.re ^ 2 + lam.im ^ 2)
            = ‖lam‖ := by rw [Complex.norm_eq_sqrt_sq_add_sq]
          _ = (p.1 : ℝ) ^ (-s.re) := hlam_abs
          _ = (p.1 : ℝ) ^ (-(1/2 : ℝ)) := by rw [hsre]
          _ < 1 := this
      simpa [det2EulerFactor, a, lam, eulerFactor_as_exp_log] using eulerFactor_as_exp_log lam hlam_lt
    simp [det2_AF, hfactor]
  have hdet_exp : det2_AF s = Complex.exp (∑' (p : Prime), a p) := by
    calc
      det2_AF s = ∏' (p : Prime), Complex.exp (a p) := hId
      _ = Complex.exp (∑' (p : Prime), a p) := hprod
  have : det2_AF s ≠ 0 := by
    have hexp : Complex.exp (∑' (p : Prime), a p) ≠ 0 := Complex.exp_ne_zero _
    exact hdet_exp.symm ▸ hexp
  exact this

/-! ### Boundary continuity via Weierstrass M-test -/

section BoundaryContinuity

open Complex

/-- AF boundary parametrization of the critical line (local copy to avoid import cycles). -/
@[simp] def boundaryPoint (t : ℝ) : ℂ := (1 / 2 : ℂ) + Complex.I * (t : ℂ)

-- Rewrite helpers: normalize 1/2 and 2⁻¹ forms for ℝ and ℂ, and expand -(boundaryPoint t).
-- These fix shape mismatches like `2 ^ (-2⁻¹)` vs `2 ^ (-(1/2))`
private lemma two_inv_real : (2 : ℝ)⁻¹ = (1 / 2 : ℝ) := by norm_num
private lemma two_inv_complex : (2 : ℂ)⁻¹ = (1 / 2 : ℂ) := by norm_num
private lemma neg_two_inv_real : -((2 : ℝ)⁻¹) = -(1 / 2 : ℝ) := by norm_num
private lemma neg_two_inv_complex : -((2 : ℂ)⁻¹) = -(1 / 2 : ℂ) := by norm_num
private lemma neg_boundaryPoint_expand (t : ℝ) :
    -(boundaryPoint t) = -(1 / 2 : ℂ) - Complex.I * (t : ℂ) := by
  simp [boundaryPoint, sub_eq_add_neg, add_comm]

-- Real rpow behaves like ordinary exponentiation on natural powers for positive bases.
lemma boundaryPoint_re (t : ℝ) : (boundaryPoint t).re = 1 / 2 := by
  simp [boundaryPoint, Complex.add_re]

lemma boundaryPoint_im (t : ℝ) : (boundaryPoint t).im = t := by
  simp [boundaryPoint, Complex.add_im]

lemma boundaryPoint_eq_two_inv (t : ℝ) :
    boundaryPoint t = (2 : ℂ)⁻¹ + Complex.I * (t : ℂ) := by
  have h : (1 / 2 : ℂ) = (2 : ℂ)⁻¹ := by norm_num
  calc
    boundaryPoint t = (1 / 2 : ℂ) + Complex.I * (t : ℂ) := rfl
    _ = (2 : ℂ)⁻¹ + Complex.I * (t : ℂ) := by
      simp [h]

def det2_AF_boundary_logSummand (p : Prime) (t : ℝ) : ℂ :=
  let s := boundaryPoint t
  Complex.log (1 - (p.1 : ℂ) ^ (-s)) + (p.1 : ℂ) ^ (-s) + ((p.1 : ℂ) ^ (-s)) ^ 2 / 2

@[simp] lemma det2_AF_boundary_logSummand_def (p : Prime) (t : ℝ) :
    det2_AF_boundary_logSummand p t =
      Complex.log (1 - (p.1 : ℂ) ^ (-(boundaryPoint t))) +
        (p.1 : ℂ) ^ (-(boundaryPoint t)) +
        ((p.1 : ℂ) ^ (-(boundaryPoint t))) ^ 2 / 2 := by
  simp [det2_AF_boundary_logSummand]

private def det2_boundary_majorant_const : ℝ :=
  (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹

private lemma two_pow_neg_two_inv_lt_one :
    (2 : ℝ) ^ (-((2 : ℝ)⁻¹)) < 1 := by
  have hy_gt : 1 < (2 : ℝ) ^ ((2 : ℝ)⁻¹) :=
    Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (by norm_num : 0 < (2 : ℝ)⁻¹)
  have hinv_lt : ((2 : ℝ) ^ ((2 : ℝ)⁻¹))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hy_gt
  have hrew :
      (2 : ℝ) ^ (-((2 : ℝ)⁻¹)) = ((2 : ℝ) ^ ((2 : ℝ)⁻¹))⁻¹ :=
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) ((2 : ℝ)⁻¹)
  simpa [hrew] using hinv_lt

private lemma two_pow_neg_one_half_lt_one :
    (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := by
  simpa [neg_two_inv_real] using two_pow_neg_two_inv_lt_one

private lemma prime_pow_neg_two_inv_lt_one (p : Prime) :
    (p.1 : ℝ) ^ (-((2 : ℝ)⁻¹)) < 1 := by
  have hp_gt_one : 1 < (p.1 : ℝ) := by exact_mod_cast p.property.one_lt
  have hy_gt : 1 < (p.1 : ℝ) ^ ((2 : ℝ)⁻¹) :=
    Real.one_lt_rpow hp_gt_one (by norm_num : 0 < (2 : ℝ)⁻¹)
  have hinv_lt : ((p.1 : ℝ) ^ ((2 : ℝ)⁻¹))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hy_gt
  have hrew :
      (p.1 : ℝ) ^ (-((2 : ℝ)⁻¹)) = ((p.1 : ℝ) ^ ((2 : ℝ)⁻¹))⁻¹ :=
    Real.rpow_neg (le_of_lt (Nat.cast_pos.mpr p.property.pos)) ((2 : ℝ)⁻¹)
  simpa [hrew] using hinv_lt

private lemma prime_pow_neg_one_half_lt_one (p : Prime) :
    (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := by
  simpa [neg_two_inv_real] using prime_pow_neg_two_inv_lt_one p

private lemma det2_boundary_majorant_const_pos :
    0 < det2_boundary_majorant_const := by
  have htwo_lt_one :
      (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := by
    simpa [neg_two_inv_real] using two_pow_neg_one_half_lt_one
  have hden :
      0 < 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    sub_pos.mpr htwo_lt_one
  simpa [det2_boundary_majorant_const] using inv_pos.mpr hden

private lemma boundary_lambda_norm (p : Prime) (t : ℝ) :
    ‖(p.1 : ℂ) ^ (-(boundaryPoint t))‖ = (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hp_pos : 0 < (p.1 : ℝ) := by exact_mod_cast (Nat.Prime.pos p.property)
  have : (boundaryPoint t).re = 1 / 2 := boundaryPoint_re t
  have hrpow :
      (p.1 : ℝ) ^ (-(boundaryPoint t).re) = (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    simp [this]
  have := Complex.norm_cpow_eq_rpow_re_of_pos hp_pos (-(boundaryPoint t))
  simpa [Complex.norm_eq_sqrt_sq_add_sq, hrpow]
    using this

private lemma neg_boundaryPoint_eq_expanded_two_inv (t : ℝ) :
    -(boundaryPoint t) = -(Complex.I * (t : ℂ)) + -((2 : ℂ)⁻¹) := by
  simp [boundaryPoint, add_comm, add_assoc, neg_two_inv_complex]

private lemma abs_cpow_boundary_expanded (p : Prime) (t : ℝ) :
    norm ((p.1 : ℂ) ^ (-(Complex.I * (t : ℂ)) + -((2 : ℂ)⁻¹)))
      = (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have := boundary_lambda_norm (p := p) (t := t)
  simpa [Complex.norm_eq_sqrt_sq_add_sq, neg_boundaryPoint_eq_expanded_two_inv t]
    using this

private lemma boundary_abs_expanded_eq_twoInv (p : Prime) (t : ℝ) :
    norm ((p.1 : ℂ) ^ (-(Complex.I * (t : ℂ)) + -((2 : ℂ)⁻¹)))
      = (p.1 : ℝ) ^ (-((2 : ℝ)⁻¹)) := by
  have := boundary_lambda_norm (p := p) (t := t)
  simpa [Complex.norm_eq_sqrt_sq_add_sq, neg_boundaryPoint_eq_expanded_two_inv t,
    neg_two_inv_real]
    using this

private lemma boundary_abs_expanded_lt_one (p : Prime) (t : ℝ) :
    norm ((p.1 : ℂ) ^ (-(Complex.I * (t : ℂ)) + -((2 : ℂ)⁻¹))) < 1 := by
  have hlt : (p.1 : ℝ) ^ (-((2 : ℝ)⁻¹)) < 1 := prime_pow_neg_two_inv_lt_one p
  simpa [boundary_abs_expanded_eq_twoInv (p := p) (t := t)] using hlt

private lemma real_pow_neg_half_pow_three (p : Prime) :
    ((p.1 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 3 = (p.1 : ℝ) ^ (-((3 : ℝ) / 2)) := by
  have hxpos : 0 < (↑↑p : ℝ) := by exact_mod_cast p.property.pos
  set r : ℝ := -(1 / 2 : ℝ)
  have htwo :
      ((↑↑p : ℝ) ^ r) * ((↑↑p : ℝ) ^ r) = (↑↑p : ℝ) ^ (r + r) := by
    simpa [r, add_comm] using
      (Real.rpow_add hxpos (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ))).symm
  have hthree :
      (↑↑p : ℝ) ^ (r + r) * (↑↑p : ℝ) ^ r =
        (↑↑p : ℝ) ^ (r + r + r) := by
    simpa [r, add_comm, add_left_comm, add_assoc] using
      (Real.rpow_add hxpos (-(1 / 2 : ℝ) + -(1 / 2 : ℝ)) (-(1 / 2 : ℝ))).symm
  have hsum : r + r + r = -((3 : ℝ) / 2) := by
    have hxr : r = -((2 : ℝ)⁻¹) := by
      simp [r]
    have : -((2 : ℝ)⁻¹) + (-((2 : ℝ)⁻¹) + -((2 : ℝ)⁻¹))
        = -((3 : ℝ) / 2) := by
      norm_num
    simpa [hxr, add_comm, add_left_comm, add_assoc] using this
  have hpow :
      ((↑↑p : ℝ) ^ r) ^ 3 =
        (↑↑p : ℝ) ^ r * ((↑↑p : ℝ) ^ r * (↑↑p : ℝ) ^ r) := by
    rw [pow_three]
  have hpow' :
      ((↑↑p : ℝ) ^ r) ^ 3 =
        (↑↑p : ℝ) ^ (r + r) * (↑↑p : ℝ) ^ r := by
    simpa [htwo, mul_comm, mul_left_comm, mul_assoc]
      using hpow
  have hstd :
      ((↑↑p : ℝ) ^ r) ^ 3 = (↑↑p : ℝ) ^ (r + r + r) := by
    simpa [hthree, mul_comm, mul_left_comm, mul_assoc] using hpow'
  simpa [hsum] using hstd

private lemma boundary_abs_expanded_pow_three (p : Prime) (t : ℝ) :
    (norm ((p.1 : ℂ) ^ (-(Complex.I * (t : ℂ)) + -((2 : ℂ)⁻¹)))) ^ 3
        = (p.1 : ℝ) ^ (-((3 : ℝ) / 2)) := by
  have hbase :
      norm ((p.1 : ℂ) ^ (-(Complex.I * (t : ℂ)) + -((2 : ℂ)⁻¹))) =
        (p.1 : ℝ) ^ (-((2 : ℝ)⁻¹)) :=
    boundary_abs_expanded_eq_twoInv (p := p) (t := t)
  have hpow :=
    real_pow_neg_half_pow_three (p := p)
  have hx : -((2 : ℝ)⁻¹) = -(1 / 2 : ℝ) := by norm_num
  have hpow_twoInv :
      ((p.1 : ℝ) ^ (-((2 : ℝ)⁻¹))) ^ 3 = (p.1 : ℝ) ^ (-((3 : ℝ) / 2)) := by
    simpa [hx]
      using hpow
  simpa [hbase] using hpow_twoInv

-- Absolute value of the expanded boundary exponent form.
private lemma boundary_one_sub_lambda_mem_slitPlane (p : Prime) (t : ℝ) :
    1 - (p.1 : ℂ) ^ (-(boundaryPoint t)) ∈ Complex.slitPlane := by
  have hlam_lt_one :
      ‖(p.1 : ℂ) ^ (-(boundaryPoint t))‖ < 1 := by
    have :=
      boundary_abs_expanded_lt_one (p := p) (t := t)
    simpa [Complex.norm_eq_sqrt_sq_add_sq, neg_boundaryPoint_eq_expanded_two_inv t]
      using this
  have hRe :
      ((p.1 : ℂ) ^ (-(boundaryPoint t))).re < 1 :=
    lt_of_le_of_lt (by exact re_le_norm (↑↑p ^ (-boundaryPoint t))) hlam_lt_one
  have hpos :
      0 < 1 - ((p.1 : ℂ) ^ (-(boundaryPoint t))).re :=
    sub_pos.mpr hRe
  exact Or.inl hpos

private lemma boundary_one_sub_lambda_expanded_mem_slitPlane (p : Prime) (t : ℝ) :
    1 - (p.1 : ℂ) ^ (-(Complex.I * (t : ℂ)) + -((2 : ℂ)⁻¹))
      ∈ Complex.slitPlane := by
  simpa [neg_boundaryPoint_eq_expanded_two_inv t] using
    boundary_one_sub_lambda_mem_slitPlane (p := p) (t := t)

lemma det2_AF_boundary_logSummand_continuous (p : Prime) :
    Continuous fun t : ℝ => det2_AF_boundary_logSummand p t := by
  classical
  have hp_ne_zero : (p.1 : ℂ) ≠ 0 :=
    by exact_mod_cast (ne_of_gt (Nat.Prime.pos p.property))
  have hCpow : Continuous fun t : ℝ => (p.1 : ℂ) ^ (-(boundaryPoint t)) := by
    have hboundary : Continuous fun t : ℝ => boundaryPoint t := by
      have : Continuous fun t : ℝ => (t : ℂ) := Complex.continuous_ofReal
      simpa [boundaryPoint, two_mul, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc]
        using
          ((continuous_const : Continuous fun _ : ℝ => (1 / 2 : ℂ))).add
            ((continuous_const : Continuous fun _ : ℝ => Complex.I).mul
              (Complex.continuous_ofReal))
    have hfun : Continuous fun s : ℂ => (p.1 : ℂ) ^ (-s) := by
      have hlin : Continuous fun s : ℂ => -s := continuous_id'.neg
      have hmul :
          Continuous fun s : ℂ =>
            (-s) * Complex.log (p.1 : ℂ) :=
        hlin.mul continuous_const
      have hcexp : Continuous fun s : ℂ =>
          Complex.exp ((-s) * Complex.log (p.1 : ℂ)) :=
        Complex.continuous_exp.comp hmul
      have hcpow :
          (fun s : ℂ => (p.1 : ℂ) ^ (-s)) =
            fun s : ℂ =>
              Complex.exp ((-s) * Complex.log (p.1 : ℂ)) := by
        ext s
        simp [Complex.cpow_def_of_ne_zero hp_ne_zero, mul_comm]
      simpa [hcpow] using hcexp
    exact hfun.comp hboundary
  have h_sq :
      Continuous fun t : ℝ =>
        ((p.1 : ℂ) ^ (-(boundaryPoint t))) ^ 2 :=
    hCpow.pow 2
  have hConstHalf :
      Continuous fun _ : ℝ => (1 / 2 : ℂ) := continuous_const
  have hterm :
      Continuous fun t : ℝ =>
        (p.1 : ℂ) ^ (-(boundaryPoint t)) +
          ((p.1 : ℂ) ^ (-(boundaryPoint t))) ^ 2 / 2 := by
    simpa [div_eq_mul_inv, add_comm, add_left_comm, add_assoc, mul_left_comm,
      mul_comm, mul_assoc]
      using hCpow.add (h_sq.mul hConstHalf)
  have hLog :
      Continuous fun t : ℝ =>
        Complex.log (1 - (p.1 : ℂ) ^ (-(boundaryPoint t))) := by
    have hsub :
        Continuous fun t : ℝ =>
          1 - (p.1 : ℂ) ^ (-(boundaryPoint t)) :=
      continuous_const.sub hCpow
    have hmem :
        ∀ t : ℝ, 1 - (p.1 : ℂ) ^ (-(boundaryPoint t)) ∈ Complex.slitPlane :=
      boundary_one_sub_lambda_mem_slitPlane (p := p)
    exact Continuous.clog hsub hmem
  simpa [det2_AF_boundary_logSummand_def, add_assoc, add_left_comm,
    add_comm] using hLog.add hterm

lemma det2_AF_prime_cube_summable :
    Summable fun p : Prime => (p.1 : ℝ) ^ (-((3 : ℝ) / 2)) := by
  simpa [neg_div] using
    AcademicRH.EulerProduct.real_prime_rpow_summable
      (r := (3 : ℝ) / 2)
      (by norm_num)

lemma det2_AF_boundary_logSummand_norm_bound (p : Prime) (t : ℝ) :
    ‖det2_AF_boundary_logSummand p t‖
        ≤ det2_boundary_majorant_const * (p.1 : ℝ) ^ (-((3 : ℝ) / 2)) := by
  classical
  set lam : ℂ := (p.1 : ℂ) ^ (-(boundaryPoint t))
  have hlam_abs_half :
      norm lam = (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    simpa [Complex.norm_eq_sqrt_sq_add_sq, lam] using
      boundary_lambda_norm (p := p) (t := t)
  have hlam_lt_expanded :
      norm ((p.1 : ℂ) ^ (-(Complex.I * (t : ℂ)) + -((2 : ℂ)⁻¹))) < 1 := by
    exact boundary_abs_expanded_lt_one (p := p) (t := t)
  have hlam_lt_one :
      norm lam < 1 := by
    simpa [lam, neg_boundaryPoint_eq_expanded_two_inv t]
      using hlam_lt_expanded
  have hden :
      (1 - norm lam)⁻¹ ≤ det2_boundary_majorant_const := by
    have hle_two : (2 : ℝ) ≤ (p.1 : ℝ) :=
      by exact_mod_cast Nat.Prime.two_le p.property
    have hpow_le :
        (p.1 : ℝ) ^ (1 / 2 : ℝ) ≥ (2 : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hle_two (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hlam_le :
        norm lam ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have :=
        inv_le_inv_of_le (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
          hpow_le
      simpa [hlam_abs_half,
        Real.rpow_neg (le_of_lt (Nat.cast_pos.mpr p.property.pos)),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        using this
    have htwo_lt_one :
        (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := by
      simpa using two_pow_neg_one_half_lt_one
    have hpos :
        0 < 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
      sub_pos.mpr htwo_lt_one
    have hineq :
        1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 - norm lam :=
      sub_le_sub_left hlam_le 1
    have :=
      one_div_le_one_div_of_le hpos hineq
    simpa [one_div, det2_boundary_majorant_const] using this
  have htail :
      ‖Complex.log (1 - lam) + lam + lam ^ 2 / 2‖
        ≤ (norm lam) ^ 3 / (1 - norm lam) := by
    simpa [Complex.norm_eq_sqrt_sq_add_sq] using
      log_one_sub_plus_z_plus_sq_cubic_tail hlam_lt_one
  have hlam_pow :
      (norm lam) ^ 3 = (p.1 : ℝ) ^ (-((3 : ℝ) / 2)) := by
    have hpow :=
      boundary_abs_expanded_pow_three (p := p) (t := t)
    have hbase :
        norm ((p.1 : ℂ) ^ (-(Complex.I * (t : ℂ)) + -((2 : ℂ)⁻¹)))
          = norm lam := by
      simp [lam, neg_boundaryPoint_eq_expanded_two_inv t]
    simpa [hbase] using hpow
  have hbound :
      ‖det2_AF_boundary_logSummand p t‖
        ≤ det2_boundary_majorant_const * (p.1 : ℝ) ^ (-((3 : ℝ) / 2)) := by
    have :
        ‖det2_AF_boundary_logSummand p t‖
          ≤ (norm lam) ^ 3 / (1 - norm lam) := by
      -- Align any expanded boundary shapes to the local `lam`.
      -- This prevents shape mismatches such as `(p : ℂ) ^ (-(I * t) + -2⁻¹)`.
      simpa [det2_AF_boundary_logSummand_def, lam] using htail
    refine this.trans ?_
    have :
        (norm lam) ^ 3 / (1 - norm lam)
          ≤ det2_boundary_majorant_const * (norm lam) ^ 3 := by
      have :=
        mul_le_mul_of_nonneg_left hden
          (by
            have : 0 ≤ norm lam := by exact norm_nonneg lam
            exact pow_nonneg this (3 : ℕ))
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using this
    have hrewrite :
        det2_boundary_majorant_const * (norm lam) ^ 3 =
          det2_boundary_majorant_const *
            (p.1 : ℝ) ^ (-((3 : ℝ) / 2)) := by
      simp [hlam_pow]
    simpa [hrewrite] using this
  exact hbound

lemma det2_AF_boundary_hasUniformSumOnCompacts :
    ∃ u : Prime → ℝ, Summable u ∧
      ∀ (p : Prime) (t : ℝ),
        ‖det2_AF_boundary_logSummand p t‖ ≤ u p := by
  classical
  refine ⟨fun p => det2_boundary_majorant_const * (p.1 : ℝ) ^ (-((3 : ℝ) / 2)), ?_, ?_⟩
  · exact (det2_AF_prime_cube_summable).mul_left det2_boundary_majorant_const
  · intro p t; exact det2_AF_boundary_logSummand_norm_bound (p := p) (t := t)

lemma det2_AF_boundary_summable (t : ℝ) :
    Summable fun p : Prime => det2_AF_boundary_logSummand p t := by
  classical
  obtain ⟨u, hSummable, hbound⟩ := det2_AF_boundary_hasUniformSumOnCompacts
  have hnorm :
      Summable fun p : Prime =>
          ‖det2_AF_boundary_logSummand p t‖ :=
    Summable.of_nonneg_of_le (by intro _; exact norm_nonneg _)
      (fun p => hbound p t) hSummable
  exact Summable.of_norm hnorm

lemma det2_AF_boundary_eq_exp_tsum (t : ℝ) :
    det2_AF (boundaryPoint t) =
      Complex.exp (∑' (p : Prime), det2_AF_boundary_logSummand p t) := by
  classical
  have hSummable := det2_AF_boundary_summable t
  have hprod :=
    (tprod_exp_of_summable
        (a := fun p : Prime => det2_AF_boundary_logSummand p t)
        hSummable).2
  have hfactor :
      ∀ p : Prime,
        Complex.exp (det2_AF_boundary_logSummand p t) =
          det2EulerFactor ((2 : ℂ)⁻¹ + Complex.I * (t : ℂ)) p := by
    intro p
    set lam : ℂ := (p.1 : ℂ) ^ (-(boundaryPoint t))
    have hlam_lt :
        ‖lam‖ < 1 := by
      have := boundary_abs_expanded_lt_one (p := p) (t := t)
      simpa [Complex.norm_eq_sqrt_sq_add_sq, lam, neg_boundaryPoint_eq_expanded_two_inv t]
        using this
    have hdet := eulerFactor_as_exp_log lam hlam_lt
    have :
        Complex.exp (det2_AF_boundary_logSummand p t) =
          det2EulerFactor (boundaryPoint t) p := by
      simpa [det2EulerFactor, det2_AF_boundary_logSummand_def, lam, add_comm,
        add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hdet.symm
    simpa [boundaryPoint_eq_two_inv] using this
  have hfactor_fun :
      (fun p : Prime =>
          det2EulerFactor ((2 : ℂ)⁻¹ + Complex.I * (t : ℂ)) p) =
        fun p : Prime => Complex.exp (det2_AF_boundary_logSummand p t) := by
    funext p; symm; exact hfactor p
  have hprod_congr :
      ∏' (p : Prime), det2EulerFactor ((2 : ℂ)⁻¹ + Complex.I * (t : ℂ)) p =
        ∏' (p : Prime), Complex.exp (det2_AF_boundary_logSummand p t) := by
    simpa using congrArg (fun f : Prime → ℂ => ∏' p, f p) hfactor_fun
  have hprodEuler :
      ∏' (p : Prime), det2EulerFactor ((2 : ℂ)⁻¹ + Complex.I * (t : ℂ)) p =
        Complex.exp (∑' (p : Prime), det2_AF_boundary_logSummand p t) :=
    hprod_congr.trans hprod
  simpa [det2_AF, boundaryPoint_eq_two_inv] using hprodEuler

lemma det2_AF_twoInv_eq_exp_tsum (t : ℝ) :
    det2_AF ((2 : ℂ)⁻¹ + Complex.I * (t : ℂ)) =
      Complex.exp (∑' (p : Prime), det2_AF_boundary_logSummand p t) := by
  calc
    det2_AF ((2 : ℂ)⁻¹ + Complex.I * (t : ℂ))
        = det2_AF (boundaryPoint t) := by
          simp [boundaryPoint_eq_two_inv]
    _ = Complex.exp (∑' (p : Prime), det2_AF_boundary_logSummand p t) :=
          det2_AF_boundary_eq_exp_tsum t

lemma det2_AF_boundary_continuous :
    Continuous fun t : ℝ => det2_AF (boundaryPoint t) := by
  classical
  obtain ⟨u, hSummableU, hbound⟩ := det2_AF_boundary_hasUniformSumOnCompacts
  have hcont_tsum :
      Continuous fun t : ℝ =>
        ∑' (p : Prime), det2_AF_boundary_logSummand p t :=
    continuous_tsum
      (fun p => det2_AF_boundary_logSummand_continuous p)
      hSummableU
      (fun p t => hbound p t)
  have hcont :
      Continuous fun t : ℝ =>
        Complex.exp (∑' (p : Prime), det2_AF_boundary_logSummand p t) :=
    Complex.continuous_exp.comp hcont_tsum
  have hrewrite :
      (fun t : ℝ => det2_AF (boundaryPoint t)) =
        fun t : ℝ => det2_AF ((2 : ℂ)⁻¹ + Complex.I * (t : ℂ)) := by
    funext t; simpa [boundaryPoint_eq_two_inv]
  have hfunexp :
      (fun t : ℝ => det2_AF ((2 : ℂ)⁻¹ + Complex.I * (t : ℂ))) =
        fun t =>
          Complex.exp (∑' (p : Prime), det2_AF_boundary_logSummand p t) := by
    funext t; exact det2_AF_twoInv_eq_exp_tsum t
  have htwoInv :
      Continuous fun t : ℝ =>
        det2_AF ((2 : ℂ)⁻¹ + Complex.I * (t : ℂ)) := by
    simpa [hfunexp] using hcont
  simpa [hrewrite] using htwoInv

lemma det2_AF_twoInv_continuous :
    Continuous fun t : ℝ =>
      det2_AF ((2 : ℂ)⁻¹ + Complex.I * (t : ℂ)) := by
  simpa [boundaryPoint_eq_two_inv] using det2_AF_boundary_continuous

end BoundaryContinuity

end RH.AcademicFramework.DiagonalFredholm
