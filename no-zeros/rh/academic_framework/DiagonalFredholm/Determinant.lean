import rh.Compat
import rh.academic_framework.EulerProduct.PrimeSeries

noncomputable section

open Complex Set
open scoped Topology BigOperators

namespace RH.AcademicFramework.DiagonalFredholm

/-! Minimal helpers (duplicated locally to avoid extra imports). -/

/-- Exponential turns sums into products (modern route).
If `a` is summable, then `∏ exp (a i) = exp (∑ a i)` and the product is `Multipliable`. -/
lemma tprod_exp_of_summable {ι : Type*} [Countable ι]
    (a : ι → ℂ) (hsum : Summable a) :
    Multipliable (fun i => Complex.exp (a i)) ∧
      (∏' i, Complex.exp (a i)) = Complex.exp (∑' i, a i) := by
  have hsum' : HasSum a (∑' i, a i) := hsum.hasSum
  have hprod : HasProd (fun i => Complex.exp (a i)) (Complex.exp (∑' i, a i)) := by
    simpa [Function.comp] using hsum'.cexp
  exact ⟨hprod.multipliable, hprod.tprod_eq⟩

/-- For `‖z‖ < 1`, the modified Euler factor `(1 - z) * exp(z + z^2/2)`
can be written as a single exponential `exp(log(1 - z) + z + z^2/2)`. -/
lemma eulerFactor_as_exp_log (z : ℂ) (hz : ‖z‖ < (1 : ℝ)) :
    (1 - z) * Complex.exp (z + z ^ 2 / 2)
      = Complex.exp (Complex.log (1 - z) + z + z ^ 2 / 2) := by
  have hne : 1 - z ≠ 0 := by
    intro h
    have hz1 : ‖z‖ = 1 := by
      have : 1 = z := sub_eq_zero.mp h
      simpa [this.symm]
    exact (ne_of_lt hz) hz1
  calc
    (1 - z) * Complex.exp (z + z ^ 2 / 2)
        = Complex.exp (Complex.log (1 - z)) * Complex.exp (z + z ^ 2 / 2) := by
          simpa [Complex.exp_log hne]
    _   = Complex.exp (Complex.log (1 - z) + (z + z ^ 2 / 2)) := by
          simpa [Complex.exp_add] using
            (Complex.exp_add (Complex.log (1 - z)) (z + z ^ 2 / 2)).symm
    _   = Complex.exp (Complex.log (1 - z) + z + z ^ 2 / 2) := by
          simpa [add_comm, add_left_comm, add_assoc]

-- (moved after `abbrev Prime` below)

/-- Cubic tail bound for the modified Weierstrass log remainder on `‖z‖ < 1`:
`‖log(1 - z) + z + z^2/2‖ ≤ ‖z‖^3 / (1 - ‖z‖)`.
This is the `log(1 + w)` cubic remainder bound specialized to `w = -z`. -/
lemma logTaylor_three (w : ℂ) : Complex.logTaylor 3 w = w - w ^ 2 / 2 := by
  unfold Complex.logTaylor
  simp [Finset.sum_range_succ, Finset.sum_range_zero]
  ring

lemma cubic_tail_log_one_sub {z : ℂ} (hz : ‖z‖ < (1 : ℝ)) :
    ‖Complex.log (1 - z) + z + z ^ 2 / 2‖ ≤ ‖z‖ ^ 3 / (1 - ‖z‖) := by
  -- Taylor remainder at order 2 for w = -z
  have hneg : ‖-z‖ < (1 : ℝ) := by simpa [norm_neg] using hz
  -- Bound the Taylor remainder with consistent casting (as in WeierstrassProduct)
  have h := (Complex.norm_log_sub_logTaylor_le (n := 2) (z := -z) hneg)
  have h23 : ((2 : ℝ) + 1) = 3 := by norm_num
  have hrem : ‖Complex.log (1 + (-z)) - Complex.logTaylor 3 (-z)‖
      ≤ ‖-z‖ ^ 3 * (1 - ‖-z‖)⁻¹ / 3 := by
    simpa [Nat.cast_add, Nat.cast_one, h23] using h
  -- Identify the remainder with our expression
  have hEq : ‖Complex.log (1 - z) + z + z ^ 2 / 2‖
      = ‖Complex.log (1 + (-z)) - Complex.logTaylor 3 (-z)‖ := by
    rw [logTaylor_three]
    congr 1
    ring
  -- Transfer bound and drop 1/3 factor
  have hstep : ‖Complex.log (1 - z) + z + z ^ 2 / 2‖
      ≤ ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ / 3 := by
    rw [hEq]
    simp only [norm_neg]
    exact hrem
  have hnonneg : 0 ≤ ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ := by
    exact mul_nonneg (pow_nonneg (norm_nonneg _) 3)
      (inv_nonneg.mpr (sub_nonneg.mpr (le_of_lt hz)))
  have hdrop : ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ / 3 ≤ ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ := by
    have : (1 / (3 : ℝ)) ≤ 1 := by norm_num
    calc ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ / 3
        = (1/3) * (‖z‖ ^ 3 * (1 - ‖z‖)⁻¹) := by ring
      _ ≤ 1 * (‖z‖ ^ 3 * (1 - ‖z‖)⁻¹) := mul_le_mul_of_nonneg_right this hnonneg
      _ = ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ := by ring
  calc ‖Complex.log (1 - z) + z + z ^ 2 / 2‖
      ≤ ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ / 3 := hstep
    _ ≤ ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ := hdrop
    _ = ‖z‖ ^ 3 / (1 - ‖z‖) := by rw [div_eq_mul_inv]

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
    have hpos1 : 0 ≤ 1 / (p.1 : ℝ) := le_of_lt (one_div_pos.mpr hp_pos)
    have : (1 / (p.1 : ℝ)) ^ σ ≤ (1 / (2 : ℝ)) ^ σ :=
      Real.rpow_le_rpow hpos1 hbase (le_of_lt hσpos)
    calc (p.1 : ℝ) ^ (-σ)
        = ((1 / (p.1 : ℝ)) ^ σ)⁻¹ := by rw [Real.rpow_neg, inv_eq_one_div]
      _ ≤ ((1 / (2 : ℝ)) ^ σ)⁻¹ := by gcongr
      _ = (2 : ℝ) ^ (-σ) := by rw [Real.rpow_neg, inv_eq_one_div]
  -- show ‖lam‖ < 1 directly using exp/log monotonicity
  have hlam_lt_one : ‖lam‖ < 1 :=
    lt_of_le_of_lt (le_trans hlam_le_sigma hlam_le_two) (by
      have hσpos : 0 < σ := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hσ
      have : (1 / (2 : ℝ)) ^ σ < 1 := by
        have hbase : 0 < 1 / (2 : ℝ) := by norm_num
        have hlt1 : 1 / (2 : ℝ) < 1 := by norm_num
        exact Real.rpow_lt_one hbase.le hlt1 hσpos
      rw [Real.rpow_neg, inv_eq_one_div]
      exact this)
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
      have h2pos : 0 < (2 : ℝ) := by norm_num
      have hy : (2 : ℝ) ^ (-σ) = Real.exp ((-σ) * Real.log (2 : ℝ)) := by
        simp [Real.rpow_def_of_pos h2pos, mul_comm]
      have hlog2pos : 0 < Real.log (2 : ℝ) := by
        have : (1 : ℝ) < (2 : ℝ) := by norm_num
        simpa using Real.log_pos this
      have hneg : (-σ) < 0 := by linarith
      have : Real.exp ((-σ) * Real.log (2 : ℝ)) < Real.exp 0 :=
        Real.exp_lt_exp.mpr (mul_neg_of_neg_of_pos hneg hlog2pos)
      have : (2 : ℝ) ^ (-σ) < 1 := by simpa [hy, Real.exp_zero] using this
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
        have : (1 / (2 : ℝ)) ^ σ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hσpos
        rw [Real.rpow_neg, inv_eq_one_div]
        exact this
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
  simpa [hfactor]
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
    let Cσ : ℝ := ((1 - (2 : ℝ) ^ (-σ))⁻¹) / 2 + (1 / 2 : ℝ)
    have hbound : ∀ p : Prime, ‖a p s‖ ≤ Cσ * (p.1 : ℝ) ^ (-(2 : ℝ) * σ) := by
      intro p; simpa [a] using log_remainder_additive_bound_of_Re_ge_sigma (s := s) hσhalf hsσ p
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
    refine Filter.Eventually.of_forall ?_; intro s
    simp [det2_AF, det2EulerFactor, a, eulerFactor_as_exp_log]
  have h_eq_exp : ∀ᶠ s in 𝓝 s0, det2_AF s = Complex.exp (∑' (p : Prime), a p s) :=
    (h_det_as_prod.and h_prod_eq_exp).mono (by intro s hs; simpa [hs.1] using hs.2)
  -- analyticAt via equality on neighborhood: per-term analytic and local identity
  have hterm_analytic : ∀ p, AnalyticAt ℂ (fun s => a p s) s0 := by
    intro p
    have hpne : (p.1 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.Prime.pos p.property))
    have hlam : AnalyticAt ℂ (fun s => (p.1 : ℂ) ^ (-s)) s0 := by
      -- cpow via composition s ↦ -s, then multiply by constant, then exp
      have hlin : AnalyticAt ℂ (fun s : ℂ => -s) s0 := analyticAt_id.neg
      have hmul : AnalyticAt ℂ (fun s => (-s) * Complex.log (p.1 : ℂ)) s0 :=
        hlin.mul analyticAt_const
      simpa [Complex.cpow_eq_exp_log, hpne] using hmul.cexp
    have hlog : AnalyticAt ℂ (fun s => Complex.log (1 - (p.1 : ℂ) ^ (-s))) s0 := by
      have hsub : AnalyticAt ℂ (fun s => 1 - (p.1 : ℂ) ^ (-s)) s0 := analyticAt_const.sub hlam
      have h_slit : 1 - (p.1 : ℂ) ^ (-s0) ∈ Complex.slitPlane := by
        -- Since ‖p^{-s0}‖ < 1, we have Re(1 - p^{-s0}) ≥ 1 - ‖p^{-s0}‖ > 0
        left
        have hp_pos : 0 < (p.1 : ℝ) := Nat.cast_pos.mpr (Nat.Prime.pos p.property)
        have hlam_norm : ‖(p.1 : ℂ) ^ (-s0)‖ = (p.1 : ℝ) ^ (-s0.re) := by
          rw [Complex.norm_eq_abs]
          exact Complex.abs_cpow_eq_rpow_re_of_pos hp_pos (-s0)
        have : (p.1 : ℝ) ^ (-s0.re) < 1 := by
          -- since hs0: 1/2 < s0.re and p ≥ 2
          have hp_gt_one : 1 < (p.1 : ℝ) := by exact_mod_cast (Nat.Prime.one_lt p.property)
          have hneg : -s0.re < 0 := by linarith [hs0]
          -- exp/log monotonicity
          have hrw : (p.1 : ℝ) ^ (-s0.re) = Real.exp ((-s0.re) * Real.log (p.1 : ℝ)) := by
            simpa [Real.rpow_def_of_pos hp_pos, mul_comm]
              using (rfl : (p.1 : ℝ) ^ (-s0.re) = Real.exp (Real.log (p.1 : ℝ) * (-s0.re)))
          have hlogpos : 0 < Real.log (p.1 : ℝ) := Real.log_pos_iff.mpr hp_gt_one
          have : Real.exp ((-s0.re) * Real.log (p.1 : ℝ)) < Real.exp 0 :=
            Real.exp_lt_exp.mpr (mul_neg_of_neg_of_pos hneg hlogpos)
          simpa [hrw, Real.exp_zero]
        have hre_pos : 0 < (1 : ℝ) - ‖(p.1 : ℂ) ^ (-s0)‖ := by
          simpa [hlam_norm] using sub_pos.mpr this
        have h_re_le : ((1 : ℝ) - ‖(p.1 : ℂ) ^ (-s0)‖) ≤ (1 - (p.1 : ℂ) ^ (-s0)).re := by
          have : ((p.1 : ℂ) ^ (-s0)).re ≤ ‖(p.1 : ℂ) ^ (-s0)‖ := Complex.re_le_abs _
          have := sub_le_sub_left this 1
          simpa [sub_eq_add_neg] using this
        have : 0 < (1 - (p.1 : ℂ) ^ (-s0)).re := lt_of_le_of_lt h_re_le hre_pos
        simpa using this
      exact AnalyticAt.clog hsub h_slit
    have hsq : AnalyticAt ℂ (fun s => ((p.1 : ℂ) ^ (-s)) ^ 2) s0 := hlam.pow 2
    have hlincomb : AnalyticAt ℂ (fun s => (p.1 : ℂ) ^ (-s) + ((p.1 : ℂ) ^ (-s)) ^ 2 / 2) s0 := by
      have hhalf : AnalyticAt ℂ (fun _ => (1 / 2 : ℂ)) s0 := analyticAt_const
      have := hlam.add (hsq.mul hhalf)
      simpa [div_eq_mul_inv] using this
    simpa [a] using hlog.add hlincomb
  -- use equality on a neighborhood to transfer analyticity of exp(tsum)
  -- transfer analyticity to `det2_AF` via equality on a neighborhood
  have h_eq_exp' : AnalyticAt ℂ (fun s => Complex.exp (∑' (p : Prime), a p s)) s0 :=
    analyticAt_const.cexp
  have : AnalyticAt ℂ det2_AF s0 :=
    h_eq_exp'.congr_of_eventuallyEq (h_eq_exp.symm)
  -- conclude within the half-plane
  simpa using this.analyticWithinAt

/-- Nonvanishing of the 2‑modified determinant on the half‑plane Re(s) > 1/2. -/
theorem det2_AF_nonzero_on_halfPlaneReGtHalf :
  ∀ {s : ℂ}, s ∈ {s : ℂ | (1 / 2 : ℝ) < s.re} → det2_AF s ≠ 0 := by
  classical
  intro s hs
  -- Fix 1/2 < σ < Re(s)
  obtain ⟨σ, hσhalf, hσ⟩ : ∃ σ, (1/2 : ℝ) < σ ∧ σ < s.re := by
    refine ⟨(s.re + 1/2)/2, ?_, ?_⟩ <;> linarith
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
    simp [det2_AF, det2EulerFactor, a, eulerFactor_as_exp_log]
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
          rw [hlam, Real.rpow_neg, inv_eq_one_div]
          have : (1 / (2 : ℝ)) ^ (1 / 2 : ℝ) < 1 :=
            Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)
          have : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := by
            rw [Real.rpow_neg]; simpa [inv_eq_one_div] using this
          calc ‖lam‖
              = (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) := hlam
            _ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
                have : (2 : ℝ) ≤ p.1 := Nat.Prime.two_le p.property
                have : (1 / p.1) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) this
                have : (1 / p.1) ^ (1/2 : ℝ) ≤ (1/2) ^ (1/2 : ℝ) :=
                  Real.rpow_le_rpow (by positivity) this (by norm_num)
                rw [Real.rpow_neg, Real.rpow_neg, inv_eq_one_div, inv_eq_one_div] at this ⊢
                exact this
            _ < 1 := this
        exact cubic_tail_log_one_sub hlam_lt
      -- bound denominator by constant C and rewrite ‖lam‖^3 = p^{-3/2}
      have hden : (1 - ‖lam‖)⁻¹ ≤ C := by
        have : ‖lam‖ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
          -- since p ≥ 2 ⇒ p^{-1/2} ≤ 2^{-1/2}
          have h2le : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.property.two_le
          have : (1 / (p.1 : ℝ)) ≤ 1 / (2 : ℝ) :=
            one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h2le
          have : (1 / (p.1 : ℝ)) ^ (1 / 2 : ℝ) ≤ (1 / (2 : ℝ)) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (by exact le_of_lt (one_div_pos.mpr hp_pos)) this (by norm_num)
          rw [Real.rpow_neg, Real.rpow_neg, inv_eq_one_div, inv_eq_one_div] at this
          rw [hlam]
          exact this
        have : 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 - ‖lam‖ := by linarith
        have hpos : 0 < 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
          have : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := by
            have : (1 / (2 : ℝ)) ^ (1 / 2 : ℝ) < 1 :=
              Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)
            rw [Real.rpow_neg, inv_eq_one_div]
            exact this
          exact sub_pos.mpr this
        rw [one_div, C]
        exact one_div_le_one_div_of_le hpos this
      have hnonneg : 0 ≤ ‖lam‖ ^ 3 := by exact pow_nonneg (norm_nonneg _) 3
      have : ‖Complex.log (1 - lam) + lam + lam ^ 2 / 2‖ ≤ C * ‖lam‖ ^ 3 := by
        calc ‖Complex.log (1 - lam) + lam + lam ^ 2 / 2‖
            ≤ ‖lam‖ ^ 3 / (1 - ‖lam‖) := hcubic
          _ = ‖lam‖ ^ 3 * (1 - ‖lam‖)⁻¹ := by rw [div_eq_mul_inv]
          _ ≤ ‖lam‖ ^ 3 * C := by
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_right hden hnonneg
          _ = C * ‖lam‖ ^ 3 := mul_comm _ _
      -- rewrite ‖lam‖^3 as p^{-3/2}
      have : ‖lam‖ ^ 3 = (p.1 : ℝ) ^ (-(3 : ℝ) / 2) := by
        calc ‖lam‖ ^ 3
            = ((p.1 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 3 := by rw [hlam]
          _ = (p.1 : ℝ) ^ (-( 1 / 2) * 3) := by rw [← Real.rpow_natCast_mul]; norm_num
          _ = (p.1 : ℝ) ^ (-(3 / 2)) := by norm_num
      rw [a, lam, this]
      exact mul_le_mul_of_nonneg_left (le_refl _) (by norm_num : (0 : ℝ) ≤ C)
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
        have : Complex.abs lam = (p.1 : ℝ) ^ (-s.re) := by
          simpa [lam] using (Complex.abs_cpow_eq_rpow_re_of_pos hp_pos (-s))
        rw [this, s]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
          Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero]
        have : (p.1 : ℝ) ^ (-(1/2 : ℝ)) < 1 := by
          rw [Real.rpow_neg, inv_eq_one_div]
          have : 1 < (p.1 : ℝ) := by
            calc (1 : ℝ) < 2 := by norm_num
              _ ≤ p.1 := Nat.Prime.two_le p.property
          have : 0 < (p.1 : ℝ) ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hp_pos _
          exact one_div_lt_one_div_of_lt this
            (Real.one_lt_rpow_of_pos_of_lt_one_of_pos this (by linarith) (by norm_num))
        exact this
      simpa [det2EulerFactor, a, lam, eulerFactor_as_exp_log] using eulerFactor_as_exp_log lam hlam_lt
    simpa [det2_AF, hfactor]
  calc det2_AF s
      = ∏' (p : Prime), Complex.exp (a p) := hId
    _ = Complex.exp (∑' (p : Prime), a p) := hprod
    _ ≠ 0 := Complex.exp_ne_zero _

end RH.AcademicFramework.DiagonalFredholm
