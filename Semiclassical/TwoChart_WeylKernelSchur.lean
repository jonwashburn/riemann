import TwoChart_SchurTest

/-!
# From translation-invariant kernel decay to `SchurData`

This file continues the analytic pipeline:

1. We define a *two-regime* profile that is bounded at the origin but decays like `|x|^{-N}`
   at infinity. Because `ℝ` has no `∞`, we implement this profile using an `if x=0` branch.
2. We compare this profile to the Japanese-bracket profile `schurDecay` (which is smooth and
   globally integrable for `N>1`).
3. We package pointwise bounds by `schurDecay N ((t-t')/h)` into a `SchurData` record on
   Lebesgue measure (`volume`) via affine change of variables.

This is the missing bridge needed to turn kernel bounds into an `L²` Schur estimate.
-/

namespace TwoChartEgorov

open scoped Real BigOperators
open MeasureTheory

noncomputable section

/-! ## A two-regime profile and comparison to `schurDecay` -/

/-- Two-regime profile: `1` at `0` and `min(1, |x|^{-N})` elsewhere. -/
def schurProfile (N : ℕ) (x : ℝ) : ℝ :=
  if x = 0 then 1 else min 1 ((|x|)⁻¹ ^ N)

lemma schurProfile_nonneg (N : ℕ) (x : ℝ) : 0 ≤ schurProfile N x := by
  by_cases hx : x = 0
  · simp [schurProfile, hx]
  · simp [schurProfile, hx]

/-- A basic comparison: `schurProfile` is controlled by `schurDecay` up to `(√2)^N`. -/
lemma schurProfile_le_sqrtTwoPow_mul_schurDecay (N : ℕ) (x : ℝ) :
    schurProfile N x ≤ (Real.sqrt 2) ^ N * schurDecay N x := by
  classical
  by_cases hx0 : x = 0
  · -- At 0: `schurProfile = 1` and `schurDecay = 1`.
    simp [schurProfile, hx0, schurDecay]
  · -- Away from 0 we split into `|x| ≤ 1` and `1 ≤ |x|`.
    have hxabs_pos : 0 < |x| := abs_pos.2 hx0
    by_cases hx : |x| ≤ 1
    · -- `|x| ≤ 1` -> profile is 1
      have hmin : schurProfile N x = 1 := by
        have : 1 ≤ (|x|)⁻¹ ^ N := by
          have hx1 : (1:ℝ) ≤ (|x|)⁻¹ := by
            have : (|x|)⁻¹ ≥ (1:ℝ)⁻¹ := inv_le_inv_of_le (by linarith) hx
            simpa using this
          exact one_le_pow_of_one_le hx1 N
        simp [schurProfile, hx0, this, min_eq_left]
      -- `⟨x⟩ ≤ √2` since `x^2 ≤ 1`
      have hbr : japaneseBracket x ≤ Real.sqrt 2 := by
        have hx2 : x^2 ≤ (1:ℝ) := by
          have : |x|^2 ≤ (1:ℝ)^2 := sq_le_sq.mpr hx
          simpa [pow_two] using this
        have : 1 + x^2 ≤ (2:ℝ) := by linarith
        simpa [japaneseBracket] using Real.sqrt_le_sqrt this
      have hpow : (japaneseBracket x) ^ N ≤ (Real.sqrt 2) ^ N :=
        pow_le_pow_of_le_left (japaneseBracket_nonneg x) hbr N
      have hsqrt2pos : 0 < (Real.sqrt 2) ^ N := by
        have : 0 < Real.sqrt 2 := by
          have : (0:ℝ) < 2 := by linarith
          simpa using Real.sqrt_pos.2 this
        simpa using pow_pos this N
      have hdec : schurDecay N x ≥ 1 / (Real.sqrt 2) ^ N := by
        have : 1 / (Real.sqrt 2) ^ N ≤ 1 / (japaneseBracket x) ^ N :=
          one_div_le_one_div_of_le (le_of_lt hsqrt2pos) hpow
        simpa [schurDecay] using this
      have : (Real.sqrt 2) ^ N * schurDecay N x ≥ 1 := by
        have h : (Real.sqrt 2) ^ N * schurDecay N x
              ≥ (Real.sqrt 2) ^ N * (1 / (Real.sqrt 2) ^ N) := by
          gcongr
        have hs : (Real.sqrt 2) ^ N * (1 / (Real.sqrt 2) ^ N) = 1 := by
          field_simp [hsqrt2pos.ne']
        linarith [h, hs]
      -- finish
      simpa [hmin] using (le_of_lt (lt_of_lt_of_le (by linarith) this))
    · -- `|x| ≥ 1`: profile is `|x|^{-N}` and `⟨x⟩ ≤ √2|x|`
      have hx' : 1 ≤ |x| := le_of_not_ge hx
      have hmin : schurProfile N x = (|x|)⁻¹ ^ N := by
        have hle : (|x|)⁻¹ ^ N ≤ 1 := by
          have hxinv : (|x|)⁻¹ ≤ (1:ℝ) := by
            have : (|x|)⁻¹ ≤ (1:ℝ)⁻¹ := inv_le_inv_of_le (by linarith) hx'
            simpa using this
          exact pow_le_one _ (inv_nonneg.2 (abs_nonneg x)) hxinv
        simp [schurProfile, hx0, hle, min_eq_right]
      have hx2 : (1:ℝ) ≤ x^2 := by
        have : (1:ℝ) ≤ |x| := hx'
        have : (1:ℝ)^2 ≤ |x|^2 := sq_le_sq.mpr this
        simpa [pow_two] using this
      have hbr : japaneseBracket x ≤ Real.sqrt 2 * |x| := by
        have : 1 + x^2 ≤ 2 * x^2 := by linarith
        have hs : Real.sqrt (1 + x^2) ≤ Real.sqrt (2 * x^2) := by
          simpa using Real.sqrt_le_sqrt this
        -- `sqrt(2*x^2) = sqrt2 * |x|`
        have hsqrt : Real.sqrt (2 * x^2) = Real.sqrt 2 * |x| := by
          -- `sqrt(2*x^2) = sqrt2 * sqrt(x^2) = sqrt2 * |x|`
          have : Real.sqrt (2 * x^2) = Real.sqrt 2 * Real.sqrt (x^2) := by
            simpa [mul_assoc] using
              (Real.sqrt_mul (show 0 ≤ (2:ℝ) by linarith) (show 0 ≤ x^2 by nlinarith))
          simpa [this, Real.sqrt_sq_eq_abs] 
        simpa [japaneseBracket, hsqrt] using hs
      -- from `⟨x⟩ ≤ √2|x|`, derive `|x|^{-1} ≤ √2/⟨x⟩`
      have hfrac : (|x|)⁻¹ ≤ Real.sqrt 2 / japaneseBracket x := by
        have hxpos : 0 < |x| := lt_of_lt_of_le (by linarith) hx'
        -- divide `⟨x⟩ ≤ √2|x|` by `|x|*⟨x⟩`
        have : japaneseBracket x / |x| ≤ Real.sqrt 2 := by
          have : japaneseBracket x / |x| ≤ (Real.sqrt 2 * |x|) / |x| := by
            exact div_le_div_of_le_right (le_of_lt hxpos) hbr
          simpa [div_mul_eq_mul_div, mul_assoc] using this
        -- rewrite
        simpa [div_eq_mul_inv, inv_mul_eq_div, mul_assoc] using this
      have : (|x|)⁻¹ ^ N ≤ (Real.sqrt 2 / japaneseBracket x) ^ N :=
        pow_le_pow_of_le_left (inv_nonneg.2 (abs_nonneg x)) hfrac N
      -- rewrite RHS as `(√2)^N * schurDecay`
      have : (|x|)⁻¹ ^ N ≤ (Real.sqrt 2) ^ N * schurDecay N x := by
        simpa [schurDecay, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
      simpa [hmin] using this

/-! ## Schur-data constructor from a `schurDecay` majorant -/

section SchurFromDecay

/-- If `‖K(t,t')‖ ≤ C * schurDecay N ((t-t')/h)` and `schurDecay` is integrable, then `K`
satisfies `SchurData` (on Lebesgue measure). -/
theorem schurData_of_bound_schurDecay
    (N : ℕ) {h : ℝ} (h_ne : h ≠ 0) {C : ℝ}
    (hC : 0 ≤ C)
    {K : ℝ → ℝ → ℂ}
    (hK : ∀ t t', ‖K t t'‖ ≤ C * schurDecay N ((t - t') / h))
    (hInt : Integrable (schurDecay N) (volume : Measure ℝ)) :
    SchurData (volume : Measure ℝ) K := by
  classical
  let I : ℝ := ∫ x : ℝ, schurDecay N x ∂(volume : Measure ℝ)
  refine
    { A := C * |h| * I
      B := C * |h| * I
      A_nonneg := by
        have : 0 ≤ I := by
          refine integral_nonneg ?_
          intro x
          exact schurDecay_nonneg (h_ne := h_ne) N x
        nlinarith [hC, abs_nonneg h, this]
      B_nonneg := by
        have : 0 ≤ I := by
          refine integral_nonneg ?_
          intro x
          exact schurDecay_nonneg (h_ne := h_ne) N x
        nlinarith [hC, abs_nonneg h, this]
      row_integrable := ?_
      col_integrable := ?_
      row_bound := ?_
      col_bound := ?_ }
  · intro t
    have hMaj :
        (fun t' => ‖K t t'‖) ≤ fun t' => C * schurDecay N ((t - t') / h) := by
      intro t'
      exact hK t t'
    have hInt' :
        Integrable (fun t' => C * schurDecay N ((t - t') / h)) (volume : Measure ℝ) := by
      simpa [sub_eq_add_neg, div_eq_mul_inv, mul_assoc, add_assoc, add_left_comm, add_comm]
        using (hInt.comp_mul_add (a := (-1/h)) (b := (t/h)))
    exact hInt'.mono' (by
      refine (ae_of_all _)
      intro t'
      exact hMaj t')
  · intro t'
    have hMaj :
        (fun t => ‖K t t'‖) ≤ fun t => C * schurDecay N ((t - t') / h) := by
      intro t
      exact hK t t'
    have hInt' :
        Integrable (fun t => C * schurDecay N ((t - t') / h)) (volume : Measure ℝ) := by
      simpa [sub_eq_add_neg, div_eq_mul_inv, mul_assoc, add_assoc, add_left_comm, add_comm]
        using (hInt.comp_mul_add (a := (1/h)) (b := (-t'/h)))
    exact hInt'.mono' (by
      refine (ae_of_all _)
      intro t
      exact hMaj t)
  · intro t
    have hAE :
        (fun t' => ‖K t t'‖)
          ≤ᵐ[(volume : Measure ℝ)] (fun t' => C * schurDecay N ((t - t') / h)) := by
      refine (ae_of_all _)
      intro t'
      exact hK t t'
    have h1 :
        (∫ t' : ℝ, ‖K t t'‖ ∂(volume : Measure ℝ))
          ≤ ∫ t' : ℝ, C * schurDecay N ((t - t') / h) ∂(volume : Measure ℝ) :=
      integral_le_integral_of_ae_le hAE
    have hRHS :
        (∫ t' : ℝ, C * schurDecay N ((t - t') / h) ∂(volume : Measure ℝ))
          = C * |h| * I := by
      have hchg :
          (∫ t' : ℝ, schurDecay N ((t - t') / h) ∂(volume : Measure ℝ)) = |h| * I := by
        simpa [I, sub_eq_add_neg, div_eq_mul_inv, mul_add, add_mul, add_assoc, add_left_comm, add_comm]
          using (integral_comp_mul_add (μ := (volume : Measure ℝ))
            (f := fun x => schurDecay N x) (a := (-1/h)) (b := (t/h))
            (by
              have : (-1/h) ≠ 0 := by
                field_simp [h_ne]
              exact this))
      simpa [I, hchg, mul_assoc] using
        (integral_mul_left C (fun t' => schurDecay N ((t - t') / h)))
    linarith [h1, hRHS]
  · intro t'
    have hAE :
        (fun t => ‖K t t'‖)
          ≤ᵐ[(volume : Measure ℝ)] (fun t => C * schurDecay N ((t - t') / h)) := by
      refine (ae_of_all _)
      intro t
      exact hK t t'
    have h1 :
        (∫ t : ℝ, ‖K t t'‖ ∂(volume : Measure ℝ))
          ≤ ∫ t : ℝ, C * schurDecay N ((t - t') / h) ∂(volume : Measure ℝ) :=
      integral_le_integral_of_ae_le hAE
    have hRHS :
        (∫ t : ℝ, C * schurDecay N ((t - t') / h) ∂(volume : Measure ℝ))
          = C * |h| * I := by
      have hchg :
          (∫ t : ℝ, schurDecay N ((t - t') / h) ∂(volume : Measure ℝ)) = |h| * I := by
        simpa [I, sub_eq_add_neg, div_eq_mul_inv, mul_add, add_mul, add_assoc, add_left_comm, add_comm]
          using (integral_comp_mul_add (μ := (volume : Measure ℝ))
            (f := fun x => schurDecay N x) (a := (1/h)) (b := (-t'/h))
            (by
              have : (1/h) ≠ 0 := by
                field_simp [h_ne]
              exact this))
      simpa [I, hchg, mul_assoc] using
        (integral_mul_left C (fun t => schurDecay N ((t - t') / h)))
    linarith [h1, hRHS]

end SchurFromDecay

end TwoChartEgorov
