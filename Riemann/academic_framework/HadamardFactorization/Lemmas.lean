import Riemann.academic_framework.HadamardFactorization.Lindelof

noncomputable section

namespace ComplexAnalysis
namespace Hadamard

open Complex Real BigOperators Finset Set Filter Topology Metric
open scoped Topology


/-- A zero-free entire function with polynomial growth is exp of a polynomial.

If H is entire, zero-free, and `|H(z)| ≤ exp(C * (1 + |z|)^n)` for some `C` and `n`,
then H = exp(P) for some polynomial P of degree at most n. -/
theorem zero_free_polynomial_growth_is_exp_poly {H : ℂ → ℂ} {n : ℕ}
    (hH : Differentiable ℂ H)
    (h_nonzero : ∀ z, H z ≠ 0)
    (h_bound : ∃ C > 0, ∀ z, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ n)) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ n ∧ ∀ z, H z = exp (Polynomial.eval z P) := by
  classical
  rcases h_bound with ⟨C, hCpos, hC⟩

  -- Step 1: build a global holomorphic logarithm by integrating the logarithmic derivative.
  let L : ℂ → ℂ := fun z => deriv H z / H z
  have hderivH : Differentiable ℂ (deriv H) := by
    intro z
    exact ((hH.analyticAt z).deriv).differentiableAt
  have hL : Differentiable ℂ L := by
    simpa [L] using (hderivH.div hH h_nonzero)

  -- A global primitive of `L`, defined by wedge integrals from `0`.
  let h : ℂ → ℂ := fun z => Complex.wedgeIntegral (0 : ℂ) z L
  have hh_deriv : ∀ z, HasDerivAt h (L z) z := by
    intro z
    -- Apply Morera's theorem on the ball `ball 0 (‖z‖ + 1)`.
    let r : ℝ := ‖z‖ + 1
    have hrpos : 0 < r := by
      dsimp [r]
      linarith [norm_nonneg z]
    have hz_ball : z ∈ Metric.ball (0 : ℂ) r := by
      have : dist z (0 : ℂ) < r := by
        simp [r, dist_zero_right]
      simpa [Metric.mem_ball] using this
    have hconserv : Complex.IsConservativeOn L (Metric.ball (0 : ℂ) r) :=
      (hL.differentiableOn).isConservativeOn
    have hcont : ContinuousOn L (Metric.ball (0 : ℂ) r) :=
      hL.continuous.continuousOn
    simpa [h, r] using hconserv.hasDerivAt_wedgeIntegral (f_cont := hcont) (hz := hz_ball)
  have hh : Differentiable ℂ h := fun z => (hh_deriv z).differentiableAt
  have hderiv_h : ∀ z, deriv h z = L z := fun z => (hh_deriv z).deriv

  -- Step 2: show `H = exp(k)` for an entire `k`.
  let k : ℂ → ℂ := fun z => h z + Complex.log (H 0)
  have hk : Differentiable ℂ k := hh.add_const (Complex.log (H 0))

  have hk_exp : ∀ z, H z = Complex.exp (k z) := by
    -- Consider `F = exp(k) / H`. Its derivative is zero, hence it's constant.
    let F : ℂ → ℂ := fun z => Complex.exp (k z) / H z
    have hF_deriv : ∀ z, deriv F z = 0 := by
      intro z
      have hH_has : HasDerivAt H (deriv H z) z := (hH z).hasDerivAt
      have hk_has : HasDerivAt k (L z) z := by
        -- `k' = h'` since the constant term has derivative 0
        have hh_has : HasDerivAt h (L z) z := hh_deriv z
        simpa [k, L] using hh_has.add_const (Complex.log (H 0))
      have hExp : HasDerivAt (fun w => Complex.exp (k w)) (Complex.exp (k z) * L z) z :=
        (HasDerivAt.cexp hk_has)
      have hDiv := (HasDerivAt.div hExp hH_has (h_nonzero z))
      -- simplify the quotient-rule formula using `L z = H'(z)/H(z)`
      have :
          deriv F z =
            ((Complex.exp (k z) * L z) * H z - Complex.exp (k z) * deriv H z) / (H z) ^ 2 := by
        simpa [F] using hDiv.deriv
      rw [this]
      -- `((exp(k) * (H'/H)) * H - exp(k) * H') / H^2 = 0`
      have hnum :
          (Complex.exp (k z) * L z) * H z - Complex.exp (k z) * deriv H z = 0 := by
        -- cancel `H z` inside `L z = H'/H`
        dsimp [L]
        field_simp [h_nonzero z]
        ring
      simp [hnum]
    have hF_diff : Differentiable ℂ F := by
      -- `F = exp(k) / H`
      exact (hk.cexp).div hH h_nonzero
    have hF_const : ∀ z, F z = F 0 := by
      intro z
      exact is_const_of_deriv_eq_zero hF_diff hF_deriv z 0
    have hF0 : F 0 = 1 := by
      -- `h 0 = 0`, so `k 0 = log(H 0)` and `exp(k 0) / H 0 = 1`.
      have hh0 : h 0 = 0 := by simp [h, Complex.wedgeIntegral]
      have hk0 : k 0 = Complex.log (H 0) := by simp [k, hh0]
      have hH0 : H 0 ≠ 0 := h_nonzero 0
      simp [F, hk0, Complex.exp_log hH0, hH0]
    intro z
    have : F z = 1 := by simpa [hF0] using (hF_const z)
    -- rearrange `F z = exp(k z)/H z = 1`
    have hHz : H z ≠ 0 := h_nonzero z
    have : Complex.exp (k z) / H z = 1 := by simpa [F] using this
    -- multiply through by `H z`
    have : Complex.exp (k z) = H z := by
      -- `a / b = 1` implies `a = b`
      field_simp [hHz] at this
      simpa using this
    exact this.symm

  -- Step 3: show all derivatives of `k` above order `n` vanish, hence `k` is a polynomial.
  have hk_re_bound : ∀ z, (k z).re ≤ C * (1 + ‖z‖) ^ n := by
    intro z
    -- From `H z = exp(k z)` and the growth bound on `H`.
    have hHz : H z ≠ 0 := h_nonzero z
    have hpos : 0 < ‖H z‖ := norm_pos_iff.mpr hHz
    have hlog_le : Real.log ‖H z‖ ≤ C * (1 + ‖z‖) ^ n := by
      have := Real.log_le_log hpos (hC z)
      simpa [Real.log_exp] using this
    have hlog_eq : Real.log ‖H z‖ = (k z).re := by
      have : ‖H z‖ = Real.exp (k z).re := by
        simpa [hk_exp z] using (Complex.norm_exp (k z))
      calc
        Real.log ‖H z‖ = Real.log (Real.exp (k z).re) := by simp [this]
        _ = (k z).re := by simp
    -- conclude
    simpa [hlog_eq] using hlog_le

  have hk_iteratedDeriv_eq_zero : ∀ m : ℕ, n < m → iteratedDeriv m k 0 = 0 := by
    intro m hm
    -- Use Cauchy estimate on `k - k 0` with radii `R` and `r = R/2`, then send `R → ∞`.
    have hm' : 0 < (m - n : ℕ) := Nat.sub_pos_of_lt hm
    have hmne : m - n ≠ 0 := (Nat.pos_iff_ne_zero.1 hm')
    -- Work with `f = k - k 0`, which vanishes at `0`.
    let f : ℂ → ℂ := fun z => k z - k 0
    have hf : Differentiable ℂ f := hk.sub_const (k 0)
    have hf0 : f 0 = 0 := by simp [f]
    -- First bound: `Re(f z) ≤ C * (1+R)^n + ‖k 0‖` on `‖z‖ ≤ R`.
    have hf_re_bound : ∀ R : ℝ, 0 < R →
        ∀ z, ‖z‖ ≤ R → (f z).re ≤ C * (1 + R) ^ n + ‖k 0‖ := by
      intro R hRpos z hzR
      have hkz : (k z).re ≤ C * (1 + ‖z‖) ^ n := hk_re_bound z
      have hkz' : (k z).re ≤ C * (1 + R) ^ n := by
        have h1 : (1 + ‖z‖ : ℝ) ≤ 1 + R := by linarith
        have hpow : (1 + ‖z‖ : ℝ) ^ n ≤ (1 + R) ^ n :=
          pow_le_pow_left₀ (by linarith [norm_nonneg z]) h1 n
        exact hkz.trans (mul_le_mul_of_nonneg_left hpow (le_of_lt hCpos))
      -- `Re(f z) = Re(k z) - Re(k 0) ≤ C (1+R)^n + ‖k 0‖`.
      have hRe0 : -(k 0).re ≤ ‖k 0‖ := by
        have habs : |(k 0).re| ≤ ‖k 0‖ := Complex.abs_re_le_norm (k 0)
        have hneg : -(k 0).re ≤ |(k 0).re| := by
          simpa using (neg_le_abs (k 0).re)
        exact hneg.trans habs
      -- assemble
      have : (f z).re ≤ C * (1 + R) ^ n + ‖k 0‖ := by
        -- `Re(f z) = Re(k z) - Re(k 0)`
        have : (f z).re = (k z).re - (k 0).re := by simp [f, sub_eq_add_neg]
        -- use `hkz'` and `hRe0`
        nlinarith [this, hkz', hRe0]
      exact this

    -- Apply Borel–Carathéodory to get a norm bound for `f` on `‖z‖ ≤ R/2`.
    have hf_bound_on_ball : ∀ R : ℝ, 0 < R →
        ∀ z, ‖z‖ ≤ R / 2 → ‖f z‖ ≤ 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
      intro R hRpos z hz
      have hR2pos : 0 < R / 2 := by nlinarith
      have hlt : R / 2 < R := by nlinarith
      have hMpos : 0 < (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        have : 0 ≤ C * (1 + R) ^ n := by
          refine mul_nonneg (le_of_lt hCpos) ?_
          exact pow_nonneg (by linarith) _
        nlinarith [this, norm_nonneg (k 0)]
      have hf_anal : AnalyticOnNhd ℂ f (Metric.closedBall 0 R) := by
        intro w hw
        exact (hf.analyticAt w)
      have hf_re : ∀ w, ‖w‖ ≤ R → (f w).re ≤ (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        intro w hw
        have := hf_re_bound R hRpos w hw
        linarith
      have hf_bc :=
        borel_caratheodory_bound (f := f) (r := R / 2) (R := R)
          (M := (C * (1 + R) ^ n + ‖k 0‖ + 1))
          hf_anal hR2pos hlt hMpos hf0 hf_re z hz
      -- simplify the constant `2*M*r/(R-r)` at `r=R/2`
      have hconst :
          2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) * (R / 2) / (R - R / 2)
            = 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        field_simp [hRpos.ne'] ; ring
      -- finish
      simpa [hconst] using hf_bc

    -- Use Cauchy estimate for iterated derivatives of `f` on the circle of radius `R/2`.
    have hCauchy : ∀ R : ℝ, 0 < R →
        ‖iteratedDeriv m f 0‖ ≤
          (m.factorial : ℝ) * (2 * (C * (1 + R) ^ n + ‖k 0‖ + 1)) / (R / 2) ^ m := by
      intro R hRpos
      have hR2pos : 0 < R / 2 := by nlinarith
      have hf_diffCont : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) (R / 2)) := hf.diffContOnCl
      have hbound_sphere :
          ∀ z ∈ Metric.sphere (0 : ℂ) (R / 2),
            ‖f z‖ ≤ 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        intro z hz
        have hz' : ‖z‖ ≤ R / 2 := by
          simpa [Metric.mem_sphere, dist_zero_right] using (le_of_eq hz)
        exact hf_bound_on_ball R hRpos z hz'
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (n := m) (c := (0 : ℂ))
          (R := R / 2) (C := 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1))
          (hR := hR2pos) hf_diffCont hbound_sphere)

    -- Let `R → ∞`: the Cauchy bound tends to `0` for `m > n`, forcing `iteratedDeriv m f 0 = 0`.
    have hf_iter_eq : iteratedDeriv m f 0 = 0 := by
      by_contra hne
      have ha : 0 < ‖iteratedDeriv m f 0‖ := norm_pos_iff.2 hne

      let RHS : ℝ → ℝ := fun R =>
        (m.factorial : ℝ) * (2 * (C * (1 + R) ^ n + ‖k 0‖ + 1)) / (R / 2) ^ m
      have hle_RHS : ∀ R : ℝ, 0 < R → ‖iteratedDeriv m f 0‖ ≤ RHS R := by
        intro R hRpos
        simpa [RHS] using hCauchy R hRpos

      -- Show `RHS R → 0` as `R → ∞`.
      have hRHS_tendsto : Tendsto RHS atTop (𝓝 0) := by
        -- First show `(C * (1+R)^n + K) / (R/2)^m → 0` for `K = ‖k 0‖ + 1`.
        let K : ℝ := ‖k 0‖ + 1
        have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hm
        have hm0 : m ≠ 0 := ne_of_gt hmpos

        have hratio : Tendsto (fun R : ℝ => R ^ n / (R / 2) ^ m) atTop (𝓝 0) := by
          -- Rewrite `R^n/(R/2)^m = 2^m * (R^n / R^m)` and use `m > n`.
          have hident :
              (fun R : ℝ => R ^ n / (R / 2) ^ m) = fun R : ℝ => (2 : ℝ) ^ m * (R ^ n / R ^ m) := by
            funext R
            simp [div_eq_mul_inv, mul_pow, mul_assoc, mul_comm]
          have hmain : Tendsto (fun R : ℝ => R ^ n / R ^ m) atTop (𝓝 0) := by
            have hp : m - n ≠ 0 := (Nat.pos_iff_ne_zero.1 (Nat.sub_pos_of_lt hm))
            have hmain' : Tendsto (fun R : ℝ => (R ^ (m - n))⁻¹) atTop (𝓝 0) := by
              simpa using (tendsto_pow_neg_atTop (𝕜 := ℝ) (n := m - n) hp)
            have hEq : (fun R : ℝ => (R ^ (m - n))⁻¹) =ᶠ[atTop] fun R : ℝ => R ^ n / R ^ m := by
              have hEq' : (fun R : ℝ => R ^ n / R ^ m) =ᶠ[atTop] fun R : ℝ => (R ^ (m - n))⁻¹ := by
                filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
                have hle : n ≤ m := le_of_lt hm
                have hm_eq : n + (m - n) = m := Nat.add_sub_of_le hle
                have hn0 : R ^ n ≠ 0 := pow_ne_zero n hR
                calc
                  R ^ n / R ^ m = R ^ n / R ^ (n + (m - n)) := by simp [hm_eq]
                  _ = R ^ n * ((R ^ (m - n))⁻¹ * (R ^ n)⁻¹) := by
                        simp [pow_add, div_eq_mul_inv, mul_comm]
                  _ = (R ^ (m - n))⁻¹ := by
                        ring_nf
                        simp [hn0]
              exact hEq'.symm
            exact Filter.Tendsto.congr' hEq hmain'
          have : Tendsto (fun R : ℝ => (2 : ℝ) ^ m * (R ^ n / R ^ m)) atTop (𝓝 ((2 : ℝ) ^ m * 0)) :=
            tendsto_const_nhds.mul hmain
          simpa [hident] using this

        have hinv : Tendsto (fun R : ℝ => ((R / 2) ^ m)⁻¹) atTop (𝓝 0) := by
          have hdiv : Tendsto (fun R : ℝ => R / 2) atTop atTop :=
            (tendsto_id.atTop_div_const (r := (2 : ℝ)) (by norm_num : (0 : ℝ) < 2))
          have hpow : Tendsto (fun R : ℝ => (R / 2) ^ m) atTop atTop :=
            (Filter.tendsto_pow_atTop (α := ℝ) (n := m) hm0).comp hdiv
          simpa using hpow.inv_tendsto_atTop

        -- Upgrade `R^n/(R/2)^m → 0` to `(1+R)^n/(R/2)^m → 0` using the factor `((1+R)/R)^n → 1`.
        have hdiv : Tendsto (fun R : ℝ => (1 + R) / R) atTop (𝓝 (1 : ℝ)) := by
          have hinv : Tendsto (fun R : ℝ => (R : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
            tendsto_inv_atTop_zero
          have hadd : Tendsto (fun R : ℝ => (1 : ℝ) + (R : ℝ)⁻¹) atTop (𝓝 (1 : ℝ)) := by
            simpa using (tendsto_const_nhds.add hinv)
          have hEq : (fun R : ℝ => (1 + R) / R) =ᶠ[atTop] fun R : ℝ => (1 : ℝ) + (R : ℝ)⁻¹ := by
            filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
            -- `((1+R)/R) = 1 + 1/R` for `R ≠ 0`.
            field_simp [hR]
            ring
          exact Filter.Tendsto.congr' hEq.symm hadd
        have hdiv_pow : Tendsto (fun R : ℝ => ((1 + R) / R) ^ n) atTop (𝓝 (1 : ℝ)) := by
          simpa using (hdiv.pow n)
        have hone_add_ratio :
            Tendsto (fun R : ℝ => (1 + R) ^ n / (R / 2) ^ m) atTop (𝓝 (0 : ℝ)) := by
          have hEq :
              (fun R : ℝ => (1 + R) ^ n / (R / 2) ^ m)
                =ᶠ[atTop] fun R : ℝ => ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m) := by
            filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
            -- algebraic identity valid for `R ≠ 0`
            have hRpow : (R ^ n : ℝ) ≠ 0 := pow_ne_zero n hR
            -- `((1+R)/R)^n * (R^n/(R/2)^m) = (1+R)^n/(R/2)^m`
            have hident :
                ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m) = (1 + R) ^ n / (R / 2) ^ m := by
              calc
                ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m)
                    = ((1 + R) ^ n / R ^ n) * (R ^ n / (R / 2) ^ m) := by
                        simp [div_pow]
                _ = ((1 + R) ^ n * R ^ n) / (R ^ n * (R / 2) ^ m) := by
                        simp [div_mul_div_comm, mul_comm]
                _ = ((1 + R) ^ n * R ^ n) / ((R / 2) ^ m * R ^ n) := by
                        simp [mul_comm]
                _ = (1 + R) ^ n / (R / 2) ^ m := by
                        simpa [mul_assoc, mul_comm, mul_left_comm] using
                          (mul_div_mul_right (a := (1 + R) ^ n) (b := (R / 2) ^ m) hRpow)
            exact hident.symm
          have hmul :
              Tendsto (fun R : ℝ => ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m)) atTop (𝓝 (0 : ℝ)) := by
            simpa [mul_zero] using (hdiv_pow.mul hratio)
          exact Filter.Tendsto.congr' hEq.symm hmul

        have h1 : Tendsto (fun R : ℝ => C * ((1 + R) ^ n / (R / 2) ^ m)) atTop (𝓝 0) := by
          simpa using (tendsto_const_nhds.mul hone_add_ratio)
        have h2 : Tendsto (fun R : ℝ => K * ((R / 2) ^ m)⁻¹) atTop (𝓝 0) := by
          simpa using (tendsto_const_nhds.mul hinv)
        have hsum :
            Tendsto (fun R : ℝ => C * ((1 + R) ^ n / (R / 2) ^ m) + K * ((R / 2) ^ m)⁻¹) atTop (𝓝 0) := by
          simpa using (h1.add h2)
        have hrew :
            (fun R : ℝ => (C * (1 + R) ^ n + K) / (R / 2) ^ m)
              = fun R : ℝ => C * ((1 + R) ^ n / (R / 2) ^ m) + K * ((R / 2) ^ m)⁻¹ := by
          funext R
          simp [div_eq_mul_inv, mul_add, mul_assoc, mul_comm]
        have hbase : Tendsto (fun R : ℝ => (C * (1 + R) ^ n + K) / (R / 2) ^ m) atTop (𝓝 0) := by
          simpa [hrew] using hsum

        -- Multiply by the constant `(m!)*2` and rewrite to `RHS`.
        have hconst :
            Tendsto (fun _ : ℝ => (m.factorial : ℝ) * (2 : ℝ)) atTop (𝓝 ((m.factorial : ℝ) * (2 : ℝ))) :=
          tendsto_const_nhds
        have hmul : Tendsto (fun R : ℝ => ((m.factorial : ℝ) * (2 : ℝ)) *
              ((C * (1 + R) ^ n + K) / (R / 2) ^ m)) atTop (𝓝 0) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using (hconst.mul hbase)
        have hRHS_rw : RHS = fun R : ℝ => ((m.factorial : ℝ) * (2 : ℝ)) *
              ((C * (1 + R) ^ n + K) / (R / 2) ^ m) := by
          funext R
          dsimp [RHS, K]
          ring_nf
        simpa [hRHS_rw] using hmul

      -- `RHS R → 0`, so eventually `RHS R < ‖iteratedDeriv m f 0‖ / 2`.
      have hsmall : ∀ᶠ R in atTop, RHS R < ‖iteratedDeriv m f 0‖ / 2 :=
        (tendsto_order.1 hRHS_tendsto).2 _ (half_pos ha)
      have hle_eventually : ∀ᶠ R in atTop, ‖iteratedDeriv m f 0‖ ≤ RHS R := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hRpos
        exact hle_RHS R hRpos
      rcases (hle_eventually.and hsmall).exists with ⟨R, hle, hlt⟩
      have : ‖iteratedDeriv m f 0‖ < ‖iteratedDeriv m f 0‖ := by
        exact (lt_of_le_of_lt hle hlt).trans (half_lt_self ha)
      exact lt_irrefl _ this

    -- Transfer back from `f = k - k 0` to `k` (derivatives of constants vanish for `m > 0`).
    have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hm
    have hm0 : m ≠ 0 := ne_of_gt hmpos
    have hkcd : ContDiffAt ℂ (↑m) k (0 : ℂ) := (hk.analyticAt 0).contDiffAt
    have hccd : ContDiffAt ℂ (↑m) (fun _ : ℂ => k 0) (0 : ℂ) := contDiffAt_const
    have hsub : iteratedDeriv m f 0 = iteratedDeriv m k 0 - iteratedDeriv m (fun _ : ℂ => k 0) 0 := by
      simpa [f] using (iteratedDeriv_sub (n := m) (x := (0 : ℂ)) hkcd hccd)
    have hconst0 : iteratedDeriv m (fun _ : ℂ => k 0) 0 = 0 := by
      simp [iteratedDeriv_const, hm0]
    have hf_eq : iteratedDeriv m f 0 = iteratedDeriv m k 0 := by
      simp [hsub, hconst0]
    simpa [hf_eq] using hf_iter_eq

  -- Step 4: build the polynomial from the Taylor coefficients at 0 and finish.
  let P : Polynomial ℂ :=
    ∑ m ∈ Finset.range (n + 1), Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)
  have hPdeg : P.natDegree ≤ n := by
    -- A finset sum of monomials indexed by `range (n+1)` has `natDegree ≤ n`.
    have hnat :
        P.natDegree ≤
          Finset.fold max 0
            (fun m : ℕ =>
              (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree)
            (Finset.range (n + 1)) := by
      simpa [P, Function.comp] using
        (Polynomial.natDegree_sum_le (s := Finset.range (n + 1))
          (f := fun m : ℕ =>
            Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)))
    have hfold :
        Finset.fold max 0
            (fun m : ℕ =>
              (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree)
            (Finset.range (n + 1)) ≤ n := by
      -- `fold max` is bounded by `n` since each monomial has `natDegree ≤ m ≤ n` on this range.
      refine (Finset.fold_max_le (f := fun m : ℕ =>
        (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree)
        (b := 0) (s := Finset.range (n + 1)) (c := n)).2 ?_
      refine ⟨Nat.zero_le n, ?_⟩
      intro m hm
      have hmon :
          (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree ≤ m :=
        Polynomial.natDegree_monomial_le _
      have hm_le : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.1 hm)
      exact hmon.trans hm_le
    exact hnat.trans hfold
  have hk_poly : ∀ z, k z = Polynomial.eval z P := by
    intro z
    -- Taylor series of an entire function, then truncate using vanishing of higher derivatives.
    have htaylor := Complex.taylorSeries_eq_of_entire' (c := (0 : ℂ)) (z := z) hk
    have htail : ∀ m : ℕ, m ∉ Finset.range (n + 1) →
        ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * (z - 0) ^ m) = 0 := by
      intro m hm'
      have hmgt : n < m := by
        have : n + 1 ≤ m := Nat.le_of_not_lt (by simpa [Finset.mem_range] using hm')
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n) this
      have hz : iteratedDeriv m k 0 = 0 := hk_iteratedDeriv_eq_zero m hmgt
      simp [hz]
    have htsum :
        (∑' m : ℕ, (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * (z - 0) ^ m)
          = ∑ m ∈ Finset.range (n + 1), (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * z ^ m := by
      simpa [sub_zero] using (tsum_eq_sum (s := Finset.range (n + 1)) htail)
    have hfinite :
        k z = ∑ m ∈ Finset.range (n + 1), (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * z ^ m := by
      calc
        k z = ∑' m : ℕ, (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * (z - 0) ^ m := by
          simpa using htaylor.symm
        _ = _ := htsum
    -- Evaluate the polynomial `P` and match the finite sum (commuting factors as needed).
    have hEval :
        Polynomial.eval z P =
          ∑ m ∈ Finset.range (n + 1), z ^ m * ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0) := by
      classical
      -- Work with `eval₂RingHom` to avoid simp loops around `Polynomial.eval`.
      change Polynomial.eval₂ (RingHom.id ℂ) z P = _
      let φ : Polynomial ℂ →+* ℂ := Polynomial.eval₂RingHom (RingHom.id ℂ) z
      change φ P = _
      -- `eval₂` of a monomial is `coeff * z^m`; commute to `z^m * coeff`.
      simp [P, φ, Polynomial.eval₂_monomial, mul_comm]
    have hfinite' :
        k z = ∑ m ∈ Finset.range (n + 1), z ^ m * ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hfinite
    simpa [hEval] using hfinite'

  refine ⟨P, hPdeg, ?_⟩
  intro z
  have : H z = Complex.exp (k z) := by simp [hk_exp z]
  -- `k = P.eval` gives `H = exp(P.eval)`
  simp [this, hk_poly z]

/-! ## Part 6: The Hadamard Factorization Theorem -/

/-
`hadamard_quotient_growth_bound` is the main analytic input needed to finish Hadamard’s
factorization theorem.

It should prove a global growth estimate for the zero-free quotient

`H(z) = f(z) / (z^ord0 * ∏' n, weierstrassFactor m (z / zeros n))`
-/

/-! ## Helper inequalities: `log⁺` vs `log (1 + ·)` -/

lemma posLog_le_log_one_add {x : ℝ} (hx : 0 ≤ x) :
    log⁺ x ≤ Real.log (1 + x) := by
  by_cases hx0 : x = 0
  · subst hx0
    simp
  · have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    -- `log⁺ x = max 0 (log x)` and `0 ≤ log (1 + x)` and `log x ≤ log (1 + x)`
    have h0 : 0 ≤ Real.log (1 + x) := by
      have : (1 : ℝ) ≤ 1 + x := by linarith
      exact Real.log_nonneg this
    have hlog : Real.log x ≤ Real.log (1 + x) := by
      have hx1 : x ≤ 1 + x := by linarith
      exact Real.log_le_log hx_pos hx1
    -- `max 0 (log x) ≤ log (1 + x)`
    simpa [Real.posLog, max_le_iff] using And.intro h0 hlog

lemma posLog_norm_le_log_one_add_norm (z : ℂ) :
    log⁺ ‖z‖ ≤ Real.log (1 + ‖z‖) :=
  posLog_le_log_one_add (x := ‖z‖) (norm_nonneg z)

/-- On any circle, the circle average of `log⁺ ‖F⁻¹‖` equals the circle average of
`log⁺ ‖F‖` minus the circle average of `log ‖F‖`.

Precisely:
`circleAverage (log⁺ ‖F⁻¹‖) c r = circleAverage (log⁺ ‖F‖) c r - circleAverage (log ‖F‖) c r`.
This is just the pointwise identity `log⁺ x - log⁺ x⁻¹ = log x` averaged over the circle. -/
lemma circleAverage_posLog_norm_inv_eq_circleAverage_posLog_norm_sub_circleAverage_log_norm
    {F : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (h_pos : CircleIntegrable (fun z ↦ log⁺ ‖F z‖) c r)
    (h_inv : CircleIntegrable (fun z ↦ log⁺ ‖(F z)⁻¹‖) c r)
    (_h_log : CircleIntegrable (fun z ↦ Real.log ‖F z‖) c r) :
    circleAverage (fun z ↦ log⁺ ‖(F z)⁻¹‖) c r
      = circleAverage (fun z ↦ log⁺ ‖F z‖) c r
          - circleAverage (fun z ↦ Real.log ‖F z‖) c r := by
  -- Pointwise identity on the circle
  have h_point :
      Set.EqOn
        (fun z : ℂ => (log⁺ ‖F z‖) - (log⁺ ‖(F z)⁻¹‖))
        (fun z : ℂ => Real.log ‖F z‖)
        (Metric.sphere c |r|) := by
    intro z _
    simpa [norm_inv] using (Real.posLog_sub_posLog_inv (x := ‖F z‖))
  -- Average of the difference equals difference of averages
  have h_sub :
      circleAverage (fun z ↦ (log⁺ ‖F z‖) - (log⁺ ‖(F z)⁻¹‖)) c r
        = circleAverage (fun z ↦ log⁺ ‖F z‖) c r
            - circleAverage (fun z ↦ log⁺ ‖(F z)⁻¹‖) c r := by
    simpa using (Real.circleAverage_sub (c := c) (R := r) h_pos h_inv)
  -- Replace the LHS integrand using the pointwise identity on the sphere
  have h_congr :
      circleAverage (fun z ↦ (log⁺ ‖F z‖) - (log⁺ ‖(F z)⁻¹‖)) c r
        = circleAverage (fun z ↦ Real.log ‖F z‖) c r := by
    simpa using
      (circleAverage_congr_sphere (f₁ := fun z ↦ (log⁺ ‖F z‖) - (log⁺ ‖(F z)⁻¹‖))
        (f₂ := fun z ↦ Real.log ‖F z‖) (c := c) (R := r) h_point)
  -- Rearrange to solve for the average of `log⁺ ‖F⁻¹‖`.
  have h_sub' :
      circleAverage (fun z ↦ log⁺ ‖F z‖ - log⁺ ‖F z‖⁻¹) c r
        = circleAverage (fun z ↦ log⁺ ‖F z‖) c r
            - circleAverage (fun z ↦ log⁺ ‖F z‖⁻¹) c r := by
    simpa [norm_inv] using h_sub
  have h_congr' :
      circleAverage (fun z ↦ log⁺ ‖F z‖ - log⁺ ‖F z‖⁻¹) c r
        = circleAverage (fun z ↦ Real.log ‖F z‖) c r := by
    simpa [norm_inv] using h_congr
  have hdiff :
      circleAverage (fun z ↦ log⁺ ‖F z‖) c r - circleAverage (fun z ↦ log⁺ ‖F z‖⁻¹) c r
        = circleAverage (fun z ↦ Real.log ‖F z‖) c r := by
    exact h_sub'.symm.trans h_congr'
  have hfinal :
      circleAverage (fun z ↦ log⁺ ‖F z‖⁻¹) c r
        = circleAverage (fun z ↦ log⁺ ‖F z‖) c r
            - circleAverage (fun z ↦ Real.log ‖F z‖) c r := by
    linarith [hdiff]
  simpa [norm_inv] using hfinal

/-! ## Circle-average bounds from `EntireOfFiniteOrder` -/

lemma circleIntegrable_posLog_norm_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) (r : ℝ) :
    CircleIntegrable (fun z ↦ log⁺ ‖f z‖) 0 r := by
  -- Use the standard meromorphic integrability lemma (entire ⇒ meromorphic).
  have hA : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
    (analyticOnNhd_univ_iff_differentiable).2 hf
  have hM : MeromorphicOn f (Set.univ : Set ℂ) := hA.meromorphicOn
  -- Restrict meromorphy to the sphere.
  have hMsphere : MeromorphicOn f (sphere (0 : ℂ) |r|) := fun z hz => hM z (by simp)
  simpa using (circleIntegrable_posLog_norm_meromorphicOn (c := (0 : ℂ)) (R := r) hMsphere)

lemma circleIntegrable_posLog_norm_of_entire_center
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) (r : ℝ) :
    CircleIntegrable (fun z ↦ log⁺ ‖f z‖) c r := by
  -- Entire ⇒ meromorphic on `univ`, hence on every sphere
  have hA : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
    (analyticOnNhd_univ_iff_differentiable).2 hf
  have hM : MeromorphicOn f (Set.univ : Set ℂ) := hA.meromorphicOn
  have hMsphere : MeromorphicOn f (sphere c |r|) := fun z hz => hM z (by simp)
  simpa using (circleIntegrable_posLog_norm_meromorphicOn (c := c) (R := r) hMsphere)

lemma circleAverage_posLog_norm_le_of_entireOfFiniteOrder
    {ρ : ℝ} {f : ℂ → ℂ} (hf : EntireOfFiniteOrder ρ f) :
    ∃ C > 0, ∀ r : ℝ, 0 ≤ r →
      circleAverage (fun z ↦ log⁺ ‖f z‖) 0 r ≤ C * (1 + r) ^ ρ := by
  rcases hf.growth with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro r hr0
  have h_int : CircleIntegrable (fun z ↦ log⁺ ‖f z‖) 0 r :=
    circleIntegrable_posLog_norm_of_entire (f := f) hf.entire r
  -- Pointwise bound on the circle: `log⁺ ‖f z‖ ≤ log (1 + ‖f z‖) ≤ C * (1 + r)^ρ`.
  have h_pw : ∀ z ∈ sphere (0 : ℂ) |r|, log⁺ ‖f z‖ ≤ C * (1 + r) ^ ρ := by
    intro z hz
    have hz_norm : ‖z‖ = r := by
      have : ‖z‖ = |r| := by simpa [Metric.mem_sphere, dist_zero_right] using hz
      simpa [abs_of_nonneg hr0] using this
    calc
      log⁺ ‖f z‖ ≤ Real.log (1 + ‖f z‖) := posLog_le_log_one_add (x := ‖f z‖) (norm_nonneg _)
      _ ≤ C * (1 + ‖z‖) ^ ρ := hC z
      _ = C * (1 + r) ^ ρ := by simp [hz_norm]
  -- Average is ≤ the constant.
  exact Real.circleAverage_mono_on_of_le_circle (c := (0 : ℂ)) (R := r) (f := fun z ↦ log⁺ ‖f z‖)
    h_int h_pw

lemma circleAverage_posLog_norm_le_of_entireOfFiniteOrder_center
    {ρ : ℝ} {f : ℂ → ℂ} (hf : EntireOfFiniteOrder ρ f) (hρ_nonneg : 0 ≤ ρ) :
    ∃ C > 0, ∀ (c : ℂ) (r : ℝ), 0 ≤ r →
      circleAverage (fun z ↦ log⁺ ‖f z‖) c r ≤ C * (1 + ‖c‖ + r) ^ ρ := by
  rcases hf.growth with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro c r hr0
  -- Integrable on any circle centered at c
  have h_int : CircleIntegrable (fun z ↦ log⁺ ‖f z‖) c r :=
    circleIntegrable_posLog_norm_of_entire_center hf.entire c r
  -- On the sphere: ‖z‖ ≤ ‖c‖ + r, hence a uniform pointwise bound.
  have h_pw : ∀ z ∈ sphere c |r|, log⁺ ‖f z‖ ≤ C * (1 + ‖c‖ + r) ^ ρ := by
    intro z hz
    have hz_norm_le : ‖z‖ ≤ ‖c‖ + r := by
      have hz' : ‖z - c‖ = |r| := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hz
      have htri : ‖z‖ ≤ ‖c‖ + ‖z - c‖ := by
        have hcz : c + (z - c) = z := by
          calc
            c + (z - c) = c + z - c := by
              simp
            _ = z := by
              simp
        simpa [hcz] using (norm_add_le c (z - c))
      simpa [hz', abs_of_nonneg hr0] using htri
    calc
      log⁺ ‖f z‖ ≤ Real.log (1 + ‖f z‖) := posLog_le_log_one_add (x := ‖f z‖) (norm_nonneg _)
      _ ≤ C * (1 + ‖z‖) ^ ρ := hC z
      _ ≤ C * (1 + (‖c‖ + r)) ^ ρ := by
            have hbase : (1 + ‖z‖ : ℝ) ≤ 1 + (‖c‖ + r) := by linarith
            have hpow : (1 + ‖z‖ : ℝ) ^ ρ ≤ (1 + (‖c‖ + r)) ^ ρ :=
              Real.rpow_le_rpow (by positivity) hbase hρ_nonneg
            exact mul_le_mul_of_nonneg_left hpow (le_of_lt hCpos)
      _ = C * (1 + ‖c‖ + r) ^ ρ := by ring_nf
  exact Real.circleAverage_mono_on_of_le_circle (c := c) (R := r) (f := fun z ↦ log⁺ ‖f z‖)
    h_int h_pw

/-! ## ValueDistribution: basic bounds we can get “for free” from `EntireOfFiniteOrder` -/

open ValueDistribution

lemma characteristic_top_le_of_entireOfFiniteOrder
    {ρ : ℝ} {f : ℂ → ℂ} (hf : EntireOfFiniteOrder ρ f) :
    ∃ C > 0, ∀ r : ℝ, 0 ≤ r →
      characteristic f ⊤ r ≤ C * (1 + r) ^ ρ + (logCounting f ⊤ r) := by
  rcases circleAverage_posLog_norm_le_of_entireOfFiniteOrder (hf := hf) with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro r hr0
  -- `characteristic = proximity + logCounting`, and `proximity_top = circleAverage log⁺`.
  have hprox : proximity f ⊤ r ≤ C * (1 + r) ^ ρ := by
    -- Rewrite `proximity` and apply the circle-average bound from `EntireOfFiniteOrder`.
    simpa [ValueDistribution.proximity_top] using hC r hr0
  -- Add `logCounting f ⊤ r` on both sides.
  have := add_le_add_right hprox (logCounting f ⊤ r)
  -- Unfold `characteristic`.
  simpa [ValueDistribution.characteristic, add_assoc, add_comm, add_left_comm] using this

/-! ## Entire functions have no poles: `logCounting f ⊤ = 0` -/

lemma logCounting_top_eq_zero_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    logCounting f ⊤ = 0 := by
  -- Entire ⇒ analytic on a neighbourhood of `univ`
  have hf_an : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
    (analyticOnNhd_univ_iff_differentiable).2 hf
  -- Hence the divisor is nonnegative, so the negative part (pole divisor) is zero.
  have hDnonneg : 0 ≤ MeromorphicOn.divisor f (Set.univ : Set ℂ) :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf_an
  have hneg : (MeromorphicOn.divisor f (Set.univ : Set ℂ))⁻ = 0 := by
    ext z
    have hz : (0 : ℤ) ≤ MeromorphicOn.divisor f (Set.univ : Set ℂ) z := hDnonneg z
    -- `z ↦ divisor f univ z` is pointwise ≥ 0, hence its negative part vanishes.
    simp [negPart_eq_zero.2 hz]
  -- Rewrite `logCounting f ⊤` as the logCounting of the pole divisor.
  simp [ValueDistribution.logCounting_top, hneg]

/-! ## Characteristic bounds for entire functions of finite order -/

lemma characteristic_top_le_of_entireOfFiniteOrder'
    {ρ : ℝ} {f : ℂ → ℂ} (hf : EntireOfFiniteOrder ρ f) :
    ∃ C > 0, ∀ r : ℝ, 0 ≤ r → characteristic f ⊤ r ≤ C * (1 + r) ^ ρ := by
  rcases circleAverage_posLog_norm_le_of_entireOfFiniteOrder (hf := hf) with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro r hr0
  -- For entire `f`, the pole-counting term vanishes.
  have hlog0 : logCounting f ⊤ r = 0 := by
    have hfun : logCounting f ⊤ = 0 := logCounting_top_eq_zero_of_entire (f := f) hf.entire
    simpa using congrArg (fun g : ℝ → ℝ => g r) hfun
  -- Unfold the characteristic and use the proximity bound.
  have hprox : proximity f ⊤ r ≤ C * (1 + r) ^ ρ := by
    simpa [ValueDistribution.proximity_top] using hC r hr0
  simpa [ValueDistribution.characteristic, hlog0] using (add_le_add_right hprox 0)

lemma characteristic_inv_top (f : ℂ → ℂ) :
    characteristic (f⁻¹) ⊤ = characteristic f 0 := by
  ext r
  simp [ValueDistribution.characteristic, ValueDistribution.proximity_inv, ValueDistribution.logCounting_inv]

lemma characteristic_zero_le_of_entireOfFiniteOrder'
    {ρ : ℝ} {f : ℂ → ℂ} (hf : EntireOfFiniteOrder ρ f) :
    ∃ C > 0, ∀ r : ℝ, 0 ≤ r →
      characteristic f 0 r ≤ C * (1 + r) ^ ρ +
        max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
  -- Bound `characteristic f 0` by `characteristic f ⊤` plus an absolute constant,
  -- using the first part of the First Main Theorem.
  rcases characteristic_top_le_of_entireOfFiniteOrder' (hf := hf) with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro r hr0
  -- Meromorphy on `univ`
  have hf_mer : MeromorphicOn f (Set.univ : Set ℂ) :=
    (analyticOnNhd_univ_iff_differentiable.2 hf.entire).meromorphicOn
  -- Quantitative First Main Theorem bound:
  have hdiff :
      |characteristic f ⊤ r - characteristic (f⁻¹) ⊤ r|
        ≤ max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| :=
    ValueDistribution.characteristic_sub_characteristic_inv_le (f := f) (hf := hf_mer) (R := r)

  -- From `|A - B| ≤ K` we get `B ≤ A + K`.
  have hdiff' :
      |characteristic (f⁻¹) ⊤ r - characteristic f ⊤ r|
        ≤ max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
    simpa [abs_sub_comm] using hdiff
  have hsub :
      characteristic (f⁻¹) ⊤ r - characteristic f ⊤ r
        ≤ max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| :=
    (le_abs_self _).trans hdiff'
  have hle_inv :
      characteristic (f⁻¹) ⊤ r ≤ characteristic f ⊤ r +
        max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| :=
    by
      -- Rearrange `B = (B - A) + A` and use `B - A ≤ K`.
      have hrew :
          characteristic (f⁻¹) ⊤ r =
            (characteristic (f⁻¹) ⊤ r - characteristic f ⊤ r) + characteristic f ⊤ r := by
        ring
      calc
        characteristic (f⁻¹) ⊤ r
            = (characteristic (f⁻¹) ⊤ r - characteristic f ⊤ r) + characteristic f ⊤ r := hrew
        _ ≤ max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| + characteristic f ⊤ r := by
              -- Add `characteristic f ⊤ r` on the right of `hsub`.
              have h := add_le_add_right hsub (characteristic f ⊤ r)
              simpa [add_assoc, add_comm, add_left_comm] using h
        _ = characteristic f ⊤ r + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
              ac_rfl
  have hle0 :
      characteristic f 0 r ≤ characteristic f ⊤ r +
        max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
    -- rewrite `characteristic (f⁻¹) ⊤` as `characteristic f 0`
    simpa [characteristic_inv_top] using hle_inv

  -- Now use the growth bound for `characteristic f ⊤ r`.
  have htop : characteristic f ⊤ r ≤ C * (1 + r) ^ ρ := hC r hr0
  have htop' :
      characteristic f ⊤ r + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖|
        ≤ C * (1 + r) ^ ρ +
          max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| :=
    by
      -- `A ≤ B` implies `A + K ≤ B + K`.
      simpa [add_assoc, add_comm, add_left_comm] using add_le_add_right htop
        (max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖|)
  exact hle0.trans htop'

/-! ## Mean-value bounds: circle averages to pointwise bounds for harmonic functions -/

lemma harmonicOnNhd_le_circleAverage_pos
    {u : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall c |r|)) :
    u c ≤ circleAverage (fun z ↦ max (u z) 0) c r := by
  -- Mean value property: `circleAverage u c r = u c`.
  have hmean : circleAverage u c r = u c :=
    HarmonicOnNhd.circleAverage_eq (f := u) (c := c) (R := r) hu
  -- Pointwise: `u ≤ max u 0`, so the average is monotone.
  have hci_u : CircleIntegrable u c r := by
    -- Harmonicity implies `C²` and hence continuity on the sphere.
    have hcont_sphere : ContinuousOn u (Metric.sphere c |r|) := by
      intro z hz
      have hz_cb : z ∈ Metric.closedBall c |r| := sphere_subset_closedBall hz
      have hz_harm : InnerProductSpace.HarmonicAt u z := hu z hz_cb
      exact hz_harm.1.continuousAt.continuousWithinAt
    exact hcont_sphere.circleIntegrable'
  have hci_pos : CircleIntegrable (fun z ↦ max (u z) 0) c r := by
    have hcont_sphere_u : ContinuousOn u (Metric.sphere c |r|) := by
      intro z hz
      have hz_cb : z ∈ Metric.closedBall c |r| := sphere_subset_closedBall hz
      have hz_harm : InnerProductSpace.HarmonicAt u z := hu z hz_cb
      exact hz_harm.1.continuousAt.continuousWithinAt
    have hpair : ContinuousOn (fun z : ℂ => (u z, (0 : ℝ))) (Metric.sphere c |r|) :=
      hcont_sphere_u.prodMk (continuousOn_const : ContinuousOn (fun _ : ℂ => (0 : ℝ)) (Metric.sphere c |r|))
    have hmax : ContinuousOn (fun p : ℝ × ℝ => max p.1 p.2) (Set.univ : Set (ℝ × ℝ)) :=
      continuous_max.continuousOn
    have hcont_pos : ContinuousOn (fun z : ℂ => max (u z) 0) (Metric.sphere c |r|) := by
      -- compose `max` with the continuous pair map `(u,0)`.
      simpa [Function.comp, Set.MapsTo] using
        (hmax.comp hpair (by intro z hz; simp))
    exact hcont_pos.circleIntegrable'
  have hmono : circleAverage u c r ≤ circleAverage (fun z ↦ max (u z) 0) c r := by
    apply Real.circleAverage_mono hci_u hci_pos
    intro z hz
    exact le_max_left _ _
  -- Rewrite with the mean value property.
  simpa [hmean] using hmono

lemma norm_le_exp_circleAverage_posLog_of_entire_nonzero
    {H : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hH_entire : Differentiable ℂ H) (hH_nonzero : ∀ z, H z ≠ 0) :
    ‖H c‖ ≤ Real.exp (circleAverage (fun z ↦ log⁺ ‖H z‖) c r) := by
  -- Apply the previous lemma to `u(z) = log ‖H z‖`.
  let u : ℂ → ℝ := fun z => Real.log ‖H z‖
  have hu : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall c |r|) := by
    intro z hz
    have hAn : AnalyticAt ℂ H z := (hH_entire.analyticAt z)
    have hHz : H z ≠ 0 := hH_nonzero z
    -- `log ‖H‖` is harmonic at each point where `H ≠ 0`.
    exact (hAn.harmonicAt_log_norm hHz)
  have hle : u c ≤ circleAverage (fun z ↦ max (u z) 0) c r :=
    harmonicOnNhd_le_circleAverage_pos (u := u) (c := c) (r := r) hu
  -- Rewrite `max (log‖H‖) 0` as `log⁺ ‖H‖`.
  have hmax : (fun z ↦ max (u z) 0) = fun z ↦ log⁺ ‖H z‖ := by
    funext z
    simp [u, Real.posLog, max_comm]
  have hle' : Real.log ‖H c‖ ≤ circleAverage (fun z ↦ log⁺ ‖H z‖) c r := by
    simpa [u, hmax] using hle
  -- Exponentiate.
  have hpos : 0 < ‖H c‖ := norm_pos_iff.mpr (hH_nonzero c)
  exact (Real.log_le_iff_le_exp hpos).1 hle'

/-! ## ZeroData implies nontriviality (used to rule out `order = ⊤` cases) -/

lemma zeroData_not_all_zero {f : ℂ → ℂ} (hz : ZeroData f) : ¬ (∀ z : ℂ, f z = 0) := by
  intro hzero
  have hsubset : ({0}ᶜ : Set ℂ) ⊆ Set.range hz.zeros := by
    intro z hz0
    have hz' : f z = 0 := hzero z
    have hzspec := (hz.zero_spec z).1 hz'
    rcases hzspec with h0 | hnon0
    · exact False.elim (hz0 h0.1)
    · exact hnon0.2
  have hcount_range : (Set.range hz.zeros).Countable := Set.countable_range hz.zeros
  have hcount_compl : ({0}ᶜ : Set ℂ).Countable := hcount_range.mono hsubset
  have hcount_univ : (Set.univ : Set ℂ).Countable := by
    have h0c : ({0} : Set ℂ).Countable := Set.countable_singleton 0
    have : ({0} ∪ ({0}ᶜ) : Set ℂ).Countable := h0c.union hcount_compl
    simpa [Set.union_compl_self] using this
  exact not_countable_complex hcount_univ

open Complex Real BigOperators Finset Set Filter Topology Metric ValueDistribution
open scoped Topology

namespace ComplexAnalysis
namespace Hadamard

/-!
## Analytic Estimates for the Hadamard Quotient

We establish that the quotient `H = f / F` of an entire function by its canonical product
has finite order. This relies on bounding the characteristic function of `H` and using
the Poisson-Jensen formula.
-/

/-!
## Cartan / minimum-modulus style lower bounds (Tao, Theorem 22)

The “missing” step to get the sharp polynomial degree bound `≤ ⌊ρ⌋` is to control how small
the canonical product can get on a *sequence of circles* `‖z‖ = R_k`.  This matches Tao’s
probabilistic-radius argument in `academic_framework/HadamardFactorization/hadamard.md`.

We begin with pointwise lower bounds for the Weierstrass factors in the far/near regimes.
-/

open scoped BigOperators

lemma log_norm_weierstrassFactor_ge_neg_two_pow {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    (-2 : ℝ) * ‖z‖ ^ (m + 1) ≤ Real.log ‖weierstrassFactor m z‖ := by
  -- Use the exact representation from `WeierstrassFactorBound`: `E_m(z) = exp(-logTail)`.
  have hz_lt : ‖z‖ < (1 : ℝ) := lt_of_le_of_lt hz (by norm_num)
  have hz1 : z ≠ (1 : ℂ) := by
    intro h
    have : (1 : ℝ) ≤ (1 / 2 : ℝ) := by
      simpa [h] using hz
    norm_num at this
  have hEq' : weierstrassFactor' m z = Complex.exp (-logTail m z) :=
    weierstrassFactor_eq_exp_neg_tail m hz_lt hz1
  have hEq : weierstrassFactor m z = Complex.exp (-logTail m z) := by
    -- `weierstrassFactor = weierstrassFactor'` by unfolding definitions.
    simpa [weierstrassFactor, weierstrassFactor', partialLogSum'] using hEq'
  -- Take `Real.log ‖·‖` and bound the real part.
  have hlog :
      Real.log ‖weierstrassFactor m z‖ = (-logTail m z).re := by
    -- `‖exp w‖ = exp (Re w)` and `log (exp x) = x`.
    simp [hEq, Complex.norm_exp, Real.log_exp]
  -- `Re w ≥ -‖w‖`.
  have hre : (-logTail m z).re ≥ -‖logTail m z‖ := by
    have habs : |(-logTail m z).re| ≤ ‖-logTail m z‖ := Complex.abs_re_le_norm _
    have : (-‖-logTail m z‖) ≤ (-logTail m z).re := by
      -- From `|re| ≤ ‖·‖` deduce `-‖·‖ ≤ re`.
      have := neg_le_of_abs_le habs
      simpa using this
    simpa [norm_neg] using this
  -- Tail norm bound: `‖logTail m z‖ ≤ 2‖z‖^(m+1)` when `‖z‖ ≤ 1/2`.
  have htail :
      ‖logTail m z‖ ≤ 2 * ‖z‖ ^ (m + 1) := by
    have h1 : ‖logTail m z‖ ≤ ‖z‖ ^ (m + 1) / (1 - ‖z‖) :=
      norm_logTail_le hz_lt m
    have h2 : ‖z‖ ^ (m + 1) / (1 - ‖z‖) ≤ 2 * ‖z‖ ^ (m + 1) :=
      norm_pow_div_one_sub_le_two hz m
    exact h1.trans h2
  -- Assemble.
  have : (-logTail m z).re ≥ (-2 : ℝ) * ‖z‖ ^ (m + 1) := by
    calc
      (-logTail m z).re ≥ -‖logTail m z‖ := hre
      _ ≥ (-2 : ℝ) * ‖z‖ ^ (m + 1) := by
            -- rewrite `-‖tail‖ ≥ - (2 * ‖z‖^(m+1))`
            nlinarith [htail]
  simpa [hlog, mul_assoc, mul_left_comm, mul_comm] using this

lemma log_norm_weierstrassFactor_ge_log_norm_one_sub_sub
    (m : ℕ) (z : ℂ) :
    Real.log ‖1 - z‖ - (m : ℝ) * max 1 (‖z‖ ^ m) ≤ Real.log ‖weierstrassFactor m z‖ := by
  classical
  by_cases hz1 : z = (1 : ℂ)
  · subst hz1
    -- `log ‖1 - 1‖ = 0` and `weierstrassFactor m 1 = 0`, so the claim is trivial.
    simp [weierstrassFactor]
  -- Expand `weierstrassFactor` and take logs (now `‖1 - z‖ > 0`).
  set S : ℂ := ∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1)
  have hS :
      weierstrassFactor m z = (1 - z) * Complex.exp S := by
    simp [weierstrassFactor, S]
  have hnorm_pos : 0 < ‖(1 : ℂ) - z‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz1))
  -- `log ‖(1-z) * exp S‖ = log ‖1-z‖ + Re S`.
  have hlog :
      Real.log ‖weierstrassFactor m z‖ = Real.log ‖1 - z‖ + S.re := by
    -- `‖uv‖ = ‖u‖*‖v‖`, and `‖exp S‖ = exp (Re S)`.
    have hne : ‖(1 : ℂ) - z‖ ≠ 0 := ne_of_gt hnorm_pos
    calc
      Real.log ‖weierstrassFactor m z‖
          = Real.log (‖(1 : ℂ) - z‖ * ‖Complex.exp S‖) := by
                simp [hS]
      _ = Real.log ‖(1 : ℂ) - z‖ + Real.log ‖Complex.exp S‖ := by
            simpa using (Real.log_mul hne (by
              -- `‖exp S‖ ≠ 0`
              exact (ne_of_gt (by simp))))
      _ = Real.log ‖(1 : ℂ) - z‖ + S.re := by
            simp [Complex.norm_exp, Real.log_exp]
      _ = Real.log ‖1 - z‖ + S.re := by simp [sub_eq_add_neg, add_comm]
  -- Bound `S.re` from below by `-‖S‖`, then by a crude dyadic bound.
  have hre : S.re ≥ -‖S‖ := by
    have habs : |S.re| ≤ ‖S‖ := Complex.abs_re_le_norm _
    have := neg_le_of_abs_le habs
    simpa using this
  have hnormS :
      ‖S‖ ≤ (m : ℝ) * max 1 (‖z‖ ^ m) := by
    -- `‖∑ t‖ ≤ ∑ ‖t‖` and each term is bounded by `max 1 (‖z‖^m)`.
    have hsum :
        ‖S‖ ≤ ∑ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖ := by
      simpa [S] using
        (norm_sum_le (s := Finset.range m) (f := fun k => z ^ (k + 1) / (k + 1)))
    have hterm :
        ∀ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖ ≤ max 1 (‖z‖ ^ m) := by
      intro k hk
      have hk' : k + 1 ≤ m := Nat.succ_le_of_lt (Finset.mem_range.1 hk)
      -- `‖z^(k+1)/(k+1)‖ ≤ ‖z‖^(k+1)` and `‖z‖^(k+1) ≤ max 1 (‖z‖^m)`.
      have hdiv : ‖z ^ (k + 1) / (k + 1)‖ ≤ ‖z‖ ^ (k + 1) := by
        -- denominator has norm ≥ 1
        have hden : (1 : ℝ) ≤ (k + 1 : ℝ) := by norm_cast; omega
        have hden' : (1 : ℝ) ≤ ‖((k + 1 : ℕ) : ℂ)‖ := by
          have hn : ‖((k + 1 : ℕ) : ℂ)‖ = (k + 1 : ℝ) := by
            simpa using (Complex.norm_natCast (k + 1))
          -- Avoid `simpa` here: in this toolchain `simp` turns `1 ≤ (k+1:ℝ)` into `True`.
          rw [hn]
          exact hden
        -- rewrite the norm of the quotient
        have hnorm :
            ‖z ^ (k + 1) / (k + 1)‖ = ‖z‖ ^ (k + 1) / ‖((k + 1 : ℕ) : ℂ)‖ := by
          simp [norm_pow, Nat.cast_add_one]
        -- now `a / b ≤ a` since `1 ≤ b`
        rw [hnorm]
        exact div_le_self (pow_nonneg (norm_nonneg z) _) hden'
      have hpow : ‖z‖ ^ (k + 1) ≤ max 1 (‖z‖ ^ m) := by
        by_cases hz1 : ‖z‖ ≤ 1
        · -- if `‖z‖ ≤ 1`, then `‖z‖^(k+1) ≤ 1`
          have hle1 : ‖z‖ ^ (k + 1) ≤ (1 : ℝ) := by
            exact pow_le_one₀ (norm_nonneg z) hz1
          exact le_trans hle1 (le_max_left _ _)
        · -- if `‖z‖ > 1`, monotonicity of powers gives `‖z‖^(k+1) ≤ ‖z‖^m`
          have hz1' : 1 ≤ ‖z‖ := le_of_not_ge hz1
          have hle : ‖z‖ ^ (k + 1) ≤ ‖z‖ ^ m := by
            exact pow_le_pow_right₀ hz1' hk'
          exact le_trans hle (le_max_right _ _)
      exact hdiv.trans hpow
    have hsum' :
        ∑ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖
          ≤ ∑ _k ∈ Finset.range m, max 1 (‖z‖ ^ m) := by
      exact Finset.sum_le_sum (fun k hk => hterm k hk)
    have hconst :
        (∑ _k ∈ Finset.range m, max 1 (‖z‖ ^ m))
          = (m : ℝ) * max 1 (‖z‖ ^ m) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    have := le_trans hsum (le_trans hsum' (le_of_eq hconst))
    exact this
  have hSre : S.re ≥ -(m : ℝ) * max 1 (‖z‖ ^ m) := by
    calc
      S.re ≥ -‖S‖ := hre
      _ ≥ -(m : ℝ) * max 1 (‖z‖ ^ m) := by
            nlinarith [hnormS]
  -- Finish.
  -- Move `S.re` to the RHS via `hlog`.
  calc
    Real.log ‖1 - z‖ - (m : ℝ) * max 1 (‖z‖ ^ m)
        ≤ Real.log ‖1 - z‖ + S.re := by linarith [hSre]
    _ = Real.log ‖weierstrassFactor m z‖ := by
          simp [hlog]

/-!
### Averages of the logarithmic singularity (Tao's probabilistic radius step)

We control the *average* size of the positive part of `log (1 / |1 - t|)` near `t = 1`
by dominating it with an integrable power singularity. This is the analytic core of the
probabilistic method used in Tao's proof of Hadamard factorization.
-/

lemma neg_log_le_sqrt_two_div {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    -Real.log x ≤ Real.sqrt (2 / x) := by
  -- Let `t := -log x ≥ 0`.
  have ht : 0 ≤ -Real.log x := by
    have hlog_le0 : Real.log x ≤ 0 := by
      -- `log x ≤ x - 1 ≤ 0` for `x ≤ 1`.
      have h := Real.log_le_sub_one_of_pos hx
      linarith
    linarith
  -- `1 + t + t^2/2 ≤ exp t`, and `exp(-log x) = 1/x`.
  have hquad := Real.quadratic_le_exp_of_nonneg ht
  have hexp : Real.exp (-Real.log x) = x⁻¹ := by
    simp [Real.exp_neg, Real.exp_log hx]
  -- Drop the nonnegative terms `1 + t` from the LHS.
  have hsq :
      (-Real.log x) ^ 2 / 2 ≤ x⁻¹ := by
    have : (-Real.log x) ^ 2 / 2 ≤ Real.exp (-Real.log x) := by
      have hle : (-Real.log x) ^ 2 / 2 ≤ 1 + (-Real.log x) + (-Real.log x) ^ 2 / 2 := by
        have : 0 ≤ (1 : ℝ) + (-Real.log x) := by linarith [ht]
        linarith
      exact hle.trans hquad
    simpa [hexp] using this
  -- Take square roots.
  have hx_inv : 0 ≤ x⁻¹ := by exact inv_nonneg.2 (le_of_lt hx)
  have h2x_inv : 0 ≤ (2 / x) := by
    have : 0 ≤ (2 : ℝ) := by norm_num
    exact div_nonneg this (le_of_lt hx)
  have hsqrt :
      |(-Real.log x)| ≤ Real.sqrt (2 / x) := by
    -- From `t^2 ≤ 2/x`, we get `|t| ≤ sqrt(2/x)`.
    have hsq' : (-Real.log x) ^ 2 ≤ 2 / x := by
      -- `t^2 / 2 ≤ x⁻¹`  ->  `t^2 ≤ 2 * x⁻¹`  ->  `t^2 ≤ 2 / x`
      have hmul : 2 * ((-Real.log x) ^ 2 / 2) ≤ 2 * x⁻¹ :=
        mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 2)
      have hmul' : (-Real.log x) ^ 2 ≤ 2 * x⁻¹ := by
        calc
          (-Real.log x) ^ 2 = 2 * ((-Real.log x) ^ 2 / 2) := by ring
          _ ≤ 2 * x⁻¹ := hmul
      simpa [div_eq_mul_inv, mul_assoc] using hmul'
    -- rewrite `t^2` as `|t|^2` and take square roots
    have habs : |(-Real.log x)| ^ 2 ≤ 2 / x := by
      simpa [sq_abs] using hsq'
    have := Real.sqrt_le_sqrt habs
    -- `sqrt(|t|^2) = |t|`
    simpa [Real.sqrt_sq_eq_abs] using this
  -- Since `t ≥ 0`, `|t| = t`.
  have habs_t : |(-Real.log x)| = -Real.log x := by
    simp [abs_of_nonneg ht]
  -- Finish.
  simpa [habs_t] using hsqrt

lemma posLog_log_one_div_abs_one_sub_le_sqrt {t : ℝ} :
    max 0 (Real.log (1 / |1 - t|)) ≤ Real.sqrt (2 / |1 - t|) := by
  by_cases ht : |1 - t| ≤ 1
  · by_cases h0 : |1 - t| = 0
    · -- then `t = 1`, both sides are 0
      have : t = 1 := by
        have : 1 - t = 0 := by simpa [abs_eq_zero] using h0
        linarith
      subst this
      simp
    · have hpos : 0 < |1 - t| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0)
      have hle : -Real.log |1 - t| ≤ Real.sqrt (2 / |1 - t|) :=
        neg_log_le_sqrt_two_div (x := |1 - t|) hpos ht
      -- On `|1-t| ≤ 1`, the log is nonnegative: `log(1/|1-t|) = -log|1-t|`.
      have hlog : Real.log (1 / |1 - t|) = -Real.log |1 - t| := by
        simp [Real.log_inv]
      have hnonneg : 0 ≤ Real.log (1 / |1 - t|) := by
        -- `1 / |1-t| ≥ 1` since `|1-t| ≤ 1`
        have : (1 : ℝ) ≤ 1 / |1 - t| := by
          have hpos' : 0 < |1 - t| := hpos
          -- `1 ≤ 1 / a` iff `a ≤ 1` for `a > 0`
          exact (one_le_div hpos').2 ht
        exact Real.log_nonneg this
      have hmax : max 0 (Real.log (1 / |1 - t|)) = Real.log (1 / |1 - t|) :=
        max_eq_right hnonneg
      -- Avoid `simp`: it rewrites `max ≤ _` into a conjunction via `max_le_iff`.
      calc
        max 0 (Real.log (1 / |1 - t|))
            = Real.log (1 / |1 - t|) := hmax
        _ = -Real.log |1 - t| := hlog
        _ ≤ Real.sqrt (2 / |1 - t|) := hle
  · -- If `|1-t| > 1`, then `log(1/|1-t|) ≤ 0`, so LHS is 0.
    have hlt : 1 < |1 - t| := lt_of_not_ge ht
    have hle0 : Real.log (1 / |1 - t|) ≤ 0 := by
      have hpos : 0 < |1 - t| := lt_trans (by norm_num) hlt
      have : (1 / |1 - t|) ≤ 1 := by
        -- `a / b ≤ 1 ↔ a ≤ b` for `b > 0`, with `a = 1`, `b = |1-t|`.
        exact (div_le_one hpos).2 (le_of_lt hlt)
      have h1 : 0 < (1 / |1 - t|) := by positivity
      exact le_trans (Real.log_le_log h1 this) (by simp)
    have hmax : max 0 (Real.log (1 / |1 - t|)) = 0 := max_eq_left hle0
    have hrhs : 0 ≤ Real.sqrt (2 / |1 - t|) := by
      have : 0 ≤ 2 / |1 - t| := by
        exact div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg _)
      exact Real.sqrt_nonneg _
    -- Avoid `simp`: it rewrites `max ≤ _` into a conjunction via `max_le_iff`.
    rw [hmax]
    exact hrhs

/-!
### Algebraic and growth lemmas for `exp (Polynomial.eval z P)`

To upgrade the degree bound from `≤ ⌈ρ⌉` to `≤ ⌊ρ⌋`, we use the fact that the order of
an exponential of a nonzero polynomial is an **integer**: it equals the degree.

The key input is a lower bound: if `P.natDegree = n` and the leading coefficient is nonzero,
then along a suitable ray we have `Re (P z) ≳ ‖z‖^n`, hence `log(1+‖exp(P z)‖) ≳ ‖z‖^n`.
-/

open Polynomial

lemma exists_pow_eq_complex {n : ℕ} (hn : 0 < n) (w : ℂ) : ∃ z : ℂ, z ^ n = w := by
  classical
  by_cases hw : w = 0
  · subst hw
    refine ⟨0, ?_⟩
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    simp [hn0]
  · refine ⟨Complex.exp (Complex.log w / n), ?_⟩
    have hn0 : (n : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    calc
      (Complex.exp (Complex.log w / n)) ^ n
          = Complex.exp ((n : ℂ) * (Complex.log w / n)) := by
              -- `(exp x)^n = exp(n*x)`
              simpa using (Complex.exp_nat_mul (Complex.log w / n) n).symm
      _ = Complex.exp (Complex.log w) := by
            -- cancel `n` against `/ n`
            simp [div_eq_mul_inv]; grind
      _ = w := by simpa using (Complex.exp_log hw)

/-!
#### A quantitative “ray” lower bound for polynomial evaluation

For a non-constant polynomial `P` of degree `n > 0`, we can choose a direction `w` on the unit
circle so that the leading term `P.leadingCoeff * (R*w)^n` is **positive real** and dominates all
lower-degree terms for large `R`. This is the core input for proving that `exp (P z)` has order
at least `n`.
-/

lemma mul_conj_div_norm (a : ℂ) (ha : a ≠ 0) :
    a * ((starRingEnd ℂ) a / (‖a‖ : ℂ)) = (‖a‖ : ℂ) := by
  have hnorm_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hnorm_ne : (‖a‖ : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hnorm_pos)
  have hmul : a * (starRingEnd ℂ) a = (Complex.normSq a : ℂ) :=
    Complex.mul_conj a
  have hcast : (Complex.normSq a : ℂ) = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast (Complex.normSq_eq_norm_sq a)
  have hdiv : ((‖a‖ ^ 2 : ℝ) : ℂ) / (‖a‖ : ℂ) = (‖a‖ : ℂ) := by
    have : ((‖a‖ ^ 2 : ℝ) : ℂ) = (‖a‖ : ℂ) * (‖a‖ : ℂ) := by
      simp [pow_two]
    calc
      ((‖a‖ ^ 2 : ℝ) : ℂ) / (‖a‖ : ℂ)
          = ((‖a‖ : ℂ) * (‖a‖ : ℂ)) / (‖a‖ : ℂ) := by simp [this]
      _ = (‖a‖ : ℂ) := by
            field_simp [hnorm_ne]
  calc
    a * ((starRingEnd ℂ) a / (‖a‖ : ℂ))
        = (a * (starRingEnd ℂ) a) / (‖a‖ : ℂ) := by
            simp [div_eq_mul_inv, mul_assoc]
    _ = (Complex.normSq a : ℂ) / (‖a‖ : ℂ) := by simp [hmul]
    _ = ((‖a‖ ^ 2 : ℝ) : ℂ) / (‖a‖ : ℂ) := by simp [hcast]
    _ = (‖a‖ : ℂ) := hdiv

open scoped NNReal

set_option maxHeartbeats 400000 in
lemma exists_z_norm_eq_re_eval_ge
    (P : Polynomial ℂ) (hn : 0 < P.natDegree) :
    ∃ R0 : ℝ, 0 < R0 ∧
      ∀ R : ℝ, R0 ≤ R →
        ∃ z : ℂ, ‖z‖ = R ∧
          (‖P.leadingCoeff‖ / 2) * R ^ P.natDegree ≤ (P.eval z).re := by
  classical
  -- Notation
  set n : ℕ := P.natDegree
  have hn0 : 0 < n := hn
  have hP0 : P ≠ 0 := by
    intro h0
    simp [n, h0] at hn0
  have hLC : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP0
  set a : ℂ := P.leadingCoeff
  have ha : a ≠ 0 := hLC
  have hnorm_a_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha

  -- Choose `w` with `w^n = conj(a)/‖a‖` so that `a * w^n = ‖a‖` (a positive real).
  set wtarget : ℂ := (starRingEnd ℂ) a / (‖a‖ : ℂ)
  have hwtarget_norm : ‖wtarget‖ = (1 : ℝ) := by
    have hnorm_ne : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hnorm_a_pos)
    calc
      ‖wtarget‖ = ‖(starRingEnd ℂ) a‖ / ‖(‖a‖ : ℂ)‖ := by
        simp [wtarget]
      _ = ‖a‖ / ‖a‖ := by simp
      _ = (1 : ℝ) := by
        field_simp [hnorm_a_pos.ne']

  rcases exists_pow_eq_complex (n := n) hn0 (w := wtarget) with ⟨w, hw⟩
  have hw_norm : ‖w‖ = (1 : ℝ) := by
    -- take norms in `w^n = wtarget`
    have hpow : (‖w‖ : ℝ) ^ n = 1 := by
      have := congrArg (fun z : ℂ => ‖z‖) hw
      simpa [norm_pow, hwtarget_norm] using this
    -- move to `ℝ≥0` to use `pow_eq_one_iff`
    let x : ℝ≥0 := ⟨‖w‖, norm_nonneg w⟩
    have hxpow : x ^ n = 1 := by
      ext
      simpa [x] using hpow
    have hx : x = 1 := (pow_eq_one_iff (M := ℝ≥0) (x := x) (n := n) (Nat.ne_of_gt hn0)).1 hxpow
    have := congrArg (fun t : ℝ≥0 => (t : ℝ)) hx
    simpa [x] using this

  -- Decompose `P` into lower terms + leading monomial.
  set S : ℝ := ∑ i ∈ Finset.range n, ‖P.coeff i‖
  -- Choose a threshold `R0` so that for `R ≥ R0` the lower terms are ≤ (‖a‖/2) R^n.
  set R0 : ℝ := max 1 (2 * S / ‖a‖)
  refine ⟨R0, ?_, ?_⟩
  · have : (0 : ℝ) < (1 : ℝ) := by norm_num
    exact lt_of_lt_of_le this (le_max_left _ _)
  · intro R hR
    have hR_ge1 : (1 : ℝ) ≤ R := by
      exact le_trans (le_max_left _ _) hR
    have hR_nonneg : 0 ≤ R := le_trans (by norm_num) hR_ge1

    -- Take `z = R * w`, so `‖z‖ = R` (since ‖w‖ = 1).
    set z : ℂ := (R : ℂ) * w
    have hz_norm : ‖z‖ = R := by
      have : ‖z‖ = |R| * ‖w‖ := by
        simp [z]
      simp [this, hw_norm, abs_of_nonneg hR_nonneg]

    -- Evaluate: `P z = (∑_{i<n} coeff i * z^i) + a * z^n`.
    have h_eval : P.eval z =
        (∑ i ∈ Finset.range n, P.coeff i * z ^ i) + P.coeff n * z ^ n := by
      -- use `eval_eq_sum_range` and split the last term
      have hsum : P.eval z = ∑ i ∈ Finset.range (n + 1), P.coeff i * z ^ i := by
        -- `n = natDegree` gives `natDegree + 1 = n + 1`
        have : P.natDegree + 1 = n + 1 := by simp [n]
        simpa [this] using (Polynomial.eval_eq_sum_range (p := P) z)
      have hsplit :
          (∑ i ∈ Finset.range (n + 1), P.coeff i * z ^ i)
            = (∑ i ∈ Finset.range n, P.coeff i * z ^ i) + P.coeff n * z ^ n := by
        simpa using (Finset.sum_range_succ (f := fun i => P.coeff i * z ^ i) n)
      exact hsum.trans hsplit

    -- Lower-term norm bound: `‖∑_{i<n} coeff i * z^i‖ ≤ S * R^(n-1)`.
    have h_lower_norm :
        ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ ≤ S * R ^ (n - 1) := by
      -- Triangle inequality + `‖z‖ = R` and `‖z‖^i ≤ R^(n-1)` for `i<n` when `R ≥ 1`.
      have h1 :
          ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖
            ≤ ∑ i ∈ Finset.range n, ‖P.coeff i * z ^ i‖ := by
        simpa using (norm_sum_le (Finset.range n) (fun i => P.coeff i * z ^ i))
      have hterm : ∀ i ∈ Finset.range n, ‖P.coeff i * z ^ i‖ ≤ ‖P.coeff i‖ * R ^ (n - 1) := by
        intro i hi
        have hi_lt : i < n := Finset.mem_range.mp hi
        have hi_le : i ≤ n - 1 := Nat.le_pred_of_lt hi_lt
        have hzpow : ‖z‖ ^ i ≤ R ^ (n - 1) := by
          -- `‖z‖ = R`, then monotone in exponent (base ≥ 1)
          have : ‖z‖ ^ i ≤ ‖z‖ ^ (n - 1) := pow_le_pow_right₀ (by simpa [hz_norm] using hR_ge1) hi_le
          simpa [hz_norm] using this
        -- combine
        calc
          ‖P.coeff i * z ^ i‖ = ‖P.coeff i‖ * ‖z‖ ^ i := by
            simp [norm_pow]
          _ ≤ ‖P.coeff i‖ * R ^ (n - 1) := by
            exact mul_le_mul_of_nonneg_left hzpow (norm_nonneg _)
      have h2 :
          ∑ i ∈ Finset.range n, ‖P.coeff i * z ^ i‖
            ≤ ∑ i ∈ Finset.range n, ‖P.coeff i‖ * R ^ (n - 1) := by
        exact Finset.sum_le_sum (fun i hi => hterm i hi)
      have h3 :
          (∑ i ∈ Finset.range n, ‖P.coeff i‖ * R ^ (n - 1))
            = (∑ i ∈ Finset.range n, ‖P.coeff i‖) * R ^ (n - 1) := by
        simp [Finset.sum_mul]
      have hsum_le : (∑ i ∈ Finset.range n, ‖P.coeff i‖) ≤ S := by
        simp [S]
      calc
        ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖
            ≤ ∑ i ∈ Finset.range n, ‖P.coeff i * z ^ i‖ := h1
        _ ≤ ∑ i ∈ Finset.range n, ‖P.coeff i‖ * R ^ (n - 1) := h2
        _ = (∑ i ∈ Finset.range n, ‖P.coeff i‖) * R ^ (n - 1) := h3
        _ ≤ S * R ^ (n - 1) := by
              exact mul_le_mul_of_nonneg_right hsum_le (pow_nonneg hR_nonneg _)

    -- Leading term real part: `(a * z^n).re = ‖a‖ * R^n`.
    have h_lead_re : (P.coeff n * z ^ n).re = ‖a‖ * R ^ n := by
      -- compute `z^n = (R*w)^n = R^n * w^n`, and `a*w^n = ‖a‖`.
      have hw_pow : w ^ n = wtarget := hw
      have ha_mul : a * w ^ n = (‖a‖ : ℂ) := by
        -- `a*w^n = a*wtarget = ‖a‖`
        have : a * w ^ n = a * wtarget := by simp [hw_pow]
        -- rewrite and use `mul_conj_div_norm`
        simpa [wtarget, a] using (this.trans (mul_conj_div_norm a ha))
      have hz_pow : z ^ n = ((R : ℂ) ^ n) * (w ^ n) := by
        -- `z = (R:ℂ) * w`
        simp [z, mul_pow, mul_comm]
      -- now
      have hcoeffn : P.coeff n = a := by simp [a, n, Polynomial.coeff_natDegree]
      have hreR : ∀ m : ℕ, (((R : ℂ) ^ m).re) = R ^ m := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
            simp [pow_succ, ih, mul_re]
      calc
        (P.coeff n * z ^ n).re
            = (a * z ^ n).re := by simp [hcoeffn]
        _ = (a * (((R : ℂ) ^ n) * (w ^ n))).re := by simp [hz_pow]
        _ = (((R : ℂ) ^ n) * (a * (w ^ n))).re := by
              ring_nf
        _ = (((R : ℂ) ^ n) * (‖a‖ : ℂ)).re := by simp [ha_mul]
        _ = (((R : ℂ) ^ n).re) * ‖a‖ := by
              -- `mul_re` and `((‖a‖:ℂ)).im = 0`
              simp [mul_re]
        _ = (R ^ n) * ‖a‖ := by simp [hreR n]
        _ = ‖a‖ * R ^ n := by ring

    -- Put everything together: real part lower bound.
    refine ⟨z, hz_norm, ?_⟩
    -- Start from `Re(P z) = Re(lower + lead) ≥ Re(lead) - ‖lower‖`.
    have hre_lower : (∑ i ∈ Finset.range n, P.coeff i * z ^ i).re
        ≥ -‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ := by
      -- `Re u ≥ -‖u‖`
      have habs : |(∑ i ∈ Finset.range n, P.coeff i * z ^ i).re|
          ≤ ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ :=
        Complex.abs_re_le_norm _
      have := neg_le_of_abs_le habs
      simpa using this
    have hre_main :
        (P.eval z).re ≥ (P.coeff n * z ^ n).re - ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ := by
      -- `Re(lower + lead) = Re(lower) + Re(lead)`
      have : (P.eval z).re = (∑ i ∈ Finset.range n, P.coeff i * z ^ i).re + (P.coeff n * z ^ n).re := by
        simp [h_eval, add_comm]
      -- use `Re(lower) ≥ -‖lower‖`
      linarith [this, hre_lower]

    -- Now dominate the lower part by `(‖a‖/2) * R^n` for `R ≥ R0`.
    have hR_ge_R0 : R0 ≤ R := hR
    have hR_ge : 2 * S / ‖a‖ ≤ R := le_trans (le_max_right _ _) hR_ge_R0
    have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR_ge1
    have hRpow_pos : 0 < R ^ n := pow_pos hRpos _
    have hn_ge1 : 1 ≤ n := Nat.succ_le_of_lt hn0
    have hpow_le : R ^ (n - 1) ≤ R ^ n := by
      -- monotone in exponent for base ≥ 1
      exact pow_le_pow_right₀ hR_ge1 (Nat.sub_le _ _)
    have hlower_le : S * R ^ (n - 1) ≤ (‖a‖ / 2) * R ^ n := by
      -- from `R ≥ 2*S/‖a‖` we get `S ≤ (‖a‖/2) * R`
      have ha_pos : 0 < ‖a‖ := hnorm_a_pos
      have hS_le : S ≤ (‖a‖ / 2) * R := by
        -- rearrange `2*S/‖a‖ ≤ R` -> `S ≤ (‖a‖/2)*R`
        have : 2 * S ≤ ‖a‖ * R := by
          have := (mul_le_mul_of_nonneg_left hR_ge (by linarith [ha_pos.le] : (0 : ℝ) ≤ ‖a‖))
          -- `(‖a‖) * (2*S/‖a‖) = 2*S`
          have hne : (‖a‖ : ℝ) ≠ 0 := ne_of_gt ha_pos
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hne] using this
        -- divide by 2
        have : S ≤ (‖a‖ * R) / 2 := by linarith
        -- rewrite `(‖a‖*R)/2 = (‖a‖/2)*R`
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
      -- now multiply by `R^(n-1)` and use `R^(n-1) * R = R^n`.
      have : S * R ^ (n - 1) ≤ (‖a‖ / 2) * R * R ^ (n - 1) := by
        have hpow_nonneg : 0 ≤ R ^ (n - 1) := pow_nonneg hR_nonneg _
        exact mul_le_mul_of_nonneg_right hS_le hpow_nonneg
      -- rearrange RHS
      -- `R * R^(n-1) = R^n`
      have hRR : R * R ^ (n - 1) = R ^ n := by
        -- `n = (n-1)+1` when `n>0`
        have : n = (n - 1) + 1 := by
          exact (Nat.sub_add_cancel hn_ge1).symm
        -- rewrite using `pow_succ`
        rw [this, pow_succ]
        ring_nf; grind
      simpa [mul_assoc, hRR] using this

    have hfinal_re :
        (‖a‖ / 2) * R ^ n ≤ (P.eval z).re := by
      -- use `hre_main`, `h_lead_re`, and `‖lower‖ ≤ (‖a‖/2) R^n`
      have hlower' : ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ ≤ (‖a‖ / 2) * R ^ n := by
        exact h_lower_norm.trans hlower_le
      have hlead : (P.coeff n * z ^ n).re = ‖a‖ * R ^ n := by simpa [a] using h_lead_re
      have hre_main' :
          (‖a‖ * R ^ n) - ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ ≤ (P.eval z).re := by
        -- `hre_main` is a `≥` statement; rewrite it
        simpa [hlead] using hre_main
      have hsub :
          (‖a‖ * R ^ n) - (‖a‖ / 2) * R ^ n ≤
            (‖a‖ * R ^ n) - ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ :=
        sub_le_sub_left hlower' (‖a‖ * R ^ n)
      have hsim : (‖a‖ * R ^ n) - (‖a‖ / 2) * R ^ n = (‖a‖ / 2) * R ^ n := by ring
      have : (‖a‖ * R ^ n) - (‖a‖ / 2) * R ^ n ≤ (P.eval z).re :=
        hsub.trans hre_main'
      simpa [hsim] using this
    -- convert `‖a‖` to `‖P.leadingCoeff‖`
    simpa [a] using hfinal_re

/-!
#### Integer-order obstruction for `exp (P.eval)`

If `exp(P)` satisfied an `EntireOfFiniteOrder` bound of exponent `ρ < natDegree P`, then the
previous ray estimate forces a contradiction. Hence `natDegree P ≤ ⌊ρ⌋` whenever
`exp(P)` has order at most `ρ` (with `ρ ≥ 0`).
-/

theorem natDegree_le_floor_of_entireOfFiniteOrder_exp_eval
    {ρ : ℝ} (hρ : 0 ≤ ρ) (P : Polynomial ℂ)
    (hExp : EntireOfFiniteOrder ρ (fun z : ℂ => Complex.exp (Polynomial.eval z P))) :
    P.natDegree ≤ Nat.floor ρ := by
  classical
  by_cases hdeg : P.natDegree = 0
  · -- constant polynomial
    simp [hdeg]
  ·
    have hnpos : 0 < P.natDegree := Nat.pos_of_ne_zero hdeg
    rcases exists_z_norm_eq_re_eval_ge (P := P) hnpos with ⟨R0, hR0pos, hray⟩
    rcases hExp.growth with ⟨C, hCpos, hC⟩
    have hLCpos : 0 < ‖P.leadingCoeff‖ := by
      have hP0 : P ≠ 0 := by
        intro h0
        simp [h0] at hdeg
      have : P.leadingCoeff ≠ 0 := (Polynomial.leadingCoeff_ne_zero).2 hP0
      exact norm_pos_iff.2 this
    let c : ℝ := ‖P.leadingCoeff‖ / 2
    have hcpos : 0 < c := by
      -- `c = ‖leadingCoeff‖ / 2` and `‖leadingCoeff‖ > 0`
      have : (0 : ℝ) < (2 : ℝ) := by norm_num
      exact (div_pos hLCpos this)
    have hn_le_real : (P.natDegree : ℝ) ≤ ρ := by
      by_contra hnlt
      have hnlt' : ρ < (P.natDegree : ℝ) := lt_of_not_ge hnlt
      let δ : ℝ := (P.natDegree : ℝ) - ρ
      have hδ : 0 < δ := sub_pos.2 hnlt'
      let K0 : ℝ := (C * (2 : ℝ) ^ ρ) / c
      have hK0 : ∃ R1, ∀ R ≥ R1, K0 + 1 ≤ R ^ δ := by
        have h : ∀ᶠ R in (atTop : Filter ℝ), K0 + 1 ≤ R ^ δ :=
          (tendsto_atTop.mp (tendsto_rpow_atTop hδ)) (K0 + 1)
        rcases (eventually_atTop.1 h) with ⟨R1, hR1⟩
        exact ⟨R1, hR1⟩
      rcases hK0 with ⟨R1, hR1⟩
      set R : ℝ := max (max R0 1) R1
      have hR_ge_R0 : R0 ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
      have hR_ge1 : (1 : ℝ) ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
      have hR_ge_R1 : R1 ≤ R := le_max_right _ _
      have hR_pos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR_ge1
      have hRδ : K0 + 1 ≤ R ^ δ := hR1 R hR_ge_R1
      rcases hray R hR_ge_R0 with ⟨z, hz_norm, hz_re⟩
      -- Lower bound `Re(P z) ≤ log(1+‖exp(P z)‖)`
      have hlog_lower :
          (P.eval z).re ≤ Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) := by
        have hpos : 0 < ‖Complex.exp (Polynomial.eval z P)‖ := by
          simp
        have hle : ‖Complex.exp (Polynomial.eval z P)‖ ≤ 1 + ‖Complex.exp (Polynomial.eval z P)‖ := by
          linarith [norm_nonneg (Complex.exp (Polynomial.eval z P))]
        have hlog_le : Real.log ‖Complex.exp (Polynomial.eval z P)‖
            ≤ Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) :=
          Real.log_le_log hpos hle
        have hlog_eq : Real.log ‖Complex.exp (Polynomial.eval z P)‖ = (P.eval z).re := by
          simp [Complex.norm_exp]
        simpa [hlog_eq] using hlog_le
      have hlog_upper :
          Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) ≤ C * (1 + ‖z‖) ^ ρ :=
        hC z
      have hmain : c * R ^ (P.natDegree : ℝ) ≤ C * (1 + R) ^ ρ := by
        have hz_re' : c * R ^ P.natDegree ≤ (P.eval z).re := by
          simpa [c] using hz_re
        have hz_re'' : c * R ^ (P.natDegree : ℝ) ≤ (P.eval z).re := by
          -- rewrite nat power as rpow
          simpa [Real.rpow_natCast, c] using hz_re'
        have : c * R ^ (P.natDegree : ℝ) ≤ Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) :=
          hz_re''.trans hlog_lower
        have : c * R ^ (P.natDegree : ℝ) ≤ C * (1 + ‖z‖) ^ ρ :=
          this.trans hlog_upper
        simpa [hz_norm] using this
      -- bound `(1+R)^ρ ≤ (R*2)^ρ = R^ρ * 2^ρ`
      have h1R_le : (1 + R : ℝ) ≤ R * 2 := by linarith
      have hpow1 : (1 + R : ℝ) ^ ρ ≤ (R * 2) ^ ρ :=
        Real.rpow_le_rpow (by linarith [hR_pos.le]) h1R_le hρ
      have hR2 : (R * 2) ^ ρ = R ^ ρ * (2 : ℝ) ^ ρ := by
        have hRnonneg : 0 ≤ R := le_of_lt hR_pos
        have h2nonneg : 0 ≤ (2 : ℝ) := by norm_num
        simpa [mul_assoc] using (Real.mul_rpow hRnonneg h2nonneg (z := ρ))
      have hmain' : c * R ^ (P.natDegree : ℝ) ≤ C * (R ^ ρ * (2 : ℝ) ^ ρ) := by
        have := le_trans hmain (mul_le_mul_of_nonneg_left hpow1 (le_of_lt hCpos))
        simpa [hR2, mul_assoc, mul_left_comm, mul_comm] using this
      -- Divide by `R^ρ` and by `c` to get `R^δ ≤ K0`, contradicting `K0+1 ≤ R^δ`.
      have hRρ_pos : 0 < R ^ ρ := Real.rpow_pos_of_pos hR_pos _
      have hRρ_ne : (R ^ ρ : ℝ) ≠ 0 := ne_of_gt hRρ_pos
      have hdiv :
          c * (R ^ (P.natDegree : ℝ) / R ^ ρ) ≤ C * (2 : ℝ) ^ ρ := by
        have h :=
            div_le_div_of_nonneg_right hmain' (le_of_lt hRρ_pos)
        have hRhs : (C * (R ^ ρ * (2 : ℝ) ^ ρ)) / (R ^ ρ) = C * (2 : ℝ) ^ ρ := by
          field_simp [hRρ_ne]
        have hLhs :
            (c * R ^ (P.natDegree : ℝ)) / (R ^ ρ)
              = c * (R ^ (P.natDegree : ℝ) / R ^ ρ) := by
          ring
        aesop
      have hRsub : R ^ δ = R ^ (P.natDegree : ℝ) / R ^ ρ := by
        -- `R^((n)-ρ) = R^n / R^ρ`
        simpa [δ] using (Real.rpow_sub hR_pos (P.natDegree : ℝ) ρ)
      have hRδ_le : c * (R ^ δ) ≤ C * (2 : ℝ) ^ ρ := by
        simpa [hRsub] using hdiv
      have hRδ_le' : R ^ δ ≤ K0 := by
        -- divide by positive `c` using `le_div_iff₀`
        have : R ^ δ ≤ (C * (2 : ℝ) ^ ρ) / c := by
          -- `R^δ ≤ (C*2^ρ)/c` ↔ `R^δ * c ≤ C*2^ρ`
          refine (le_div_iff₀ hcpos).2 ?_
          -- rewrite to match `hRδ_le`
          simpa [mul_assoc, mul_left_comm, mul_comm] using hRδ_le
        simpa [K0] using this
      have : K0 + 1 ≤ K0 := le_trans hRδ (le_trans hRδ_le' (le_rfl))
      exact (not_lt_of_ge this) (lt_add_of_pos_right _ (by norm_num : (0 : ℝ) < 1))
    exact (Nat.le_floor_iff hρ).2 hn_le_real


/--
**Poisson-Jensen Upper Bound for Entire Functions**

If `H` is entire and zero-free, then `log |H(z)|` is bounded by the characteristic function
`T(R, H)` via the Poisson kernel estimate. Note that for zero-free functions, `N(r, H) = 0`,
so `T(r, H) = m(r, H)`.
-/
lemma log_norm_le_characteristic {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hH_nz : ∀ z, H z ≠ 0) (z : ℂ) (R : ℝ) (hR : ‖z‖ < R) :
    Real.log ‖H z‖ ≤ (R + ‖z‖) / (R - ‖z‖) * characteristic H ⊤ R := by
  -- u(w) = log |H(w)| is harmonic because H is entire and zero-free
  let u := fun w => Real.log ‖H w‖
  have hu_harm : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall 0 R) := by
    intro w _
    exact (hH.analyticAt w).harmonicAt_log_norm (hH_nz w)
  -- Apply the Poisson upper bound for harmonic functions:
  -- u(z) ≤ Avg(P * u⁺) (since u⁻ ≥ 0 and P ≥ 0).
  -- The max of the Poisson kernel P(z, ζ) is (R+|z|)/(R-|z|).
  have h_bound := InnerProductSpace.HarmonicOnNhd.poisson_upper_bound
    (f := u) (R := R) (z := z) (by linarith [norm_nonneg z]) hR hu_harm
  -- Relate circle average of u⁺ to the characteristic function
  -- proximity H ⊤ R = circleAverage (log⁺ |H|) = circleAverage (u⁺)
  have h_prox : proximity H ⊤ R = circleAverage (fun w => max (u w) 0) 0 R := by
    simp only [proximity, u, Real.posLog_def, max_comm]
    rfl
  -- For entire zero-free H, characteristic = proximity (since N(r, H) = 0)
  have h_char : characteristic H ⊤ R = proximity H ⊤ R := by
    rw [characteristic, logCounting_top_eq_zero_of_entire hH, add_zero]
  -- Combine estimates
  rw [h_char, h_prox]
  refine h_bound.trans ?_
  gcongr



end Hadamard
end ComplexAnalysis
