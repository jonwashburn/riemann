import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Gamma
import Mathlib.Analysis.SpecialFunctions.Trigonometric
import Mathlib.NumberTheory.ZetaFunction
import rh.RS.SchurGlobalization

namespace RH.Blockers

open Complex

/-!
Blockers triage: formal statements for items recorded in BLOCKERS.md.
-/

-- Trivial zeros classification (to be supplied or cited when available)
theorem zeta_zero_in_Re_le_zero_is_trivial
    (z : ℂ) (hz : z.re ≤ 0) (hzero : riemannZeta z = 0) :
    ∃ n : ℕ, 0 < n ∧ z = (-2 : ℂ) * (n : ℂ) := by
  classical
  -- Functional equation specialized at 1 - z:
  -- ζ(z) = 2^z π^{z-1} sin(π z/2) Γ(1-z) ζ(1-z)
  have h_fe :
      riemannZeta z
        = (2 : ℂ) ^ z * (Real.pi : ℂ) ^ (z - 1)
            * Complex.sin ((Real.pi : ℂ) * z / 2)
            * Complex.Gamma (1 - z) * riemannZeta (1 - z) := by
    -- Using `riemannZeta_one_sub (1 - z)` and simplifying
    simpa [one_sub_sub, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (riemannZeta_one_sub (1 - z))
  -- Nonvanishing of the reflected factor on Re(1 - z) ≥ 1
  have h_refl_nonzero : riemannZeta (1 - z) ≠ 0 := by
    have h_re : (1 : ℝ) ≤ (1 - z).re := by
      -- (1 - z).re = 1 - z.re ≥ 1 - 0 = 1
      simpa [Complex.sub_re, Complex.one_re] using (sub_le_sub_left hz 1)
    simpa using riemannZeta_ne_zero_of_one_le_re (s := (1 - z)) h_re
  -- Gamma has no zeros on ℂ
  have h_gamma_ne : Complex.Gamma (1 - z) ≠ 0 := Complex.Gamma_ne_zero (1 - z)
  -- Nonzero of cpow factors (exp never vanishes)
  have h_two_cpow_ne : (2 : ℂ) ^ z ≠ 0 := Complex.cpow_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
  have h_pi_cpow_ne : (Real.pi : ℂ) ^ (z - 1) ≠ 0 :=
    Complex.cpow_ne_zero (by exact_mod_cast (ne_of_gt Real.pi_pos))
  -- If sin ≠ 0 then RHS ≠ 0 ⇒ ζ z ≠ 0, contradicting hzero
  have h_sin_eq_zero : Complex.sin ((Real.pi : ℂ) * z / 2) = 0 := by
    by_contra hsin
    have hprod_ne :
        (2 : ℂ) ^ z * (Real.pi : ℂ) ^ (z - 1)
          * Complex.sin ((Real.pi : ℂ) * z / 2)
          * Complex.Gamma (1 - z) * riemannZeta (1 - z) ≠ 0 := by
      have hAB : (2 : ℂ) ^ z * (Real.pi : ℂ) ^ (z - 1) ≠ 0 :=
        mul_ne_zero h_two_cpow_ne h_pi_cpow_ne
      have hABS : (2 : ℂ) ^ z * (Real.pi : ℂ) ^ (z - 1)
          * Complex.sin ((Real.pi : ℂ) * z / 2) ≠ 0 :=
        mul_ne_zero hAB hsin
      have hABSG :
          (2 : ℂ) ^ z * (Real.pi : ℂ) ^ (z - 1)
            * Complex.sin ((Real.pi : ℂ) * z / 2)
            * Complex.Gamma (1 - z) ≠ 0 :=
        mul_ne_zero hABS h_gamma_ne
      exact mul_ne_zero hABSG h_refl_nonzero
    -- From functional equation, ζ z = RHS; contradiction
    have : riemannZeta z ≠ 0 := by simpa [h_fe] using hprod_ne
    exact this hzero
  -- Zeros of sin are integer multiples of π: π z / 2 = k π ⇒ z = 2k
  obtain ⟨k : ℤ, hk⟩ := Complex.sin_eq_zero_iff.mp h_sin_eq_zero
  -- Multiply both sides of (π z / 2 = k π) by 2/π to get z = 2k
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hz_int : z = (2 : ℂ) * (k : ℤ) := by
    -- (π z) / 2 = k π  ⇒  (π/2) z = k π ⇒ z = (2/π) (k π) = 2 k
    have hk' : ((Real.pi : ℂ) / 2) * z = (k : ℤ) * (Real.pi : ℂ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hk
    have h2_ne : (2 : ℂ) ≠ 0 := by norm_num
    have hπ2_ne : (Real.pi : ℂ) / 2 ≠ 0 := by
      -- pi/2 ≠ 0 since pi ≠ 0
      have : (2 : ℂ) ≠ 0 := by norm_num
      have : (Real.pi : ℂ) * (2 : ℂ) ≠ 0 := mul_ne_zero hpi_ne this
      -- simpler: division by nonzero is nonzero
      simpa [div_eq_mul_inv] using mul_ne_zero hpi_ne (by norm_num : (2 : ℂ) ≠ 0)
    -- Left-cancel by (π/2) and right-cancel by π
    have := congrArg (fun w => (2 : ℂ) / (Real.pi : ℂ) * w) hk'
    -- Simplify to obtain z = 2 k
    have hleft : (2 : ℂ) / (Real.pi : ℂ) * ((Real.pi : ℂ) / 2) = (1 : ℂ) := by
      field_simp [div_eq_mul_inv, hpi_ne]
    have hright : (2 : ℂ) / (Real.pi : ℂ) * ((k : ℤ) * (Real.pi : ℂ)) = (2 : ℂ) * (k : ℤ) := by
      field_simp [div_eq_mul_inv, hpi_ne, mul_comm, mul_left_comm, mul_assoc]
    simpa [hleft, hright] using this
  -- From hz and z = 2k, deduce k ≤ 0, so write k = -n with n ≥ 1 (exclude 0 via ζ(0) ≠ 0)
  have hk_real : z.im = 0 := by
    -- z = 2k is purely real
    have : (2 : ℂ) * (k : ℤ) ∈ Set.range (fun r : ℝ => (r : ℂ)) := by
      refine ⟨(2 : ℝ) * (k : ℤ), ?_⟩
      simp
    simpa [hz_int] using Complex.imag_of_real ((2 : ℝ) * (k : ℤ))
  have hk_le : (k : ℤ) ≤ 0 := by
    -- z.re = 2k ≤ 0 ⇒ k ≤ 0
    have : z.re = (2 : ℝ) * (k : ℤ) := by
      simpa [hz_int] using congrArg Complex.re hz_int
    have : (2 : ℝ) * (k : ℤ) ≤ 0 := by simpa [this]
    have h2pos : (0 : ℝ) < 2 := by norm_num
    have hk' : (k : ℤ) ≤ 0 := by
      have := (mul_le_mul_left_of_nonneg (le_of_lt h2pos)).1 this
      -- division by 2 on ℝ
      simpa using (le_of_mul_le_mul_left this h2pos)
    exact hk'
  -- Express k = -n with n ≥ 0, and exclude n = 0 using ζ(0) ≠ 0
  rcases Int.le.dest hk_le with ⟨n, hn, hk_eq⟩
  -- k = -n with n ≥ 0
  have hz_neg_even : z = (-2 : ℂ) * (n : ℂ) := by
    simpa [hz_int, hk_eq, two_mul, Int.cast_neg, Int.cast_ofNat, mul_comm, mul_left_comm, mul_assoc]
  -- Exclude n = 0 using ζ(0) = -1/2 ≠ 0
  have h_n_pos : 0 < n := by
    by_contra hzero_n
    have : z = 0 := by simpa [hzero_n, hz_neg_even] using rfl
    have : riemannZeta 0 = 0 := by simpa [this] using hzero
    -- mathlib: ζ(0) = -1 / 2
    have : riemannZeta 0 = (-((1 : ℝ) / 2) : ℂ) := by
      simpa using riemannZeta_zero
    -- contradiction since -1/2 ≠ 0
    have : ((-((1 : ℝ) / 2) : ℂ) = 0) := by simpa [this]
    simpa using this
  exact ⟨n, h_n_pos, hz_neg_even⟩

/-!
Convenience wrappers: trivial zeros at negative even integers from mathlib.
These are usable immediately while full classification remains a blocker.
-/

@[simp] lemma zeta_trivial_zero (n : ℕ) :
    riemannZeta ((-2 : ℂ) * ((n + 1 : ℕ) : ℂ)) = 0 := by
  simpa using riemannZeta_neg_two_mul_nat_add_one n

lemma zeta_eq_zero_of_neg_even {s : ℂ}
    (h : ∃ n : ℕ, s = (-2 : ℂ) * ((n + 1 : ℕ) : ℂ)) :
    riemannZeta s = 0 := by
  rcases h with ⟨n, rfl⟩
  simpa using riemannZeta_neg_two_mul_nat_add_one n

-- Non-vanishing on the boundary line Re(s) = 1 (handled by Schur route)
theorem zeta_nonvanishing_on_Re_eq_one
    (z : ℂ) (hz : z.re = 1) : riemannZeta z ≠ 0 := by
  exact RH.RS.ZetaNoZerosOnRe1FromSchur z hz

end RH.Blockers
