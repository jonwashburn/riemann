import TwoChart_WeylKernelSchur
import TwoChart_WeylRemainderKernel

/-!
# `L²` Schur bound for Weyl kernels from `SmΛ`-type bounds

This file ties together:

* the IBP kernel estimate `norm_weylKernelIcc_le_explicit_hinv` from
  `TwoChart_WeylRemainderKernel.lean`,
* the Schur-data constructor from `TwoChart_WeylKernelSchur.lean`, and
* the abstract `L²` Schur test `schur_l2Energy_le` from `TwoChart_SchurTest.lean`.

We keep the smoothness/interval-integrability hypotheses from the IBP lemma explicit; the
`SmΛ` theory built so far only supplies the uniform derivative bounds on compact `τ`-intervals.
-/

namespace TwoChartEgorov

open scoped Real BigOperators
open MeasureTheory

noncomputable section

section TrivialKernelBound

variable {a : ℝ → ℝ → ℝ → ℂ}
variable {h t tp R : ℝ}

/-- A “no IBP” (trivial) kernel bound: the oscillatory factor has unit norm. -/
theorem norm_weylKernelIcc_le_trivial
    (h_ne : h ≠ 0)
    {C : ℝ} (hC : 0 ≤ C)
    (hBound : ∀ τ ∈ Set.Icc (-R) R, ‖a h ((t + tp) / 2) τ‖ ≤ C)
    (hInt : IntervalIntegrable (fun τ => phase h t tp τ * a h ((t + tp)/2) τ) volume (-R) R) :
    ‖weylKernelIcc a h t tp R‖ ≤ |(2 * Real.pi * h)⁻¹| * (2*R) * C := by
  -- Pull out the scalar factor and bound the interval integral.
  have hphase : ∀ τ : ℝ, ‖phase h t tp τ‖ = 1 := by
    intro τ
    -- `phase` is a complex exponential of an imaginary number.
    simp [phase, Complex.abs_exp]
  have hI :
      ‖∫ τ in (-R)..R, phase h t tp τ * a h ((t + tp)/2) τ‖ ≤ (2*R) * C := by
    -- apply the uniform `Icc` bound lemma from `TwoChart_WeylRemainderKernel.lean`
    have hBound' : ∀ τ ∈ Set.Icc (-R) R, ‖phase h t tp τ * a h ((t + tp) / 2) τ‖ ≤ C := by
      intro τ hτ
      -- `‖phase‖ = 1`
      simpa [norm_mul, hphase τ] using (le_trans (by
        have := hBound τ hτ
        exact this) (le_rfl))
    -- reuse the existing lemma `intervalIntegral_norm_le_two_mul_R_mul_const`
    simpa using (intervalIntegral_norm_le_two_mul_R_mul_const (f := fun τ =>
      phase h t tp τ * a h ((t + tp)/2) τ) (R := R) (C := C) (hC := hC) hBound')
  -- Finish.
  have : weylKernelIcc a h t tp R = (2 * Real.pi * h)⁻¹ *
      ∫ τ in (-R)..R, phase h t tp τ * a h ((t + tp)/2) τ := by
    simp [weylKernelIcc]
  -- Take norms.
  calc
    ‖weylKernelIcc a h t tp R‖
        = ‖(2 * Real.pi * h)⁻¹ *
            ∫ τ in (-R)..R, phase h t tp τ * a h ((t + tp)/2) τ‖ := by
              simp [this]
    _ ≤ ‖(2 * Real.pi * h)⁻¹‖ * ‖∫ τ in (-R)..R, phase h t tp τ * a h ((t + tp)/2) τ‖ := by
          simpa [norm_mul] using (norm_mul_le _ _)
    _ ≤ ‖(2 * Real.pi * h)⁻¹‖ * ((2*R) * C) := by
          gcongr
    _ = |(2 * Real.pi * h)⁻¹| * (2*R) * C := by
          simp [Real.norm_eq_abs, mul_assoc, mul_left_comm, mul_comm]

end TrivialKernelBound

section SchurMajorantForWeylKernel

variable {a : ℝ → ℝ → ℝ → ℂ}
variable {h t tp R : ℝ}

/-- A convenient “Schur-majorant” form: if we have both a trivial bound and an IBP bound,
we can dominate the kernel by the integrable profile `schurDecay` (up to an explicit constant). -/
theorem norm_weylKernelIcc_le_schurDecay_of_two_bounds
    (h_ne : h ≠ 0)
    {N : ℕ} (hN : 2 ≤ N)
    {C0 C1 : ℝ} (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (htriv : ‖weylKernelIcc a h t tp R‖ ≤ C0)
    (hibp : t ≠ tp → ‖weylKernelIcc a h t tp R‖ ≤ C1 * (|h| / |t - tp|) ^ N) :
    ‖weylKernelIcc a h t tp R‖ ≤ (max C0 C1) * (Real.sqrt 2) ^ N * schurDecay N ((t - tp) / h) := by
  classical
  by_cases hdiag : t = tp
  · -- on the diagonal, use the trivial bound and `schurDecay(...)=1`.
    subst hdiag
    have : schurDecay N ((t - t)/h) = 1 := by simp [schurDecay]
    have hmax : C0 ≤ max C0 C1 := le_max_left _ _
    have hsqrt : 0 ≤ (Real.sqrt 2) ^ N := by
      have : 0 ≤ Real.sqrt 2 := by exact Real.sqrt_nonneg _
      exact pow_nonneg this N
    have hdec_nonneg : 0 ≤ schurDecay N 0 := schurDecay_nonneg (h_ne := h_ne) N 0
    calc
      ‖weylKernelIcc a h t t R‖ ≤ C0 := htriv
      _ ≤ (max C0 C1) * ((Real.sqrt 2) ^ N * schurDecay N 0) := by
            nlinarith [hmax, hsqrt, hdec_nonneg]
      _ = (max C0 C1) * (Real.sqrt 2) ^ N * schurDecay N ((t - t) / h) := by
            simp [mul_assoc, this]
  · -- off-diagonal: combine the two bounds by `min` and compare to `schurProfile`.
    have h1 : ‖weylKernelIcc a h t tp R‖ ≤ max C0 C1 := le_trans htriv (le_max_left _ _)
    have h2 : ‖weylKernelIcc a h t tp R‖ ≤ max C0 C1 * (|h| / |t - tp|) ^ N := by
      have hmax : C1 ≤ max C0 C1 := le_max_right _ _
      have : ‖weylKernelIcc a h t tp R‖ ≤ C1 * (|h| / |t - tp|) ^ N := hibp (by exact hdiag)
      exact le_trans this (by
        have hn : 0 ≤ (|h| / |t - tp|) ^ N := by
          exact pow_nonneg (by exact div_nonneg (abs_nonneg _) (abs_nonneg _)) _
        nlinarith [hmax, hn])
    -- thus `≤ max C0 C1 * min(1, (|h|/|t-tp|)^N)`.
    have hmin :
        ‖weylKernelIcc a h t tp R‖
          ≤ (max C0 C1) * (min (1:ℝ) ((|h| / |t - tp|) ^ N)) := by
      have hmin' : ‖weylKernelIcc a h t tp R‖ ≤ min (max C0 C1) (max C0 C1 * (|h| / |t - tp|) ^ N) :=
        le_min h1 h2
      -- factor `max C0 C1`
      have hfact : min (max C0 C1) (max C0 C1 * (|h| / |t - tp|) ^ N)
            = (max C0 C1) * min (1:ℝ) ((|h| / |t - tp|) ^ N) := by
        by_cases hmx : max C0 C1 = 0
        · simp [hmx]
        · have hmx0 : 0 < max C0 C1 := lt_of_le_of_ne (le_max_left _ _) (Ne.symm hmx)
          -- standard algebraic identity for positive factors:
          -- `min A (A*B) = A * min 1 B` when `A>0`.
          -- We use `min_mul_left` lemma.
          simpa [mul_assoc] using (min_mul_left (max C0 C1) (1:ℝ) ((|h|/|t-tp|)^N))
      simpa [hfact, mul_assoc] using hmin'
    -- identify the profile as `schurProfile` of the scaled variable.
    have hprof :
        min (1:ℝ) ((|h| / |t - tp|) ^ N) = schurProfile N ((t - tp) / h) := by
      -- since `t ≠ tp`, the `if` branch in `schurProfile` is inactive, and algebra shows equality.
      have : ((t - tp) / h) ≠ 0 := by
        intro hzero
        have : t - tp = 0 := by
          have : (t - tp) = h * 0 := by
            simpa [div_eq_mul_inv] using congrArg (fun z => z * h) hzero
          simpa using this
        exact hdiag (sub_eq_zero.mp this)
      -- `| (t-tp)/h |^{-N} = (|h|/|t-tp|)^N`.
      -- (simple rewrite with absolute values).
      simp [schurProfile, this, abs_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg, pow_two]
    -- compare to `schurDecay`
    have hcomp : schurProfile N ((t - tp) / h) ≤ (Real.sqrt 2) ^ N * schurDecay N ((t - tp) / h) :=
      schurProfile_le_sqrtTwoPow_mul_schurDecay (N := N) ((t - tp) / h)
    -- finish
    calc
      ‖weylKernelIcc a h t tp R‖
          ≤ (max C0 C1) * schurProfile N ((t - tp) / h) := by
                simpa [hprof, mul_assoc] using hmin
      _ ≤ (max C0 C1) * ((Real.sqrt 2) ^ N * schurDecay N ((t - tp) / h)) := by
            gcongr
      _ = (max C0 C1) * (Real.sqrt 2) ^ N * schurDecay N ((t - tp) / h) := by
            ring

end SchurMajorantForWeylKernel

end TwoChartEgorov
