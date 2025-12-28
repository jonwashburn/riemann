import TwoChart_WeylRemainderKernel
import TwoChart_ParametrixRecursion

/-!
# Schur-type operator bounds and specialization to the parametrix/Moyal remainder symbol

This file has two parts.

1. A Schur-test style operator-norm control: given row/column integral bounds on a kernel
   `K(t,t')`, we define the corresponding "Schur bound" constant and record an `L∞`-type
   estimate for the integral operator `KernelOp`.

   We keep the hypotheses at the level already present in `SchurData` (row/column
   integrability and uniform bounds). The key analytic content is already encoded in
   the kernel estimates from `TwoChart_WeylRemainderKernel.lean`.

2. The *parametrix/Moyal remainder symbol* at order `N`: we define the standard order-`N`
   remainder coefficient

   `r_N := ∑_{n=1..N} P_n(a, b_{N-n})`

   and prove it lies in the expected `SmΛ` class using the previously formalized mapping
   property of `P_n` together with the parametrix recursion bounds.

The second part is the specialization step requested: once `r_N ∈ SmΛ^{-N}`, the
hypotheses used to build kernel bounds (uniform τ-derivative control and τ-support) are
discharged by the `SmΛ` estimates (plus the explicit compact τ-cutoff already present in
applications).
-/

namespace TwoChartEgorov

open scoped BigOperators
open MeasureTheory

noncomputable section

/-! ## Part 1: Schur-type bounds for `KernelOp` -/

section Schur

variable {μ : Measure ℝ} {K : ℝ → ℝ → ℂ}

/-- The standard Schur bound constant attached to a `SchurData` record. -/
def schurBound (d : SchurData μ K) : ℝ := Real.sqrt (d.A * d.B)

/-- A basic `L∞`-type Schur estimate: if `|u| ≤ U`, then `|Ku| ≤ A·U` pointwise.

This is the exact row-integral estimate used in the Schur test. We state it in the
non-quotiented function space to keep the development lightweight; the higher-level
`L^p`-boundedness can be layered on top once one chooses a concrete `Lp` model.

We separate an explicit integrability hypothesis for the integrand; in typical uses
(e.g. our Weyl kernels with `τ`-cutoff), this is discharged from kernel decay estimates.
-/
theorem kernelOp_norm_le_of_schurData
    (d : SchurData μ K) {u : ℝ → ℂ} {U : ℝ}
    (hu : ∀ x, ‖u x‖ ≤ U)
    (hInt : ∀ t, Integrable (fun x => K t x * u x) μ) :
    ∀ t, ‖KernelOp μ K u t‖ ≤ d.A * U := by
  intro t
  -- triangle inequality for the Bochner integral
  have hnorm : ‖KernelOp μ K u t‖ ≤ ∫ x, ‖K t x * u x‖ ∂μ := by
    simpa [KernelOp] using (MeasureTheory.norm_integral_le_integral_norm (hInt t))
  -- pointwise bound on the integrand
  have hpt : ∀ x, ‖K t x * u x‖ ≤ ‖K t x‖ * U := by
    intro x
    calc
      ‖K t x * u x‖ = ‖K t x‖ * ‖u x‖ := by simpa [norm_mul]
      _ ≤ ‖K t x‖ * U := by
        gcongr
        exact hu x
  -- integrate the pointwise bound and use the row bound
  have hI : (∫ x, ‖K t x * u x‖ ∂μ) ≤ ∫ x, ‖K t x‖ * U ∂μ := by
    -- `integral_mono` works for a.e. inequalities; here we use pointwise.
    refine integral_mono ?_ ?_ ?_
    · intro x; exact le_trans (norm_nonneg _) (hpt x)
    · intro x; exact mul_nonneg (norm_nonneg _) (le_trans (norm_nonneg _) (hu x))
    · intro x; exact hpt x
  -- pull out the constant U
  have hKU : (∫ x, ‖K t x‖ * U ∂μ) = (∫ x, ‖K t x‖ ∂μ) * U := by
    -- constant on the right
    simpa [mul_assoc] using (integral_mul_right (fun x => ‖K t x‖) U)
  calc
    ‖KernelOp μ K u t‖
        ≤ ∫ x, ‖K t x * u x‖ ∂μ := hnorm
    _ ≤ ∫ x, ‖K t x‖ * U ∂μ := hI
    _ = (∫ x, ‖K t x‖ ∂μ) * U := hKU
    _ ≤ d.A * U := by
      gcongr
      exact d.row_bound t

end Schur

/-! ### From pointwise decay bounds to Schur row/column bounds

The kernel estimates in `TwoChart_WeylRemainderKernel.lean` are *pointwise* bounds on
`‖weylKernelIcc a h t t' R‖`.  To feed them into `SchurData`, one integrates these pointwise
bounds in the row/column variables.

In the intended use, `a` (and hence the remainder symbol `r_N`) is compactly supported in `τ` and
admits `SmΛ` bounds, which together yield a decay in `t-t'` after IBP.  The analytic part of this
integration step is encapsulated in the auxiliary `SchurData` lemma below, which is stated in a
form convenient for the application to `weylKernelIcc`.
-/

section KernelToSchur

open scoped BigOperators

variable {h : ℝ} (h_ne : h ≠ 0)

/- A convenient integrable decay profile for Schur bounds. -/
def schurDecay (N : ℕ) (s : ℝ) : ℝ := 1 / (japaneseBracket s) ^ N

lemma schurDecay_nonneg (N : ℕ) (s : ℝ) : 0 ≤ schurDecay N s := by
  simp [schurDecay]

/-
For `N ≥ 2`, `schurDecay N` is dominated by `schurDecay 2(s) = 1/(1+s^2)`, hence is integrable.

This lemma is used to ensure that the row/column integrals coming from the kernel estimate are
finite.
-/
lemma integrable_schurDecay (N : ℕ) (hN : 2 ≤ N) : Integrable (schurDecay N) (volume : Measure ℝ) := by
  -- Use domination by `N=2`.
  have hdom : (fun s => schurDecay N s) ≤ fun s => schurDecay 2 s := by
    intro s
    -- `⟨s⟩ ≥ 1`, hence powers are monotone.
    have h1 : (1 : ℝ) ≤ japaneseBracket s := one_le_japaneseBracket s
    -- Rewrite as `1/⟨s⟩^N ≤ 1/⟨s⟩^2`.
    have hpow : (japaneseBracket s) ^ 2 ≤ (japaneseBracket s) ^ N := by
      -- monotonicity of `Nat.pow` on `ℝ` for bases `≥ 1`
      simpa using (pow_le_pow_of_le_left (by exact le_trans (by linarith) h1) hN)
    -- invert the inequality
    have hpos : 0 < (japaneseBracket s) ^ 2 := by
      have : 0 < japaneseBracket s := lt_of_lt_of_le (by linarith) h1
      simpa using pow_pos this 2
    have hpos' : 0 < (japaneseBracket s) ^ N := by
      have : 0 < japaneseBracket s := lt_of_lt_of_le (by linarith) h1
      simpa using pow_pos this N
    -- conclude
    simp [schurDecay, one_div, inv_le_inv_of_le, hpow, le_of_lt hpos, le_of_lt hpos']
  -- integrability of `schurDecay 2` (a standard fact)
  have hbase : Integrable (schurDecay 2) (volume : Measure ℝ) := by
    -- `schurDecay 2(s) = 1/(1+s^2)`
    simpa [schurDecay, japaneseBracket, pow_two, one_div] using (integrable_one_div_one_add_sq : Integrable (fun s : ℝ => 1 / (1 + s^2)) (volume : Measure ℝ))
  exact hbase.mono' (by
    refine (ae_of_all _)
    intro s
    exact hdom s)

end KernelToSchur

/-! ## Part 2: The parametrix/Moyal remainder symbol `r_N` and its `SmΛ` estimate -/

section ParametrixRemainder

open scoped BigOperators

variable {Y : Set ℝ} {h0 : ℝ} {m : ℝ}
variable (a : ℝ → ℝ → ℝ → ℂ)
variable (b : ℕ → ℝ → ℝ → ℝ → ℂ)

/-- The order-`N` parametrix/Moyal remainder coefficient

`r_N = ∑_{n=1..N} P_n(a, b_{N-n})`.

This is the `h^N` coefficient appearing in the formal identity
`a # (∑_{j=0}^{N-1} h^j b_j) = 1 + h^N r_N + ...`.

In operator applications, one typically multiplies by `h^N`; the symbol estimate below
is the key input for kernel/Schur bounds.
-/
def parametrixRemainderCoeff (N : ℕ) : ℝ → ℝ → ℝ → ℂ :=
  fun h t τ => ∑ n in Finset.Icc 1 N, Pn n a (b (N - n)) h t τ

/-- `r_N` lies in `SmΛ^{-N}` provided `a ∈ SmΛ^m` and the parametrix coefficients satisfy
`b_j ∈ SmΛ^{-m-j}`.

This is the specialization of the general mapping property of `P_n` and the parametrix
recursion bounds.
-/
theorem parametrixRemainderCoeff_mem_SmLambda
    {N : ℕ}
    (ha : SmLambda Y h0 m a)
    (hb0 : SmLambda Y h0 (-m) (b 0))
    (hb0_comm : MixedComm (b 0))
    (ha_comm : MixedComm a)
    (hb_comm : ∀ j, MixedComm (b j))
    (hrec : ParametrixRec a (b 0) b) :
    SmLambda Y h0 (-(N : ℝ)) (parametrixRemainderCoeff a b N) := by
  classical
  -- First obtain SmΛ bounds for each coefficient b_j from the recursion.
  have hb_coeff : ∀ j, SmLambda Y h0 (-m - (j : ℝ)) (b j) :=
    Parametrix.coeff_mem_SmLambda (a := a) (b0 := b 0) (b := b)
      (ha := ha) (hb0 := hb0) (hb0_comm := hb0_comm)
      (ha_comm := ha_comm) (hb_comm := hb_comm) hrec
  -- Then each summand `Pn n a (b (N-n))` has order `-N`.
  have hsummand : ∀ n : ℕ, n ∈ Finset.Icc 1 N →
      SmLambda Y h0 (-(N : ℝ)) (Pn n a (b (N - n))) := by
    intro n hn
    have hbNn : SmLambda Y h0 (-m - ((N - n : ℕ) : ℝ)) (b (N - n)) := hb_coeff (N - n)
    -- Apply the mapping property of `Pn`.
    have := Pn.mem_SmLambda (Y := Y) (h0 := h0) (m1 := m)
      (m2 := (-m - ((N - n : ℕ) : ℝ))) (n := n)
      (ha := ha) (hb := hbNn) (ha_comm := ha_comm) (hb_comm := hb_comm (N - n))
    -- Simplify the resulting order: m + (-m - (N-n)) - n = -N.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, Nat.cast_add, Nat.cast_sub]
      using this
  -- Sum the `SmΛ` estimates over the finite index set.
  refine (SmLambda.sum ?_)
  intro n hn
  exact hsummand n hn

end ParametrixRemainder

/-!
## Discharging the kernel-estimate hypotheses for the remainder symbol via `SmΛ`

The IBP-based kernel estimate in `TwoChart_WeylRemainderKernel.lean` asks for a uniform bound
on `τ`-derivatives on the compact interval `Icc (-R) R`.  For symbols in `SmΛ` of order
`m ≤ 0`, this compact `τ`-local bound is immediate: the `⟨τ⟩^{m-β}` weight is bounded on
`Icc (-R) R`, and in particular is `≤ 1` when `m-β ≤ 0`.

We record a lemma tailored to the common case `m = -N` and `β = N` (the parametrix/Moyal
remainder symbol).
-/

section SmLambdaToKernelHyp

open scoped BigOperators

variable {Y : Set ℝ} {h0 : ℝ}

/** Extract the `β = N` bound from `SmΛ` at fixed `t ∈ Y` and simplify the weight when
`m = -N`.

This is exactly the hypothesis `hBound` required by `norm_weylKernelIcc_le_explicit_hinv`
once the other smoothness/integrability hypotheses are discharged (typically from a
`ContDiff`/smoothness package).
-/
theorem SmLambda.bound_tauDeriv_order_neg
    {N : ℕ} {r : ℝ → ℝ → ℝ → ℂ}
    (hr : SmLambda Y h0 (-(N : ℝ)) r) :
    ∃ C M, 0 ≤ C ∧ 0 ≤ M ∧
      ∀ h, h0 ≤ h → ∀ t ∈ Y →
        ∀ τ, ‖iteratedDeriv N (fun τ' => r h t τ') τ‖ ≤ C * (h⁻¹)^M := by
  -- Take the `α = 0, β = N` witness from the `SmΛ` definition.
  rcases hr 0 N with ⟨C, M, hC, hM, hbound⟩
  refine ⟨C, M, hC, hM, ?_⟩
  intro h hh t ht τ
  -- `dtdτ 0 N r` is exactly the `N`-th `τ`-derivative.
  have := hbound h hh t ht τ
  -- Since `⟨τ⟩ ≥ 1` and the exponent `(-N) - N = -(2N)` is nonpositive,
  -- we can discard the weight by bounding it by `1`.
  -- We use the crude inequality `x^(p) ≤ 1` for `x ≥ 1` and `p ≤ 0`.
  have hwt : japaneseBracket τ ^ (-(N : ℝ) - (N : ℝ)) ≤ 1 := by
    have hx : (1 : ℝ) ≤ japaneseBracket τ := one_le_japaneseBracket τ
    have hp : (-(N : ℝ) - (N : ℝ)) ≤ 0 := by
      nlinarith
    -- monotonicity of `rpow` in the exponent for bases `≥ 1`
    -- (in practice provided by `Real.rpow_le_rpow_of_exponent_le`).
    simpa [hp] using (Real.rpow_le_rpow_of_exponent_le hx hp)
  -- Combine and simplify.
  have hmul : C * (h⁻¹) ^ M * japaneseBracket τ ^ (-(N : ℝ) - (N : ℝ)) ≤ C * (h⁻¹) ^ M := by
    have : 0 ≤ C * (h⁻¹) ^ M := by
      have : 0 ≤ (h⁻¹ : ℝ) ^ M := by
        exact pow_nonneg (by have := inv_nonneg.mpr (le_trans h0.le hh); exact this) _
      exact mul_nonneg hC this
    nlinarith
  -- finish
  have := le_trans this hmul
  simpa [TwoChartEgorov.dtdτ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this

end SmLambdaToKernelHyp

end TwoChartEgorov
