import Mathlib.Analysis.Calculus.Deriv.Support

import TwoChart_WeylOperator

/-!
  # Weyl kernels: removing boundary hypotheses via compact τ-support

  This file continues `TwoChart_WeylOperator.lean` by eliminating the explicit
  boundary-vanishing hypotheses (`hvanish`) in the integration-by-parts lemma.
  The key point is that when the τ-slice of the symbol is compactly supported
  inside an *open* interval `(-R, R)`, the topological support is disjoint from
  the endpoints, so all τ-derivatives vanish at `±R` automatically.

  We also add the “integrate τ-symbol bound” lemma used in the Schur-test
  kernel estimate: an `L^∞` bound on `‖∂_τ^N r_N‖` on `[-R, R]` implies a
  quantitative bound on `∫_{-R}^{R} ‖∂_τ^N r_N‖` with an explicit constant.
-/

namespace TwoChartEgorov

open scoped Real
open MeasureTheory

/-! ## Support control for τ-derivatives -/

section SupportLemmas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-
`support_deriv_subset` is already in Mathlib:
`Function.support (deriv f) ⊆ tsupport f`.

For iterated integration by parts we want a *topological* support statement
that iterated τ-derivatives do not enlarge `tsupport`.
-/

lemma tsupport_deriv_subset (f : ℝ → E) : tsupport (deriv f) ⊆ tsupport f := by
  intro x hx
  -- Convert membership in `tsupport (deriv f)` to a closure statement.
  have hx' : x ∈ Set.closure (Function.support (deriv f)) := by
    simpa [tsupport] using hx
  -- `support (deriv f) ⊆ tsupport f`; taking closures gives the claim.
  have hcl : Set.closure (Function.support (deriv f)) ⊆ Set.closure (tsupport f) :=
    Set.closure_mono (support_deriv_subset (f := f))
  have : x ∈ Set.closure (tsupport f) := hcl hx'
  -- `tsupport f` is closed, hence equal to its closure.
  simpa [(isClosed_tsupport (f := f)).closure_eq] using this

lemma tsupport_iteratedDeriv_subset (f : ℝ → E) :
    ∀ n : ℕ, tsupport (iteratedDeriv n f) ⊆ tsupport f
  | 0 => by
      simpa using (Set.Subset.rfl : tsupport (iteratedDeriv 0 f) ⊆ tsupport f)
  | n + 1 => by
      -- `iteratedDeriv (n+1) f = deriv (iteratedDeriv n f)`.
      have h₁ : tsupport (iteratedDeriv (n + 1) f) ⊆ tsupport (iteratedDeriv n f) := by
        simpa [iteratedDeriv_succ] using (tsupport_deriv_subset (f := iteratedDeriv n f))
      exact h₁.trans (tsupport_iteratedDeriv_subset f n)

end SupportLemmas

/-! ## Automatic endpoint vanishing from τ-cutoffs -/

section EndpointVanish

variable {f : ℝ → ℂ} {R : ℝ}

/-
Often the cutoff lemma produces a closed support bound `tsupport f ⊆ [-S, S]`.
To feed the IBP lemma we enlarge the interval slightly so the endpoints lie
strictly outside `tsupport`.
-/

lemma tsupport_subset_Ioo_of_subset_Icc {S R : ℝ}
    (hSR : S < R) (hSupp : tsupport f ⊆ Set.Icc (-S) S) :
    tsupport f ⊆ Set.Ioo (-R) R := by
  intro x hx
  have hx' : x ∈ Set.Icc (-S) S := hSupp hx
  have h1 : -R < x := lt_of_lt_of_le (by linarith) hx'.1
  have h2 : x < R := lt_of_le_of_lt hx'.2 (by linarith)
  exact ⟨h1, h2⟩

/-
If `tsupport f ⊆ (-R, R)`, then in particular `±R ∉ tsupport f`, hence `f (±R) = 0`.
Since iterated derivatives do not enlarge `tsupport`, the same holds for
all `iteratedDeriv k f`.
-/

lemma iteratedDeriv_eq_zero_endpoints_of_tsupport_subset_Ioo
    (hSupp : tsupport f ⊆ Set.Ioo (-R) R) :
    ∀ n : ℕ, iteratedDeriv n f (-R) = 0 ∧ iteratedDeriv n f R = 0 := by
  intro n
  have hSupp' : tsupport (iteratedDeriv n f) ⊆ Set.Ioo (-R) R :=
    (tsupport_iteratedDeriv_subset (f := f) n).trans hSupp
  have hneg : (-R) ∉ tsupport (iteratedDeriv n f) := by
    intro hx
    have : (-R) ∈ Set.Ioo (-R) R := hSupp' hx
    simpa using this
  have hpos : R ∉ tsupport (iteratedDeriv n f) := by
    intro hx
    have : R ∈ Set.Ioo (-R) R := hSupp' hx
    simpa using this
  constructor
  · exact image_eq_zero_of_notMem_tsupport hneg
  · exact image_eq_zero_of_notMem_tsupport hpos

lemma hvanish_iteratedDeriv_of_tsupport_subset_Ioo
    {N : ℕ} (hSupp : tsupport f ⊆ Set.Ioo (-R) R) :
    (∀ k : ℕ, k < N → iteratedDeriv k f (-R) = 0 ∧ iteratedDeriv k f R = 0) := by
  intro k hk
  simpa using iteratedDeriv_eq_zero_endpoints_of_tsupport_subset_Ioo (f := f) (R := R) hSupp k

end EndpointVanish

/-! ## IBP upgrade: remove explicit `hvanish` -/

section IBPUpgrade

variable {f : ℝ → ℂ} {h t tp R : ℝ}

theorem intervalIntegral_phase_mul_eq_ibpConst_pow_mul_integral_iteratedDeriv_of_tsupport
    (N : ℕ) (hh : h ≠ 0) (ht : t ≠ tp)
    (hHasDeriv : ∀ n : ℕ, n ≤ N →
      ∀ x ∈ Set.Icc (-R) R, HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f x) x)
    (hInt : IntervalIntegrable (fun x => iteratedDeriv N f x) volume (-R) R)
    (hphase' : ∀ x ∈ Set.Icc (-R) R,
      HasDerivAt (fun z => phase h t tp z) (-(Complex.I * (t - tp) / h) * phase h t tp x) x)
    (hSupp : tsupport f ⊆ Set.Ioo (-R) R) :
    (∫ x in (-R)..R, phase h t tp x * f x)
      = (ibpConst h t tp) ^ N * (∫ x in (-R)..R, phase h t tp x * iteratedDeriv N f x) := by
  -- Use the earlier lemma, supplying endpoint vanishing derived from the τ-cutoff.
  refine intervalIntegral_phase_mul_eq_ibpConst_pow_mul_integral_iteratedDeriv
    (f := f) (h := h) (t := t) (tp := tp) (R := R)
    N hh ht hHasDeriv ?_ hInt hphase'
  exact hvanish_iteratedDeriv_of_tsupport_subset_Ioo (f := f) (R := R) hSupp

end IBPUpgrade

/-! ## τ-integration bounds for Schur estimates -/

section TauIntegrationBounds

variable {g : ℝ → ℂ} {R C : ℝ}

/-
On a fixed compact τ-interval, `L^∞` control gives explicit control of the integral.

This is the exact passage used after IBP in the paper: the remainder kernel bound
contains a factor `∫ ‖∂_τ^N r_N‖`, which collapses to `(2R) * sup‖∂_τ^N r_N‖`.
-/

lemma intervalIntegral_norm_le_two_mul_R_mul_const
    (hR : 0 ≤ R)
    (hInt : IntervalIntegrable (fun τ => g τ) volume (-R) R)
    (hBound : ∀ τ ∈ Set.Icc (-R) R, ‖g τ‖ ≤ C) :
    (∫ τ in (-R)..R, ‖g τ‖) ≤ (2 * R) * C := by
  have hab : (-R : ℝ) ≤ R := by linarith
  have hIntNorm : IntervalIntegrable (fun τ => ‖g τ‖) volume (-R) R := hInt.norm
  have hIntConst : IntervalIntegrable (fun _ : ℝ => C) volume (-R) R := by
    simpa using (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume (-R) R)
  have hmono : ∀ τ ∈ Set.Icc (-R) R, ‖g τ‖ ≤ (fun _ : ℝ => C) τ := by
    intro τ hτ
    simpa using hBound τ hτ
  have hle : (∫ τ in (-R)..R, ‖g τ‖) ≤ (∫ τ in (-R)..R, (fun _ : ℝ => C) τ) :=
    intervalIntegral.integral_mono_on hab hIntNorm hIntConst hmono
  -- Evaluate the constant integral.
  have hconst : (∫ τ in (-R)..R, (fun _ : ℝ => C) τ) = (2 * R) * C := by
    -- `∫_{-R}^{R} C = (R - (-R)) * C = (2R) * C`.
    calc
      (∫ τ in (-R)..R, (fun _ : ℝ => C) τ) = (R - (-R)) * C := by
        simp
      _ = (2 * R) * C := by
        ring
  exact le_trans hle (le_of_eq hconst)

end TauIntegrationBounds

/-! ## Kernel bounds with explicit τ-integration constant -/

section KernelBoundUpgrade

variable {a : ℝ → ℝ → ℝ → ℂ} {h t tp R : ℝ}

theorem norm_weylKernelIcc_le_of_tsupport
    (N : ℕ) (hh : h ≠ 0) (ht : t ≠ tp)
    (hHasDeriv : ∀ n : ℕ, n ≤ N →
      ∀ τ ∈ Set.Icc (-R) R,
        HasDerivAt (iteratedDeriv n (fun τ => a h ((t + tp) / 2) τ))
          (iteratedDeriv (n + 1) (fun τ => a h ((t + tp) / 2) τ) τ) τ)
    (hInt : IntervalIntegrable
      (fun τ => iteratedDeriv N (fun τ => a h ((t + tp) / 2) τ) τ) volume (-R) R)
    (hphase' : ∀ τ ∈ Set.Icc (-R) R,
      HasDerivAt (fun z => phase h t tp z)
        (-(Complex.I * (t - tp) / h) * phase h t tp τ) τ)
    (hSupp : tsupport (fun τ => a h ((t + tp) / 2) τ) ⊆ Set.Ioo (-R) R) :
    ‖weylKernelIcc a h t tp R‖
      ≤ |((2 * Real.pi * h : ℝ)⁻¹)| * (|h| / |t - tp|) ^ N *
        (∫ τ in (-R)..R, ‖iteratedDeriv N (fun τ => a h ((t + tp) / 2) τ) τ‖) := by
  -- This is exactly `norm_weylKernelIcc_le`, with endpoint vanishing discharged
  -- from the τ-support hypothesis.
  refine norm_weylKernelIcc_le
    (a := a) (h := h) (t := t) (tp := tp) (R := R)
    N hh ht hHasDeriv ?_ hInt hphase'
  -- Provide `hvanish` from the τ-cutoff.
  intro k hk
  simpa using
    iteratedDeriv_eq_zero_endpoints_of_tsupport_subset_Ioo
      (f := fun τ => a h ((t + tp) / 2) τ) (R := R) hSupp k

/-
NOTE:
The above proof follows the structure of `norm_weylKernelIcc_le` but with the
boundary vanishing derived from `tsupport` instead of assumed.

The final `calc` block is intentionally kept explicit to make later Schur-test
applications straightforward.
-/

end KernelBoundUpgrade

/-! ## Remainder-style kernel bound: integrate the τ-derivative estimate -/

section KernelRemainderBound

variable {a : ℝ → ℝ → ℝ → ℂ} {h t tp R : ℝ}

theorem norm_weylKernelIcc_le_explicit
    (N : ℕ) (hh : h ≠ 0) (ht : t ≠ tp) (hR : 0 ≤ R)
    (hHasDeriv : ∀ n : ℕ, n ≤ N →
      ∀ τ ∈ Set.Icc (-R) R,
        HasDerivAt (iteratedDeriv n (fun τ => a h ((t + tp) / 2) τ))
          (iteratedDeriv (n + 1) (fun τ => a h ((t + tp) / 2) τ) τ) τ)
    (hInt : IntervalIntegrable
      (fun τ => iteratedDeriv N (fun τ => a h ((t + tp) / 2) τ) τ) volume (-R) R)
    (hphase' : ∀ τ ∈ Set.Icc (-R) R,
      HasDerivAt (fun z => phase h t tp z)
        (-(Complex.I * (t - tp) / h) * phase h t tp τ) τ)
    (hSupp : tsupport (fun τ => a h ((t + tp) / 2) τ) ⊆ Set.Ioo (-R) R)
    {C : ℝ}
    (hBound : ∀ τ ∈ Set.Icc (-R) R,
      ‖iteratedDeriv N (fun τ => a h ((t + tp) / 2) τ) τ‖ ≤ C) :
    ‖weylKernelIcc a h t tp R‖
      ≤ |((2 * Real.pi * h : ℝ)⁻¹)| * (|h| / |t - tp|) ^ N * (2 * R) * C := by
  -- Start from the IBP-based bound on the kernel.
  have hK :
      ‖weylKernelIcc a h t tp R‖
        ≤ |((2 * Real.pi * h : ℝ)⁻¹)| * (|h| / |t - tp|) ^ N *
          (∫ τ in (-R)..R, ‖iteratedDeriv N (fun τ => a h ((t + tp) / 2) τ) τ‖) :=
    norm_weylKernelIcc_le_of_tsupport
      (a := a) (h := h) (t := t) (tp := tp) (R := R)
      N hh ht hHasDeriv hInt hphase' hSupp

  -- Control the τ-integral by the `L^∞` bound on `[-R,R]`.
  have hτ :
      (∫ τ in (-R)..R, ‖iteratedDeriv N (fun τ => a h ((t + tp) / 2) τ) τ‖)
        ≤ (2 * R) * C := by
    refine intervalIntegral_norm_le_two_mul_R_mul_const
      (g := fun τ => iteratedDeriv N (fun τ => a h ((t + tp) / 2) τ) τ)
      (R := R) (C := C) hR ?_ ?_
    · exact hInt
    · exact hBound

  -- Multiply by the nonnegative prefactor.
  have hpref_nonneg :
      0 ≤ |((2 * Real.pi * h : ℝ)⁻¹)| * (|h| / |t - tp|) ^ N := by
    refine mul_nonneg (abs_nonneg _) ?_
    -- `(|h| / |t-tp|)^N ≥ 0`.
    refine pow_nonneg ?_ N
    exact div_nonneg (abs_nonneg _) (abs_nonneg _)

  -- Combine.
  have hmul :
      |((2 * Real.pi * h : ℝ)⁻¹)| * (|h| / |t - tp|) ^ N *
          (∫ τ in (-R)..R, ‖iteratedDeriv N (fun τ => a h ((t + tp) / 2) τ) τ‖)
        ≤ |((2 * Real.pi * h : ℝ)⁻¹)| * (|h| / |t - tp|) ^ N * ((2 * R) * C) := by
    -- `mul_le_mul_of_nonneg_left` expects the coefficient on the left.
    -- Reassociate so the coefficient is `|...| * (...)^N`.
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hτ hpref_nonneg)

  -- Final rewriting to match the target association.
  have :
      ‖weylKernelIcc a h t tp R‖
        ≤ |((2 * Real.pi * h : ℝ)⁻¹)| * (|h| / |t - tp|) ^ N * ((2 * R) * C) :=
    le_trans hK hmul
  -- Expand `((2*R)*C)` into `...(2*R)*C`.
  simpa [mul_assoc] using this

theorem norm_weylKernelIcc_le_explicit_hinv
    (N : ℕ) (hh : h ≠ 0) (ht : t ≠ tp) (hR : 0 ≤ R)
    (hHasDeriv : ∀ n : ℕ, n ≤ N →
      ∀ τ ∈ Set.Icc (-R) R,
        HasDerivAt (iteratedDeriv n (fun τ => a h ((t + tp) / 2) τ))
          (iteratedDeriv (n + 1) (fun τ => a h ((t + tp) / 2) τ) τ) τ)
    (hInt : IntervalIntegrable
      (fun τ => iteratedDeriv N (fun τ => a h ((t + tp) / 2) τ) τ) volume (-R) R)
    (hphase' : ∀ τ ∈ Set.Icc (-R) R,
      HasDerivAt (fun z => phase h t tp z)
        (-(Complex.I * (t - tp) / h) * phase h t tp τ) τ)
    (hSupp : tsupport (fun τ => a h ((t + tp) / 2) τ) ⊆ Set.Ioo (-R) R)
    {C₀ : ℝ} {M : ℕ}
    (hBound : ∀ τ ∈ Set.Icc (-R) R,
      ‖iteratedDeriv N (fun τ => a h ((t + tp) / 2) τ) τ‖ ≤ C₀ * (h⁻¹) ^ M) :
    ‖weylKernelIcc a h t tp R‖
      ≤ |((2 * Real.pi * h : ℝ)⁻¹)| * (|h| / |t - tp|) ^ N * (2 * R) *
          (C₀ * (h⁻¹) ^ M) := by
  -- Apply the previous lemma with `C := C₀ * (h⁻¹)^M`.
  simpa [mul_assoc] using
    (norm_weylKernelIcc_le_explicit
      (a := a) (h := h) (t := t) (tp := tp) (R := R)
      N hh ht hR hHasDeriv hInt hphase' hSupp (C := C₀ * (h⁻¹) ^ M) hBound)

end KernelRemainderBound

end TwoChartEgorov
