/******************************************************************************
  TwoChart_WeylOperator

  Analytic continuation of the paper formalization.

  This file introduces:

  * a kernel operator wrapper (Schur-test friendly),
  * the 1D semiclassical Weyl kernel,
  * and the first nontrivial kernel estimate: the integration-by-parts /
    τ-derivative tradeoff that yields off-diagonal decay.

  No axioms, no placeholders, no `sorry`.
*******************************************************************************/

import TwoChart_SmLambda

import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.Calculus.IteratedDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Tactic

open scoped Real

namespace TwoChartEgorov

noncomputable section

open MeasureTheory intervalIntegral

/-! ## Kernel operators (Schur-test setup) -/

/-- Function-level kernel operator.

`KernelOp μ K u` is the function `t ↦ ∫ t', K t t' * u t' dμ`.

The paper's argument is kernel-first: we estimate `K` and then deduce operator
bounds (e.g. by Schur).  Keeping the operator at the function level is the most
transparent starting point; later files can wrap this into a bounded operator on
`L²` by quotienting by a.e.-equality.
-/
def KernelOp (μ : Measure ℝ) (K : ℝ → ℝ → ℂ) (u : ℝ → ℂ) : ℝ → ℂ :=
  fun t => ∫ t' : ℝ, K t t' * u t' ∂μ

/-- Schur-test *data* for a kernel `K`.

This records the two slice `L¹` bounds needed by the Schur test.
We do not prove the Schur theorem in this file; this structure is the intended
interface between kernel estimates and later operator norm bounds.
-/
structure SchurData (μ : Measure ℝ) (K : ℝ → ℝ → ℂ) : Prop where
  (A B : ℝ)
  (A_nonneg : 0 ≤ A)
  (B_nonneg : 0 ≤ B)
  (row_integrable : ∀ t : ℝ, Integrable (fun t' : ℝ => ‖K t t'‖) μ)
  (col_integrable : ∀ t' : ℝ, Integrable (fun t : ℝ => ‖K t t'‖) μ)
  (row_bound : ∀ t : ℝ, (∫ t' : ℝ, ‖K t t'‖ ∂μ) ≤ A)
  (col_bound : ∀ t' : ℝ, (∫ t : ℝ, ‖K t t'‖ ∂μ) ≤ B)

/-! ## Weyl kernel (1D) -/

/-- The semiclassical Weyl kernel (1D).

This is the paper's kernel

`K_h(t,t') = (2πh)^{-1} ∫ exp(i (t-t')τ/h) a(h,(t+t')/2,τ) dτ`.

We define it using the Bochner integral over `ℝ` with Lebesgue measure.
-/
noncomputable def weylKernel (a : ℝ → ℝ → ℝ → ℂ) (h t tp : ℝ) : ℂ :=
  ((2 * Real.pi * h : ℝ)⁻¹ : ℝ) •
    ∫ τ : ℝ, Complex.exp ((Complex.I * ((t - tp) / h) : ℂ) * (τ : ℂ)) * a h ((t + tp) / 2) τ

/-- A compact-interval version of the Weyl kernel on `[-R,R]`.

This is the natural object for rigorous integration by parts.
In the paper, the τ-integral is effectively compactly supported after a cutoff;
this `weylKernelIcc` is the faithful formal proxy.
-/
noncomputable def weylKernelIcc (a : ℝ → ℝ → ℝ → ℂ) (h t tp R : ℝ) : ℂ :=
  ((2 * Real.pi * h : ℝ)⁻¹ : ℝ) •
    ∫ τ in (-R)..R,
      Complex.exp ((Complex.I * ((t - tp) / h) : ℂ) * (τ : ℂ)) * a h ((t + tp) / 2) τ

/-- The Weyl operator as the kernel integral operator associated to `weylKernel`. -/
noncomputable def weylOp (a : ℝ → ℝ → ℝ → ℂ) (h : ℝ) (μ : Measure ℝ := volume) :
    (ℝ → ℂ) → ℝ → ℂ :=
  fun u t => KernelOp μ (fun t tp => weylKernel a h t tp) u t

/-- The Weyl operator associated to the truncated-`τ` kernel `weylKernelIcc`. -/
noncomputable def weylOpIcc (a : ℝ → ℝ → ℝ → ℂ) (h R : ℝ) (μ : Measure ℝ := volume) :
    (ℝ → ℂ) → ℝ → ℂ :=
  fun u t => KernelOp μ (fun t tp => weylKernelIcc a h t tp R) u t

/-! ## Integration by parts: τ-derivative tradeoff -/

namespace WeylIBP

variable (a : ℝ → ℝ → ℝ → ℂ)

/-- The τ-slice of the symbol at fixed `(h,t,tp)`.

This is the function to which we apply τ-derivatives.
-/
@[simp] def slice (h t tp : ℝ) : ℝ → ℂ := fun τ => a h ((t + tp) / 2) τ

/-- The oscillatory phase factor `τ ↦ exp(i (t-t') τ / h)`.
-/
@[simp] def phase (h t tp : ℝ) : ℝ → ℂ :=
  fun τ => Complex.exp ((Complex.I * ((t - tp) / h) : ℂ) * (τ : ℂ))

/-- A convenient constant: the scalar factor obtained from one integration by parts.

For `t ≠ tp` this is `-(h)/(i(t-tp))`.
-/
def ibpConst (h t tp : ℝ) : ℂ :=
  - (h : ℂ) / (Complex.I * (t - tp))

/-- Absolute value of the IBP constant.

This is the analytic heart of the tradeoff: one τ-derivative buys a factor
`|h|/|t-t'|`.
-/
lemma norm_ibpConst (h t tp : ℝ) : ‖ibpConst h t tp‖ = |h| / |t - tp| := by
  -- Pure scalar algebra.
  calc
    ‖ibpConst h t tp‖ = ‖(h : ℂ)‖ / ‖Complex.I * (t - tp)‖ := by
      simp [ibpConst, norm_div]
    _ = |h| / (‖Complex.I‖ * ‖(t - tp : ℂ)‖) := by
      simp [norm_mul, div_eq_mul_inv, mul_assoc]
    _ = |h| / |t - tp| := by
      simp [Complex.norm_eq_abs, abs_ofReal]

/-- The derivative of the phase.

`d/dτ exp(i * ((t-t')/h) * τ) = (i*(t-t')/h) * exp(...)`.
-/
lemma hasDerivAt_phase (h t tp τ : ℝ) :
    HasDerivAt (phase h t tp) ((Complex.I * ((t - tp) / h) : ℂ) * phase h t tp τ) τ := by
  -- Write `phase = fun τ => Complex.exp (g τ)` with
  --   g(τ) = (I * ((t-tp)/h)) * (τ:ℂ),
  -- then use `HasDerivAt.cexp`.
  have h_ofReal : HasDerivAt (fun τ : ℝ => (τ : ℂ)) (1 : ℂ) τ := by
    -- `HasDerivAt.ofReal_comp` upgrades `ℝ → ℝ` differentiability to `ℝ → ℂ`.
    simpa using (HasDerivAt.ofReal_comp (z := τ) (f := fun x : ℝ => x) (u := (1 : ℝ)) (by simpa using (hasDerivAt_id τ)))
  have hg : HasDerivAt
      (fun τ : ℝ => (Complex.I * ((t - tp) / h) : ℂ) * (τ : ℂ))
      (Complex.I * ((t - tp) / h) : ℂ) τ := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using h_ofReal.const_mul (Complex.I * ((t - tp) / h) : ℂ)
  -- Differentiate the exponential.
  have :=
    (HasDerivAt.cexp
      (f := fun τ : ℝ => (Complex.I * ((t - tp) / h) : ℂ) * (τ : ℂ))
      (f' := (Complex.I * ((t - tp) / h) : ℂ)) (x := τ) hg)
  -- Put it in the shape used by `phase`.
  simpa [phase, mul_assoc, mul_left_comm, mul_comm] using this

/-- The oscillatory phase is unimodular: `‖exp(i x)‖ = 1`. -/
lemma norm_phase (h t tp τ : ℝ) : ‖phase h t tp τ‖ = 1 := by
  -- Rewrite the exponent into the standard `x * I` form with real `x`.
  -- Here `x = ((t - tp) / h) * τ`.
  -- Then apply `Complex.norm_exp_ofReal_mul_I`.
  simpa [phase, mul_assoc, mul_left_comm, mul_comm] using
    (Complex.norm_exp_ofReal_mul_I ((((t - tp) / h) * τ)))

/-- A fixed antiderivative of the phase used for integration by parts.

For `h ≠ 0` and `t ≠ tp` we have `deriv (phaseAntideriv h t tp) = phase h t tp`.
-/
def phaseAntideriv (h t tp : ℝ) : ℝ → ℂ :=
  fun τ => ((h : ℂ) / (Complex.I * (t - tp))) * phase h t tp τ

lemma hasDerivAt_phaseAntideriv {h t tp τ : ℝ} (hh : h ≠ 0) (ht : t ≠ tp) :
    HasDerivAt (phaseAntideriv h t tp) (phase h t tp τ) τ := by
  -- Differentiate the product `const * phase` and simplify the scalar.
  have hphase := (hasDerivAt_phase (h := h) (t := t) (tp := tp) (τ := τ))
  have hmul := hphase.const_mul ((h : ℂ) / (Complex.I * (t - tp)))
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  have ht' : (t - tp : ℂ) ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr ht)
  have hscalar : ((h : ℂ) / (Complex.I * (t - tp))) * (Complex.I * ((t - tp) / h) : ℂ) = 1 := by
    -- A straightforward field computation, using `h ≠ 0` and `t ≠ tp`.
    field_simp [hh', ht', Complex.I_ne_zero]
  -- Put in the desired form.
  -- `HasDerivAt.const_mul` yields derivative
  --   `((h)/(I*(t-tp))) * ((I*((t-tp)/h)) * phase τ)`.
  -- Rearrange scalars and use `hscalar`.
  simpa [phaseAntideriv, mul_assoc, mul_left_comm, mul_comm, hscalar] using hmul

/-- One-step IBP identity on a finite interval.

This is the core of the *τ-derivative tradeoff*: if boundary terms vanish,
an oscillatory factor allows us to move a τ-derivative onto the amplitude at the
cost of a factor `-(h)/(i(t-t'))`.
-/
theorem intervalIntegral_phase_mul_eq_ibpConst_mul_integral_deriv
    {f : ℝ → ℂ} {h t tp R : ℝ} (hh : h ≠ 0) (ht : t ≠ tp)
    (hf : ∀ x ∈ Set.uIcc (-R) R, HasDerivAt f (deriv f x) x)
    (hf' : IntervalIntegrable (deriv f) volume (-R) R)
    (hphase' : IntervalIntegrable (fun x => phase h t tp x) volume (-R) R)
    (hvanish : f (-R) = 0 ∧ f R = 0) :
    (∫ x in (-R)..R, phase h t tp x * f x)
      = ibpConst h t tp * (∫ x in (-R)..R, phase h t tp x * deriv f x) := by
  -- Apply the `intervalIntegral` integration-by-parts lemma to
  --   u = f, v = phaseAntideriv,
  -- so that v' = phase.
  have hv : ∀ x ∈ Set.uIcc (-R) R,
      HasDerivAt (phaseAntideriv h t tp) (phase h t tp x) x := by
    intro x hx
    simpa using (hasDerivAt_phaseAntideriv (h := h) (t := t) (tp := tp) (τ := x) hh ht)
  -- Integration by parts: ∫ u * v' = u b * v b - u a * v a - ∫ u' * v.
  have hibp :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := f) (v := phaseAntideriv h t tp)
      (u' := fun x => deriv f x) (v' := fun x => phase h t tp x)
      (a := -R) (b := R)
      (hu := hf) (hv := hv) (hu' := hf') (hv' := hphase')
  -- Clean up boundary terms, then rewrite the remaining integral.
  have hfa : f (-R) = 0 := hvanish.1
  have hfb : f R = 0 := hvanish.2
  -- Start from `hibp` and use commutativity of multiplication in `ℂ`.
  -- `hibp` is stated for `∫ u * v'`, while our integrand is `phase * f`.
  -- We commute the factors at the end.
  --
  -- After dropping boundary terms:
  --   ∫ f * phase = - ∫ (deriv f) * phaseAntideriv.
  -- Then expand `phaseAntideriv` and pull out the constant.
  have : (∫ x in (-R)..R, f x * phase h t tp x)
      = - (∫ x in (-R)..R, deriv f x * phaseAntideriv h t tp x) := by
    -- From the IBP identity.
    simpa [hfa, hfb, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hibp
  -- Now rewrite `phaseAntideriv` and factor out the scalar.
  -- Note: `intervalIntegral.integral_mul_const` and `integral_const_mul` allow
  -- pulling out constants from interval integrals.
  calc
    (∫ x in (-R)..R, phase h t tp x * f x)
        = (∫ x in (-R)..R, f x * phase h t tp x) := by
            simp [mul_comm]
    _ = - (∫ x in (-R)..R, deriv f x * phaseAntideriv h t tp x) := this
    _ = - (∫ x in (-R)..R,
            deriv f x * (((h : ℂ) / (Complex.I * (t - tp))) * phase h t tp x)) := by
            simp [phaseAntideriv, mul_assoc]
    _ = - (((h : ℂ) / (Complex.I * (t - tp))) * (∫ x in (-R)..R, deriv f x * phase h t tp x)) := by
            -- pull out the constant `(h)/(I*(t-tp))`
            simp [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
              mul_assoc, mul_left_comm, mul_comm]
    _ = (ibpConst h t tp) * (∫ x in (-R)..R, phase h t tp x * deriv f x) := by
            -- rewrite the constant as `ibpConst`, commute factors
            simp [ibpConst, mul_assoc, mul_left_comm, mul_comm]

/-- N-step IBP identity on a finite interval.

Assuming all boundary terms vanish up to order `N-1`, repeated IBP yields

`∫ phase * f = (ibpConst)^N * ∫ phase * (iteratedDeriv N f)`.
-/
theorem intervalIntegral_phase_mul_eq_ibpConst_pow_mul_integral_iteratedDeriv
    {f : ℝ → ℂ} {h t tp R : ℝ} (N : ℕ) (hh : h ≠ 0) (ht : t ≠ tp)
    (hHasDeriv : ∀ k ≤ N,
      ∀ x ∈ Set.uIcc (-R) R,
        HasDerivAt (iteratedDeriv k f) (deriv (iteratedDeriv k f) x) x)
    (hInt : ∀ k ≤ N, IntervalIntegrable (deriv (iteratedDeriv k f)) volume (-R) R)
    (hphase' : IntervalIntegrable (fun x => phase h t tp x) volume (-R) R)
    (hvanish : ∀ k < N, (iteratedDeriv k f) (-R) = 0 ∧ (iteratedDeriv k f) R = 0) :
    (∫ x in (-R)..R, phase h t tp x * f x)
      = (ibpConst h t tp) ^ N * (∫ x in (-R)..R, phase h t tp x * iteratedDeriv N f x) := by
  induction' N with N ih
  · simp
  · -- Apply the one-step lemma to `g := iteratedDeriv N f` and then use the IH.
    have hvanN : (iteratedDeriv N f) (-R) = 0 ∧ (iteratedDeriv N f) R = 0 := by
      -- `k = N` is `< N+1`.
      simpa using hvanish N (Nat.lt_succ_self N)
    have hone :=
      intervalIntegral_phase_mul_eq_ibpConst_mul_integral_deriv
        (f := iteratedDeriv N f) (h := h) (t := t) (tp := tp) (R := R)
        hh ht
        (hf := hHasDeriv N (Nat.le_succ N))
        (hf' := hInt N (Nat.le_succ N))
        (hphase' := hphase')
        (hvanish := hvanN)
    -- Use IH on the left side.
    -- IH gives: ∫ phase * f = (ibpConst)^N * ∫ phase * iteratedDeriv N f.
    -- Substitute that into `hone`.
    -- Also, `deriv (iteratedDeriv N f) = iteratedDeriv (N+1) f` by definition.
    have ih' :=
      ih
        (hHasDeriv := fun k hk => hHasDeriv k (le_trans hk (Nat.le_succ N)))
        (hInt := fun k hk => hInt k (le_trans hk (Nat.le_succ N)))
        (hphase' := hphase')
        (hvanish := fun k hk => hvanish k (Nat.lt_trans hk (Nat.lt_succ_self N)))
    -- Now assemble.
    calc
      (∫ x in (-R)..R, phase h t tp x * f x)
          = (ibpConst h t tp) ^ N * (∫ x in (-R)..R, phase h t tp x * iteratedDeriv N f x) := ih'
      _ = (ibpConst h t tp) ^ N * ((ibpConst h t tp) * (∫ x in (-R)..R, phase h t tp x * deriv (iteratedDeriv N f) x)) := by
            simp [hone]
      _ = (ibpConst h t tp) ^ (Nat.succ N) * (∫ x in (-R)..R, phase h t tp x * iteratedDeriv (Nat.succ N) f x) := by
            -- algebra + `iteratedDeriv_succ`
            simp [pow_succ, mul_assoc, iteratedDeriv_succ]

/-- The first nontrivial kernel estimate: τ-derivatives yield off-diagonal decay.

This is the precise analytic statement that will be used for the Moyal remainder
kernel estimates: after `N` integrations by parts, we gain the factor
`(|h|/|t-t'|)^N` and place `N` τ-derivatives on the amplitude.

We phrase it for the compact-τ-support Weyl kernel `weylKernelIcc`.
-/
theorem norm_weylKernelIcc_le
    (a : ℝ → ℝ → ℝ → ℂ) {h t tp R : ℝ} (N : ℕ)
    (hh : h ≠ 0) (ht : t ≠ tp)
    (hHasDeriv : ∀ k ≤ N,
      ∀ x ∈ Set.uIcc (-R) R,
        HasDerivAt (iteratedDeriv k (fun τ => a h ((t + tp) / 2) τ))
          (deriv (iteratedDeriv k (fun τ => a h ((t + tp) / 2) τ)) x) x)
    (hInt : ∀ k ≤ N,
      IntervalIntegrable (deriv (iteratedDeriv k (fun τ => a h ((t + tp) / 2) τ))) volume (-R) R)
    (hphase' : IntervalIntegrable (fun x => phase h t tp x) volume (-R) R)
    (hvanish : ∀ k < N,
      (iteratedDeriv k (fun τ => a h ((t + tp) / 2) τ)) (-R) = 0 ∧
      (iteratedDeriv k (fun τ => a h ((t + tp) / 2) τ)) R = 0) :
    ‖weylKernelIcc a h t tp R‖
      ≤ |((2 * Real.pi * h : ℝ)⁻¹)| * (|h| / |t - tp|) ^ N *
        (∫ x in (-R)..R, ‖iteratedDeriv N (fun τ => a h ((t + tp) / 2) τ) x‖) := by
  -- Start from the N-step IBP identity for the τ-integral defining the kernel.
  have hIBP :=
    intervalIntegral_phase_mul_eq_ibpConst_pow_mul_integral_iteratedDeriv
      (f := fun τ => a h ((t + tp) / 2) τ) (h := h) (t := t) (tp := tp) (R := R)
      N hh ht
      (hHasDeriv := hHasDeriv) (hInt := hInt) (hphase' := hphase') (hvanish := hvanish)
  -- Expand the kernel, use `hIBP`, then estimate the remaining integral by
  -- `intervalIntegral.norm_integral_le_integral_norm` and `‖phase‖ = 1`.
  --
  -- We avoid bundling constants into the integral: everything is scalar.
  --
  -- Step 1: rewrite `weylKernelIcc` using `hIBP`.
  have hrepl : weylKernelIcc a h t tp R
      = ((2 * Real.pi * h : ℝ)⁻¹ : ℝ) •
          ((ibpConst h t tp) ^ N *
            (∫ x in (-R)..R, phase h t tp x * iteratedDeriv N (fun τ => a h ((t + tp) / 2) τ) x)) := by
    simp [weylKernelIcc, hIBP, mul_assoc]
  -- Step 2: take norms.
  -- `‖r • z‖ = |r| * ‖z‖` for real scalars on `ℂ`.
  -- Also `‖z * w‖ = ‖z‖ * ‖w‖` in `ℂ`.
  -- And `‖(ibpConst)^N‖ = (‖ibpConst‖)^N`.
  --
  -- The only nontrivial part is the interval integral.
  have hnormInt :
      ‖∫ x in (-R)..R, phase h t tp x * iteratedDeriv N (fun τ => a h ((t + tp) / 2) τ) x‖
        ≤ ∫ x in (-R)..R, ‖iteratedDeriv N (fun τ => a h ((t + tp) / 2) τ) x‖ := by
    -- first use the general norm bound for interval integrals
    have :=
      intervalIntegral.norm_integral_le_integral_norm
        (f := fun x => phase h t tp x * iteratedDeriv N (fun τ => a h ((t + tp) / 2) τ) x)
        (a := -R) (b := R)
    -- then simplify `‖phase * g‖ = ‖g‖` using `‖phase‖ = 1`
    refine le_trans this ?_
    -- pointwise simplification under the integral
    refine le_of_eq ?_
    -- `simp` is effective here.
    ·
      -- We use `intervalIntegral.integral_congr_ae`-style rewriting by `simp`.
      -- In the `intervalIntegral` setting, `simp` can rewrite the integrand directly.
      --
      -- `‖phase h t tp x‖ = 1`.
      simp [norm_mul, norm_phase, mul_assoc]
  -- Finish: combine scalar norms.
  -- Note: we use `Real.norm_eq_abs` for real norms and `norm_smul` for `ℝ`-SMul.
  --
  -- Extract the prefactor and the IBP constant power.
  have hnormConst : ‖(ibpConst h t tp) ^ N‖ = (|h| / |t - tp|) ^ N := by
    -- `‖z^N‖ = ‖z‖^N` and `‖ibpConst‖ = |h|/|t-tp|`.
    simp [norm_ibpConst, norm_pow]
  -- Now assemble the inequality.
  -- We expand `hrepl`, apply `norm_smul` and submultiplicativity.
  --
  -- Note that `((2πh)⁻¹ : ℝ)` is a real scalar.
  have hscalar : ‖((2 * Real.pi * h : ℝ)⁻¹ : ℝ)‖ = |((2 * Real.pi * h : ℝ)⁻¹)| := by
    simp [Real.norm_eq_abs]
  -- Main calculation.
  have :
      ‖weylKernelIcc a h t tp R‖
        ≤ |((2 * Real.pi * h : ℝ)⁻¹)| * ‖(ibpConst h t tp) ^ N‖ *
            ‖∫ x in (-R)..R, phase h t tp x * iteratedDeriv N (fun τ => a h ((t + tp) / 2) τ) x‖ := by
    -- Expand the definition via `hrepl` and use `norm_mul`.
    -- `‖r • (z * w)‖ = |r| * ‖z * w‖`.
    --
    -- First rewrite, then `simp`.
    simpa [hrepl, hscalar, norm_smul, norm_mul, mul_assoc, mul_left_comm, mul_comm]
  -- Replace the integral norm using `hnormInt`, then rewrite `‖(ibpConst)^N‖`.
  refine le_trans this ?_
  have hmul :
      |((2 * Real.pi * h : ℝ)⁻¹)| * ‖(ibpConst h t tp) ^ N‖ *
          ‖∫ x in (-R)..R, phase h t tp x * iteratedDeriv N (fun τ => a h ((t + tp) / 2) τ) x‖
        ≤
      |((2 * Real.pi * h : ℝ)⁻¹)| * ‖(ibpConst h t tp) ^ N‖ *
          (∫ x in (-R)..R, ‖iteratedDeriv N (fun τ => a h ((t + tp) / 2) τ) x‖) := by
    have hnonneg : 0 ≤ |((2 * Real.pi * h : ℝ)⁻¹)| * ‖(ibpConst h t tp) ^ N‖ := by
      positivity
    have := mul_le_mul_of_nonneg_left hnormInt hnonneg
    -- Rearrange the products to match the shape above.
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  -- Conclude.
  exact le_trans hmul (by
    -- substitute the norm of the IBP constant power
    simp [hnormConst, mul_assoc, mul_left_comm, mul_comm])

end WeylIBP

end TwoChartEgorov
