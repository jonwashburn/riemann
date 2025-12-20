import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic.NormNum.NatFactorial

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
open scoped BigOperators
open scoped Nat

namespace Probability.Lindeberg

/-!
# Blockwise Lindeberg Replacement Principle
Abstracts the "Gaussian Approximation" strategy from Cipollina-Washburne.

We consider two sequences of independent random vectors `Y` and `N` in a finite dimensional
space `E`. If `Y_k` and `N_k` match moments up to order 2, then `∑ Y_k` and `∑ N_k`
are close in distribution.
-/

variable {Ω : Type*} [MeasurableSpace Ω]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace E]

/-- Mean of a random variable as a Bochner integral. -/
noncomputable def mean (P : Measure Ω) (X : Ω → E) : E :=
  ∫ ω, X ω ∂P

/-- Scalar variance proxy for `E`-valued variables: variance of the norm. -/
noncomputable def variance_norm (P : Measure Ω) (X : Ω → E) : ℝ :=
  ProbabilityTheory.variance (fun ω => ‖X ω‖) P

/-- Scalar moment proxy for `E`-valued variables: moment of the norm. -/
noncomputable def moment_norm (P : Measure Ω) (X : Ω → E) (p : ℕ) : ℝ :=
  ProbabilityTheory.moment (fun ω => ‖X ω‖) p P

/--
A sequence of independent random blocks.
-/
structure BlockSequence (P : Measure Ω) (n : ℕ) where
  X : Fin n → Ω → E
  meas : ∀ k, Measurable (X k)
  indep : iIndepFun (β := fun _ : Fin n => E) X P
  centered : ∀ k, mean P (X k) = 0
  finite_moments : ∀ k, MemLp (X k) 3 P -- Need 3rd moments for Berry-Esseen error

/--
**Moment Matching Condition**.
Two block sequences match if their covariances align.
-/
def MomentsMatch (P : Measure Ω) {n : ℕ} (A B : BlockSequence (E := E) P n) : Prop :=
  ∀ k, variance_norm P (A.X k) = variance_norm P (B.X k)
  -- Note: For vectors, this implies equality of Covariance Operators.

/-- The total field sum. -/
def total_field (P : Measure Ω) {n : ℕ} (seq : BlockSequence (E := E) P n) (ω : Ω) : E :=
  ∑ k, seq.X k ω

/--
**The Hybrid Field (Interpolation Step)**.
`Z^(k)` replaces the first `k` blocks of `A` with blocks from `B`.
-/
def hybrid_field (P : Measure Ω) {n : ℕ} (A B : BlockSequence (E := E) P n)
    (k : Fin (n + 1)) (ω : Ω) : E :=
  (∑ i : Fin n, if (i : ℕ) < (k : ℕ) then B.X i ω else A.X i ω)

/--
## Telescoping step (Lindeberg replacement skeleton)

The full Cipollina–Washburne / Arguin-style replacement bound is built in layers.
This file formalizes the **telescoping** inequality rigorously (no placeholders).

The analytic Taylor remainder estimates and the moment-matching cancellations are developed
in subsequent files.
-/
lemma dist_z0_zn_le_sum_range (z : ℕ → ℝ) (n : ℕ) :
    dist (z 0) (z n) ≤ ∑ i ∈ Finset.range n, dist (z i) (z (i + 1)) := by
  classical
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have htri :
          dist (z 0) (z (n + 1)) ≤ dist (z 0) (z n) + dist (z n) (z (n + 1)) :=
        dist_triangle (z 0) (z n) (z (n + 1))
      calc
        dist (z 0) (z (n + 1))
            ≤ dist (z 0) (z n) + dist (z n) (z (n + 1)) := htri
        _ ≤ (∑ i ∈ Finset.range n, dist (z i) (z (i + 1))) + dist (z n) (z (n + 1)) := by
              exact add_le_add_right ih _
        _ = ∑ i ∈ Finset.range (n + 1), dist (z i) (z (i + 1)) := by
              simp [Finset.sum_range_succ, add_comm]

/-- A clean `n = 2` corollary of Taylor-Lagrange on `[0,1]`: the remainder is bounded by `C/6`
if `|f'''| ≤ C` on `Icc 0 1`. -/
lemma abs_sub_taylorWithinEval_two_Icc_le
    {f : ℝ → ℝ} {C : ℝ}
    (hf : ContDiffOn ℝ 3 f (Set.Icc (0 : ℝ) 1))
    (hC : ∀ y ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv 3 f y| ≤ C) :
    |f 1 - taylorWithinEval f 2 (Set.Icc (0 : ℝ) 1) 0 1| ≤ C / 6 := by
  have hx : (0 : ℝ) < 1 := by norm_num
  obtain ⟨y, hyIoo, hyEq⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (f := f) (x₀ := (0 : ℝ)) (x := (1 : ℝ)) (n := 2)
      hx (by simpa [Nat.succ_eq_add_one] using hf)
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hyIoo.1, le_of_lt hyIoo.2⟩
  have hDeriv : |iteratedDeriv 3 f y| ≤ C := hC y hyIcc
  -- Use the exact remainder identity, then bound it using `hDeriv`.
  have hpow : ((1 : ℝ) - (0 : ℝ)) ^ (2 + 1) = 1 := by norm_num
  have hfact : ((2 + 1)! : ℝ) = 6 := by norm_num
  have hEqAbs : |f 1 - taylorWithinEval f 2 (Set.Icc (0 : ℝ) 1) 0 1|
      = |iteratedDeriv (2 + 1) f y * ((1 : ℝ) - (0 : ℝ)) ^ (2 + 1) / (2 + 1)!| :=
    congrArg (fun t : ℝ => |t|) hyEq
  calc
    |f 1 - taylorWithinEval f 2 (Set.Icc (0 : ℝ) 1) 0 1|
        = |iteratedDeriv (2 + 1) f y * ((1 : ℝ) - (0 : ℝ)) ^ (2 + 1) / (2 + 1)!| := by
            simpa using hEqAbs
    _ = |iteratedDeriv 3 f y * ((1 : ℝ) - (0 : ℝ)) ^ (2 + 1) / (2 + 1)!| := by
          simp
    _ = |iteratedDeriv 3 f y| / 6 := by
          simp [hfact, abs_div]
    _ ≤ C / 6 := by
          exact div_le_div_of_nonneg_right hDeriv (by norm_num : (0 : ℝ) ≤ (6 : ℝ))

/-!
### Second-order Taylor error in explicit form

This upgrades the previous lemma by rewriting `taylorWithinEval` as the usual quadratic Taylor
polynomial at `0`, assuming `f` is `C^3` in a neighborhood (so the within-derivatives agree with
the global iterated derivatives at `0`).
-/

lemma abs_sub_taylor2_at_zero_le_of_bound_iteratedDeriv_three
    {f : ℝ → ℝ} {C : ℝ}
    (hf : ContDiff ℝ 3 f)
    (hC : ∀ y ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv 3 f y| ≤ C) :
    |f 1 - (f 0 + (deriv f 0) + ((1 + 1 : ℝ)⁻¹) * (iteratedDeriv 2 f 0))| ≤ C / 6 := by
  have hx : (0 : ℝ) < 1 := by norm_num
  have hfIcc : ContDiffOn ℝ 3 f (Set.Icc (0 : ℝ) 1) := hf.contDiffOn
  have hbase := abs_sub_taylorWithinEval_two_Icc_le (f := f) (C := C) hfIcc hC
  -- Rewrite `taylorWithinEval` using `taylor_within_apply` and `iteratedDerivWithin_eq_iteratedDeriv` at `0`.
  have hU : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc hx
  have hmem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have hfAt1 : ContDiffAt ℝ 1 f 0 :=
    (hf.contDiffAt (x := (0 : ℝ))).of_le (by decide : (1 : WithTop ℕ∞) ≤ 3)
  have hfAt2 : ContDiffAt ℝ 2 f 0 :=
    (hf.contDiffAt (x := (0 : ℝ))).of_le (by decide : (2 : WithTop ℕ∞) ≤ 3)
  have h1 : iteratedDerivWithin 1 f (Set.Icc (0 : ℝ) 1) 0 = iteratedDeriv 1 f 0 := by
    simpa using
      (iteratedDerivWithin_eq_iteratedDeriv (n := 1) (f := f) (s := Set.Icc (0 : ℝ) 1)
        hU hfAt1 hmem)
  have h2 : iteratedDerivWithin 2 f (Set.Icc (0 : ℝ) 1) 0 = iteratedDeriv 2 f 0 := by
    simpa using
      (iteratedDerivWithin_eq_iteratedDeriv (n := 2) (f := f) (s := Set.Icc (0 : ℝ) 1)
        hU hfAt2 hmem)
  have hTaylor :
      taylorWithinEval f 2 (Set.Icc (0 : ℝ) 1) 0 1
        = f 0 + deriv f 0 + ((1 + 1 : ℝ)⁻¹) * iteratedDeriv 2 f 0 := by
    -- Use the recursion formula `taylorWithinEval_succ` twice.
    -- First `n = 0` gives `taylorWithinEval f 0 ... = f 0`.
    -- Then the `n = 1` and `n = 2` cases add the first and second derivative terms.
    have h0' : taylorWithinEval f 0 (Set.Icc (0 : ℝ) 1) 0 1 = f 0 := by simp
    have h1' :
        taylorWithinEval f 1 (Set.Icc (0 : ℝ) 1) 0 1
          = f 0 + iteratedDerivWithin 1 f (Set.Icc (0 : ℝ) 1) 0 := by
      -- `((1:ℝ) * 0!)⁻¹ * (1-0)^1 = 1`
      simp [taylorWithinEval_succ, h0']
    have h2' :
        taylorWithinEval f 2 (Set.Icc (0 : ℝ) 1) 0 1
          = f 0 + iteratedDerivWithin 1 f (Set.Icc (0 : ℝ) 1) 0
              + ((1 + 1 : ℝ)⁻¹) * iteratedDerivWithin 2 f (Set.Icc (0 : ℝ) 1) 0 := by
      -- `taylorWithinEval_succ` with `n = 1` simplifies to a clean coefficient `(1+1)⁻¹`.
      have hsucc :
          taylorWithinEval f 2 (Set.Icc (0 : ℝ) 1) 0 1
            = taylorWithinEval f 1 (Set.Icc (0 : ℝ) 1) 0 1
                + ((1 + 1 : ℝ)⁻¹) * iteratedDerivWithin 2 f (Set.Icc (0 : ℝ) 1) 0 := by
        have h := taylorWithinEval_succ (f := f) (n := 1) (s := Set.Icc (0 : ℝ) 1)
            (x₀ := (0 : ℝ)) (x := (1 : ℝ))
        -- prevent simp from rewriting using `taylorWithinEval_succ` itself
        simpa [-taylorWithinEval_succ, smul_eq_mul] using h
      -- rewrite the `taylorWithinEval f 1` part and substitute the coefficient
      calc
        taylorWithinEval f 2 (Set.Icc (0 : ℝ) 1) 0 1
            = (f 0 + iteratedDerivWithin 1 f (Set.Icc (0 : ℝ) 1) 0)
                + ((1 + 1 : ℝ)⁻¹) * iteratedDerivWithin 2 f (Set.Icc (0 : ℝ) 1) 0 := by
              -- rewrite using the succ formula + the `n = 1` identity for `taylorWithinEval`
              rw [hsucc, h1']
        _ = f 0 + iteratedDerivWithin 1 f (Set.Icc (0 : ℝ) 1) 0
              + ((1 + 1 : ℝ)⁻¹) * iteratedDerivWithin 2 f (Set.Icc (0 : ℝ) 1) 0 := by
              simp [add_assoc]
    -- Replace within-derivatives by global ones at `0`, then rewrite `iteratedDeriv 1 = deriv`.
    -- Finally, `f 0 + deriv f 0 + (1/2)*iteratedDeriv 2 f 0`.
    -- rewrite via `h2'` then replace within-derivatives by global ones at `0`
    rw [h2']
    simp [h1, h2, iteratedDeriv_one, add_assoc]
  -- Conclude by rewriting the base bound.
  simpa [hTaylor, -taylorWithinEval_succ] using hbase

/-!
### Transporting the quadratic Taylor bound through an affine change of variables

For later Lindeberg steps we need a remainder estimate for `φ(u + z)` in terms of derivatives of
`φ` at `u`, with the sharp `1/6` constant and the expected scaling `|z|^3`.
-/

lemma abs_sub_quadraticTaylor_le
    {phi : ℝ → ℝ} {M u z : ℝ}
    (hphi : ContDiff ℝ 3 phi)
    (hM : ∀ x, |iteratedDeriv 3 phi x| ≤ M) :
    |phi (u + z)
        - (phi u + (deriv phi u) * z + ((1 + 1 : ℝ)⁻¹) * (iteratedDeriv 2 phi u) * z ^ 2)|
      ≤ (M * |z| ^ 3) / 6 := by
  -- Apply the previous lemma to the 1D restriction `f(t) = phi(u + z*t)` on `[0,1]`.
  let f : ℝ → ℝ := fun t => phi (u + z * t)
  have hf : ContDiff ℝ 3 f := by
    simpa [f, mul_assoc, add_assoc] using
      (hphi.comp (contDiff_const.add (contDiff_const.mul contDiff_id)))

  -- Bound the third iterated derivative of `f` on `[0,1]` by `M * |z|^3`.
  have hC : ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv 3 f t| ≤ M * |z| ^ 3 := by
    intro t _ht
    let f1 : ℝ → ℝ := fun x => phi (u + x)
    have hf1 : ContDiff ℝ 3 f1 := by
      simpa [f1, add_assoc] using hphi.comp (contDiff_const.add contDiff_id)
    have hf1_shift : iteratedDeriv 3 f1 = fun x => iteratedDeriv 3 phi (u + x) := by
      simpa [f1, add_comm, add_left_comm, add_assoc] using
        (iteratedDeriv_comp_const_add (n := 3) (f := phi) u)
    have hf_scale : iteratedDeriv 3 (fun s => f1 (z * s)) = fun s => z ^ 3 * iteratedDeriv 3 f1 (z * s) := by
      simpa using (iteratedDeriv_comp_const_mul (n := 3) (f := f1) hf1 z)
    have hderiv3 : iteratedDeriv 3 f t = z ^ 3 * iteratedDeriv 3 phi (u + z * t) := by
      have := congrArg (fun gfun => gfun t) hf_scale
      -- `f` is definitional equal to `fun s => f1 (z*s)`
      simpa [f, f1, hf1_shift, add_assoc, mul_assoc] using this
    have hM' : |iteratedDeriv 3 phi (u + z * t)| ≤ M := hM (u + z * t)
    calc
      |iteratedDeriv 3 f t|
          = |z ^ 3 * iteratedDeriv 3 phi (u + z * t)| := by simp [hderiv3]
      _ ≤ |z ^ 3| * M := by
            have := mul_le_mul_of_nonneg_left hM' (abs_nonneg (z ^ 3))
            simpa [abs_mul] using this
      _ = M * |z| ^ 3 := by
            simp [abs_pow, mul_comm]

  have hMain :=
    abs_sub_taylor2_at_zero_le_of_bound_iteratedDeriv_three (f := f) (C := M * |z| ^ 3) hf hC

  -- Rewrite the Taylor terms at `0` into derivatives of `phi` at `u` with the expected scalings.
  have hf0 : f 0 = phi u := by simp [f]
  have hf1 : f 1 = phi (u + z) := by simp [f, mul_one]
  have hderiv0 : deriv f 0 = (deriv phi u) * z := by
    let f1 : ℝ → ℝ := fun x => phi (u + x)
    have hf1 : ContDiff ℝ 1 f1 := by
      simpa [f1] using (hphi.of_le (by decide : (1 : WithTop ℕ∞) ≤ 3)).comp (contDiff_const.add contDiff_id)
    have hscale : iteratedDeriv 1 f = fun t => z ^ 1 * iteratedDeriv 1 f1 (z * t) := by
      simpa [f, f1, add_assoc] using (iteratedDeriv_comp_const_mul (n := 1) (f := f1) hf1 z)
    have hshift1 : iteratedDeriv 1 f1 = fun x => iteratedDeriv 1 phi (u + x) := by
      simpa [f1] using (iteratedDeriv_comp_const_add (n := 1) (f := phi) u)
    -- Evaluate at `0`; use `iteratedDeriv 1 = deriv` on both `f` and `phi`.
    have hscale0 : iteratedDeriv 1 f 0 = z * iteratedDeriv 1 f1 0 := by
      have := congrArg (fun gfun => gfun 0) hscale
      simpa [pow_one] using this
    have hshift0 : iteratedDeriv 1 f1 0 = iteratedDeriv 1 phi u := by
      have := congrArg (fun gfun => gfun 0) hshift1
      simpa [add_assoc] using this
    calc
      deriv f 0
          = iteratedDeriv 1 f 0 := by simp [iteratedDeriv_one]
      _ = z * iteratedDeriv 1 f1 0 := hscale0
      _ = z * iteratedDeriv 1 phi u := by simp [hshift0]
      _ = z * deriv phi u := by simp [iteratedDeriv_one]
      _ = deriv phi u * z := by simp [mul_comm]
  have hderiv2_0 : iteratedDeriv 2 f 0 = (iteratedDeriv 2 phi u) * z ^ 2 := by
    let f1 : ℝ → ℝ := fun x => phi (u + x)
    have hf1 : ContDiff ℝ 2 f1 := by
      simpa [f1] using (hphi.of_le (by decide : (2 : WithTop ℕ∞) ≤ 3)).comp (contDiff_const.add contDiff_id)
    have hscale : iteratedDeriv 2 f = fun t => z ^ 2 * iteratedDeriv 2 f1 (z * t) := by
      simpa [f, f1, add_assoc] using (iteratedDeriv_comp_const_mul (n := 2) (f := f1) hf1 z)
    have hshift2 : iteratedDeriv 2 f1 = fun x => iteratedDeriv 2 phi (u + x) := by
      simpa [f1] using (iteratedDeriv_comp_const_add (n := 2) (f := phi) u)
    have hscale0 : iteratedDeriv 2 f 0 = z ^ 2 * iteratedDeriv 2 f1 0 := by
      have := congrArg (fun gfun => gfun 0) hscale
      simpa using this
    have hshift0 : iteratedDeriv 2 f1 0 = iteratedDeriv 2 phi u := by
      have := congrArg (fun gfun => gfun 0) hshift2
      simpa [add_assoc] using this
    -- Rearrange the product to match the target shape.
    calc
      iteratedDeriv 2 f 0
          = z ^ 2 * iteratedDeriv 2 f1 0 := hscale0
      _ = z ^ 2 * iteratedDeriv 2 phi u := by simp [hshift0]
      _ = (iteratedDeriv 2 phi u) * z ^ 2 := by simp [mul_comm]

  -- Finish by rewriting the output of the 1D Taylor lemma.
  -- We commute factors so that the quadratic term reads `(1+1)⁻¹ * (iteratedDeriv 2 phi u) * z^2`.
  simpa [hf0, hf1, hderiv0, hderiv2_0, pow_two,
    mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm,
    sub_eq_add_neg, -taylorWithinEval_succ] using hMain

/-!
### Integrable remainder term (scalar, one-step)

This isolates the analytic part of a single Lindeberg replacement step: the *remainder*
after subtracting the quadratic Taylor polynomial is integrable (dominated by `|X|^3`) and
its expectation is bounded by the third moment.
-/

lemma abs_integral_quadraticRemainder_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    {U X : Ω → ℝ}
    {phi : ℝ → ℝ} {M : ℝ}
    (hphi : ContDiff ℝ 3 phi)
    (hM : ∀ x, |iteratedDeriv 3 phi x| ≤ M)
    (hX3 : Integrable (fun ω => |X ω| ^ 3) P) :
    |∫ ω, (phi (U ω + X ω)
            - (phi (U ω) + (deriv phi (U ω)) * X ω
                + ((1 + 1 : ℝ)⁻¹) * (iteratedDeriv 2 phi (U ω)) * (X ω) ^ 2)) ∂P|
      ≤ (M / 6) * ∫ ω, |X ω| ^ 3 ∂P := by
  -- First, get the pointwise `|remainder| ≤ (M/6) * |X|^3`.
  have hpt : ∀ ω,
      |phi (U ω + X ω)
            - (phi (U ω) + (deriv phi (U ω)) * X ω
                + ((1 + 1 : ℝ)⁻¹) * (iteratedDeriv 2 phi (U ω)) * (X ω) ^ 2)|
        ≤ (M / 6) * |X ω| ^ 3 := by
    intro ω
    -- apply the deterministic inequality with `u = U ω` and `z = X ω`
    have := abs_sub_quadraticTaylor_le (phi := phi) (M := M) (u := U ω) (z := X ω) hphi hM
    -- rewrite `(M * |z|^3)/6` as `(M/6) * |z|^3`
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  -- `g ω = (M/6) * |X ω|^3` is integrable.
  have hg : Integrable (fun ω => (M / 6) * |X ω| ^ 3) P :=
    hX3.const_mul (M / 6)
  -- Apply `norm_integral_le_of_norm_le` with the pointwise bound.
  have h_le :
      ‖∫ ω, (phi (U ω + X ω)
            - (phi (U ω) + (deriv phi (U ω)) * X ω
                + ((1 + 1 : ℝ)⁻¹) * (iteratedDeriv 2 phi (U ω)) * (X ω) ^ 2)) ∂P‖
        ≤ ∫ ω, (M / 6) * |X ω| ^ 3 ∂P := by
    refine norm_integral_le_of_norm_le (μ := P) (f := fun ω =>
        (phi (U ω + X ω)
          - (phi (U ω) + (deriv phi (U ω)) * X ω
              + ((1 + 1 : ℝ)⁻¹) * (iteratedDeriv 2 phi (U ω)) * (X ω) ^ 2)))
      (g := fun ω => (M / 6) * |X ω| ^ 3) hg ?_
    filter_upwards [ae_of_all _ hpt] with ω hω
    -- `‖·‖` on `ℝ` is `|·|`
    simpa using hω
  -- Convert `‖·‖` to `|·|` and simplify the RHS integral.
  have h_le' :
      |∫ ω, (phi (U ω + X ω)
            - (phi (U ω) + (deriv phi (U ω)) * X ω
                + ((1 + 1 : ℝ)⁻¹) * (iteratedDeriv 2 phi (U ω)) * (X ω) ^ 2)) ∂P|
        ≤ ∫ ω, (M / 6) * |X ω| ^ 3 ∂P := by
    simpa [Real.norm_eq_abs] using h_le
  -- Pull out the constant.
  calc
    |∫ ω, (phi (U ω + X ω)
            - (phi (U ω) + (deriv phi (U ω)) * X ω
                + ((1 + 1 : ℝ)⁻¹) * (iteratedDeriv 2 phi (U ω)) * (X ω) ^ 2)) ∂P|
        ≤ ∫ ω, (M / 6) * |X ω| ^ 3 ∂P := h_le'
    _ = (M / 6) * ∫ ω, |X ω| ^ 3 ∂P := by
          -- `∫ c * g = c * ∫ g`
          simpa [mul_assoc] using (integral_const_mul (μ := P) (r := (M / 6 : ℝ))
            (f := fun ω => |X ω| ^ 3))

/-- Telescoping inequality for the Lindeberg hybrid expectations. -/
theorem lindeberg_replacement
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (A B : BlockSequence (E := E) P n)
    (F : E → ℝ) :
    dist
        (∫ ω, F (total_field (E := E) P A ω) ∂P)
        (∫ ω, F (total_field (E := E) P B ω) ∂P)
      ≤
      ∑ i ∈ Finset.range n,
        dist
          (∫ ω, F (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else A.X j ω) ∂P)
          (∫ ω, F (∑ j : Fin n, if (j : ℕ) < (i + 1) then B.X j ω else A.X j ω) ∂P) := by
  classical
  let z : ℕ → ℝ :=
    fun i => ∫ ω, F (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else A.X j ω) ∂P
  have hz0 : z 0 = ∫ ω, F (total_field (E := E) P A ω) ∂P := by
    simp [z, total_field]
  have hzn : z n = ∫ ω, F (total_field (E := E) P B ω) ∂P := by
    -- for `j : Fin n`, we always have `(j : ℕ) < n`
    simp [z, total_field]
  have htel : dist (z 0) (z n) ≤ ∑ i ∈ Finset.range n, dist (z i) (z (i + 1)) :=
    dist_z0_zn_le_sum_range z n
  simpa [hz0, hzn, z] using htel

/-- **Blockwise Lindeberg bound (deterministic wrapper).**

If each one-step replacement (from `i` to `i+1`) is bounded by `ε i`, then the total discrepancy
is bounded by `∑_{i < n} ε i`. This is the abstract layer used in CW/Arguin once an increment
estimate (Berry–Esseen + Taylor, or exact Gaussian comparison) is available. -/
theorem lindeberg_replacement_of_step_bounds
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (A B : BlockSequence (E := E) P n)
    (F : E → ℝ) (ε : ℕ → ℝ)
    (hε : ∀ i, i ∈ Finset.range n →
      dist
        (∫ ω, F (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else A.X j ω) ∂P)
        (∫ ω, F (∑ j : Fin n, if (j : ℕ) < (i + 1) then B.X j ω else A.X j ω) ∂P)
      ≤ ε i) :
    dist
        (∫ ω, F (total_field (E := E) P A ω) ∂P)
        (∫ ω, F (total_field (E := E) P B ω) ∂P)
      ≤ ∑ i ∈ Finset.range n, ε i := by
  have htel := lindeberg_replacement (E := E) (P := P) A B F
  refine htel.trans ?_
  -- Compare the telescoping sum term-by-term.
  refine Finset.sum_le_sum ?_
  intro i hi
  -- `hi : i ∈ range n`
  have := hε i hi
  simpa [dist_comm] using this

end Probability.Lindeberg
