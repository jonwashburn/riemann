import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Power Series Coefficients and Iterated Derivatives

This file collects general lemmas relating power series coefficients to iterated derivatives
for analytic functions. These are one-variable specializations of the multilinear theory
in Mathlib.

## Main results

* `HasFPowerSeriesAt.iteratedDeriv_eq_coeff`: For a function with a power series at `z`,
  the `n`-th iterated derivative at `z` equals `n!` times the `n`-th coefficient.

* `AnalyticAt.eventually_eq_zero_or_exists_coeff_ne_zero`: Identity principle via coefficients:
  for an analytic `f` at `z`, either `f` is eventually `0` near `z`, or some power-series
  coefficient at `z` is nonzero.

* `AnalyticAt.eventually_eq_zero_or_exists_deriv_ne_zero`: Identity principle via derivatives:
  for an analytic `f` at `z`, either `f` is eventually `0` near `z`, or some iterated derivative
  at `z` is nonzero.

## Implementation notes

These are extracted from the Riemann Project's RS/BWP layer for potential Mathlib inclusion.
The core relationship between Taylor coefficients and iterated derivatives is a standard
result in complex analysis; see e.g. Ahlfors "Complex Analysis", §5.1.
-/

namespace HasFPowerSeriesAt

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {f : 𝕜 → E} {p : FormalMultilinearSeries 𝕜 𝕜 E} {z : 𝕜}

/-- For a function with a power series at `z`, the `n`-th iterated derivative at `z`
equals `n!` times the `n`-th coefficient (one-variable Taylor's formula at the center). -/
lemma iteratedDeriv_eq_coeff (hp : HasFPowerSeriesAt f p z) (n : ℕ) :
    iteratedDeriv n f z = (Nat.factorial n : 𝕜) • p.coeff n := by
  rcases hp with ⟨r, hr⟩
  have h := (hr.factorial_smul (y := (1 : 𝕜)) n)
  have : ((n.factorial : 𝕜)) • p.coeff n =
      (iteratedFDeriv 𝕜 n f z) (fun _ => (1 : 𝕜)) := by
    simpa [one_pow, one_smul,
      (Nat.cast_smul_eq_nsmul (R := 𝕜) (M := E)),
      iteratedDeriv_eq_iteratedFDeriv] using h
  simpa [iteratedDeriv_eq_iteratedFDeriv] using this.symm

end HasFPowerSeriesAt

namespace AnalyticAt

open Topology Set Filter

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- One-variable evaluation of a formal multilinear series at a constant vector. -/
lemma apply_eq_pow_smul_coeff
    (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : ℕ) (y : 𝕜) :
    (p n) (fun _ : Fin n => y) = y ^ n • p.coeff n := by simp

/-- If a non-zero scalar multiplied by a vector is zero, the vector must be zero.
Helper for the identity principle proof. -/
lemma smul_eq_zero_iff_of_ne_zero
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [NoZeroSMulDivisors R M]
    {r : R} (hr : r ≠ 0) {m : M} :
    r • m = 0 ↔ m = 0 := by
  constructor
  · intro h
    have := (smul_eq_zero.mp h).resolve_left hr
    exact this
  · intro h
    simp [h]

/-- Identity principle alternative via coefficients:
for an analytic `f` at `z`, either `f` is eventually `0` near `z`,
or some power-series coefficient at `z` is nonzero. -/
lemma eventually_eq_zero_or_exists_coeff_ne_zero
    {f : 𝕜 → E} {z : 𝕜} (h : AnalyticAt 𝕜 f z) :
    (∀ᶠ w in 𝓝 z, f w = 0) ∨ ∃ n, (h.choose).coeff n ≠ 0 := by
  classical
  let p := h.choose
  have hp : HasFPowerSeriesAt f p z := h.choose_spec
  by_cases hAll : ∀ n, p.coeff n = 0
  · left
    have hzero : ∀ᶠ y in 𝓝 (0 : 𝕜), f (z + y) = 0 := by
      filter_upwards [hp.eventually_hasSum] with y hy
      have hy' : HasSum (fun n => y ^ n • p.coeff n) (f (z + y)) := by
        simpa [apply_eq_pow_smul_coeff] using hy
      have hseq0 : (fun n => y ^ n • p.coeff n) = 0 := by
        funext n; simp [hAll n]
      have hy0 : HasSum (fun _ : ℕ => 0) (f (z + y)) := by
        simpa [hseq0] using hy'
      exact (hasSum_zero.unique hy0).symm
    rcases (Filter.eventually_iff_exists_mem).1 hzero with ⟨V, hVmem, hV⟩
    have hcont : ContinuousAt (fun w : 𝕜 => w - z) z := (continuousAt_id.sub continuousAt_const)
    have hVmem0 : V ∈ 𝓝 (z - z) := by simpa [sub_self] using hVmem
    have hpre : (fun w : 𝕜 => w - z) ⁻¹' V ∈ 𝓝 z := hcont hVmem0
    have hzρ : ∀ᶠ w in 𝓝 z, f w = 0 := by
      refine Filter.mem_of_superset hpre ?_
      intro w hw
      have : f (z + (w - z)) = 0 := hV (w - z) hw
      simpa [add_sub_cancel] using this
    exact hzρ
  · right
    exact not_forall.mp hAll

/-- Iterated derivatives of an analytic function at a point are given by the
corresponding power-series coefficients picked out by `AnalyticAt`.

More precisely, if `h : AnalyticAt 𝕜 f z` and `p` is the power series chosen
by `h` (i.e. `p = h.choose`), then the `n`-th iterated derivative of `f` at `z`
is `n! • p.coeff n`. This is just `HasFPowerSeriesAt.iteratedDeriv_eq_coeff`
repackaged at the `AnalyticAt` level. -/
lemma iteratedDeriv_eq_coeff
    [CompleteSpace E]
    {f : 𝕜 → E} {z : 𝕜}
    (h : AnalyticAt 𝕜 f z) (n : ℕ) :
    iteratedDeriv n f z = (Nat.factorial n : 𝕜) • (h.choose).coeff n := by
  classical
  let p := h.choose
  have hp : HasFPowerSeriesAt f p z := h.choose_spec
  simpa [p] using hp.iteratedDeriv_eq_coeff n

/-- Identity principle alternative via iterated derivatives (derivative form).
For an analytic `f` at `z`, either `f` is eventually `0` near `z`,
or some iterated derivative at `z` is nonzero.

Note: this uses the standard relation between the Taylor coefficients and
iterated derivatives: `iteratedDeriv n f z = (Nat.factorial n) • (coeff n)`. -/
lemma eventually_eq_zero_or_exists_deriv_ne_zero
    [CompleteSpace E]
    {f : 𝕜 → E} {z : 𝕜} (h : AnalyticAt 𝕜 f z) :
    (∀ᶠ w in 𝓝 z, f w = 0) ∨ ∃ n, iteratedDeriv n f z ≠ 0 := by
  classical
  let p := h.choose
  have hp : HasFPowerSeriesAt f p z := h.choose_spec
  have hcoeff := AnalyticAt.eventually_eq_zero_or_exists_coeff_ne_zero h
  refine hcoeff.imp id ?_
  rintro ⟨n, hn⟩
  have hrel : iteratedDeriv n f z = (Nat.factorial n : 𝕜) • p.coeff n :=
    hp.iteratedDeriv_eq_coeff n
  refine ⟨n, ?_⟩
  intro h_deriv_zero
  have h_smul_zero : (Nat.factorial n : 𝕜) • p.coeff n = 0 := by
    rwa [hrel] at h_deriv_zero
  have h_factorial_ne_zero : (Nat.factorial n : 𝕜) ≠ 0 :=
    by exact_mod_cast Nat.factorial_ne_zero n
  have h_coeff_zero : p.coeff n = 0 :=
    (smul_eq_zero_iff_of_ne_zero h_factorial_ne_zero).mp h_smul_zero
  exact hn h_coeff_zero

end AnalyticAt
