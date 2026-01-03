import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Riemann.RS.BWP.Constants
-- Consolidated Mathlib-style imports (general lemmas now available from these):
-- import Riemann.Mathlib.Analysis.Analytic.PowerSeriesCoefficients
-- import Riemann.Mathlib.Topology.FilterNhdsWithin
-- import Riemann.Mathlib.Analysis.Complex.SchurFunction

/-!
# Boundary Wedge Proof - Basic Definitions

This module contains the fundamental definitions used throughout the boundary wedge proof:
- Auxiliary lemmas
- Analytic functions
- Residue bookkeeping
- Poisson balayage
- Dyadic annuli and counts
- Product constant calibration
- Decay functions and weights
- Residue bookkeeping

## Consolidation Note

The following general lemmas have been consolidated into Mathlib-style files:

* `HasFPowerSeriesAt.iteratedDeriv_eq_coeff` → `Riemann.Mathlib.Analysis.Analytic.PowerSeriesCoefficients`
* `AnalyticAt.eventually_eq_zero_or_exists_coeff_ne_zero` → same file
* `AnalyticAt.eventually_eq_zero_or_exists_deriv_ne_zero` → same file
* `Filter.eventually_nhdsWithin_iff` → `Riemann.Mathlib.Topology.FilterNhdsWithin`
* `TopologicalSpace.discreteTopology_iff_isOpen_singleton_mem` → same file

These lemmas are retained here for backward compatibility with the existing RS codebase.
For new code, prefer importing from the consolidated locations above.
-/

namespace HasFPowerSeriesAt

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {f : 𝕜 → E} {p : FormalMultilinearSeries 𝕜 𝕜 E} {z : 𝕜}

/-- For a function with a power series at `z`, the `n`-th iterated derivative at `z`
equals `n!` times the `n`-th coefficient (one–variable Taylor’s formula at the center). -/
lemma iteratedDeriv_eq_coeff (hp : HasFPowerSeriesAt f p z) (n : ℕ) :
    iteratedDeriv n f z = (Nat.factorial n : 𝕜) • p.coeff n := by
  -- Extract a ball expansion
  rcases hp with ⟨r, hr⟩
  have h :=
    (hr.factorial_smul (y := (1 : 𝕜)) n)
  have : ((n.factorial : 𝕜)) • p.coeff n =
      (iteratedFDeriv 𝕜 n f z) (fun _ => (1 : 𝕜)) := by
    simpa [one_pow, one_smul,
      (Nat.cast_smul_eq_nsmul (R := 𝕜) (M := E)),
      iteratedDeriv_eq_iteratedFDeriv] using h
  simpa [iteratedDeriv_eq_iteratedFDeriv] using this.symm

end HasFPowerSeriesAt
namespace AnalyticAt

open Topology Set Filter

variable {𝕜 E : Type*}
  [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

-- One-variable evaluation of a formal multilinear series at a constant vector
lemma apply_eq_pow_smul_coeff
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : ℕ) (y : 𝕜) :
    (p n) (fun _ : Fin n => y) = y ^ n • p.coeff n := by simp

/-- Identity-principle alternative via coefficients:
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
corresponding power–series coefficients picked out by `AnalyticAt`.

More precisely, if `h : AnalyticAt 𝕜 f z` and `p` is the power series chosen
by `h` (i.e. `p = h.choose`), then the `n`‑th iterated derivative of `f` at `z`
is `n! • p.coeff n`.  This is just `HasFPowerSeriesAt.iteratedDeriv_eq_coeff`
repackaged at the `AnalyticAt` level. -/
lemma iteratedDeriv_eq_coeff
    [CompleteSpace E]
    {f : 𝕜 → E} {z : 𝕜}
    (h : AnalyticAt 𝕜 f z) (n : ℕ) :
    iteratedDeriv n f z = (Nat.factorial n : 𝕜) • (h.choose).coeff n := by
  classical
  -- unpack the power series witness from `h`
  let p := h.choose
  have hp : HasFPowerSeriesAt f p z := h.choose_spec
  -- apply the general Taylor–coefficient formula
  simpa [p] using hp.iteratedDeriv_eq_coeff n

-- If a non-zero scalar multiplied by a vector is zero, the vector must be zero.
lemma smul_eq_zero_iff_ne_zero_of_left
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [NoZeroSMulDivisors R M]
    {r : R} (hr : r ≠ 0) {m : M} :
    r • m = 0 ↔ m = 0 := by
  constructor
  · intro h
    -- Use the no-zero-smul-divisors property: r • m = 0 implies r = 0 or m = 0.
    -- Since r ≠ 0, we must have m = 0.
    have := (smul_eq_zero.mp h).resolve_left hr
    exact this
  · intro h
    simp [h]

/-- Identity-principle alternative via iterated derivatives (derivative form).
For an analytic `f` at `z`, either `f` is eventually `0` near `z`,
or some iterated derivative at `z` is nonzero.

Note: this uses the standard relation between the Taylor coefficients and
iterated derivatives: `iteratedDeriv n f z = (Nat.factorial n) • (coeff n)`. -/
lemma eventually_eq_zero_or_exists_deriv_ne_zero
    [CompleteSpace E]
    {f : 𝕜 → E} {z : 𝕜} (h : AnalyticAt 𝕜 f z) :
    (∀ᶠ w in 𝓝 z, f w = 0) ∨ ∃ n, iteratedDeriv n f z ≠ 0 := by
  classical
  -- Consistently use the power series `p` chosen by the `AnalyticAt` instance `h`.
  let p := h.choose
  have hp : HasFPowerSeriesAt f p z := h.choose_spec
  -- Apply the coefficient-based version of the identity principle.
  -- Since `p` is definitionally `h.choose`, the result of this lemma is about `p`.
  have hcoeff := AnalyticAt.eventually_eq_zero_or_exists_coeff_ne_zero h
  -- If `f` is eventually zero, we are done.
  refine hcoeff.imp id ?_
  -- Otherwise, there exists a non-zero coefficient.
  rintro ⟨n, hn⟩ -- `hn` is `p.coeff n ≠ 0`.
  -- Use the relation between derivatives and coefficients from mathlib.
  have hrel : iteratedDeriv n f z = (Nat.factorial n : 𝕜) • p.coeff n :=
    hp.iteratedDeriv_eq_coeff n
  -- We now prove the derivative is non-zero, completing the goal.
  refine ⟨n, ?_⟩
  intro h_deriv_zero
  -- If the derivative is zero, the corresponding smul is zero.
  have h_smul_zero : (Nat.factorial n : 𝕜) • p.coeff n = 0 := by
    rwa [hrel] at h_deriv_zero
  -- The factorial is non-zero in a field of characteristic zero.
  have h_factorial_ne_zero : (Nat.factorial n : 𝕜) ≠ 0 :=
    by exact_mod_cast Nat.factorial_ne_zero n
  -- A non-zero scalar times a vector is zero iff the vector is zero.
  have h_coeff_zero : p.coeff n = 0 :=
    (smul_eq_zero_iff_ne_zero_of_left h_factorial_ne_zero).mp h_smul_zero
  -- This creates a contradiction with `hn`.
  exact hn h_coeff_zero
end AnalyticAt
namespace Filter
open scoped Filter Topology Set
/-- A property holds eventually in `𝓝[s] a` iff there exists a neighborhood of `a`
where the property holds for all points in the intersection with `s`. -/
theorem eventually_nhdsWithin_iff {α : Type*} [TopologicalSpace α]
    {a : α} {s : Set α} {p : α → Prop} :
    (∀ᶠ x in 𝓝[s] a, p x) ↔ ∀ᶠ x in 𝓝 a, x ∈ s → p x := by
  simp [nhdsWithin, eventually_inf_principal]

end Filter
namespace TopologicalSpace
/-- A subtype has discrete topology iff every singleton (as a subset of the subtype) is open. -/
theorem discreteTopology_iff_isOpen_singleton_mem {α : Type*} [TopologicalSpace α] {s : Set α} :
    DiscreteTopology s ↔ ∀ x : s, IsOpen ({x} : Set s) := by
  constructor
  · intro _
    exact fun _ => isOpen_discrete _
  · intro h
    constructor
    ext U
    constructor
    · intro _; trivial
    · intro _
      -- Show U is open by showing it's a union of open singletons
      have : U = ⋃ x ∈ U, {x} := by
        ext y
        simp only [Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, exists_eq_right']
      rw [this]
      exact isOpen_biUnion (fun x _ => h x)
end TopologicalSpace


/- Convenience alias in the project namespace to match existing calls. -/

namespace RH.RS.BoundaryWedgeProof

open Real Complex
open MeasureTheory

/-! ## Whitney interval and basic structures -/

/-- Whitney interval structure (shared with certificate). -/
abbrev WhitneyInterval := RH.Cert.WhitneyInterval

/-- Canonical interior point for Whitney interval `I` at height `I.len` above the
boundary and horizontally centered at `I.t0`. -/
@[simp] noncomputable def zWhitney (I : WhitneyInterval) : ℂ :=
  ({ re := (1 / 2 : ℝ) + I.len, im := I.t0 } : ℂ)

@[simp] lemma zWhitney_re (I : WhitneyInterval) :
    (zWhitney I).re = (1 / 2 : ℝ) + I.len := rfl

@[simp] lemma zWhitney_im (I : WhitneyInterval) :
    (zWhitney I).im = I.t0 := rfl

/-- Harmonic potential in Whitney half–plane coordinates. For `p = (t, σ)`,
set `s := (1/2 + σ) + I · t` and return `Re (log (J_canonical s))`. -/
noncomputable def U_halfplane (p : ℝ × ℝ) : ℝ :=
  let s : ℂ := (((1 / 2 : ℝ) + p.2) : ℂ) + Complex.I * (p.1 : ℂ)
  (Complex.log (J_canonical s)).re

/-- Gradient of `U_halfplane` with respect to `(t, σ)`, i.e. `(∂ₜ U, ∂ᵪ U)`. -/
noncomputable def gradU_whitney (p : ℝ × ℝ) : ℝ × ℝ :=
  (deriv (fun t : ℝ => U_halfplane (t, p.2)) p.1,
   deriv (fun σ : ℝ => U_halfplane (p.1, σ)) p.2)

/-! ## Product constant calibration -/

lemma product_constant_calibration
  {Cdecay Cν A B : ℝ}
  (hCdecay_nonneg : 0 ≤ Cdecay) (hCν_nonneg : 0 ≤ Cν)
  (hCdecay_le : Cdecay ≤ A) (hCν_le : Cν ≤ B)
  (hAB : A * B ≤ Kxi_paper) :
  Cdecay * Cν ≤ Kxi_paper := by
  have hA_nonneg : 0 ≤ A := le_trans hCdecay_nonneg hCdecay_le
  have h1 : Cdecay * Cν ≤ A * Cν :=
    mul_le_mul_of_nonneg_right hCdecay_le hCν_nonneg
  have h2 : A * Cν ≤ A * B :=
    mul_le_mul_of_nonneg_left hCν_le hA_nonneg
  exact le_trans (le_trans h1 h2) hAB

/-! ## Decay functions and weights -/

/-- Geometric decay weight `(1/4)^k`. -/
@[simp] noncomputable def decay4 (k : ℕ) : ℝ := (1 / 4 : ℝ) ^ k

@[simp] lemma decay4_nonneg (k : ℕ) : 0 ≤ decay4 k := by
  unfold decay4
  have : 0 ≤ (1 / 4 : ℝ) := by norm_num
  exact pow_nonneg this _

@[simp] lemma decay4_le_one (k : ℕ) : decay4 k ≤ 1 := by
  unfold decay4
  have h0 : 0 ≤ (1 / 4 : ℝ) := by norm_num
  have h1 : (1 / 4 : ℝ) ≤ 1 := by norm_num
  exact pow_le_one₀ h0 h1

/-- Packaging weights from counts: `φ k = (1/4)^k · ν_k`. -/
@[simp] noncomputable def phi_of_nu (nu : ℕ → ℝ) (k : ℕ) : ℝ := decay4 k * nu k


/-! ## Residue bookkeeping

This section introduces a minimal placeholder interface for residue bookkeeping,
allowing us to encode that residue contributions are a finite nonnegative sum.
It will be replaced by a genuine residue/winding-number accounting over zeros
of `J_canonical` in the Whitney box once that infrastructure is wired. -/

/-- A residue atom with nonnegative weight (interface form). -/
structure ResidueAtom where
  ρ : ℂ
  weight : ℝ
  hnonneg : 0 ≤ weight

/-- Residue bookkeeping on a Whitney interval: a finite list of atoms and its total. -/
structure ResidueBookkeeping (I : WhitneyInterval) where
  atoms : List ResidueAtom
  total : ℝ := atoms.foldl (fun s a => s + a.weight) 0
  total_nonneg : 0 ≤ total

/-- Residue-based critical atoms total from bookkeeping. -/
@[simp] noncomputable def critical_atoms_res (I : WhitneyInterval) (bk : ResidueBookkeeping I) : ℝ := bk.total

@[simp] lemma critical_atoms_res_nonneg (I : WhitneyInterval) (bk : ResidueBookkeeping I) :
  0 ≤ critical_atoms_res I bk := bk.total_nonneg


@[simp] lemma poissonKernel_zWhitney
    (I : WhitneyInterval) (t : ℝ) :
    RH.AcademicFramework.HalfPlaneOuterV2.poissonKernel (zWhitney I) t
      = (1 / Real.pi) * (I.len / ((I.len) ^ 2 + (t - I.t0) ^ 2)) := by
  have hlen_pos : 0 < I.len := I.len_pos
  simp [RH.AcademicFramework.HalfPlaneOuterV2.poissonKernel, zWhitney]

/-- Poisson balayage (harmonic measure) of the Whitney base interval as seen from
the canonical interior point `zWhitney I`. -/
noncomputable def poisson_balayage (I : WhitneyInterval) : ℝ :=
  ∫ t in I.interval,
    RH.AcademicFramework.HalfPlaneOuterV2.poissonKernel (zWhitney I) t

/-- Poisson balayage is nonnegative: the half‑plane Poisson kernel is nonnegative on Ω. -/
theorem poisson_balayage_nonneg : ∀ I : WhitneyInterval, 0 ≤ poisson_balayage I := by
  intro I
  unfold poisson_balayage
  -- The canonical point belongs to Ω since I.len > 0
  have hzΩ : zWhitney I ∈ RH.AcademicFramework.HalfPlaneOuterV2.Ω := by
    simp [RH.AcademicFramework.HalfPlaneOuterV2.Ω, zWhitney, I.len_pos]
  -- Pointwise kernel nonnegativity on Ω
  have hker_nonneg : ∀ t : ℝ,
      0 ≤ RH.AcademicFramework.HalfPlaneOuterV2.poissonKernel (zWhitney I) t :=
    fun t => RH.AcademicFramework.HalfPlaneOuterV2.poissonKernel_nonneg (z := zWhitney I) hzΩ t
  -- Set integral of a nonnegative function is nonnegative
  refine integral_nonneg_of_ae ?h
  exact Filter.Eventually.of_forall (fun t => hker_nonneg t)

/-! A convenient normalization identity for the Poisson balayage: multiplying by π
turns the Poisson-normalized integrand into its core kernel on the base interval. -/
lemma pi_mul_poisson_balayage_eq_core (I : WhitneyInterval) :
  Real.pi * poisson_balayage I
    = ∫ t in I.interval, I.len / ((I.len) ^ 2 + (t - I.t0) ^ 2) := by
  classical
  unfold poisson_balayage
  -- Expand the Poisson kernel at the canonical Whitney point
  have h :
      (fun t : ℝ =>
        RH.AcademicFramework.HalfPlaneOuterV2.poissonKernel (zWhitney I) t)
      = (fun t : ℝ => (1 / Real.pi) * (I.len / ((I.len) ^ 2 + (t - I.t0) ^ 2))) := by
    funext t; simp
  -- Push the identity under the set integral and cancel π
  simp [mul_comm, mul_left_comm, div_eq_mul_inv]
  -- Pull π into the integral and cancel with π⁻¹
  rw [← integral_const_mul]
  congr 1
  ext t
  ring_nf
  rw [mul_assoc Real.pi I.len, mul_comm I.len, ← mul_assoc, mul_assoc]
  have : Real.pi * Real.pi⁻¹ = 1 := by
    rw [← div_eq_mul_inv, div_self Real.pi_ne_zero]
  rw [this, one_mul]

/-! ### Wiring rectangle interior remainder to Poisson via the core kernel

If an interior remainder `Rint` is identified with the base core kernel integral,
then it equals `π · poisson_balayage I` by the explicit Poisson kernel formula
at the canonical Whitney point. -/
lemma interior_remainder_pi_poisson_of_eq_core
  (I : WhitneyInterval) {Rint : ℝ}
  (hCore : Rint = ∫ t in I.interval, I.len / ((I.len) ^ 2 + (t - I.t0) ^ 2)) :
  Rint = Real.pi * poisson_balayage I := by
  have h := pi_mul_poisson_balayage_eq_core I
  have h' : ∫ t in I.interval, I.len / ((I.len) ^ 2 + (t - I.t0) ^ 2)
              = Real.pi * poisson_balayage I := by
    simpa [eq_comm] using h
  exact hCore.trans h'

/-! ## Dyadic annuli and counts -/

/-- Dyadic scale factor 2^k. -/
@[simp] def dyadicScale (k : ℕ) : ℝ := (2 : ℝ) ^ k

/-- k‑th dyadic annulus around the Whitney center `I.t0` with base size `I.len`.
A point with boundary coordinate `γ` belongs to annulus k if its distance to
`I.t0` is in `(2^k·len, 2^{k+1}·len]`. -/
def annulusDyadic (I : WhitneyInterval) (k : ℕ) (γ : ℝ) : Prop :=
  dyadicScale k * I.len < |γ - I.t0| ∧ |γ - I.t0| ≤ dyadicScale (k + 1) * I.len

/-- Core list recursion for the weighted count on annulus k. -/
noncomputable def nu_dyadic_core (I : WhitneyInterval) (k : ℕ) : List ResidueAtom → ℝ := by
  classical
  exact fun
  | [] => 0
  | (a :: t) => (if annulusDyadic I k a.ρ.im then a.weight else 0) + nu_dyadic_core I k t

/-- Weighted dyadic counts from residue bookkeeping: ν_I,bk(k). -/
@[simp] noncomputable def nu_dyadic (I : WhitneyInterval) (bk : ResidueBookkeeping I) (k : ℕ) : ℝ :=
  nu_dyadic_core I k bk.atoms

/-- Each ν_I,bk(k) is nonnegative since atom weights are nonnegative. -/
lemma nu_dyadic_nonneg (I : WhitneyInterval) (bk : ResidueBookkeeping I) (k : ℕ) :
  0 ≤ nu_dyadic I bk k := by
  unfold nu_dyadic
  -- Prove by recursion on the atoms list
  revert bk
  intro bk
  -- Inner lemma: nonnegativity for any atoms list
  have hCore : ∀ (L : List ResidueAtom), 0 ≤ nu_dyadic_core I k L := by
    classical
    intro L; induction L with
    | nil => simp [nu_dyadic_core]
    | cons a t ih =>
        have hterm : 0 ≤ (if annulusDyadic I k a.ρ.im then a.weight else 0) := by
          by_cases h : annulusDyadic I k a.ρ.im
          · simpa [h] using a.hnonneg
          · simp [h]
        have hrest : 0 ≤ nu_dyadic_core I k t := ih
        exact add_nonneg hterm hrest
  simpa using hCore bk.atoms

/-! ### Canonical residue bookkeeping: finite representation of zeros

This section defines residue bookkeeping for each Whitney interval `I`. Inside the
Whitney box, we enumerate zeros of the completed zeta function (more precisely,
`riemannXi_ext`) and attach to each zero a nonnegative weight proportional to its order
(e.g. `π · order`). The structure `ResidueBookkeeping I` contains:

- `atoms`: a finite list of atoms `(ρ, weight, 0 ≤ weight)`;
- `total`: the total weight, i.e. the finite sum of the atom weights;
- a proof that `total ≥ 0`.

Finiteness of `atoms` follows from the isolated-zero property of analytic functions
and compactness of Whitney boxes. See the lemmas on isolated zeros and the proof that
`zeroSetXi ∩ K` is finite for compact `K`.

References:
- Ahlfors, Complex Analysis (argument principle and residue theorem)
- Koosis, The Logarithmic Integral
- Edwards, Riemann's Zeta Function (zeros of ξ)

-/

/- Canonical residue bookkeeping for Whitney interval `I`.

We enumerate zeros of `riemannXi_ext` inside the Whitney box associated to `I` and
assign weight `π · (order at ρ)` to each zero `ρ`. The atoms are obtained via
`zerosInBox α I` (finite on compact sets) and `zeroOrderAt`. The total weight is
the finite sum of the nonnegative atom weights.

Type safety: the bookkeeping is indexed by `I`, which keeps atoms associated to
the correct interval.
-/

open Complex Filter Set Real Topology RH
open RH.AcademicFramework.CompletedXi
--open RH.RS.Whitney

/-- Upper half-plane chart `(t,σ) ↦ (1/2 + σ) + i t`. -/
@[simp] noncomputable def hpChart (p : ℝ × ℝ) : ℂ := ((1 / 2 : ℝ) + p.2) + (Complex.I : ℂ) * p.1

lemma hpChart_continuous : Continuous hpChart := by
  -- hpChart p = ((1/2 + p.2) : ℂ) + Complex.I * (p.1 : ℝ)
  unfold hpChart
  have h12 :
      Continuous (fun p : ℝ × ℝ => ((2 : ℂ)⁻¹) + ((p.2 : ℝ) : ℂ)) :=
    continuous_const.add (continuous_ofReal.comp continuous_snd)
  have h3 :
      Continuous (fun p : ℝ × ℝ => (Complex.I : ℂ) * ((p.1 : ℝ) : ℂ)) :=
    continuous_const.mul (continuous_ofReal.comp continuous_fst)
  simpa [add_assoc] using h12.add h3


/-- Complex Whitney box over `I` with aperture `α`: image of `I.interval × [0, α|I|]` by `hpChart`.
We use the closed strip `[0, α|I|]` to get compactness (the open/half-open version differs by a null boundary). -/
def whitneyBoxC (α : ℝ) (I : WhitneyInterval) : Set ℂ :=
  hpChart '' ((I.interval) ×ˢ Set.Icc (0 : ℝ) (α * I.len))

lemma whitneyBoxC_compact (α : ℝ) (I : WhitneyInterval) :
    IsCompact (whitneyBoxC α I) := by
  have hIntC : IsCompact (I.interval) := by
    -- `I.interval` is `Icc`, hence compact
    simpa [RH.Cert.WhitneyInterval.interval] using isCompact_Icc
  have hSegC : IsCompact (Set.Icc (0 : ℝ) (α * I.len)) := isCompact_Icc
  have hProd := hIntC.prod hSegC
  have hcont : Continuous hpChart := hpChart_continuous
  simpa [whitneyBoxC] using hProd.image hcont

/-- Zero set of `riemannXi_ext`. -/
def zeroSetXi : Set ℂ := {z | riemannXi_ext z = 0}

open Set RH.AcademicFramework.CompletedXi

lemma analyticAt_completedRiemannZeta (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
  AnalyticAt ℂ completedRiemannZeta s := by
  classical
  -- Work on the open set U = ℂ \ {0,1}
  let U : Set ℂ := ({0} : Set ℂ)ᶜ ∩ ({1} : Set ℂ)ᶜ
  have hU_open : IsOpen U :=
    (isOpen_compl_iff.mpr isClosed_singleton).inter
      (isOpen_compl_iff.mpr isClosed_singleton)
  -- s ∈ U
  have hsU : s ∈ U := by
    refine And.intro ?hs0' ?hs1'
    · change s ∉ ({0} : Set ℂ)
      simpa [Set.mem_singleton_iff] using hs0
    · change s ∉ ({1} : Set ℂ)
      simpa [Set.mem_singleton_iff] using hs1
  -- Differentiability of completedRiemannZeta on U
  have hDiffOn : DifferentiableOn ℂ completedRiemannZeta U := by
    intro z hz
    have hz0 : z ≠ 0 := by
      have hnot : z ∉ ({0} : Set ℂ) := hz.1
      simpa [Set.mem_singleton_iff] using hnot
    have hz1 : z ≠ 1 := by
      have hnot : z ∉ ({1} : Set ℂ) := hz.2
      simpa [Set.mem_singleton_iff] using hnot
    exact (differentiableAt_completedZeta (s := z) hz0 hz1).differentiableWithinAt
  -- Analytic on U, hence analytic at s (U is open, s ∈ U)
  have hAnalOn :
      AnalyticOn ℂ completedRiemannZeta U :=
    (analyticOn_iff_differentiableOn
      (f := completedRiemannZeta) (s := U) hU_open).mpr hDiffOn
  have hAnalOnNhd :
      AnalyticOnNhd ℂ completedRiemannZeta U :=
    (hU_open.analyticOn_iff_analyticOnNhd (𝕜 := ℂ) (f := completedRiemannZeta)).1 hAnalOn
  exact hAnalOnNhd s hsU

lemma zeroSetXi_relClosed_off_poles :
    ∃ u : Set ℂ, IsClosed u ∧
      zeroSetXi ∩ (({0} : Set ℂ)ᶜ ∩ ({1} : Set ℂ)ᶜ)
        = u ∩ (({0} : Set ℂ)ᶜ ∩ ({1} : Set ℂ)ᶜ) := by
  -- On ℂ \ {0,1}, riemannXi_ext is continuous, so the preimage of {0} is relatively closed.
  have hcont : ContinuousOn riemannXi_ext (({0} : Set ℂ)ᶜ ∩ ({1} : Set ℂ)ᶜ) :=
    riemannXi_ext_continuous_on_compl01
  obtain ⟨u, hu_closed, hu_eq⟩ :=
    (continuousOn_iff_isClosed).1 hcont ({0} : Set ℂ) isClosed_singleton
  refine ⟨u, hu_closed, ?_⟩
  simpa [zeroSetXi, Set.preimage, Set.mem_setOf_eq, Set.inter_assoc] using hu_eq

theorem summable_one_div_nat_rpow {p : ℝ} :
    Summable (fun n => 1 / (n : ℝ) ^ p : ℕ → ℝ) ↔ 1 < p := by
  simp

-- P-series on ℝ: ∑ 1/(n+1)^p converges for p > 1
lemma summable_one_div_nat_pow (p : ℝ) (hp : 1 < p) :
  Summable (fun n : ℕ => 1 / (n + 1 : ℝ) ^ p) := by
  -- Get the p-series (unshifted) and then shift the index by 1
  have h0 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) :=
    (Real.summable_one_div_nat_rpow (p := p)).mpr hp
  simpa [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ p) 1).2 h0

lemma summable_one_div_nat_pow_two :
  Summable (fun n : ℕ => 1 / (n + 1 : ℝ) ^ 2) := by
  simpa [Real.rpow_natCast] using summable_one_div_nat_pow 2 (by norm_num)

-- A positive Dirichlet-series value for ζ at 2
lemma riemannZeta_two_ne_zero : riemannZeta (2 : ℂ) ≠ 0 := by
  -- On Re s > 1, ζ s = ∑' (n ≥ 1) 1 / n^s; specialize at s = 2
  have _ : (1 : ℝ) < (2 : ℝ) := by norm_num
  have hz :
      riemannZeta (2 : ℂ)
        = ∑' n : ℕ, (1 : ℂ) / (n + 1 : ℂ) ^ (2 : ℂ) := by
    simpa using
      (zeta_eq_tsum_one_div_nat_add_one_cpow (s := (2 : ℂ))
        (by simp))
  -- Rewrite RHS as ofReal of a strictly positive real series
  have hcpow :
      ∀ n : ℕ, (1 : ℂ) / (n + 1 : ℂ) ^ (2 : ℂ)
              = Complex.ofReal (1 / (n + 1 : ℝ) ^ 2) := by
    intro n
    simp [pow_two, Complex.ofReal_inv, Complex.ofReal_mul]
  have hz' :
      riemannZeta (2 : ℂ)
        = Complex.ofReal (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ 2) := by
    simp [hz, Complex.ofReal_tsum]  -- all terms are real
  -- The real series is > 0 as its first term is 1 and all terms are ≥ 0.
  have hpos :
      0 < (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ 2) := by
    -- Use tsum decomposition: tsum a = a 0 + tsum (tail)
    have hdecomp := Summable.tsum_eq_zero_add (f := fun n : ℕ => 1 / (n + 1 : ℝ) ^ 2)
    have htail_nonneg :
        0 ≤ ∑' n : ℕ, 1 / (n + 2 : ℝ) ^ 2 :=
      tsum_nonneg (fun n => by
        have : 0 ≤ 1 / (n + 2 : ℝ) ^ 2 := by
          have : 0 < (n + 2 : ℝ) := by exact add_pos_of_nonneg_of_pos (by positivity) (by norm_num)
          have hxpos : 0 < ((n + 2 : ℝ) ^ 2) := by positivity
          have hinv_nonneg : 0 ≤ ((n + 2 : ℝ) ^ 2)⁻¹ := inv_nonneg.mpr (le_of_lt hxpos)
          simpa [one_div] using hinv_nonneg
        simpa [Real.norm_eq_abs, Complex.norm_of_nonneg this] using this)
    -- tsum = 1 + nonneg tail > 0
    have hsummable : Summable (fun n : ℕ => 1 / (n + 1 : ℝ) ^ 2) :=
      summable_one_div_nat_pow_two
    have heq :
        (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ 2)
          = 1 + (∑' n : ℕ, 1 / (n + 2 : ℝ) ^ 2) := by
      simpa [Nat.cast_add, Nat.cast_one, one_div, one_add_one_eq_two,
              add_comm, add_left_comm, add_assoc]
        using hdecomp hsummable
    have hpos_tail : 0 < 1 + (∑' n : ℕ, 1 / (n + 2 : ℝ) ^ 2) := by
      exact add_pos_of_pos_of_nonneg (by norm_num) htail_nonneg
    rw [heq]
    exact hpos_tail
  -- Conclude ζ(2) has positive real part, hence ζ(2) ≠ 0
  have : (riemannZeta (2 : ℂ)).re ≠ 0 := by
    simpa [hz'] using ne_of_gt hpos
  exact fun h0 => this (by simp [h0])

-- Completed zeta at 2 is nonzero (use factorization on Ω)
lemma completedRiemannZeta_two_ne_zero : completedRiemannZeta (2 : ℂ) ≠ 0 := by
  -- On Ω, Λ = Γℝ · ζ; at 2, Γℝ(2) ≠ 0 and ζ(2) ≠ 0
  have hΩ : (1 / 2 : ℝ) < (2 : ℝ) := by norm_num
  have hΓ : Complex.Gammaℝ (2 : ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp)
  have hfact := RH.AcademicFramework.CompletedXi.xi_ext_factorization_on_Ω
                  (z := (2 : ℂ)) (by simpa [RH.RS.Ω, Set.mem_setOf_eq] using hΩ)
  -- riemannXi_ext = completedRiemannZeta; G_ext = Gammaℝ
  have : completedRiemannZeta (2 : ℂ)
       = Complex.Gammaℝ (2 : ℂ) * riemannZeta (2 : ℂ) := by
    simpa [RH.AcademicFramework.CompletedXi.riemannXi_ext,
           RH.AcademicFramework.CompletedXi.G_ext] using hfact
  intro hΛ
  have hprod0 : Complex.Gammaℝ (2 : ℂ) * riemannZeta (2 : ℂ) = 0 := by
    aesop
  have hprod_ne : Complex.Gammaℝ (2 : ℂ) * riemannZeta (2 : ℂ) ≠ 0 :=
    mul_ne_zero hΓ riemannZeta_two_ne_zero
  exact hprod_ne hprod0

/-! ### Non-vanishing at special points (fully implemented) -/

-- Λ(1) ≠ 0, via the identity Λ(1) = ζ(1) (since Γℝ(1) = 1) and `riemannZeta_one_ne_zero`
lemma completedRiemannZeta_one_ne_zero : completedRiemannZeta (1 : ℂ) ≠ 0 := by
  -- From mathlib: `riemannZeta 1 = completedRiemannZeta 1 / Gammaℝ 1`
  have hdef :
      riemannZeta (1 : ℂ) = completedRiemannZeta 1 / Complex.Gammaℝ 1 :=
    by
      simpa using
        (riemannZeta_def_of_ne_zero (s := (1 : ℂ)) (by exact one_ne_zero))
  -- But `Gammaℝ 1 = 1`
  have hΓ : Complex.Gammaℝ (1 : ℂ) = 1 := by
    simp
  -- Hence `riemannZeta 1 = completedRiemannZeta 1`
  have : riemannZeta (1 : ℂ) = completedRiemannZeta 1 := by
    simpa [hΓ, div_one] using hdef
  -- Conclude by `riemannZeta_one_ne_zero` from mathlib
  exact fun h => riemannZeta_one_ne_zero (by simpa [this] using h)

-- Λ(0) ≠ 0 by the functional equation Λ(0) = Λ(1) and the above
lemma completedRiemannZeta_zero_ne_zero : completedRiemannZeta (0 : ℂ) ≠ 0 := by
  -- Functional equation at `s = 1`: `Λ(1 - 1) = Λ(1)`
  have hFE : completedRiemannZeta (0 : ℂ) = completedRiemannZeta 1 := by
    simpa using (completedRiemannZeta_one_sub (1 : ℂ))
  -- Conclude
  exact fun h0 => completedRiemannZeta_one_ne_zero (by simpa [hFE] using h0)

lemma completedRiemannZeta_not_locally_zero_on_U :
  ∀ z ∈ (({0} : Set ℂ)ᶜ ∩ ({1} : Set ℂ)ᶜ), ¬ (∀ᶠ w in 𝓝 z, completedRiemannZeta w = 0) := by
  classical
  intro z hz heq
  -- Analytic on U as an open set (from the earlier analyticOn proof)
  let U : Set ℂ := (({0} : Set ℂ)ᶜ ∩ ({1} : Set ℂ)ᶜ)
  have hUopen : IsOpen U := by
    simpa [U] using
      (IsOpen.inter (isOpen_compl_iff.mpr isClosed_singleton)
                    (isOpen_compl_iff.mpr isClosed_singleton))
  have hAnalOnU : AnalyticOn ℂ completedRiemannZeta U := by
    intro w hw
    have hw0 : w ≠ 0 := by
      have : w ∉ ({0} : Set ℂ) := hw.left
      simpa [Set.mem_singleton_iff] using this
    have hw1 : w ≠ 1 := by
      have : w ∉ ({1} : Set ℂ) := hw.2
      simpa [Set.mem_singleton_iff] using this
    exact (analyticAt_completedRiemannZeta (s := w) hw0 hw1).analyticWithinAt
  -- Identity principle: if analytic on a preconnected set and frequently zero near z, then zero on all of U
  have hfre :
      ∃ᶠ w in 𝓝[≠] z, completedRiemannZeta w = 0 := by
    -- from IsolatedZeros: eventually ⇒ frequently on punctured nhds
    have hzAn : AnalyticAt ℂ completedRiemannZeta z := by
      -- z ∈ U ⇒ differentiable at z (since z ≠ 0,1)
      have hz0 : z ≠ 0 := by
        have : z ∉ ({0} : Set ℂ) := hz.1
        simpa [Set.mem_singleton_iff] using this
      have hz1 : z ≠ 1 := by
        have : z ∉ ({1} : Set ℂ) := hz.2
        simpa [Set.mem_singleton_iff] using this
      simpa [AnalyticAt] using
        (analyticAt_completedRiemannZeta (s := z) hz0 hz1)
    -- use AnalyticAt.frequently_zero_iff_eventually_zero
    simpa using
      (AnalyticAt.frequently_zero_iff_eventually_zero
        (𝕜 := ℂ) (f := completedRiemannZeta) (w := z) hzAn).mpr heq
  -- Use identity principle on the preconnected set U (ℂ minus two points is preconnected)
  have hUpre : IsPreconnected U := by
    -- ℂ \ finite set is connected when `rank ℝ ℂ > 1`, hence preconnected.
    have hfin : ({0} ∪ ({1} : Set ℂ)).Finite :=
      (Set.finite_singleton (0 : ℂ)).union (Set.finite_singleton (1 : ℂ))
    have hcount : ({0} ∪ ({1} : Set ℂ)).Countable := hfin.countable
    have hconn :
        IsConnected (({0} ∪ ({1} : Set ℂ))ᶜ) :=
      Set.Countable.isConnected_compl_of_one_lt_rank
        (rank_real_complex ▸ Nat.one_lt_ofNat) hcount
    have hpre' :
        IsPreconnected (({0} : Set ℂ)ᶜ ∩ ({1} : Set ℂ)ᶜ) := by
      rw [← Set.compl_union]
      exact hconn.isPreconnected
    simpa [U] using hpre'
  have hEqOn :
      EqOn completedRiemannZeta 0 U :=
    (AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (hUopen.analyticOn_iff_analyticOnNhd.mp hAnalOnU) hUpre hz hfre)
  -- Evaluate at s = 2 ∈ U: contradiction with nonvanishing
  have h2U : (2 : ℂ) ∈ U := by
    simp [U]
  have : completedRiemannZeta (2 : ℂ) = 0 := hEqOn h2U
  exact completedRiemannZeta_two_ne_zero this

-- Zeros are finite on compact sets avoiding {0,1}.
lemma zeroSetXi_inter_compact_finite_on_U
  {K : Set ℂ} (hK : IsCompact K)
  (hKU : K ⊆ (({0} : Set ℂ)ᶜ ∩ ({1} : Set ℂ)ᶜ)) :
  Set.Finite (zeroSetXi ∩ K) := by
  classical
  -- Strategy: show each zero in K is isolated, then use compactness
  let S := zeroSetXi ∩ K
  -- S is closed in K
  have hSClosed : IsClosed S := by
    show IsClosed (zeroSetXi ∩ K)
    -- zeroSetXi ∩ K is the preimage of {0} under completedRiemannZeta, intersected with K
    -- Since completedRiemannZeta is continuous on K (which avoids {0,1}), this is closed
    have : zeroSetXi ∩ K = K ∩ {z | completedRiemannZeta z = 0} := Set.inter_comm _ _
    rw [this]
    exact ContinuousOn.preimage_isClosed_of_isClosed
      (RH.AcademicFramework.CompletedXi.riemannXi_ext_continuous_on_compl01.mono hKU)
      hK.isClosed isClosed_singleton
  -- S is compact
  have hSCompact : IsCompact S := hK.of_isClosed_subset hSClosed (Set.inter_subset_right)
  -- Each point of S has an isolating neighborhood
  have hIsolated : ∀ z ∈ S, ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ S ∩ V = {z} := by
    intro z ⟨hzZero, hzK⟩
    have hzU : z ∈ (({0} : Set ℂ)ᶜ ∩ ({1} : Set ℂ)ᶜ) := hKU hzK
    have hz0 : z ≠ 0 := fun h => hzU.1 (h ▸ Set.mem_singleton z)
    have hz1 : z ≠ 1 := fun h => hzU.2 (h ▸ Set.mem_singleton z)
    -- Analyticity gives isolated zeros
    have hAn : AnalyticAt ℂ completedRiemannZeta z :=
      analyticAt_completedRiemannZeta z hz0 hz1
    rcases AnalyticAt.eventually_eq_zero_or_eventually_ne_zero hAn with hEqZero | hNeZero
    · -- Can't be eventually zero (would contradict ζ(2) ≠ 0 by identity principle)
      exfalso
      exact completedRiemannZeta_not_locally_zero_on_U z hzU hEqZero
    · -- Get isolating neighborhood from eventually_ne_zero
      -- hNeZero : ∀ᶠ (w : ℂ) in 𝓝[≠] z, completedRiemannZeta w ≠ 0
      -- This means there exists a neighborhood V of z where completedRiemannZeta is nonzero except possibly at z
      -- From eventually in nhdsWithin, extract a neighborhood where the property holds
      have hNeZero_nhds : ∀ᶠ x in 𝓝 z, x ≠ z → completedRiemannZeta x ≠ 0 := by
        exact Filter.eventually_nhdsWithin_iff.mp hNeZero --refine hNeZero.mono fun x hx => ?_
      obtain ⟨V, hVmem, hVne⟩ : ∃ V ∈ 𝓝 z, ∀ x ∈ V, x ≠ z → completedRiemannZeta x ≠ 0 := by
        rwa [Filter.eventually_iff_exists_mem] at hNeZero_nhds
      rcases mem_nhds_iff.mp hVmem with ⟨W, hWV, hWopen, hzW⟩
      refine ⟨W, hWopen, hzW, ?_⟩
      ext w
      simp [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · intro ⟨⟨hwZero, _⟩, hwW⟩
        by_contra hwne
        have hwV : w ∈ V := hWV hwW
        have hne0 : completedRiemannZeta w ≠ 0 := hVne w hwV hwne
        exact hne0 hwZero
      · intro hw
        subst hw
        exact ⟨⟨hzZero, hzK⟩, hzW⟩
  -- Use compactness to get finiteness
  -- Each point has an isolating neighborhood, so S is discrete
  -- A compact discrete space is finite
  have : DiscreteTopology S := by
    rw [TopologicalSpace.discreteTopology_iff_isOpen_singleton_mem]
    intro ⟨z, hzS⟩
    obtain ⟨V, hVopen, hzV, hSV⟩ := hIsolated z hzS
    -- Show {⟨z, hzS⟩} is open in S
    -- Use that V ⊆ ℂ is open and S ∩ V = {z}
    have : ({⟨z, hzS⟩} : Set S) = (Subtype.val : S → ℂ) ⁻¹' V := by
      ext ⟨w, hwS⟩
      simp only [Set.mem_singleton_iff, Set.mem_preimage, Subtype.mk.injEq]
      constructor
      · intro hw
        subst hw
        exact hzV
      · intro hwV
        have hiff : (w ∈ S ∩ V) ↔ w = z := by
          have : (w ∈ S ∩ V) ↔ w ∈ ({z} : Set ℂ) := by simp [hSV]
          simp [Set.mem_singleton_iff] at this
          exact this
        exact hiff.mp ⟨hwS, hwV⟩
    rw [this]
    exact hVopen.preimage continuous_subtype_val

  have hSDiscrete : IsDiscrete (zeroSetXi ∩ K) := by
    rw [isDiscrete_iff_discreteTopology]
    exact this
  exact IsCompact.finite hSCompact hSDiscrete

/-
/-- Zeros of a nontrivial analytic function are isolated: on any compact set they are finite.
We package the standard result: `zeroSetXi ∩ K` is finite for any compact `K`. -/
lemma zeroSetXi_inter_compact_finite' {K : Set ℂ} (hK : IsCompact K) :
    Set.Finite (zeroSetXi ∩ K) := by
  -- Use: zeros are closed & discrete; closed discrete subset meets a compact set in finitely many points.
  -- This is `tendsto_cofinite_cocompact_iff` + `IsClosed.tendsto_coe_cofinite_iff`.
  -- Step 1: zero set is closed (done above). It is discrete by isolated zeros of analytic functions.
  have hClosed : IsClosed zeroSetXi := zeroSetXi_isClosed
  -- Discreteness: for each z with `riemannXi_ext z = 0`, analyticity implies an isolated zero (unless identically zero).
  -- Since `riemannXi_ext 2 ≠ 0`, it is not identically zero on any open set; hence zeros are isolated globally.
  have hNotIdent : riemannXi_ext 2 ≠ 0 := by
    -- classical fact: ζ(2) ≠ 0 ⇒ Λ(2) ≠ 0; in mathlib this is standard
    -- Replace with a direct reference available in your version.
    admit
  have hDiscr : DiscreteTopology zeroSetXi := by
    -- Use `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` at each zero
    -- and `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` to exclude the "identically zero" branch.
    -- This is a standard argument; see Mathlib.Analysis.Analytic.IsolatedZeros.
    -- We only sketch it here; replace `admit` with the standard proof if desired.
    admit
  -- Now apply `IsClosed.tendsto_coe_cofinite_iff` + `tendsto_cofinite_cocompact_iff`
  -- to conclude: compact sets meet `zeroSetXi` in finitely many points.
  have hTendsto :
      Tendsto ((↑) : zeroSetXi → ℂ) cofinite (cocompact ℂ) :=
    (IsClosed.tendsto_coe_cofinite_iff (X := ℂ) (s := zeroSetXi)).mpr hDiscr
  -- `tendsto_cofinite_cocompact_iff` gives finite preimages of compact sets
  have hFinPre := (tendsto_cofinite_cocompact_iff.mp hTendsto) K hK
  -- Translate to the statement about `zeroSetXi ∩ K`.
  -- `f ⁻¹' K` for the subtype inclusion is precisely `Subtype.val ⁻¹' K = {x | (x : ℂ) ∈ K}`,
  -- which corresponds to `zeroSetXi ∩ K`.
  simpa [Set.preimage, Set.inter_eq_left, Set.mem_setLike, Subtype.coe_prop] using hFinPre
  -/

/- Finite list of zeros of `riemannXi_ext` in the complex Whitney box.

**Mathematical content**: The intersection `zeroSetXi ∩ whitneyBoxC α I` is finite because:
1. `whitneyBoxC α I` is compact (closed and bounded image of compact rectangle)
2. Zeros of an analytic function on a compact set are isolated, hence finite
3. The zeros automatically avoid {0, 1} (neither is a zero of completedRiemannZeta)

**Proof strategy**: Apply the principle of isolated zeros for analytic functions:
- `completedRiemannZeta` is analytic on ℂ \ {0, 1}
- The identity principle shows zeros are isolated (cannot accumulate)
- On a compact set, an isolated set is finite

**References**:
- Ahlfors, "Complex Analysis" (1979), §5.3 Theorem 6 (isolated zeros)
- Conway, "Functions of One Complex Variable" (1978), Theorem VII.2.6

**Implementation status**: The full proof requires:
1. Showing `whitneyBoxC α I ⊆ ℂ \ {0, 1}` (needs architectural constraint α · I.len < 1/2)
2. Applying `zeroSetXi_inter_compact_finite_on_U` with appropriate hypotheses
3. We axiomatize the finiteness, as it's a standard consequence of our prior lemmas plus
   the calibration constraint (α = 0.08, typical I.len ≤ 1 ⇒ α · I.len < 1/2).
-/


/-- Zeros of `riemannXi_ext` are finite on any compact set (no avoidance hypothesis).

Proof idea:
- Near `s = 1`, the function `(s - 1) · Λ(s)` extends continuously with value `1`, hence there
  is a neighborhood `U₁` of `1` free of zeros of `Λ`.
- Near `s = 0`, the function `s · Λ(s)` extends continuously with value `-1`, hence there is
  a neighborhood `U₀` of `0` free of zeros of `Λ`.
- On the compact set `K' = K \ (U₀ ∪ U₁) ⊆ ℂ \ {0,1}`, apply the earlier finiteness lemma
  `zeroSetXi_inter_compact_finite_on_U`.
- Since there are no zeros in `U₀ ∪ U₁`, we have `zeroSetXi ∩ K = zeroSetXi ∩ K'`, hence finite.
-/
lemma zeroSetXi_inter_compact_finite
  {K : Set ℂ} (hK : IsCompact K) : Set.Finite (zeroSetXi ∩ K) := by
  classical
  -- Define helper functions that are continuous at the special points
  -- g₁(s) = (s-1)·Λ₀(s) - (s-1)/s + 1 equals (s-1)·Λ(s) for s ≠ 1 and satisfies g₁(1) = 1
  let g₁ : ℂ → ℂ := fun s => (s - 1) * completedRiemannZeta₀ s - (s - 1) / s + 1
  -- g₀(s) = s·Λ₀(s) - 1 - s/(1-s) equals s·Λ(s) for s ≠ 0 and satisfies g₀(0) = -1
  let g₀ : ℂ → ℂ := fun s => s * completedRiemannZeta₀ s - 1 - s / (1 - s)
  -- Continuity at the special points and evaluation there
  have hcont₁ : ContinuousAt g₁ 1 := by
    -- Each term is continuous at 1 (no denominator vanishes at 1)
    have hΛ0 : ContinuousAt completedRiemannZeta₀ 1 :=
      (differentiable_completedZeta₀ 1).continuousAt
    have hlin : ContinuousAt (fun s : ℂ => s - 1) 1 :=
      (continuousAt_id.sub continuousAt_const)
    have hmul : ContinuousAt (fun s : ℂ => (s - 1) * completedRiemannZeta₀ s) 1 :=
      hlin.mul (hΛ0)
    have hdiv : ContinuousAt (fun s : ℂ => (s - 1) / s) 1 := by
      -- (s - 1)/s = (s - 1) * (1/s); both factors continuous at 1
      have hinv : ContinuousAt (fun s : ℂ => s⁻¹) 1 :=
        (continuousAt_inv₀ (by simp)).comp continuousAt_id
      exact (hlin.mul hinv)
    simpa [g₁] using hmul.sub hdiv |>.add continuousAt_const
  have hg₁_one : g₁ 1 = (1 : ℂ) := by
    simp [g₁]
  have hcont₀ : ContinuousAt g₀ 0 := by
    -- Each term is continuous at 0 (no denominator vanishes at 0 in s/(1-s))
    have hΛ0 : ContinuousAt completedRiemannZeta₀ 0 :=
      (differentiable_completedZeta₀ 0).continuousAt
    have hlin : ContinuousAt (fun s : ℂ => s) 0 := continuousAt_id
    have hmul : ContinuousAt (fun s : ℂ => s * completedRiemannZeta₀ s) 0 :=
      hlin.mul hΛ0
    have hdiv : ContinuousAt (fun s : ℂ => s / (1 - s)) 0 := by
      -- s/(1-s) = s * (1/(1-s)); denominator ≠ 0 at 0
      have hden : ContinuousAt (fun s : ℂ => 1 - s) 0 :=
        (continuousAt_const.sub continuousAt_id)
      have hden0 : (1 - (0 : ℂ)) ≠ 0 := by simp
      have hinv : ContinuousAt (fun s : ℂ => (1 - s)⁻¹) 0 :=
        (continuousAt_inv₀ hden0).comp hden
      have hmul' : ContinuousAt (fun s : ℂ => s * (1 - s)⁻¹) 0 :=
        hlin.mul hinv
      exact (by simpa [div_eq_mul_inv] using hmul')
    simpa [g₀] using (hmul.sub continuousAt_const).sub hdiv
  have hg₀_zero : g₀ 0 = (-1 : ℂ) := by
    simp [g₀]
  -- Neighborhoods free of zeros near 1 and 0 via continuity and nonvanishing
  have hU₁ : {z | g₁ z ≠ 0} ∈ 𝓝 (1 : ℂ) := by
    -- Use that {0}ᶜ is an open neighborhood of g₁ 1
    have hopen : IsOpen (({0} : Set ℂ)ᶜ) := isOpen_compl_iff.mpr isClosed_singleton
    have hmem : g₁ 1 ∈ (({0} : Set ℂ)ᶜ) := by simp [hg₁_one]
    exact hcont₁.preimage_mem_nhds (isOpen_iff_mem_nhds.mp hopen _ hmem)
  obtain ⟨U₁, hU₁mem, hU₁subset⟩ :
      ∃ U₁ ∈ 𝓝 (1 : ℂ), U₁ ⊆ {z | g₁ z ≠ 0} := by
    -- standard nhds extraction
    aesop--simpa [Filter.eventually_iff_exists_mem] using hU₁
  have hU₀ : {z | g₀ z ≠ 0} ∈ 𝓝 (0 : ℂ) := by
    have hopen : IsOpen (({0} : Set ℂ)ᶜ) := isOpen_compl_iff.mpr isClosed_singleton
    have hmem : g₀ 0 ∈ (({0} : Set ℂ)ᶜ) := by simp [hg₀_zero]
    exact hcont₀.preimage_mem_nhds (isOpen_iff_mem_nhds.mp hopen _ hmem)
  obtain ⟨U₀, hU₀mem, hU₀subset⟩ :
      ∃ U₀ ∈ 𝓝 (0 : ℂ), U₀ ⊆ {z | g₀ z ≠ 0} := by
    aesop--simpa [Filter.eventually_iff_exists_mem] using hU₀
  -- On U₁ and U₀ there are no zeros of Λ
  have hNoZero_U₁ :
      zeroSetXi ∩ U₁ = (∅ : Set ℂ) := by
    -- If z ∈ U₁ then g₁ z ≠ 0; for z ≠ 1 it implies Λ z ≠ 0;
    -- for z = 1 we have `completedRiemannZeta_one_ne_zero`.
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    rcases hz with ⟨hzZero, hzU⟩
    have hg1_ne : g₁ z ≠ 0 := hU₁subset hzU
    have hz_not_one_or : z = 1 ∨ z ≠ 1 := em (z = 1)
    rcases hz_not_one_or with rfl | hzne1
    · -- z = 1
      -- zeroSetXi at 1 contradicts nonvanishing at 1
      have : completedRiemannZeta (1 : ℂ) = 0 := by
        simpa [zeroSetXi, RH.AcademicFramework.CompletedXi.riemannXi_ext] using hzZero
      exact completedRiemannZeta_one_ne_zero this
    · -- z ≠ 1: use that (z-1)·Λ(z) = g₁ z ≠ 0
      have hΛ_ne : completedRiemannZeta z ≠ 0 := by
        -- For z ≠ 1, from completedRiemannZeta_eq:
        -- g₁ z = (z - 1) * completedRiemannZeta z
        have hg1_eq :
            g₁ z = (z - 1) * completedRiemannZeta z := by
          -- expand Λ via Λ₀ and split the (z-1)/(1 - z) term
          have hΛ :
              completedRiemannZeta z
                = completedRiemannZeta₀ z - 1 / z - 1 / (1 - z) := by
            simpa using completedRiemannZeta_eq z
          -- denominator is nonzero since z ≠ 1
          have hz1 : (1 - z) ≠ 0 := sub_ne_zero.mpr (ne_comm.mp hzne1)
          -- (z - 1)/(1 - z) = -1
          have hdiv : (z - 1) / (1 - z) = (-1 : ℂ) := by
            field_simp [hz1]; simp
          -- compare g₁ with (z - 1) * Λ and use hdiv
          have : g₁ z - (z - 1) * completedRiemannZeta z
                = 1 + (z - 1) / (1 - z) := by
            have :
                (z - 1) * completedRiemannZeta z
                  = (z - 1) * completedRiemannZeta₀ z - (z - 1) / z - (z - 1) / (1 - z) := by
              rw [hΛ]
              ring
            calc g₁ z - (z - 1) * completedRiemannZeta z
                = (z - 1) * completedRiemannZeta₀ z - (z - 1) / z + 1
                    - ((z - 1) * completedRiemannZeta₀ z - (z - 1) / z - (z - 1) / (1 - z)) := by
                  simp [g₁, this]
              _ = 1 + (z - 1) / (1 - z) := by ring
          have : g₁ z - (z - 1) * completedRiemannZeta z = 0 := by
            simpa [hdiv] using this
          exact sub_eq_zero.mp this
        -- now divide by (z-1) ≠ 0
        exact fun h0 => hg1_ne (by simp [hg1_eq, h0] : g₁ z = 0)
      -- contradiction with zeroSet definition
      exact hΛ_ne (by simpa [zeroSetXi, RH.AcademicFramework.CompletedXi.riemannXi_ext] using hzZero)
  have hNoZero_U₀ :
      zeroSetXi ∩ U₀ = (∅ : Set ℂ) := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    rcases hz with ⟨hzZero, hzU⟩
    have hg0_ne : g₀ z ≠ 0 := hU₀subset hzU
    have hz_not_zero_or : z = 0 ∨ z ≠ 0 := em (z = 0)
    rcases hz_not_zero_or with rfl | hzne0
    · -- z = 0
      have : completedRiemannZeta (0 : ℂ) = 0 := by
        simpa [zeroSetXi, RH.AcademicFramework.CompletedXi.riemannXi_ext] using hzZero
      exact completedRiemannZeta_zero_ne_zero this
    · -- z ≠ 0: g₀ z = z * Λ z ≠ 0 ⇒ Λ z ≠ 0
      have hΛ_ne : completedRiemannZeta z ≠ 0 := by
        have hg0_eq : g₀ z = z * completedRiemannZeta z := by
          have : completedRiemannZeta z
              = completedRiemannZeta₀ z - 1 / z - 1 / (1 - z) := by
            simpa using completedRiemannZeta_eq z
          simp [g₀, this, sub_eq_add_neg, add_comm, add_assoc,
                mul_add, div_eq_mul_inv, hzne0]
        exact fun h0 => hg0_ne (by simp [hg0_eq, h0] : g₀ z = 0)
      exact hΛ_ne (by simpa [zeroSetXi, RH.AcademicFramework.CompletedXi.riemannXi_ext] using hzZero)
  -- Remove neighborhoods U₀ ∪ U₁ from K; compact remainder, avoiding {0,1}
  let K' : Set ℂ := K \ (interior U₀ ∪ interior U₁)
  have hK' : IsCompact K' := hK.diff (IsOpen.union isOpen_interior isOpen_interior)
  -- Replace K by K' for zeros
  have hZeros_eq :
      zeroSetXi ∩ K = zeroSetXi ∩ K' := by
    ext z
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨h_zero, hK_mem⟩
      refine ⟨h_zero, hK_mem, ?_⟩
      by_contra h_in_int
      rcases h_in_int with (h_in_U₀ | h_in_U₁)
      · have h_in_U₀' : z ∈ U₀ := interior_subset h_in_U₀
        have : z ∈ zeroSetXi ∩ U₀ := ⟨h_zero, h_in_U₀'⟩
        rw [hNoZero_U₀] at this; exact this
      · have h_in_U₁' : z ∈ U₁ := interior_subset h_in_U₁
        have : z ∈ zeroSetXi ∩ U₁ := ⟨h_zero, h_in_U₁'⟩
        rw [hNoZero_U₁] at this; exact this
    · rintro ⟨h_zero, hK_mem, _⟩
      exact ⟨h_zero, hK_mem⟩
  -- K' avoids {0,1}
  have hK'U : K' ⊆ (({0} : Set ℂ)ᶜ ∩ ({1} : Set ℂ)ᶜ) := by
    intro z hz
    have h_not_in_int : z ∉ interior U₀ ∪ interior U₁ := hz.2
    refine ⟨?_, ?_⟩
    · intro h_z_eq_0; subst h_z_eq_0
      exact h_not_in_int (Set.mem_union_left _ (mem_interior_iff_mem_nhds.mpr hU₀mem))
    · intro h_z_eq_1; subst h_z_eq_1
      exact h_not_in_int (Set.mem_union_right _ (mem_interior_iff_mem_nhds.mpr hU₁mem))
  -- Compactness of K' and avoidance allow applying the previous finiteness lemma
  have hfin' : Set.Finite (zeroSetXi ∩ K') :=
    zeroSetXi_inter_compact_finite_on_U hK' hK'U

  -- Translate back to K via equality
  simpa [hZeros_eq] using hfin'

noncomputable def zerosInBox (α : ℝ) (I : WhitneyInterval) : Finset ℂ :=
  (zeroSetXi_inter_compact_finite (whitneyBoxC_compact α I)).toFinset

lemma mem_zerosInBox_iff {α : ℝ} (I : WhitneyInterval) {ρ : ℂ} :
    ρ ∈ zerosInBox α I ↔ ρ ∈ zeroSetXi ∧ ρ ∈ whitneyBoxC α I := by
  simp [zerosInBox, Set.Finite.mem_toFinset]



open ContinuousLinearMap

/-- `J_canonical` is analytic on Ω away from the zero set of `riemannXi_ext`
and the pole at `1`. -/
lemma analyticAt_J_canonical {z : ℂ}
    (hzΩ : z ∈ Ω) (hz_ne_one : z ≠ 1) (hzXi : riemannXi_ext z ≠ 0) :
    AnalyticAt ℂ J_canonical z := by
  classical
  have hz_ne_zero : z ≠ 0 := by
    have hRe : (1 / 2 : ℝ) < z.re := hzΩ
    intro hz0
    have : (1 / 2 : ℝ) < (0 : ℝ) := by simpa [hz0] using hRe
    linarith
  have hdet : AnalyticWithinAt ℂ det2 Ω z := det2_analytic_on_RSΩ z hzΩ
  have hout : AnalyticWithinAt ℂ outer_exists.outer Ω z := outer_exists.analytic z hzΩ
  have hxi : AnalyticAt ℂ riemannXi_ext z :=
    analyticAt_completedRiemannZeta z hz_ne_zero hz_ne_one
  have hden :
      AnalyticWithinAt ℂ (fun w => outer_exists.outer w * riemannXi_ext w) Ω z :=
    hout.mul (hxi.analyticWithinAt (s := Ω))
  have hden_ne : outer_exists.outer z * riemannXi_ext z ≠ 0 :=
    mul_ne_zero (outer_exists.nonzero z hzΩ) hzXi
  have hquot :
      AnalyticWithinAt ℂ
        (fun w : ℂ => det2 w / (outer_exists.outer w * riemannXi_ext w)) Ω z :=
    hdet.div hden hden_ne
  obtain ⟨F, hEq, hF⟩ :=
    (analyticWithinAt_iff_exists_analyticAt (𝕜 := ℂ) (E := ℂ) (F := ℂ)).1 hquot
  have hΩ : (Ω : Set ℂ) ∈ 𝓝 z := isOpen_Ω.mem_nhds hzΩ
  have hEq' :
      (fun w : ℂ => det2 w / (outer_exists.outer w * riemannXi_ext w)) =ᶠ[𝓝 z] F := by
    have hinsert : insert z Ω = Ω := by simp [Set.insert_eq_of_mem hzΩ]
    have hnhds : 𝓝[Ω] z = 𝓝 z := nhdsWithin_eq_nhds.2 hΩ
    simpa [hinsert, hnhds] using hEq
  have hAnalytic :
      AnalyticAt ℂ (fun w : ℂ => det2 w / (outer_exists.outer w * riemannXi_ext w)) z :=
    hF.congr hEq'.symm
  rw [J_canonical]
  exact hAnalytic

/-- Linear part of the upper half-plane coordinate map `(t, σ) ↦ σ + I * t`.

This is an `ℝ`‑linear map `ℝ × ℝ → ℂ` obtained by taking the second coordinate as a real
scalar, and adding `I` times the first coordinate. -/
noncomputable def halfPlaneLinear : ℝ × ℝ →L[ℝ] ℂ :=
  (snd ℝ ℝ ℝ).smulRight (1 : ℂ) +
  (fst ℝ ℝ ℝ).smulRight (Complex.I)

/-- Coordinate map `(t, σ) ↦ (1/2 + σ) + I * t` used in the definition of `U_halfplane`.

We separate the constant shift `(1/2 : ℝ)` from the linear part so that the Frechét derivative
is just `halfPlaneLinear`. -/
noncomputable def halfPlaneCoord (p : ℝ × ℝ) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) + halfPlaneLinear p

@[simp] lemma halfPlaneLinear_apply (p : ℝ × ℝ) :
  halfPlaneLinear p = (p.2 : ℝ) + Complex.I * (p.1 : ℂ) := by
  -- expand the definition: snd picks σ, fst picks t
  simp [halfPlaneLinear, smulRight]  -- standard CLM algebra
  exact CommMonoid.mul_comm (↑p.1) Complex.I

@[simp] lemma halfPlaneCoord_apply (p : ℝ × ℝ) :
  halfPlaneCoord p = ((1 / 2 : ℝ) + p.2 : ℝ) + Complex.I * (p.1 : ℂ) := by
  -- constant shift plus the linear part
  simp [halfPlaneCoord, halfPlaneLinear_apply, add_comm, add_left_comm, add_assoc]

lemma halfPlaneCoord_mem_Ω_of_pos {p : ℝ × ℝ} (hp : 0 < p.2) :
    halfPlaneCoord p ∈ Ω := by
  have hRe : (1 / 2 : ℝ) < (1 / 2 : ℝ) + p.2 := by linarith
  simpa [Ω, halfPlaneCoord_apply, add_comm, add_left_comm, add_assoc] using hRe

lemma halfPlaneCoord_sub_half (p : ℝ × ℝ) :
    (halfPlaneCoord p).re - (1 / 2 : ℝ) = p.2 := by
  simp [halfPlaneCoord_apply, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]

/-- Heights (measured as `σ = Re ρ - 1/2`) of the zeros of `riemannXi_ext` that lie
in the Whitney box of aperture `α` over `I`. -/
noncomputable def zeroHeights (α : ℝ) (I : WhitneyInterval) : Finset ℝ :=
  (zerosInBox α I).image fun ρ : ℂ => ρ.re - (1 / 2 : ℝ)

/-- Supremum (actually the finite maximum) of the zero heights in the aperture-`α`
Whitney box.  It is `0` if no zeros are present. -/
noncomputable def zeroHeightSup (α : ℝ) (I : WhitneyInterval) : ℝ :=
  if h : (zeroHeights α I).Nonempty then
    (zeroHeights α I).max' h
  else
    0

lemma zeroHeight_nonneg {α : ℝ} (I : WhitneyInterval) {ρ : ℂ}
    (hρ : ρ ∈ zerosInBox α I) :
    0 ≤ ρ.re - (1 / 2 : ℝ) := by
  classical
  rcases (mem_zerosInBox_iff (α := α) I).mp hρ with ⟨_, hWhitney⟩
  rcases hWhitney with ⟨p, hp, rfl⟩
  have hσ : 0 ≤ p.2 := (Set.mem_Icc.mp hp.2).1
  have hrepr :
      (halfPlaneCoord p).re - (1 / 2 : ℝ) = p.2 := by
    simp [halfPlaneCoord, halfPlaneLinear, add_comm, add_assoc, sub_eq_add_neg]
  simpa [hrepr] using hσ

lemma zeroHeightSup_nonneg (α : ℝ) (I : WhitneyInterval) :
    0 ≤ zeroHeightSup α I := by
  classical
  by_cases h : (zeroHeights α I).Nonempty
  ·
    have hne := h
    obtain ⟨σ, hσ⟩ := h
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hσ
    have hσ_nonneg : 0 ≤ ρ.re - (1 / 2 : ℝ) :=
      zeroHeight_nonneg (α := α) I hρ
    have hσ_le :
        ρ.re - (1 / 2 : ℝ) ≤ (zeroHeights α I).max' hne :=
      Finset.le_max' (zeroHeights α I) (ρ.re - 1 / 2) hσ
    exact
      le_trans hσ_nonneg
        (by simpa [zeroHeightSup, hne] using hσ_le)
  · simp [zeroHeightSup, h]

lemma le_zeroHeightSup_of_mem {α : ℝ} (I : WhitneyInterval) {σ : ℝ}
    (hσ : σ ∈ zeroHeights α I) :
    σ ≤ zeroHeightSup α I := by
  classical
  have hne : (zeroHeights α I).Nonempty := ⟨σ, hσ⟩
  have : σ ≤ (zeroHeights α I).max' hne :=
    Finset.le_max' (zeroHeights α I) σ hσ
  simpa [zeroHeightSup, hne] using this

lemma zeroHeight_mem_zeroHeights {α : ℝ} (I : WhitneyInterval)
    {ρ : ℂ} (hρ : ρ ∈ zerosInBox α I) :
    ρ.re - (1 / 2 : ℝ) ∈ zeroHeights α I := by
  classical
  exact Finset.mem_image.mpr ⟨ρ, hρ, rfl⟩

lemma zeroHeight_le_sup {α : ℝ} (I : WhitneyInterval)
    {ρ : ℂ} (hρ : ρ ∈ zerosInBox α I) :
    ρ.re - (1 / 2 : ℝ) ≤ zeroHeightSup α I := by
  exact le_zeroHeightSup_of_mem I (zeroHeight_mem_zeroHeights I hρ)

lemma zero_and_pole_free_above_height
    {α ε : ℝ} (I : WhitneyInterval)
    (hε_nonneg : 0 ≤ ε)
    (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α * I.len))
    (hheight : zeroHeightSup α I < ε)
    {p : ℝ × ℝ}
    (hp : p ∈ I.interval ×ˢ Set.Icc ε (α * I.len)) :
    riemannXi_ext (halfPlaneCoord p) ≠ 0 ∧ halfPlaneCoord p ≠ 1 := by
  classical
  rcases hp with ⟨hp_t, hp_σ⟩
  have hp_bounds := Set.mem_Icc.mp hp_σ
  have hp_nonneg : 0 ≤ p.2 := le_trans hε_nonneg hp_bounds.1
  have hp_full : p ∈ I.interval ×ˢ Set.Icc (0 : ℝ) (α * I.len) :=
    ⟨hp_t, ⟨hp_nonneg, hp_bounds.2⟩⟩
  have hWhitney : halfPlaneCoord p ∈ whitneyBoxC α I := by
    refine ⟨p, hp_full, ?_⟩
    simp [halfPlaneCoord]
    exact add_assoc 2⁻¹ (↑p.2) (Complex.I * ↑p.1)
  constructor
  · intro hzero
    have hZeroInBox : halfPlaneCoord p ∈ zerosInBox α I := by
      refine (mem_zerosInBox_iff (α := α) I).mpr ?_
      exact ⟨by simpa using hzero, hWhitney⟩
    have hheight_le :
        (halfPlaneCoord p).re - (1 / 2 : ℝ) ≤ zeroHeightSup α I :=
      zeroHeight_le_sup (α := α) I hZeroInBox
    have hrepr :
        (halfPlaneCoord p).re - (1 / 2 : ℝ) = p.2 := by
      simp [halfPlaneCoord_apply, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
    have hheight_ge : ε ≤ (halfPlaneCoord p).re - (1 / 2 : ℝ) := by
      simpa [hrepr] using hp_bounds.1
    have hcontr : ε ≤ zeroHeightSup α I :=
      le_trans hheight_ge hheight_le
    exact (not_lt_of_ge hcontr) hheight
  · intro hOne
    have hp1 : p.1 = 0 := by
      simpa [halfPlaneCoord_apply] using congrArg (Complex.im) hOne
    have hp2 : p.2 = 1 / 2 := by
      have hRe := congrArg Complex.re hOne
      have hRe' :
          (1 / 2 : ℝ) + p.2 = 1 := by
        simp only [halfPlaneCoord_apply, hp1, Complex.add_re, Complex.ofReal_re,
          Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
          mul_zero, sub_zero, add_zero] at hRe
        simpa using hRe
      exact by linarith [hRe']
    have : (1 / 2 : ℝ) ∈ Set.Icc ε (α * I.len) := by
      rw [Set.mem_Icc, ← hp2]
      exact hp_bounds
    exact havoid this

lemma riemannXi_ext_zero_avoids_poles {ρ : ℂ} (hρ : riemannXi_ext ρ = 0) : ρ ≠ 0 ∧ ρ ≠ 1 := by
  constructor
  · rintro rfl; exact completedRiemannZeta_zero_ne_zero hρ
  · rintro rfl; exact completedRiemannZeta_one_ne_zero hρ


open AnalyticAt
/-- Multiplicity (order) of the zero of `riemannXi_ext` at `ρ`.

This function computes the order of vanishing of `riemannXi_ext` at a point `ρ`.
If `ρ` is not a zero, the order is 0. Otherwise, it is the smallest `n ≥ 1`
such that the `n`-th derivative of `riemannXi_ext` at `ρ` is non-zero.

This relies on the identity principle for analytic functions, which guarantees that
for a non-identically-zero analytic function, any zero is isolated and has a
finite integer order. We have already proven that `riemannXi_ext` is not identically
zero on any connected open set of its domain.
-/
noncomputable def zeroOrderAt (ρ : ℂ) : ℕ :=
  if hρ : riemannXi_ext ρ = 0 then
    let f := riemannXi_ext
    have h_poles : ρ ≠ 0 ∧ ρ ≠ 1 := riemannXi_ext_zero_avoids_poles hρ
    have h_an : AnalyticAt ℂ f ρ := analyticAt_completedRiemannZeta ρ h_poles.1 h_poles.2
    have h_not_locally_zero : ¬ (∀ᶠ w in 𝓝 ρ, f w = 0) :=
      completedRiemannZeta_not_locally_zero_on_U ρ h_poles
    have h_exists_deriv_ne_zero : ∃ n, iteratedDeriv n f ρ ≠ 0 :=
      (h_an.eventually_eq_zero_or_exists_deriv_ne_zero).resolve_left h_not_locally_zero
    Nat.find h_exists_deriv_ne_zero
  else
    0

-- alternate definition using coefficients
noncomputable def zeroOrderAt' (ρ : ℂ) : ℕ :=
  if hρ : riemannXi_ext ρ = 0 then
    let f := riemannXi_ext
    have h_poles : ρ ≠ 0 ∧ ρ ≠ 1 := riemannXi_ext_zero_avoids_poles hρ
    have h_an : AnalyticAt ℂ f ρ := analyticAt_completedRiemannZeta ρ h_poles.1 h_poles.2
    have h_not_locally_zero : ¬ (∀ᶠ w in 𝓝 ρ, f w = 0) :=
      completedRiemannZeta_not_locally_zero_on_U ρ h_poles
    have h_exists_coeff_ne_zero : ∃ n, (h_an.choose).coeff n ≠ 0 :=
      (AnalyticAt.eventually_eq_zero_or_exists_coeff_ne_zero h_an).resolve_left h_not_locally_zero
    Nat.find h_exists_coeff_ne_zero
  else
    0

/-- Analytic, finite zero enumeration packaged as `ResidueBookkeeping`. -/
noncomputable def residue_bookkeeping (I : WhitneyInterval) : ResidueBookkeeping I :=
  let α := (0.08 : ℝ)  -- aperture parameter (matches A_default from Constants)
  let Z := zerosInBox α I
  let atoms_list : List ResidueAtom :=
    Z.toList.map (fun ρ =>
      { ρ := ρ
      , weight := (zeroOrderAt ρ : ℝ) * Real.pi
      , hnonneg := mul_nonneg (Nat.cast_nonneg _) Real.pi_pos.le })
  { atoms := atoms_list
  , total := atoms_list.foldl (fun s a => s + a.weight) 0
  , total_nonneg := by
      -- The sum of nonnegative weights is nonnegative
      suffices ∀ (L : List ResidueAtom) (init : ℝ), 0 ≤ init →
          0 ≤ L.foldl (fun s a => s + a.weight) init by
        exact this atoms_list 0 (le_refl 0)
      intro L init h_init
      induction L generalizing init with
      | nil => simpa [List.foldl]
      | cons a t ih =>
        simp only [List.foldl]
        exact ih (init + a.weight) (add_nonneg h_init a.hnonneg) }

/-- The atoms list from residue bookkeeping. -/
lemma residue_bookkeeping_atoms_def (I : WhitneyInterval) :
  (residue_bookkeeping I).atoms =
    (zerosInBox 0.08 I).toList.map (fun ρ =>
      { ρ := ρ, weight := (zeroOrderAt ρ : ℝ) * Real.pi, hnonneg := mul_nonneg (Nat.cast_nonneg _) Real.pi_pos.le }) := by
  simp [residue_bookkeeping]

/-- The total weight from residue bookkeeping equals the sum of atom weights. -/
lemma residue_bookkeeping_total_def (I : WhitneyInterval) :
  (residue_bookkeeping I).total =
    (residue_bookkeeping I).atoms.foldl (fun s a => s + a.weight) 0 := by
  simp [residue_bookkeeping]

/-- Total weight is nonnegative (automatic from structure). -/
lemma residue_bookkeeping_total_nonneg (I : WhitneyInterval) :
  0 ≤ (residue_bookkeeping I).total :=
  (residue_bookkeeping I).total_nonneg

/-- Empty atoms list implies zero dyadic counts. -/
lemma nu_dyadic_of_empty_atoms (I : WhitneyInterval) (k : ℕ) :
  (residue_bookkeeping I).atoms = [] →
  nu_dyadic I (residue_bookkeeping I) k = 0 := by
  intro h
  simp [nu_dyadic, nu_dyadic_core, h]

/-- Critical atoms residue contribution from canonical bookkeeping. -/
noncomputable def critical_atoms_res_canonical (I : WhitneyInterval) : ℝ :=
  critical_atoms_res I (residue_bookkeeping I)

/-- Critical atoms are nonnegative (from residue bookkeeping structure). -/
lemma critical_atoms_res_canonical_nonneg (I : WhitneyInterval) :
  0 ≤ critical_atoms_res_canonical I :=
  critical_atoms_res_nonneg I (residue_bookkeeping I)

/-! ### Interpretation: Dyadic counts from residue bookkeeping

The dyadic count `ν_I(k)` measures the total residue weight of zeros whose
imaginary parts lie in the k-th dyadic annulus centered at `I.t0`:

  annulus(k) := {γ : |γ - I.t0| ∈ (2^k·len, 2^(k+1)·len]}

This spatial decomposition is fundamental for:
  1. Decay estimates (far zeros contribute less via Poisson kernel decay)
  2. VK zero-density bounds (control ∑ₖ νₖ via unconditional estimates)
  3. Schur test setup (off-diagonal decay proportional to distance)

**Key Properties**:
  - Each νₖ ≥ 0 (weights are nonnegative)
  - ∑ₖ νₖ = total weight (dyadic decomposition is partition)
  - νₖ satisfies VK bounds via Vinogradov-Korobov density theorem
-/
open Classical in
/-- Interpretation: ν_I,bk(k) equals the sum of weights of atoms whose imaginary
part lies in the k‑th dyadic annulus aligned with `I`. -/
lemma nu_dyadic_eq_sum (I : WhitneyInterval) (bk : ResidueBookkeeping I) (k : ℕ) :
  nu_dyadic I bk k =
    (bk.atoms.foldr (fun a s => (if annulusDyadic I k a.ρ.im then a.weight else 0) + s) 0) := by
  classical
  revert bk; intro bk; cases bk with
  | _ atoms total total_nonneg =>
    induction atoms with
    | nil => simp [nu_dyadic, nu_dyadic_core]
    | cons a t ih =>
        simp only [nu_dyadic, nu_dyadic_core, List.foldr_cons]
        congr 1

/-- Canonical `nu` used for KD and counts: ν_default(k) = ν_dyadic I (residue_bookkeeping I) k.

This is the standard dyadic counting function used throughout the proof, defined as the
weighted count of zeros in the k-th dyadic annulus from the canonical residue bookkeeping.

**Mathematical Role**: Encodes the spatial distribution of zeros in the Whitney box,
which enters the Schur test for the kernel decomposition and the VK bound for the
total zero count.

**Current Behavior**: With empty atoms, ν_default(k) = 0 for all k, making all
energy bounds trivially satisfied (degenerate but sound case).
-/
@[simp] noncomputable def nu_default (I : WhitneyInterval) (k : ℕ) : ℝ :=
  nu_dyadic I (residue_bookkeeping I) k

/-- Each dyadic count is nonnegative. -/
lemma nu_default_nonneg (I : WhitneyInterval) (k : ℕ) : 0 ≤ nu_default I k := by
  simp [nu_default]
  exact nu_dyadic_nonneg I (residue_bookkeeping I) k

open Classical in
/-- Dyadic count equals foldr sum over atoms (interpretation lemma). -/
lemma nu_default_eq_sum (I : WhitneyInterval) (k : ℕ) :
  nu_default I k =
    ((residue_bookkeeping I).atoms.foldr
      (fun a s => (if annulusDyadic I k a.ρ.im then a.weight else 0) + s) 0) := by
  simp [nu_default]
  exact nu_dyadic_eq_sum I (residue_bookkeeping I) k

/-! ## Calibration constants -/

/-- Default calibration constants: pick `A = 0.08`, `B = 2`, so `A·B = 0.16 = Kxi_paper`. -/
noncomputable def A_default : ℝ := 0.08
noncomputable def B_default : ℝ := 2

/-- Default diagonal constant, extracted from the calibrated diagonal bounds. -/
noncomputable def Cdiag_default : ℝ := 0.04

/-- Default Schur cross-term constant from the decay-4 majorization. -/
noncomputable def C_cross_default : ℝ := 0.04

/-- A convenient default numeric constant for VK counts packaging. -/
@[simp] def Cnu_default : ℝ := 2

lemma Cnu_default_nonneg : 0 ≤ Cnu_default := by
  simp [Cnu_default]

lemma Cnu_default_le_two : Cnu_default ≤ 2 := by
  simp [Cnu_default]

lemma default_AB_le : A_default * B_default ≤ Kxi_paper := by
  have h : A_default * B_default = Kxi_paper := by
    norm_num [A_default, B_default, Kxi_paper]
  simp [h]

lemma Cdiag_default_nonneg : 0 ≤ Cdiag_default := by
  norm_num [Cdiag_default]

lemma C_cross_default_nonneg : 0 ≤ C_cross_default := by
  norm_num [C_cross_default]

/-- Calibrated arithmetic closure: `Cdiag_default + C_cross_default ≤ A_default`. -/
lemma hCalib : Cdiag_default + C_cross_default ≤ A_default := by
  have hsum : Cdiag_default + C_cross_default = 0.08 := by
    norm_num [Cdiag_default, C_cross_default]
  simp [hsum, A_default]

end RH.RS.BoundaryWedgeProof
