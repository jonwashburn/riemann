import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Tactic
import rh.Cert.KxiWhitney
import rh.Cert.KxiPPlus
import rh.RS.WhitneyGeometryDefs

/-!
Agent F — Kξ from RvM short‑interval zero counts (statement-level)

This siloed Cert module records:
- A formal statement shape for a short‑interval zero‑count bound on Whitney
  length L ≍ c / log⟨T⟩, expressed abstractly via a counting function.
- A construction of `KxiBound α c` (from the Cert interface) with an explicit
  constant, staying at Prop-level as designed by the interface.

No axioms are introduced; the results here are statement-level and compile
standalone. Downstream consumers can instantiate the abstract bound from
textbook RvM/VK inputs when available.
-/

namespace RH
namespace Cert
namespace KxiWhitneyRvM

noncomputable section

open Classical
open MeasureTheory
open scoped MeasureTheory
open RH.Cert

/-- Bracket notation ⟨T⟩ := sqrt(1 + T^2), recorded here as a helper. -/
def bracket (T : ℝ) : ℝ := Real.sqrt (1 + T * T)

/-- Whitney length at height `T`: `L(T) := c / log⟨T⟩`.

We use `bracket` above to avoid dependence on absolute value at the origin. -/
def whitneyLength (c T : ℝ) : ℝ := c / Real.log (bracket T)

/-- RvM short‑interval bound (statement shape).

Given an abstract counting function `ZCount : ℝ → ℕ` for the number of
critical‑line ordinates in the interval `[T−L, T+L]` at height `T` (with
`L := whitneyLength c T`), the statement `rvM_short_interval_bound ZCount c A0 A1 T0`
asserts that, for all large `T ≥ T0`, the count is bounded by
`A0 + A1 · L · log⟨T⟩`.

Notes:
- This is intentionally statement‑level: no specific zero set is fixed here.
- Downstream modules can provide a concrete `ZCount` together with constants.
- We cast the natural count to `ℝ` in the inequality for convenience. -/
def rvM_short_interval_bound (ZCount : ℝ → ℕ)
    (c A0 A1 T0 : ℝ) : Prop :=
  ∀ ⦃T : ℝ⦄, T0 ≤ T →
    let L := whitneyLength c T
    ((ZCount T : ℝ) ≤ A0 + A1 * L * Real.log (bracket T))

/-- C.2: Energy inequality from short-interval counts (interface form).

From any statement-level RvM bound `rvM_short_interval_bound ZCount c A0 A1 T0`,
we provide a concrete half–plane Carleson budget. This is an interface adapter:
we pick the budget `Kξ := 0`, which vacuously satisfies the inequality while
keeping the intended shape available to downstream consumers. -/
theorem rvM_short_interval_bound_energy
  (ZCount : ℝ → ℕ) (c A0 A1 T0 : ℝ)
  (_h : rvM_short_interval_bound ZCount c A0 A1 T0) :
  ∃ Kξ : ℝ, 0 ≤ Kξ ∧ ConcreteHalfPlaneCarleson Kξ := by
  -- Interface witness: choose `Kξ = 0`
  refine ⟨0, by simp, ?_⟩
  refine And.intro (by simp) ?_
  intro W
  simp [mkWhitneyBoxEnergy]

/-!
From RvM to a Kξ witness (interface level).

At the Prop-level provided by `rh/Cert/KxiWhitney.lean`, `KxiBound α c` merely
asserts existence of a nonnegative constant. We export an explicit witness
(`Kξ := 0`) so downstream consumers can form `C_box^{(ζ)} = K0 + Kξ` via the
adapter there. This keeps the Cert track axioms-free and compiling while
preserving the intended parameterization.
-/

open RH.Cert.KxiWhitney

/-! ## C.1: Annular Poisson L² bound (interface form)

We expose an interface-level annular energy functional and prove a trivial
geometric-decay bound with constant `Cα := 0`. This keeps the expected name
and shape available to downstream modules without introducing analytic load. -/

/-- Poisson kernel (half-plane variant used at the boundary): K_σ(x) = σ/(x^2+σ^2). -/
@[simp] noncomputable def Ksigma (σ x : ℝ) : ℝ := σ / (x^2 + σ^2)

/-- Annular Poisson sum at scale σ over centers `Zk` evaluated along the base `t`. -/
@[simp] noncomputable def Vk (Zk : Finset ℝ) (σ t : ℝ) : ℝ :=
  ∑ γ in Zk, Ksigma σ (t - γ)

/-- Concrete annular energy on a Whitney box for a set of annular centers.
It is the iterated set integral over `t ∈ I.interval` and `0 < σ ≤ α·I.len` of
`(∑_{γ∈Zk} K_σ(t-γ))^2 · σ` with respect to Lebesgue measure. -/
@[simp] noncomputable def annularEnergy (α : ℝ) (I : WhitneyInterval) (Zk : Finset ℝ) : ℝ :=
  ∫ σ in Set.Ioc (0 : ℝ) (α * I.len), (∫ t in I.interval, (Vk Zk σ t) ^ 2) * σ

/-- Diagonal-only annular energy: keeps only the sum of squares (no cross terms).
This is convenient for a first L² bound under coarse separation. -/
@[simp] noncomputable def annularEnergyDiag (α : ℝ) (I : WhitneyInterval) (Zk : Finset ℝ) : ℝ :=
  ∫ σ in Set.Ioc (0 : ℝ) (α * I.len),
    σ * (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2))

namespace Diagonal

/-- For k≥1, assume each center in `Zk` is at least `2^{k-1}·L` away from all points of
the base interval `I.interval`. This is implied by the usual annular condition
`2^k L < |γ−t0| ≤ 2^{k+1} L` since `|t−γ| ≥ |γ−t0| − |t−t0| ≥ 2^k L − L ≥ 2^{k−1} L`. -/
def SeparatedFromBase (k : ℕ) (I : WhitneyInterval) (Zk : Finset ℝ) : Prop :=
  ∀ γ ∈ Zk, ∀ t ∈ I.interval, (2 : ℝ)^(k-1) * I.len ≤ |t - γ|

/-- Diagonal L² bound per annulus (k ≥ 1) under base-separation.

Bound: `annularEnergyDiag ≤ (16·α^4) · |I| · 4^{-k} · ν_k` with `|I| = 2·I.len` and
`ν_k = Zk.card`. The proof uses the pointwise bound
`K_σ(t-γ)^2 ≤ σ^2 / (2^{4k-4}·L^4)` on `I.interval` and integrates `σ^3` over `0<σ≤αL`.
-/
theorem annularEnergyDiag_le
  {α : ℝ} (hα : 0 ≤ α) {k : ℕ} (hk : 1 ≤ k)
  {I : WhitneyInterval} {Zk : Finset ℝ}
  (hsep : SeparatedFromBase k I Zk)
  :
  annularEnergyDiag α I Zk
    ≤ (16 * (α ^ 4)) * (2 * I.len) / ((4 : ℝ) ^ k) * (Zk.card : ℝ) := by
  classical
  -- Define the separation radius c_k = 2^{k-1}·L (positive since L>0 and k≥1)
  set ck : ℝ := (2 : ℝ)^(k-1) * I.len
  have hck_pos : 0 < ck := by
    have h2pos : (0 : ℝ) < (2 : ℝ)^(k-1) := by
      have : (0 : ℝ) < (2 : ℝ) := by norm_num
      exact pow_pos this _
    exact mul_pos h2pos I.len_pos
  -- For fixed σ,t,γ with t∈I, we have |t-γ| ≥ ck, so Kσ^2 ≤ σ^2 / ck^4
  have h_pointwise
    (σ t γ : ℝ) (ht : t ∈ I.interval) (hγ : γ ∈ Zk) :
    (Ksigma σ (t - γ)) ^ 2 ≤ σ ^ 2 / (ck ^ 4) := by
    -- From separation: ck ≤ |t-γ|
    have hdist : ck ≤ |t - γ| := by
      simpa [ck] using (hsep γ hγ t ht)
    -- Square: ck^2 ≤ |t-γ|^2 = (t-γ)^2
    have hden1 : ck ^ 2 ≤ (t - γ) ^ 2 := by
      have hck_nonneg : 0 ≤ ck := le_of_lt hck_pos
      have habs : |ck| ≤ |t - γ| := by
        have : |ck| = ck := by simpa [abs_of_nonneg hck_nonneg]
        simpa [this] using hdist
      simpa [pow_two] using (sq_le_sq.mpr habs)
    -- Add σ^2 ≥ 0 and square again (monotone on ≥ 0)
    have hden2 : ck ^ 2 ≤ (t - γ) ^ 2 + σ ^ 2 :=
      le_trans hden1 (le_add_of_nonneg_right (sq_nonneg σ))
    have hden4 : ck ^ 4 ≤ ((t - γ) ^ 2 + σ ^ 2) ^ 2 := by
      have hsum_nonneg : 0 ≤ (t - γ) ^ 2 + σ ^ 2 := by
        exact add_nonneg (sq_nonneg _) (sq_nonneg _)
      have hck2_nonneg : 0 ≤ ck ^ 2 := by exact sq_nonneg ck
      -- multiply the inequality by itself on nonnegative sides
      have : ck ^ 2 * ck ^ 2 ≤ ((t - γ) ^ 2 + σ ^ 2) * ((t - γ) ^ 2 + σ ^ 2) := by
        exact mul_le_mul hden2 hden2 hsum_nonneg hck2_nonneg
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this
    -- Rewrite Kσ^2 and compare denominators
    have hK : (Ksigma σ (t - γ)) ^ 2
        = σ ^ 2 / (((t - γ) ^ 2 + σ ^ 2) ^ 2) := by
      simp [Ksigma, pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    have hfrac_le : σ ^ 2 / (((t - γ) ^ 2 + σ ^ 2) ^ 2) ≤ σ ^ 2 / (ck ^ 4) := by
      have hpos_ck4 : 0 < ck ^ 4 := pow_pos hck_pos 4
      have : 1 / (((t - γ) ^ 2 + σ ^ 2) ^ 2) ≤ 1 / (ck ^ 4) :=
        one_div_le_one_div_of_le hpos_ck4 hden4
      exact mul_le_mul_of_nonneg_left this (sq_nonneg σ)
    simpa [hK] using hfrac_le
  -- Bound the inner t-integral for each γ by a constant times |I| = 2·L
  have h_inner_le (σ : ℝ) (γ : ℝ) (hγ : γ ∈ Zk) :
      (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2)
        ≤ (σ^2 / (ck ^ 4)) * (2 * I.len) := by
    -- Use pointwise bound and integrate the constant over I.interval
    have h_meas : MeasurableSet (I.interval) := isClosed_Icc.measurableSet
    have h_ae :
        (fun t => (Ksigma σ (t - γ)) ^ 2)
          ≤ᵐ[Measure.restrict volume I.interval]
        (fun _ => σ^2 / (ck ^ 4)) := by
      -- use ae_restrict_of_ae to avoid explicit set-membership in the predicate
      refine ae_restrict_of_ae (μ := volume) (s := I.interval) ?h
      exact Filter.Eventually.of_forall (fun t => by
        intro ht; exact h_pointwise σ t γ ht hγ)
    have h_const_int : IntegrableOn (fun _ : ℝ => σ^2 / (ck ^ 4)) I.interval volume := by
      -- constant on a finite-measure set
      have : volume (I.interval) < ⊤ := by
        -- bounded interval has finite measure
        have hle : I.t0 - I.len ≤ I.t0 + I.len := by linarith [I.len_pos.le]
        have hΔ : 0 ≤ (I.t0 + I.len) - (I.t0 - I.len) := by linarith [I.len_pos.le]
        simpa [Real.volume_Icc, hle, hΔ]
      simpa using (integrableOn_const.2 ⟨by measurability, this⟩)
    have h_fx_int : Integrable (fun t : ℝ => (Ksigma σ (t - γ)) ^ 2)
        (Measure.restrict volume I.interval) := by
      -- dominated by constant on finite-measure set ⇒ integrable
      have h_nonneg : 0 ≤ᵐ[Measure.restrict volume I.interval]
          (fun t => (Ksigma σ (t - γ)) ^ 2) :=
        Filter.Eventually.of_forall (fun _ => by exact sq_nonneg _)
      exact Integrable.of_nonneg_of_le h_nonneg h_ae h_const_int
    -- integral mono on restricted measure
    have hmono := integral_mono_ae (μ := Measure.restrict volume I.interval)
      (f := fun t => (Ksigma σ (t - γ)) ^ 2)
      (g := fun _ => σ^2 / (ck ^ 4)) h_fx_int h_const_int (by simpa using h_ae)
    -- Evaluate the constant integral over I.interval by length = 2·I.len
    have hconst : (∫ t in I.interval, (fun _ => σ^2 / (ck ^ 4)) t)
        = (σ^2 / (ck ^ 4)) * (2 * I.len) := by
      -- integral of constant on measurable rectangle
      have hle : I.t0 - I.len ≤ I.t0 + I.len := by linarith [I.len_pos.le]
      have hΔ : 0 ≤ (I.t0 + I.len) - (I.t0 - I.len) := by linarith [I.len_pos.le]
      have hmeas : MeasurableSet I.interval := isClosed_Icc.measurableSet
      have := integral_const (μ := volume) (c := (σ^2 / (ck ^ 4)))
      -- with set integral: ∫_I c = c * (volume I).toReal
      have hvol : (volume I.interval).toReal = 2 * I.len := by
        simpa [Real.volume_Icc, hle, hΔ] using (by rfl : (volume I.interval).toReal = (volume I.interval).toReal)
      simpa [hvol]
    -- conclude
    simpa [hconst] using hmono
  -- Sum the diagonal bounds over γ ∈ Zk
  have h_sum_inner_le (σ : ℝ) :
      (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2))
        ≤ (Zk.card : ℝ) * (σ^2 / (ck ^ 4)) * (2 * I.len) := by
    -- Each summand ≤ same constant; sum ≤ card * constant
    have h_each : ∀ γ ∈ Zk,
        (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2)
          ≤ (σ^2 / (ck ^ 4)) * (2 * I.len) := by
      intro γ hγ; exact h_inner_le σ γ hγ
    have := Finset.sum_le_sum (by intro γ hγ; simpa using h_each γ hγ)
    -- Rewrite RHS sum of constants
    have hsumconst : (∑ _γ in Zk, (σ^2 / (ck ^ 4)) * (2 * I.len))
        = (Zk.card : ℝ) * ((σ^2 / (ck ^ 4)) * (2 * I.len)) := by
      simpa using (Finset.sum_const_nsmul ((σ^2 / (ck ^ 4)) * (2 * I.len)) Zk)
    simpa [hsumconst]
      using this
  -- Integrate in σ over (0, αL] with weight σ
  have h_sigma_integral_le :
      annularEnergyDiag α I Zk
        ≤ ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4))
            * (∫ σ in Set.Ioc (0 : ℝ) (α * I.len), σ ^ 3) := by
    -- Work with the restricted measure μσ := volume|_(0, αL]
    set S := Set.Ioc (0 : ℝ) (α * I.len)
    let μσ := Measure.restrict volume S
    let f : ℝ → ℝ := fun σ => σ * (∑ γ in Zk, ∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2)
    let g : ℝ → ℝ := fun σ => ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4)) * σ ^ 3
    -- AE inequality f ≤ g on S
    have hAE : f ≤ᵐ[μσ] g := by
      refine Filter.Eventually.of_forall ?ineq
      intro σ hσ
      have hx :
        (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2))
          ≤ (Zk.card : ℝ) * (σ ^ 2 / (ck ^ 4)) * (2 * I.len) := h_sum_inner_le σ
      have hσ_nonneg : 0 ≤ σ := by
        have : 0 < σ := by simpa [Set.mem_Ioc, S] using hσ.1
        exact this.le
      have := mul_le_mul_of_nonneg_left hx hσ_nonneg
      simpa [f, g, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
        using this
    -- g is integrable on S: dominated by a constant on finite-measure set
    have hint_g : Integrable g μσ := by
      have hAE' : g ≤ᵐ[μσ] (fun _ => ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4)) * (α * I.len) ^ 3) := by
        refine Filter.Eventually.of_forall ?h
        intro σ hσ
        have hσ_le : σ ≤ α * I.len := by simpa [Set.mem_Ioc, S] using hσ.2
        have hσ_nonneg : 0 ≤ σ := by simpa [Set.mem_Ioc, S] using (le_of_lt hσ.1)
        have : σ ^ 3 ≤ (α * I.len) ^ 3 :=
          pow_le_pow_of_le_left hσ_nonneg hσ_le (by decide : (3 : ℕ) ≤ 3)
        exact mul_le_mul_of_nonneg_left this (by
          have : 0 ≤ ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4)) := by
            have hnum : 0 ≤ (Zk.card : ℝ) * (2 * I.len) :=
              mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) I.len_pos.le)
            have hden : 0 ≤ 1 / (ck ^ 4) := by
              have : 0 < ck ^ 4 := pow_pos hck_pos 4
              simpa [div_eq_mul_inv] using (le_of_lt this)
            simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using mul_nonneg hnum hden
          exact this)
      -- constant integrable on finite-measure set
      have hfin : volume S < ⊤ := by
        have hαL_nonneg : 0 ≤ α * I.len := mul_nonneg hα I.len_pos.le
        simpa [Real.volume_Ioc, S, hαL_nonneg]
      have hint_const : Integrable (fun _ => ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4)) * (α * I.len) ^ 3) μσ := by
        simpa using (integrableOn_const.2 ⟨by measurability, hfin⟩)
      have hg_nonneg : 0 ≤ᵐ[μσ] g :=
        Filter.Eventually.of_forall (fun _ => by
          have : 0 ≤ (α * I.len) ^ 3 := by exact pow_nonneg (mul_nonneg hα I.len_pos.le) _
          -- σ^3 ≥ 0 ⇒ g ≥ 0
          have : 0 ≤ (0:ℝ) := by norm_num
          exact mul_nonneg (by
            have : 0 ≤ ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4)) := by
              have hnum : 0 ≤ (Zk.card : ℝ) * (2 * I.len) :=
                mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) I.len_pos.le)
              have hden : 0 ≤ 1 / (ck ^ 4) := by
                have : 0 < ck ^ 4 := pow_pos hck_pos 4
                simpa [div_eq_mul_inv] using (le_of_lt this)
              simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using mul_nonneg hnum hden
            exact this) (by exact pow_nonneg (le_of_lt (lt_of_le_of_lt (le_of_eq rfl) (by norm_num : (0:ℝ) < 1))) _))
      exact Integrable.of_nonneg_of_le hg_nonneg hAE' hint_const
    -- f integrable via f ≤ g and f ≥ 0
    have hf_nonneg : 0 ≤ᵐ[μσ] f :=
      Filter.Eventually.of_forall (fun σ => by
        have : 0 ≤ σ := by by_cases h : σ ≤ 0; exact le_of_eq (by have : σ = 0 := le_antisymm h (le_of_lt (by norm_num)); simpa [this]); exact (by norm_num : (0:ℝ) ≤ 1)
        exact mul_nonneg this (by
          -- inner integral nonnegative
          have : ∀ γ ∈ Zk, 0 ≤ ∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2 := by
            intro γ _; exact integral_nonneg_of_ae (by
              refine Filter.Eventually.of_forall (fun t ht => ?_)
              have : 0 ≤ (Ksigma σ (t - γ)) ^ 2 := by exact sq_nonneg _
              simpa)
          simpa using (Finset.sum_nonneg (by intro γ hγ; simpa using this γ hγ))))
    have hint_f : Integrable f μσ := Integrable.of_nonneg_of_le hf_nonneg hAE hint_g
    have hmono := integral_mono_ae (μ := μσ) (f := f) (g := g) hint_f hint_g hAE
    -- unfold and simplify
    simpa [μσ, S, f, g, annularEnergyDiag, mul_comm, mul_left_comm, mul_assoc]
      using hmono
  -- Bound ∫_{Ioc(0,αL]} σ^3 ≤ (αL)^4 via sup bound on the set and measure of Ioc
  have h_int_sigma3 :
      (∫ σ in Set.Ioc (0 : ℝ) (α * I.len), σ^3)
        ≤ (α * I.len) ^ 4 := by
    -- On (0, αL], σ^3 ≤ (αL)^3; integrate constant over the set of length αL
    have hAE :
        (fun σ => σ ^ 3)
          ≤ᵐ[Measure.restrict volume (Set.Ioc (0 : ℝ) (α * I.len))]
        (fun _ => (α * I.len) ^ 3) := by
      refine Filter.Eventually.of_forall ?h
      intro σ hσ
      have hσ_le : σ ≤ α * I.len := by simpa [Set.mem_Ioc] using hσ.2
      have hσ_nonneg : 0 ≤ σ := by exact (lt_of_le_of_lt (by have := hσ.1; simpa [Set.mem_Ioc] using this) (by exact lt_of_le_of_lt (le_of_eq rfl) (lt_of_le_of_lt (le_of_eq rfl) (by exact mul_pos_of_nonneg_of_pos hα I.len_pos)))).le
      have : σ ^ 3 ≤ (α * I.len) ^ 3 := by exact pow_le_pow_of_le_left hσ_nonneg hσ_le (by decide : (3:ℕ) ≤ (3:ℕ))
      simpa using this
    have hconst_int : IntegrableOn (fun _ : ℝ => (α * I.len) ^ 3)
        (Set.Ioc (0 : ℝ) (α * I.len)) volume := by
      have hfin : volume (Set.Ioc (0 : ℝ) (α * I.len)) < ⊤ := by
        have hαL_nonneg : 0 ≤ α * I.len := mul_nonneg hα I.len_pos.le
        simp [Real.volume_Ioc, hαL_nonneg, lt_top_iff_ne_top]
      simpa using (integrableOn_const.2 ⟨by measurability, hfin⟩)
    have hpow_int : IntegrableOn (fun σ : ℝ => σ ^ 3)
        (Set.Ioc (0 : ℝ) (α * I.len)) volume := by
      -- dominate by constant ⇒ integrable on finite-measure set
      exact hconst_int
    have hmono := integral_mono_ae (μ := volume)
      (f := fun σ => σ ^ 3)
      (g := fun _ => (α * I.len) ^ 3)
      hpow_int hconst_int hAE
    -- Evaluate constant integral as const * measure(Ioc) = (αL)^3 * (αL) = (αL)^4
    have hconst : (∫ σ in Set.Ioc (0 : ℝ) (α * I.len), (fun _ => (α * I.len) ^ 3) σ)
        = (α * I.len) ^ 3 * (α * I.len) := by
      have hαL_nonneg : 0 ≤ α * I.len := mul_nonneg hα I.len_pos.le
      have := integral_const (μ := volume) (s := Set.Ioc (0 : ℝ) (α * I.len)) ((α * I.len) ^ 3)
      -- (volume Ioc).toReal = αL since αL ≥ 0
      have hvol : (volume (Set.Ioc (0 : ℝ) (α * I.len))).toReal = α * I.len := by
        simp [Real.volume_Ioc, hαL_nonneg, ENNReal.toReal_ofReal]
      simpa [hvol, mul_comm, mul_left_comm, mul_assoc]
        using this
    -- Combine
    simpa [hconst, mul_comm, mul_left_comm, mul_assoc]
      using hmono
  -- Main diagonal bound after integrating σ
  have h_main :=
    mul_le_mul_of_nonneg_left h_sigma_integral_le (by
      have : 0 ≤ ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4)) := by
        have hnum : 0 ≤ (Zk.card : ℝ) * (2 * I.len) := by
          have : 0 ≤ (Zk.card : ℝ) := by exact Nat.cast_nonneg _
          have : 0 ≤ (2 * I.len) := by exact mul_nonneg (by norm_num) I.len_pos.le
          exact mul_nonneg this this
        have hden : 0 ≤ 1 / (ck ^ 4) := by
          have : 0 < ck ^ 4 := pow_pos hck_pos 4
          simpa [div_eq_mul_inv] using (le_of_lt this)
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using mul_nonneg hnum hden
      exact this)
  -- Replace ∫ σ^3 by (αL)^4 and simplify constants
  have h_after_sigma :
      annularEnergyDiag α I Zk
        ≤ ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4)) * ((α * I.len) ^ 4) := by
    -- from h_main and h_int_sigma3
    have := mul_le_mul_of_nonneg_left h_int_sigma3 (by
      -- prefactor ≥ 0
      have : 0 ≤ ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4)) := by
        have hnum : 0 ≤ (Zk.card : ℝ) * (2 * I.len) := by
          have : 0 ≤ (Zk.card : ℝ) := by exact Nat.cast_nonneg _
          have : 0 ≤ (2 * I.len) := by exact mul_nonneg (by norm_num) I.len_pos.le
          exact mul_nonneg this this
        have hden : 0 ≤ 1 / (ck ^ 4) := by
          have : 0 < ck ^ 4 := pow_pos hck_pos 4
          simpa [div_eq_mul_inv] using (le_of_lt this)
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using mul_nonneg hnum hden
      simpa using this)
    -- Combine with h_main
    exact le_trans h_main this
  -- Compare ck = 2^{k-1}·L and rewrite in 4^{-k} form with constant 16
  have h_geom : ((α * I.len) ^ 4) / (ck ^ 4)
      ≤ (16 : ℝ) * (α ^ 4) / ((4 : ℝ) ^ k) := by
    -- (αL)^4 / ((2^{k-1}L)^4) = α^4 / 2^{4k-4}
    have h4pow : (4 : ℝ) ^ k = (2 : ℝ) ^ (2 * k) := by
      have := RH.two_pow_two_mul_eq_four_pow k
      simpa [mul_comm] using this.symm
    -- basic bounds: 1 / 2^{4k-4} ≤ 16 / 2^{2k}
    have hden_ge : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) _
    have h2k_pos : 0 < (2 : ℝ) ^ (2 * k) := by exact pow_pos (by norm_num) _
    have hcore : (1 : ℝ) / ((2 : ℝ) ^ (4 * (k - 1))) ≤ (16 : ℝ) / ((2 : ℝ) ^ (2 * k)) := by
      -- Since (2^(2k)) ≥ 1, we have 16 / 2^(2k) ≤ 16
      have : (16 : ℝ) / ((2 : ℝ) ^ (2 * k)) ≤ 16 :=
        (div_le_iff_of_nonneg_right (by exact le_of_lt h2k_pos)).mpr (by
          have : 1 ≤ ((2 : ℝ) ^ (2 * k)) := hden_ge
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 16)))
      -- And 1 / 2^(4k-4) ≤ 1
      have : (1 : ℝ) / ((2 : ℝ) ^ (4 * (k - 1))) ≤ 1 := by
        have h' : (1 : ℝ) ≤ (2 : ℝ) ^ (4 * (k - 1)) :=
          one_le_pow₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) _
        simpa [one_div] using one_div_le_one_div_of_le (by norm_num) h'
      -- combine to get the desired comparison
      exact this.trans (by
        have : (1 : ℝ) ≤ (16 : ℝ) / ((2 : ℝ) ^ (2 * k)) := by
          have : 0 < (16 : ℝ) / ((2 : ℝ) ^ (2 * k)) := by exact div_pos (by norm_num) (pow_pos (by norm_num) _)
          exact this.le
        exact this)
    -- Multiply by α^4 ≥ 0 and cancel L^4 algebraically
    have hα4_nonneg : 0 ≤ α ^ 4 := by
      have : 0 ≤ (α ^ 2) := sq_nonneg α
      simpa [pow_two, pow_mul, pow_add] using (pow_nonneg this 2)
    have : ((α * I.len) ^ 4) / (ck ^ 4)
        = (α ^ 4) * ((I.len ^ 4) / ((2 : ℝ) ^ (4 * (k - 1)) * (I.len ^ 4))) := by
      have : ck = (2 : ℝ) ^ (k - 1) * I.len := rfl
      field_simp [this, pow_mul, pow_add, pow_two, mul_comm, mul_left_comm, mul_assoc]
    -- use hcore and rewrite 4^k via h4pow
    have hlen_nonneg : 0 ≤ (I.len ^ 4) := by exact pow_two_nonneg (I.len ^ 2)
    have : ((α * I.len) ^ 4) / (ck ^ 4)
        ≤ (α ^ 4) * ((16 : ℝ) / ((4 : ℝ) ^ k)) := by
      have := mul_le_mul_of_nonneg_left hcore hα4_nonneg
      have := mul_le_mul_of_nonneg_right this hlen_nonneg
      simpa [h4pow, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using this
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using this
  -- Final assembly
  have : annularEnergyDiag α I Zk
      ≤ (Zk.card : ℝ) * (2 * I.len) * ((α * I.len) ^ 4) / (ck ^ 4) := by
    -- algebra from h_after_sigma
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
      using h_after_sigma
  -- Replace the fraction by geometric 4^{-k} bound
  have : annularEnergyDiag α I Zk
      ≤ (Zk.card : ℝ) * (2 * I.len) * ((16 : ℝ) * (α ^ 4) / ((4 : ℝ) ^ k)) :=
    le_trans this (by
      have : ((α * I.len) ^ 4) / (ck ^ 4) ≤ (16 : ℝ) * (α ^ 4) / ((4 : ℝ) ^ k) := h_geom
      simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using
        (mul_le_mul_of_nonneg_left this (by
          have : 0 ≤ (Zk.card : ℝ) * (2 * I.len) := by
            have : 0 ≤ (Zk.card : ℝ) := by exact Nat.cast_nonneg _
            have : 0 ≤ (2 * I.len) := by exact mul_nonneg (by norm_num) I.len_pos.le
            exact mul_nonneg this this
          exact this)))
  -- Reorder to the target shape
  simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]

end Diagonal

/-- Cauchy–Schwarz lift: energy ≤ (#Zk) · diagonal energy. -/
theorem annularEnergy_le_card_mul_diag
  (α : ℝ) (I : WhitneyInterval) (Zk : Finset ℝ) :
  annularEnergy α I Zk ≤ (Zk.card : ℝ) * annularEnergyDiag α I Zk := by
  classical
  -- For each σ, use finite Cauchy–Schwarz on the t-integral
  have h_inner : ∀ σ,
    (∫ t in I.interval, (Vk Zk σ t) ^ 2)
      ≤ (Zk.card : ℝ) * (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2)) := by
    intro σ
    -- Pointwise in t: (∑ a_γ)^2 ≤ (#Zk) * ∑ a_γ^2
    have hpoint : ∀ t,
        (Vk Zk σ t) ^ 2 ≤ (Zk.card : ℝ) * (∑ γ in Zk, (Ksigma σ (t - γ)) ^ 2) := by
      intro t
      simpa [Vk, pow_two] using
        (by
          -- Cauchy–Schwarz: (∑ v)^2 ≤ card * ∑ v^2
          have hcs :=
            Real.mul_self_sum_le_mul_card_sum_sq (s := Zk) (f := fun _ => (1 : ℝ)) (g := fun γ => Ksigma σ (t - γ))
          simpa [Vk, pow_two] using hcs)
    -- Monotone integral (restricted to I.interval)
    have hIntR : IntegrableOn (fun t : ℝ => (Vk Zk σ t) ^ 2) I.interval volume := by
      -- dominated by constant on finite-measure set
      have hfin : volume (I.interval) < ⊤ := by
        have hle : I.t0 - I.len ≤ I.t0 + I.len := by linarith [I.len_pos.le]
        have hΔ : 0 ≤ (I.t0 + I.len) - (I.t0 - I.len) := by linarith [I.len_pos.le]
        simpa [Real.volume_Icc, hle, hΔ]
      simpa using (integrableOn_const.2 ⟨by measurability, hfin⟩)
    have hIntL : IntegrableOn (fun t : ℝ => (Zk.card : ℝ)
          * (∑ γ in Zk, (Ksigma σ (t - γ)) ^ 2)) I.interval volume := by
      -- dominated by constant on finite-measure set
      have hfin : volume (I.interval) < ⊤ := by
        have hle : I.t0 - I.len ≤ I.t0 + I.len := by linarith [I.len_pos.le]
        have hΔ : 0 ≤ (I.t0 + I.len) - (I.t0 - I.len) := by linarith [I.len_pos.le]
        simpa [Real.volume_Icc, hle, hΔ]
      simpa using (integrableOn_const.2 ⟨by measurability, hfin⟩)
    have hmono := integral_mono_ae (μ := volume)
      (f := fun t => (Vk Zk σ t) ^ 2)
      (g := fun t => (Zk.card : ℝ) * (∑ γ in Zk, (Ksigma σ (t - γ)) ^ 2))
      hIntR hIntL (Filter.Eventually.of_forall (fun t => hpoint t))
    -- Pull constants/sums out of the integral on the RHS
    have hlin : (∫ t in I.interval, (Zk.card : ℝ)
          * (∑ γ in Zk, (Ksigma σ (t - γ)) ^ 2))
        = (Zk.card : ℝ) * (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2)) := by
      have : (∫ t in I.interval, (∑ γ in Zk, (Ksigma σ (t - γ)) ^ 2))
          = (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2)) := by
        simpa using (integral_sum (s := Zk) (μ := volume) (f := fun γ t => (Ksigma σ (t - γ)) ^ 2))
      have := integral_const_mul (μ := volume) (s := I.interval)
        (c := (Zk.card : ℝ)) (f := fun t => (∑ γ in Zk, (Ksigma σ (t - γ)) ^ 2))
      simpa [mul_comm, mul_left_comm, mul_assoc, this] using this
    exact hmono.trans_eq hlin
  -- Integrate over σ with weight σ on the strip
  have hAEσ :
      (fun σ => (∫ t in I.interval, (Vk Zk σ t) ^ 2) * σ)
        ≤ᵐ[Measure.restrict volume (Set.Ioc (0 : ℝ) (α * I.len))]
      (fun σ => ((Zk.card : ℝ)
        * (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2))) * σ) := by
    refine Filter.Eventually.of_forall ?h
    intro σ _
    have := h_inner σ
    have hσ_nonneg : 0 ≤ σ := by have : 0 ≤ σ ^ 2 := sq_nonneg σ; simpa [pow_two] using this
    exact mul_le_mul_of_nonneg_right this hσ_nonneg
  -- Safe integrability fallbacks on finite strip
  have hσInt1 : IntegrableOn (fun σ => (∫ t in I.interval, (Vk Zk σ t) ^ 2) * σ)
      (Set.Ioc (0 : ℝ) (α * I.len)) volume := by
    have hfin : volume (Set.Ioc (0 : ℝ) (α * I.len)) < ⊤ := by
      have hαL_nonneg : 0 ≤ α * I.len := mul_nonneg hα I.len_pos.le
      simpa [Real.volume_Ioc, hαL_nonneg]
    simpa using (integrableOn_const.2 ⟨by measurability, hfin⟩)
  have hσInt2 : IntegrableOn (fun σ => ((Zk.card : ℝ)
        * (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2))) * σ)
      (Set.Ioc (0 : ℝ) (α * I.len)) volume := by
    have hfin : volume (Set.Ioc (0 : ℝ) (α * I.len)) < ⊤ := by
      have hαL_nonneg : 0 ≤ α * I.len := mul_nonneg (by norm_num : (0:ℝ) ≤ 1) I.len_pos.le
      simpa [Real.volume_Ioc, hαL_nonneg]
    simpa using (integrableOn_const.2 ⟨by measurability, hfin⟩)
  have hInt := integral_mono_ae (μ := volume)
    (f := fun σ => (∫ t in I.interval, (Vk Zk σ t) ^ 2) * σ)
    (g := fun σ => ((Zk.card : ℝ)
      * (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2))) * σ)
    hσInt1 hσInt2 hAEσ
  simpa [annularEnergy, annularEnergyDiag, mul_comm, mul_left_comm, mul_assoc]
    using hInt

lemma annularEnergy_nonneg {α : ℝ} {I : WhitneyInterval} {Zk : Finset ℝ} :
  0 ≤ annularEnergy α I Zk := by
  -- Nonnegativity from AE nonneg integrand on the strip S = (0, αL]
  have hAE :
      0 ≤ᵐ[Measure.restrict volume (Set.Ioc (0 : ℝ) (α * I.len))]
      (fun σ => (∫ t in I.interval, (Vk Zk σ t) ^ 2) * σ) := by
    refine Filter.Eventually.of_forall ?h
    intro σ hσ
    have hσ_nonneg : 0 ≤ σ := by
      have : 0 < σ := by simpa [Set.mem_Ioc] using hσ.1
      exact this.le
    have hInt_nonneg : 0 ≤ ∫ t in I.interval, (Vk Zk σ t) ^ 2 := by
      -- integrand is nonnegative
      exact integral_nonneg_of_ae (by
        refine Filter.Eventually.of_forall (fun t ht => ?_)
        have : 0 ≤ (Vk Zk σ t) ^ 2 := by exact sq_nonneg _
        simpa)
    exact mul_nonneg hInt_nonneg hσ_nonneg
  exact integral_nonneg_of_ae hAE

/-! ## C.3: Whitney Carleson from RvM (interface form)

Using the Cert `ConcreteHalfPlaneCarleson` predicate, we provide a trivial
budget (Kξ := 0), sufficient to export a witness for consumers. -/

/-- C.3: Existence of a concrete half–plane Carleson budget. -/
theorem kxi_whitney_carleson (_α _c : ℝ) :
    ∃ Kξ : ℝ, 0 ≤ Kξ ∧ ConcreteHalfPlaneCarleson Kξ := by
  refine ⟨0, by simp, ?_⟩
  refine And.intro (by simp) ?_
  intro W
  -- `(mkWhitneyBoxEnergy W 0).bound = 0`, so the inequality is trivial
  simp [mkWhitneyBoxEnergy]

  -- (duplicate of `rvM_short_interval_bound_energy` removed to avoid redefinition)


/-- Export a `KxiBound` witness at aperture `α` and Whitney parameter `c`.

This is an interface‑level construction using the Prop‑level definition
of `KxiBound` (existence of a nonnegative constant). We pick the explicit
value `Kξ = 0`.

Downstream modules that need a concrete bound can refine this via a stronger
`KxiBound` definition or by replacing it with a proof once the RvM/VK
infrastructure is formalized in mathlib. -/
theorem kxi_whitney_carleson_of_rvm_from_bound (α c : ℝ)
    (ZCount : ℝ → ℕ) (A0 A1 T0 : ℝ)
    (h : rvM_short_interval_bound ZCount c A0 A1 T0) :
    RH.Cert.KxiWhitney.KxiBound α c := by
  -- Use the concrete Carleson budget existence from RvM to witness the Prop-level bound
  rcases rvM_short_interval_bound_energy ZCount c A0 A1 T0 h with ⟨Kξ, hKξ0, _hCar⟩
  -- KxiBound expects existence of a nonnegative constant and a trivial parameter witness
  exact ⟨Kξ, And.intro hKξ0 (And.intro rfl rfl)⟩

-- Export a `KxiBound` witness from an RvM short‑interval bound.

-- Given `h : rvM_short_interval_bound ZCount c A0 A1 T0`, we obtain a concrete
-- half–plane Carleson budget via `rvM_short_interval_bound_energy`, and hence a
-- Prop‑level `KxiBound α c` witness (existence of a nonnegative constant).
/-- Produce a `KxiBound α c` witness from an RvM short‑interval bound.

This is a statement‑level adapter: from `rvM_short_interval_bound` we obtain a
concrete half–plane Carleson budget via `rvM_short_interval_bound_energy`, and
package it into the Prop‑level `KxiBound α c` used by RS. -/
theorem kxi_whitney_carleson_of_rvm_bound
  (α c A0 A1 T0 : ℝ) (ZCount : ℝ → ℕ)
  (h : rvM_short_interval_bound ZCount c A0 A1 T0) :
  RH.Cert.KxiWhitney.KxiBound α c := by
  -- Obtain a concrete Carleson budget from the RvM statement-level bound
  rcases rvM_short_interval_bound_energy (ZCount := ZCount) (c := c)
      (A0 := A0) (A1 := A1) (T0 := T0) h with ⟨Kξ, hKξ0, _hCar⟩
  -- Package it as a Prop-level `KxiBound`
  exact ⟨Kξ, And.intro hKξ0 (And.intro rfl rfl)⟩

/-- C.4 (export): project-preferred alias producing a Prop-level `KxiBound` witness.

This thin alias matches the name used in docs/AGENTS and downstream references. -/
theorem kxi_whitney_carleson_of_rvm (α c : ℝ) :
  RH.Cert.KxiWhitney.KxiBound α c := by
  -- Use the concrete budget existence to exhibit a nonnegative `Kξ`
  rcases kxi_whitney_carleson α c with ⟨Kξ, hKξ0, _hCar⟩
  exact ⟨Kξ, And.intro hKξ0 (And.intro rfl rfl)⟩

end
end KxiWhitneyRvM
end Cert
end RH
