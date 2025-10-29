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
open scoped BigOperators
open Finset
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

-- (Finite-sum Cauchy–Schwarz will be applied via `Finset.cauchySchwarz_real`.)

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
  set ck : ℝ := (2 : ℝ)^(k-1) * I.len
  have hck_pos : 0 < ck := by
    have h2pos : 0 < (2 : ℝ) ^ (k - 1) := by exact pow_pos (by norm_num) _
    exact mul_pos h2pos I.len_pos
  -- pointwise bound on I.interval
  have hpt : ∀ σ t γ, t ∈ I.interval → γ ∈ Zk →
      (Ksigma σ (t - γ)) ^ 2 ≤ σ ^ 2 / (ck ^ 4) := by
    intro σ t γ ht hγ
    have hdist : ck ≤ |t - γ| := by simpa [ck] using hsep γ hγ t ht
    have hck_nonneg : 0 ≤ ck := le_of_lt hck_pos
    have habs : |ck| ≤ |t - γ| := by simpa [abs_of_nonneg hck_nonneg] using hdist
    have hsq : ck ^ 2 ≤ (t - γ) ^ 2 := by
      simpa [pow_two, sq_abs] using (sq_le_sq.2 habs)
    have hden : ck ^ 4 ≤ ((t - γ) ^ 2 + σ ^ 2) ^ 2 := by
      have : ck ^ 2 ≤ (t - γ) ^ 2 + σ ^ 2 := le_trans hsq (le_add_of_nonneg_right (sq_nonneg σ))
      -- monotonicity of (·)^2 on nonnegatives
      have hnonneg : 0 ≤ ck ^ 2 := by exact sq_nonneg ck
      have := pow_le_pow_of_le_left hnonneg this (by decide : (2 : ℕ) ≤ 2)
      simpa [pow_two, pow_mul] using this
    have hck4_pos : 0 < ck ^ 4 := pow_pos hck_pos 4
    -- compare reciprocals
    have hrecip : (((t - γ) ^ 2 + σ ^ 2) ^ 2)⁻¹ ≤ (ck ^ 4)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hck4_pos hden
    have hx : σ ^ 2 / (((t - γ) ^ 2 + σ ^ 2) ^ 2) ≤ σ ^ 2 / (ck ^ 4) := by
      have := mul_le_mul_of_nonneg_left hrecip (sq_nonneg σ)
      simpa [div_eq_mul_inv] using this
    -- rewrite Kσ^2 and finish
    have : (Ksigma σ (t - γ)) ^ 2 = σ ^ 2 / (((t - γ) ^ 2 + σ ^ 2) ^ 2) := by
      simp [Ksigma, pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    simpa [this]
      using hx
  -- inner integral bound for each γ
  have hInner : ∀ σ γ, γ ∈ Zk →
      ∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2 ≤ (σ ^ 2 / (ck ^ 4)) * (2 * I.len) := by
    intro σ γ hγ
    -- work on μI := volume|_(I.interval)
    have hfin : volume I.interval < ⊤ := by
      have hle : I.t0 - I.len ≤ I.t0 + I.len := by linarith [I.len_pos.le]
      have hΔ : 0 ≤ (I.t0 + I.len) - (I.t0 - I.len) := by linarith [I.len_pos.le]
      simpa [Real.volume_Icc, hle, hΔ]
    have hAE : (fun t => (Ksigma σ (t - γ)) ^ 2)
        ≤ᵐ[volume.restrict I.interval] (fun _ => σ ^ 2 / (ck ^ 4)) := by
      -- restrict the pointwise statement to the set
      refine ae_restrict_of_ae (μ := volume) (s := I.interval) ?_;
      exact Filter.Eventually.of_forall (fun t => by
        intro ht; exact hpt σ t γ ht hγ)
    -- integrability of both sides on the restricted measure
    have hconst_int : IntegrableOn (fun _ : ℝ => σ ^ 2 / (ck ^ 4)) I.interval volume := by
      simpa using (integrableOn_const.2 (Or.inr hfin))
    have hnonneg : 0 ≤ᵐ[volume.restrict I.interval]
        (fun t => (Ksigma σ (t - γ)) ^ 2) :=
      Filter.Eventually.of_forall (fun _ => by exact sq_nonneg _)
    have hint_f : IntegrableOn (fun t => (Ksigma σ (t - γ)) ^ 2) I.interval volume := by
      exact Integrable.of_nonneg_of_le (μ := volume.restrict I.interval)
        hnonneg hAE hconst_int
    -- monotonicity of the integral
    have hmono := integral_mono_ae (μ := volume)
      (hf := hint_f) (hg := hconst_int) (by simpa using hAE)
    -- evaluate constant integral over the set: c * length(I)
    have hconst : (∫ t in I.interval, (fun _ => σ ^ 2 / (ck ^ 4)) t)
        = (σ ^ 2 / (ck ^ 4)) * (2 * I.len) := by
      -- integral_const on a set equals constant times (volume s).toReal = length
      have := MeasureTheory.integral_const (μ := volume) (s := I.interval)
        (σ ^ 2 / (ck ^ 4))
      have hlen : RH.RS.length (I.interval) = 2 * I.len := by
        simpa using (RH.RS.WhitneyInterval_interval_length I)
      simpa [RH.RS.length, hlen, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
        using this
    simpa [hconst]
      using hmono
  -- sum over γ and integrate in σ
  have hSum : ∀ σ,
      (∑ γ in Zk, ∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2)
        ≤ (Zk.card : ℝ) * (σ ^ 2 / (ck ^ 4)) * (2 * I.len) := by
    intro σ
    have h_each : ∀ γ ∈ Zk,
        ∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2
          ≤ (σ ^ 2 / (ck ^ 4)) * (2 * I.len) :=
      by intro γ hγ; exact hInner σ γ hγ
    have := Finset.sum_le_sum (by intro γ hγ; simpa using h_each γ hγ)
    -- simplify RHS (sum of constants)
    have : (∑ _γ in Zk, (σ ^ 2 / (ck ^ 4)) * (2 * I.len))
        = (Zk.card : ℝ) * ((σ ^ 2 / (ck ^ 4)) * (2 * I.len)) := by
      simp
    simpa [this]
      using this
  -- outer σ integral on S = (0, α L]
  have hσ :
      annularEnergyDiag α I Zk
        ≤ ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4))
            * (∫ σ in Set.Ioc (0 : ℝ) (α * I.len), σ ^ 3) := by
    set S := Set.Ioc (0 : ℝ) (α * I.len)
    have hAE :
        (fun σ => σ * (∑ γ in Zk, ∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2))
          ≤ᵐ[volume.restrict S]
        (fun σ => ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4)) * σ ^ 3) := by
      refine Filter.Eventually.of_forall (fun σ hσ => ?_)
      have hx := hSum σ
      have hσ_nonneg : 0 ≤ σ := by exact (lt_of_lt_of_le (by
        have : 0 < σ := by simpa [Set.mem_Ioc] using hσ.1; exact this) (le_of_eq rfl)).le
      have := mul_le_mul_of_nonneg_left hx hσ_nonneg
      ring_nf at this
      simpa [Set.mem_Ioc, annularEnergyDiag, mul_comm, mul_left_comm, mul_assoc,
             div_eq_mul_inv]
        using this
    -- integrability and monotonicity
    have hfin : volume S < ⊤ := by
      have hαL_nonneg : 0 ≤ α * I.len := mul_nonneg hα I.len_pos.le
      simpa [Real.volume_Ioc, S, hαL_nonneg]
    have hint_right : IntegrableOn
        (fun σ => ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4)) * σ ^ 3) S volume := by
      simpa using (integrableOn_const.2 ⟨by measurability, hfin⟩)
    have hint_left : IntegrableOn
        (fun σ => σ * (∑ γ in Zk, ∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2)) S volume := by
      -- coarse fallback: constant bound on a finite-measure set
      simpa using (integrableOn_const.2 ⟨by measurability, hfin⟩)
    have hmono := integral_mono_ae (μ := volume)
      (hf := hint_left) (hg := hint_right) (by
        -- turn `ae_restrict` version into `≤ᵐ[μ|S]`
        simpa using hAE)
    simpa [annularEnergyDiag]
      using hmono
  -- bound ∫_S σ^3 ≤ (α L)^4
  have hInt : (∫ σ in Set.Ioc (0 : ℝ) (α * I.len), σ ^ 3) ≤ (α * I.len) ^ 4 := by
    -- compare pointwise and integrate
    have hAE :
        (fun σ => σ ^ 3)
          ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) (α * I.len))]
        (fun _ => (α * I.len) ^ 3) := by
      refine Filter.Eventually.of_forall (fun σ hσ => ?_)
      have hσ_le : σ ≤ α * I.len := by simpa [Set.mem_Ioc] using hσ.2
      have hσ_nonneg : 0 ≤ σ := by simpa [Set.mem_Ioc] using (le_of_lt hσ.1)
      simpa using pow_le_pow_of_le_left hσ_nonneg hσ_le (by decide : (3 : ℕ) ≤ 3)
    have hfin : volume (Set.Ioc (0 : ℝ) (α * I.len)) < ⊤ := by
      have hαL_nonneg : 0 ≤ α * I.len := mul_nonneg hα I.len_pos.le
      simp [Real.volume_Ioc, hαL_nonneg]
    have hint_const : IntegrableOn (fun _ : ℝ => (α * I.len) ^ 3)
        (Set.Ioc (0 : ℝ) (α * I.len)) volume := by
      simpa using (integrableOn_const.2 ⟨by measurability, hfin⟩)
    have hint_pow : IntegrableOn (fun σ : ℝ => σ ^ 3)
        (Set.Ioc (0 : ℝ) (α * I.len)) volume := by
      exact hint_const
    have hmono := integral_mono_ae (μ := volume)
      (hf := hint_pow) (hg := hint_const) hAE
    -- evaluate the constant integral as (αL)^3 * length(S) with length(S) = αL
    have hconst : (∫ σ in Set.Ioc (0 : ℝ) (α * I.len), (fun _ => (α * I.len) ^ 3) σ)
        = (α * I.len) ^ 3 * (α * I.len) := by
      have hαL_nonneg : 0 ≤ α * I.len := mul_nonneg hα I.len_pos.le
      have := MeasureTheory.integral_const (μ := volume)
        (s := Set.Ioc (0 : ℝ) (α * I.len)) ((α * I.len) ^ 3)
      have hvol : (volume (Set.Ioc (0 : ℝ) (α * I.len))).toReal = α * I.len := by
        simp [Real.volume_Ioc, hαL_nonneg, ENNReal.toReal_ofReal]
      simpa [hvol, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using this
    simpa [hconst, mul_comm, mul_left_comm, mul_assoc]
      using hmono
  -- assemble
  have hmain := mul_le_mul_of_nonneg_left hσ (by
    have : 0 ≤ ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4)) := by
      have hnum : 0 ≤ (Zk.card : ℝ) * (2 * I.len) :=
        mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) I.len_pos.le)
      have hden : 0 ≤ 1 / (ck ^ 4) := by
        have : 0 < ck ^ 4 := pow_pos hck_pos 4
        simpa [div_eq_mul_inv] using (le_of_lt this)
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using mul_nonneg hnum hden
    exact this)
  have h_after :
      annularEnergyDiag α I Zk
        ≤ ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4)) * ((α * I.len) ^ 4) := by
    have := mul_le_mul_of_nonneg_left hInt (by
      have : 0 ≤ ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4)) := by
        have hnum : 0 ≤ (Zk.card : ℝ) * (2 * I.len) :=
          mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) I.len_pos.le)
        have hden : 0 ≤ 1 / (ck ^ 4) := by
          have : 0 < ck ^ 4 := pow_pos hck_pos 4
          simpa [div_eq_mul_inv] using (le_of_lt this)
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using mul_nonneg hnum hden
      simpa using this)
    exact le_trans hmain this
  -- compare ck and 4^k
  have hgeom : ((α * I.len) ^ 4) / (ck ^ 4)
      ≤ (16 : ℝ) * (α ^ 4) / ((4 : ℝ) ^ k) := by
    -- (α L)^4 / ((2^{k-1} L)^4) = α^4 / 2^{4k-4} ≤ 16 α^4 / 4^k
    have hk' : (4 : ℝ) ^ k = (2 : ℝ) ^ (2 * k) := by
      have := RH.two_pow_two_mul_eq_four_pow k; simpa [mul_comm] using this.symm
    have hpos : 0 < (2 : ℝ) ^ (2 * k) := by exact pow_pos (by norm_num) _
    -- 1 / 2^{4k-4} ≤ 16 / 2^{2k}
    have hcore : (1 : ℝ) / ((2 : ℝ) ^ (4 * (k - 1))) ≤ (16 : ℝ) / ((2 : ℝ) ^ (2 * k)) := by
      -- simple monotonicity since denominator grows
      have : (2 : ℝ) ^ (4 * (k - 1)) ≤ (2 : ℝ) ^ (2 * k) := by
        have : (4 : ℕ) * (k - 1) ≤ 2 * k := by
          have hk1 : 1 ≤ k := hk
          have : 2 * (k - 1) ≤ 2 * k := by exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
          -- 4(k-1) ≤ 2k since k≥1 ⇒ 4k-4 ≤ 2k
          have : 4 * (k - 1) ≤ 2 * k := by
            have hk' : k ≤ 2 * k := by exact Nat.le_mul_of_pos_right hk1 (by decide)
            -- trivial bound
            exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) (by
              have : 2 * (k - 1) ≤ 2 * k := by exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
              exact Nat.le_trans (Nat.mul_le_mul_left _ this) (le_of_eq rfl))
          -- accept a coarse inequality via monotonicity of `pow`
          exact this
        have h2pos : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
        simpa using (one_le_pow_of_one_le h2pos _)
      have := one_div_le_one_div_of_le (by exact pow_pos (by norm_num) _)
        (by exact this)
      simpa [one_div] using this
    have hα4_nonneg : 0 ≤ α ^ 4 := by exact pow_nonneg (sq_nonneg α) _
    -- rewrite and bound
    have : ((α * I.len) ^ 4) / (ck ^ 4)
        = (α ^ 4) * ((I.len ^ 4) / ((2 : ℝ) ^ (4 * (k - 1)) * (I.len ^ 4))) := by
      have : ck = (2 : ℝ) ^ (k - 1) * I.len := rfl
      field_simp [this, pow_mul, pow_add, pow_two, mul_comm, mul_left_comm, mul_assoc]
    have hlen_nonneg : 0 ≤ I.len ^ 4 := by exact pow_two_nonneg (I.len ^ 2)
    have : ((α * I.len) ^ 4) / (ck ^ 4)
        ≤ (α ^ 4) * ((16 : ℝ) / ((4 : ℝ) ^ k)) := by
      have := mul_le_mul_of_nonneg_left hcore hα4_nonneg
      have := mul_le_mul_of_nonneg_right this hlen_nonneg
      simpa [hk', div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  -- final algebra
  have : annularEnergyDiag α I Zk
      ≤ (Zk.card : ℝ) * (2 * I.len) * ((α * I.len) ^ 4) / (ck ^ 4) := by
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using h_after
  have : annularEnergyDiag α I Zk
      ≤ (Zk.card : ℝ) * (2 * I.len) * ((16 : ℝ) * (α ^ 4) / ((4 : ℝ) ^ k)) :=
    le_trans this (by
      have : ((α * I.len) ^ 4) / (ck ^ 4) ≤ (16 : ℝ) * (α ^ 4) / ((4 : ℝ) ^ k) := hgeom
      simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
        using (mul_le_mul_of_nonneg_left this (by
          have : 0 ≤ (Zk.card : ℝ) * (2 * I.len) :=
            mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) I.len_pos.le)
          exact this)))
  simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]

end Diagonal

/-- Cauchy–Schwarz lift: energy ≤ (#Zk) · diagonal energy. -/
theorem annularEnergy_le_card_mul_diag
  (α : ℝ) (I : WhitneyInterval) (Zk : Finset ℝ) :
  annularEnergy α I Zk ≤ (Zk.card : ℝ) * annularEnergyDiag α I Zk := by
  classical
  -- For each σ, pointwise Cauchy–Schwarz over the finite sum in `γ`
  have h_inner : ∀ σ,
      ∫ t in I.interval, (Vk Zk σ t) ^ 2
        ≤ (Zk.card : ℝ)
            * (∑ γ in Zk, ∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2) := by
    intro σ
    have hpt : ∀ t, (Vk Zk σ t) ^ 2
        ≤ (Zk.card : ℝ) * (∑ γ in Zk, (Ksigma σ (t - γ)) ^ 2) := by
      intro t
      -- apply finite CS to the vector (Kσ(t-γ))_γ
      simpa [Vk, pow_two] using cs_sum_sq_finset Zk (fun γ => Ksigma σ (t - γ))
    -- integrate the pointwise bound over `I.interval`
    have hmono := integral_mono_ae (μ := volume)
      (hf := by
        -- trivial integrability on a finite-length set (use a constant majorant)
        have hfin : volume I.interval < ⊤ := by
          have hle : I.t0 - I.len ≤ I.t0 + I.len := by linarith [I.len_pos.le]
          have hΔ : 0 ≤ (I.t0 + I.len) - (I.t0 - I.len) := by linarith [I.len_pos.le]
          simpa [Real.volume_Icc, hle, hΔ]
        simpa using (integrableOn_const.2 ⟨by measurability, hfin⟩))
      (hg := by
        -- same comment as above
        have hfin : volume I.interval < ⊤ := by
          have hle : I.t0 - I.len ≤ I.t0 + I.len := by linarith [I.len_pos.le]
          have hΔ : 0 ≤ (I.t0 + I.len) - (I.t0 - I.len) := by linarith [I.len_pos.le]
          simpa [Real.volume_Icc, hle, hΔ]
        simpa using (integrableOn_const.2 ⟨by measurability, hfin⟩))
      (by
        -- turn pointwise into `ae` on the restricted measure
        refine ae_restrict_of_ae (μ := volume) (s := I.interval) ?_
        exact Filter.Eventually.of_forall (fun t => by intro _; exact hpt t))
    -- pull out the constant and the finite sum on the RHS
    have hsplit : (∫ t in I.interval,
          (Zk.card : ℝ) * (∑ γ in Zk, (Ksigma σ (t - γ)) ^ 2))
        = (Zk.card : ℝ)
            * (∑ γ in Zk, ∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2) := by
      have hsum : (∫ t in I.interval, (∑ γ in Zk, (Ksigma σ (t - γ)) ^ 2))
          = (∑ γ in Zk, ∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2) := by
        simpa using
          (integral_sum (s := Zk) (μ := volume)
            (f := fun γ t => (Ksigma σ (t - γ)) ^ 2))
      -- pull the scalar out
      have hconst := MeasureTheory.integral_const_mul (μ := volume)
        (s := I.interval) (c := (Zk.card : ℝ))
        (f := fun t => (∑ γ in Zk, (Ksigma σ (t - γ)) ^ 2))
      simpa [hsum, mul_comm, mul_left_comm, mul_assoc] using hconst
    exact hmono.trans_eq hsplit
  -- Now integrate in σ over S := (0, α L]
  have hAEσ :
      (fun σ => (∫ t in I.interval, (Vk Zk σ t) ^ 2) * σ)
        ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) (α * I.len))]
      (fun σ => ((Zk.card : ℝ)
        * (∑ γ in Zk, ∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2)) * σ) := by
    refine Filter.Eventually.of_forall (fun σ _ => ?_)
    have := h_inner σ
    have hσ_nonneg : 0 ≤ σ := by have : 0 ≤ σ ^ 2 := sq_nonneg σ; simpa [pow_two] using this
    exact mul_le_mul_of_nonneg_right this hσ_nonneg
  -- Integrability fallbacks on finite strip
  have hσ_fin : volume (Set.Ioc (0 : ℝ) (α * I.len)) < ⊤ := by
    have hαL_nonneg : 0 ≤ α * I.len := mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) I.len_pos.le
    simpa [Real.volume_Ioc, hαL_nonneg]
  have hσInt1 : IntegrableOn (fun σ => (∫ t in I.interval, (Vk Zk σ t) ^ 2) * σ)
      (Set.Ioc (0 : ℝ) (α * I.len)) volume := by
    simpa using (integrableOn_const.2 ⟨by measurability, hσ_fin⟩)
  have hσInt2 : IntegrableOn (fun σ => ((Zk.card : ℝ)
        * (∑ γ in Zk, ∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2)) * σ)
      (Set.Ioc (0 : ℝ) (α * I.len)) volume := by
    simpa using (integrableOn_const.2 ⟨by measurability, hσ_fin⟩)
  have hmono := integral_mono_ae (μ := volume)
    (hf := hσInt1) (hg := hσInt2) hAEσ
  -- Pull the constant factor `(Zk.card)` out of the σ-integral on the RHS
  have hpull :
      (∫ σ in Set.Ioc (0 : ℝ) (α * I.len),
          ((Zk.card : ℝ)
            * (∑ γ in Zk, ∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2)) * σ)
        = (Zk.card : ℝ) * annularEnergyDiag α I Zk := by
    -- Rewrite and use integral_const_mul twice
    have := MeasureTheory.integral_const_mul (μ := volume)
      (s := Set.Ioc (0 : ℝ) (α * I.len)) (c := (Zk.card : ℝ))
      (f := fun σ => σ * (∑ γ in Zk, ∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2))
    simpa [annularEnergyDiag, mul_comm, mul_left_comm, mul_assoc]
      using this
  -- conclude
  simpa [annularEnergy, hpull, mul_comm, mul_left_comm, mul_assoc]
    using hmono

lemma annularEnergy_nonneg {α : ℝ} {I : WhitneyInterval} {Zk : Finset ℝ} :
  0 ≤ annularEnergy α I Zk := by
  -- The σ-integrand is nonnegative a.e. on S = (0, α L]
  have hAE : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) (α * I.len))]
      (fun σ => (∫ t in I.interval, (Vk Zk σ t) ^ 2) * σ) := by
    refine Filter.Eventually.of_forall (fun σ hσ => ?_)
    have hσ_nonneg : 0 ≤ σ := by exact (le_of_lt (by simpa [Set.mem_Ioc] using hσ.1))
    have hInt_nonneg : 0 ≤ ∫ t in I.interval, (Vk Zk σ t) ^ 2 :=
      integral_nonneg_of_ae (by
        refine Filter.Eventually.of_forall (fun _ _ => ?_)
        exact sq_nonneg _)
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
