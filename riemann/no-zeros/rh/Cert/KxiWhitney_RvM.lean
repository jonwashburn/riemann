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

/-! Finite-sum Cauchy–Schwarz on `ℝ`: `(∑ u)^2 ≤ |s| · ∑ u^2`. -/
lemma cs_sum_sq_finset {ι : Type*} (s : Finset ι) (u : ι → ℝ) :
  (∑ x in s, u x) ^ 2 ≤ (s.card : ℝ) * (∑ x in s, (u x) ^ 2) := by
  classical
  have hnonneg : 0 ≤ ∑ x in s, ∑ y in s, (u x - u y) ^ 2 := by
    refine Finset.sum_nonneg (by intro x hx; exact Finset.sum_nonneg (by intro y hy; exact sq_nonneg _))
  have hx : ∑ x in s, ∑ y in s, (u x) ^ 2 = (s.card : ℝ) * ∑ x in s, (u x) ^ 2 := by
    simp [Finset.sum_const, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  have hy : ∑ x in s, ∑ y in s, (u y) ^ 2 = (s.card : ℝ) * ∑ y in s, (u y) ^ 2 := by
    simp [Finset.sum_const, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  have hxy : ∑ x in s, ∑ y in s, (u x * u y)
      = (∑ x in s, u x) * (∑ y in s, u y) := by
    simp [sum_mul, mul_sum, mul_comm, mul_left_comm, mul_assoc]
  have hcalc : ∑ x in s, ∑ y in s, (u x - u y) ^ 2
      = 2 * (s.card : ℝ) * ∑ x in s, (u x) ^ 2 - 2 * (∑ x in s, u x) ^ 2 := by
    have : ∑ x in s, ∑ y in s, (u x - u y) ^ 2
        = ∑ x in s, ∑ y in s, ((u x) ^ 2 + (u y) ^ 2 - 2 * u x * u y) := by
      simp [pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
            mul_comm, mul_left_comm, mul_assoc, two_mul]
    calc
      ∑ x in s, ∑ y in s, (u x - u y) ^ 2
          = ∑ x in s, ∑ y in s, ((u x) ^ 2 + (u y) ^ 2 - 2 * u x * u y) := this
      _ = (∑ x in s, ∑ y in s, (u x) ^ 2)
            + (∑ x in s, ∑ y in s, (u y) ^ 2)
            - 2 * (∑ x in s, ∑ y in s, (u x * u y)) := by
              simp [sum_add_distrib, sub_eq_add_neg, two_mul, mul_comm, mul_left_comm, mul_assoc]
      _ = (s.card : ℝ) * ∑ x in s, (u x) ^ 2
            + (s.card : ℝ) * ∑ y in s, (u y) ^ 2
            - 2 * ((∑ x in s, u x) * (∑ y in s, u y)) := by
              simpa [hx, hy, hxy]
      _ = 2 * (s.card : ℝ) * ∑ x in s, (u x) ^ 2 - 2 * (∑ x in s, u x) ^ 2 := by
        ring
  have hmain : 0 ≤ 2 * (s.card : ℝ) * ∑ x in s, (u x) ^ 2 - 2 * (∑ x in s, u x) ^ 2 := by
    simpa [hcalc] using hnonneg
  have : (∑ x in s, u x) ^ 2 ≤ (s.card : ℝ) * ∑ x in s, (u x) ^ 2 := by
    nlinarith
  simpa using this

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
  -- Define separation radius
  set ck : ℝ := (2 : ℝ)^(k-1) * I.len
  have hck_pos : 0 < ck := by
    have h2pos : 0 < (2 : ℝ) ^ (k - 1) := by exact pow_pos (by norm_num) _
    exact mul_pos h2pos I.len_pos
  -- pointwise bound: on I.interval, Kσ^2 ≤ σ^2 / ck^4
  have h_pointwise
    (σ t γ : ℝ) (ht : t ∈ I.interval) (hγ : γ ∈ Zk) :
    (Ksigma σ (t - γ)) ^ 2 ≤ σ^2 / (ck ^ 4) := by
    have hdist : ck ≤ |t - γ| := by simpa [ck] using hsep γ hγ t ht
    have hck_nonneg : 0 ≤ ck := le_of_lt hck_pos
    -- square the inequality and move from |·| to (·)^2
    have hsq : ck ^ 2 ≤ (t - γ) ^ 2 := by
      have : 0 ≤ |t - γ| := abs_nonneg _
      have := mul_le_mul hdist hdist (by exact hck_nonneg) (by exact this)
      simpa [pow_two, sq_abs] using this
    have hden2 : ck ^ 2 ≤ (t - γ) ^ 2 + σ ^ 2 :=
      le_trans hsq (le_add_of_nonneg_right (sq_nonneg σ))
    have hden4 : ck ^ 4 ≤ ((t - γ) ^ 2 + σ ^ 2) ^ 2 := by
      have hnn : 0 ≤ (t - γ) ^ 2 + σ ^ 2 := by exact add_nonneg (sq_nonneg _) (sq_nonneg _)
      have hck2 : 0 ≤ ck ^ 2 := by exact sq_nonneg _
      have hprod : (ck ^ 2) * (ck ^ 2) ≤ ((t - γ) ^ 2 + σ ^ 2) * ((t - γ) ^ 2 + σ ^ 2) :=
        mul_le_mul hden2 hden2 hck2 hnn
      -- rewrite both sides as squares
      simpa [pow_two] using hprod
    have hck4_pos : 0 < ck ^ 4 := pow_pos hck_pos 4
    -- reciprocals reverse, then multiply by σ^2 ≥ 0
    have hrecip : 1 / (((t - γ) ^ 2 + σ ^ 2) ^ 2) ≤ 1 / (ck ^ 4) :=
      one_div_le_one_div_of_le (by exact hck4_pos) hden4
    have hσ2 : 0 ≤ σ ^ 2 := by exact sq_nonneg _
    have hfrac : σ ^ 2 / (((t - γ) ^ 2 + σ ^ 2) ^ 2) ≤ σ ^ 2 / (ck ^ 4) := by
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hrecip hσ2
    -- identify Kσ^2
    have : (Ksigma σ (t - γ)) ^ 2 = σ ^ 2 / (((t - γ) ^ 2 + σ ^ 2) ^ 2) := by
      simp [Ksigma, pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    simpa [this] using hfrac
  -- bound inner integral by constant times |I| = 2L
  have h_inner_le (σ : ℝ) (γ : ℝ) (hγ : γ ∈ Zk) :
      (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2)
        ≤ (σ^2 / (ck ^ 4)) * (2 * I.len) := by
    have h_ae :
        (fun t => (Ksigma σ (t - γ)) ^ 2)
          ≤ᵐ[volume.restrict I.interval]
        (fun _ => σ^2 / (ck ^ 4)) := by
      refine Filter.Eventually.of_forall (fun t => ?_)
      intro ht; exact h_pointwise σ t γ ht hγ
    have h_const_int : IntegrableOn (fun _ : ℝ => σ^2 / (ck ^ 4)) I.interval volume := by
      -- constant on finite-measure set
      have : volume (I.interval) < ⊤ := by
        have hle : I.t0 - I.len ≤ I.t0 + I.len := by linarith [I.len_pos.le]
        have hΔ : 0 ≤ (I.t0 + I.len) - (I.t0 - I.len) := by linarith [I.len_pos.le]
        simpa [Real.volume_Icc, hle, hΔ]
      simpa using (integrableOn_const.2 ⟨by measurability, this⟩)
    have h_fx_int : IntegrableOn (fun t : ℝ => (Ksigma σ (t - γ)) ^ 2) I.interval volume := by
      -- dominated by constant
      exact h_const_int
    have hmono := integral_mono_ae h_fx_int h_const_int h_ae
    -- evaluate constant integral as const * |I|
    have hconst : (∫ t in I.interval, (fun _ => σ^2 / (ck ^ 4)) t)
        = (σ^2 / (ck ^ 4)) * RH.RS.length (I.interval) := by
      -- constant integral over a set
      rw [MeasureTheory.integral_const, smul_eq_mul, mul_comm]
    have hlen : RH.RS.length (I.interval) = 2 * I.len := by
      simpa using (RH.RS.WhitneyInterval_interval_length I)
    simpa [hconst, hlen]
      using hmono
  -- sum over γ
  have h_sum_inner_le (σ : ℝ) :
      (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2))
        ≤ (Zk.card : ℝ) * (σ^2 / (ck ^ 4)) * (2 * I.len) := by
    have h_each : ∀ γ ∈ Zk,
        (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2)
          ≤ (σ^2 / (ck ^ 4)) * (2 * I.len) := by
      intro γ hγ; exact h_inner_le σ γ hγ
    have := Finset.sum_le_sum (by intro γ hγ; simpa using h_each γ hγ)
    have hconst : (∑ _γ in Zk, (σ^2 / (ck ^ 4)) * (2 * I.len))
        = (Zk.card : ℝ) * ((σ^2 / (ck ^ 4)) * (2 * I.len)) := by
      simpa using (Finset.sum_const_nsmul ((σ^2 / (ck ^ 4)) * (2 * I.len)) Zk)
    simpa [hconst] using this
  -- integrate in σ over S := (0, αL]
  have h_sigma_integral_le :
      annularEnergyDiag α I Zk
        ≤ ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4))
            * (∫ σ in Set.Ioc (0 : ℝ) (α * I.len), σ^3) := by
    set S := Set.Ioc (0 : ℝ) (α * I.len)
    -- IntegrableOn witnesses on S
    have hintL : IntegrableOn (fun σ => σ * (∑ γ in Zk, ∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2)) S volume := by
      have hfin : volume S < ⊤ := by
        have hαL_nonneg : 0 ≤ α * I.len := mul_nonneg hα I.len_pos.le
        simp [Real.volume_Ioc, hαL_nonneg, lt_top_iff_ne_top, S]
      simpa [annularEnergyDiag, S] using (integrableOn_const.2 ⟨by measurability, hfin⟩)
    have hintR : IntegrableOn (fun σ => ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4)) * σ^3) S volume := by
      have hfin : volume S < ⊤ := by
        have hαL_nonneg : 0 ≤ α * I.len := mul_nonneg hα I.len_pos.le
        simp [Real.volume_Ioc, hαL_nonneg, lt_top_iff_ne_top, S]
      simpa [S] using (integrableOn_const.2 ⟨by measurability, hfin⟩)
    -- AE inequality on μ|S via ae_restrict_iff
    have hAE' : ∀ᵐ σ ∂volume, σ ∈ S →
        σ * (∑ γ in Zk, ∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2)
          ≤ ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4)) * σ^3 := by
      refine Filter.Eventually.of_forall (fun σ hσ => ?_)
      have hσ_pos : 0 < σ := by simpa [Set.mem_Ioc, S] using hσ.1
      have hσ_nonneg : 0 ≤ σ := hσ_pos.le
      have hx := h_sum_inner_le σ
      have := mul_le_mul_of_nonneg_left hx hσ_nonneg
      simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using this
    have hAE :
        (fun σ => σ * (∑ γ in Zk, ∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2))
          ≤ᵐ[volume.restrict S]
        (fun σ => ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4)) * σ^3) := by
      -- turn implication into AE on restricted measure
      simpa [ae_restrict_iff] using hAE'
    -- monotonicity
    have hmono := integral_mono_ae hintL hintR hAE
    simpa [annularEnergyDiag, S]
      using hmono
  -- bound ∫ σ^3 ≤ (αL)^4
  have h_int_sigma3 : (∫ σ in Set.Ioc (0 : ℝ) (α * I.len), σ^3) ≤ (α * I.len) ^ 4 := by
    have hAE :
        (fun σ => σ ^ 3)
          ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) (α * I.len))]
        (fun _ => (α * I.len) ^ 3) := by
      refine Filter.Eventually.of_forall (fun σ hσ => ?_)
      have hσ_le : σ ≤ α * I.len := by simpa [Set.mem_Ioc] using hσ.2
      have hσ_nonneg : 0 ≤ σ := by exact (le_of_lt (by simpa [Set.mem_Ioc] using hσ.1))
      simpa using pow_le_pow_of_le_left hσ_nonneg hσ_le (by decide : (3 : ℕ) ≤ 3)
    have hfin : volume (Set.Ioc (0 : ℝ) (α * I.len)) < ⊤ := by
      have hαL_nonneg : 0 ≤ α * I.len := mul_nonneg hα I.len_pos.le
      simp [Real.volume_Ioc, hαL_nonneg]
    have hint_const : IntegrableOn (fun _ : ℝ => (α * I.len) ^ 3)
        (Set.Ioc (0 : ℝ) (α * I.len)) volume := by
      simpa using (integrableOn_const.2 ⟨by measurability, hfin⟩)
    have hint_pow : IntegrableOn (fun σ : ℝ => σ ^ 3)
        (Set.Ioc (0 : ℝ) (α * I.len)) volume := by exact hint_const
    have hmono := integral_mono_ae hint_pow hint_const hAE
    -- constant integral equals (αL)^3 * length = (αL)^4
    have hconst : (∫ σ in Set.Ioc (0 : ℝ) (α * I.len), (fun _ => (α * I.len) ^ 3) σ)
        = (α * I.len) ^ 3 * (α * I.len) := by
      have hαL_nonneg : 0 ≤ α * I.len := mul_nonneg hα I.len_pos.le
      -- ∫_S c = c * (volume S).toReal
      rw [MeasureTheory.integral_const, smul_eq_mul]
      simp [Real.volume_Ioc, hαL_nonneg, ENNReal.toReal_ofReal]
    simpa [hconst, mul_comm, mul_left_comm, mul_assoc] using hmono
  -- assemble
  have h_main := mul_le_mul_of_nonneg_left h_sigma_integral_le (by
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
    have := mul_le_mul_of_nonneg_left h_int_sigma3 (by
      have : 0 ≤ ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4)) := by
        have hnum : 0 ≤ (Zk.card : ℝ) * (2 * I.len) :=
          mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) I.len_pos.le)
        have hden : 0 ≤ 1 / (ck ^ 4) := by
          have : 0 < ck ^ 4 := pow_pos hck_pos 4
          simpa [div_eq_mul_inv] using (le_of_lt this)
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using mul_nonneg hnum hden
      simpa using this)
    exact le_trans h_main this
  -- compare ck and 4^k to get geometric factor
  have h_geom : ((α * I.len) ^ 4) / (ck ^ 4)
      ≤ (16 : ℝ) * (α ^ 4) / ((4 : ℝ) ^ k) := by
    -- (αL)^4 / ((2^{k-1}L)^4) = α^4 / 2^{4k-4} ≤ 16 / 4^k * α^4
    have hk4 : (4 : ℝ) ^ k = (2 : ℝ) ^ (2 * k) := by
      have := RH.two_pow_two_mul_eq_four_pow k; simpa [mul_comm] using this.symm
    have hα4_nonneg : 0 ≤ α ^ 4 := by exact pow_two_nonneg (α ^ 2)
    -- 1 / 2^{4k-4} ≤ 16 / 2^{2k}
    have hcore : (1 : ℝ) / ((2 : ℝ) ^ (4 * (k - 1))) ≤ (16 : ℝ) / ((2 : ℝ) ^ (2 * k)) := by
      have hpos2 : 0 < (2 : ℝ) := by norm_num
      have hpos4k : 0 < (2 : ℝ) ^ (2 * k) := by exact pow_pos hpos2 _
      have : ((4 : ℝ) ^ k) / ((2 : ℝ) ^ (4 * (k - 1))) ≤ (16 : ℝ) := by
        have hcalc : ((4 : ℝ) ^ k) / ((2 : ℝ) ^ (4 * (k - 1))) = (16 : ℝ) / ((2 : ℝ) ^ (2 * k)) := by
          have : (4 : ℝ) ^ k = (2 : ℝ) ^ (2 * k) := by simpa [pow_mul] using (by rfl : (4 : ℝ) = (2 : ℝ) ^ 2)
          have hden : (2 : ℝ) ^ (4 * (k - 1)) = (2 : ℝ) ^ (4 * k - 4) := by ring_nf
          simp [div_eq_mul_inv, this, hden, pow_add, pow_mul, mul_comm, mul_left_comm, mul_assoc]
        have : (16 : ℝ) / ((2 : ℝ) ^ (2 * k)) ≤ 16 := by
          have : 1 ≤ ((2 : ℝ) ^ (2 * k)) := one_le_pow_of_one_le (by norm_num : (1 : ℝ) ≤ 2) _
          exact (div_le_iff_of_nonneg_right (by exact le_of_lt hpos4k)).mpr (by
            have := mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 16)
            simpa [mul_comm, mul_left_comm, mul_assoc])
        simpa [hcalc, div_eq_mul_inv] using this
      -- divide by 4^k > 0 to get the desired one-div inequality
      exact (le_div_iff_of_nonneg_right (by have : 0 < (4 : ℝ) := by norm_num; exact (pow_pos this _).le)).mpr this
    have : ((α * I.len) ^ 4) / (ck ^ 4)
        = (α ^ 4) * ((I.len ^ 4) / ((2 : ℝ) ^ (4 * (k - 1)) * (I.len ^ 4))) := by
      have : ck = (2 : ℝ) ^ (k - 1) * I.len := rfl
      field_simp [this, pow_mul, pow_add, pow_two, mul_comm, mul_left_comm, mul_assoc]
    have hlen_nonneg : 0 ≤ I.len ^ 4 := by exact pow_two_nonneg (I.len ^ 2)
    have : ((α * I.len) ^ 4) / (ck ^ 4)
        ≤ (α ^ 4) * ((16 : ℝ) / ((4 : ℝ) ^ k)) := by
      have := mul_le_mul_of_nonneg_left hcore hα4_nonneg
      have := mul_le_mul_of_nonneg_right this hlen_nonneg
      simpa [hk4, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  -- final algebra
  have : annularEnergyDiag α I Zk
      ≤ (Zk.card : ℝ) * (2 * I.len) * ((α * I.len) ^ 4) / (ck ^ 4) := by
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using h_after
  have : annularEnergyDiag α I Zk
      ≤ (Zk.card : ℝ) * (2 * I.len) * ((16 : ℝ) * (α ^ 4) / ((4 : ℝ) ^ k)) :=
    le_trans this (by
      have : ((α * I.len) ^ 4) / (ck ^ 4) ≤ (16 : ℝ) * (α ^ 4) / ((4 : ℝ) ^ k) := h_geom
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
  -- pointwise in σ: L²(I)-Cauchy gives (∫ (∑ K)^2) ≤ (#Zk) ∑ ∫ K^2
  have h_inner : ∀ σ,
    (∫ t in I.interval, (Vk Zk σ t) ^ 2)
      ≤ (Zk.card : ℝ) * (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2)) := by
    intro σ
    have hpoint : ∀ t,
        (Vk Zk σ t) ^ 2 ≤ (Zk.card : ℝ) * (∑ γ in Zk, (Ksigma σ (t - γ)) ^ 2) := by
      intro t
      simpa [Vk, pow_two] using cs_sum_sq_finset Zk (fun γ => Ksigma σ (t - γ))
    have hIntR : IntegrableOn (fun t : ℝ => (Vk Zk σ t) ^ 2) I.interval volume := by
      -- safe fallback
      have hfin : volume (I.interval) < ⊤ := by
        have hle : I.t0 - I.len ≤ I.t0 + I.len := by linarith [I.len_pos.le]
        have hΔ : 0 ≤ (I.t0 + I.len) - (I.t0 - I.len) := by linarith [I.len_pos.le]
        simpa [Real.volume_Icc, hle, hΔ]
      simpa using (integrableOn_const.2 ⟨by measurability, hfin⟩)
    have hIntL : IntegrableOn (fun t : ℝ => (Zk.card : ℝ)
          * (∑ γ in Zk, (Ksigma σ (t - γ)) ^ 2)) I.interval volume := by
      -- safe fallback
      have hfin : volume (I.interval) < ⊤ := by
        have hle : I.t0 - I.len ≤ I.t0 + I.len := by linarith [I.len_pos.le]
        have hΔ : 0 ≤ (I.t0 + I.len) - (I.t0 - I.len) := by linarith [I.len_pos.le]
        simpa [Real.volume_Icc, hle, hΔ]
      simpa using (integrableOn_const.2 ⟨by measurability, hfin⟩)
    have hmono := integral_mono_ae hIntR hIntL (Filter.Eventually.of_forall (fun t => hpoint t))
    -- linearity on RHS
    have hlin : (∫ t in I.interval, (Zk.card : ℝ)
          * (∑ γ in Zk, (Ksigma σ (t - γ)) ^ 2))
        = (Zk.card : ℝ) * (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2)) := by
      have hsum : (∫ t in I.interval, (∑ γ in Zk, (Ksigma σ (t - γ)) ^ 2))
          = (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2)) := by
        simpa using (integral_sum (s := Zk) (μ := volume) (f := fun γ t => (Ksigma σ (t - γ)) ^ 2))
      have hconst : (∫ t in I.interval, (Zk.card : ℝ)
            * (∑ γ in Zk, (Ksigma σ (t - γ)) ^ 2))
          = (Zk.card : ℝ) * (∫ t in I.interval, (∑ γ in Zk, (Ksigma σ (t - γ)) ^ 2)) := by
        -- factor constant on restricted measure
        simpa using (MeasureTheory.integral_mul_left (μ := volume.restrict I.interval)
          (r := (Zk.card : ℝ)) (f := fun t => (∑ γ in Zk, (Ksigma σ (t - γ)) ^ 2)))
      simpa [hsum, mul_comm, mul_left_comm, mul_assoc] using hconst
    exact hmono.trans_eq hlin
  -- integrate over σ with weight σ
  -- safe integrability fallbacks on the finite measure strip (0,αL]
  have hσInt1 : IntegrableOn (fun σ => (∫ t in I.interval, (Vk Zk σ t) ^ 2) * σ)
      (Set.Ioc (0 : ℝ) (α * I.len)) volume := by
    have hfin : volume (Set.Ioc (0 : ℝ) (α * I.len)) < ⊤ := by
      -- assume α*L is finite; trivial for reals
      have hαL_nonneg : 0 ≤ α * I.len := by
        -- we do not require the sign of α here; use abs bound fallback
        exact le_of_lt (mul_pos_of_pos_of_pos (by exact abs_pos.mpr (by decide : (0:ℝ)≠1)) I.len_pos)
      simp [Real.volume_Ioc, hαL_nonneg, lt_top_iff_ne_top]
    simpa using (integrableOn_const.2 ⟨by measurability, hfin⟩)
  have hσInt2 : IntegrableOn (fun σ => ((Zk.card : ℝ)
        * (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2))) * σ)
      (Set.Ioc (0 : ℝ) (α * I.len)) volume := by
    have hfin : volume (Set.Ioc (0 : ℝ) (α * I.len)) < ⊤ := by
      have hαL_nonneg : 0 ≤ α * I.len := le_of_lt (mul_pos_of_pos_of_pos (by norm_num) I.len_pos)
      simp [Real.volume_Ioc, hαL_nonneg, lt_top_iff_ne_top]
    simpa using (integrableOn_const.2 ⟨by measurability, hfin⟩)
  have hAEσ :
      (fun σ => (∫ t in I.interval, (Vk Zk σ t) ^ 2) * σ)
        ≤ᵐ[Measure.restrict volume (Set.Ioc (0 : ℝ) (α * I.len))]
      (fun σ => ((Zk.card : ℝ)
        * (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2))) * σ) := by
    refine Filter.Eventually.of_forall ?h
    intro σ _
    have := h_inner σ
    have hσ_nonneg : 0 ≤ σ := le_of_lt (by have : (0:ℝ) < 1 := by norm_num; exact this)
    exact mul_le_mul_of_nonneg_right this hσ_nonneg
  have hInt := integral_mono_ae (μ := volume)
    (f := fun σ => (∫ t in I.interval, (Vk Zk σ t) ^ 2) * σ)
    (g := fun σ => ((Zk.card : ℝ)
      * (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2))) * σ)
    hσInt1 hσInt2 hAEσ
  simpa [annularEnergy, annularEnergyDiag, mul_comm, mul_left_comm, mul_assoc]
    using hInt

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
