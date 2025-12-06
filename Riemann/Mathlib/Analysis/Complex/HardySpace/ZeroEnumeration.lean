
import Riemann.Mathlib.Analysis.Complex.HardySpace.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Meromorphic.Order

/-!
# Zero Enumeration for Analytic Functions

This file provides the infrastructure for enumerating zeros of analytic functions
on the unit disc, with multiplicities.

## Main definitions

* `Complex.ZeroEnumeration` : A structure representing an enumeration of zeros
  with multiplicities for an analytic function on the unit disc.

## Main results

* `Complex.ZeroEnumeration.empty` : Construction for functions with no zeros.
* `Complex.exists_zero_enumeration_of_no_zeros` : Existence theorem.

## Implementation notes

The zero enumeration structure tracks zeros with their multiplicities and
connects to the meromorphic order at each point.
-/

noncomputable section

open Complex Set Metric Filter Topology Real MeasureTheory
open scoped UnitDisc ENNReal NNReal

namespace Complex

/-! ### Zero enumeration structure -/

/-- An enumeration of zeros for an analytic function on the unit disc.

For an analytic function f on the unit disc, we enumerate its zeros as a sequence
(zₙ) with multiplicities (mₙ). The structure ensures:

1. Each zero is either in the disc or has multiplicity 0 (dummy entry)
2. Zeros are distinct where multiplicities are positive
3. Every zero of f in the disc appears in the enumeration
4. The enumeration matches the meromorphic order at each point

This is the correct structure for Jensen's formula and the Blaschke condition.
-/
structure ZeroEnumeration (f : ℂ → ℂ) (hf : AnalyticOn ℂ f unitDisc) where
  /-- The sequence of zeros (may have repeats or dummy values outside disc). -/
  zeros : ℕ → ℂ
  /-- The multiplicity of each zero. -/
  mult : ℕ → ℕ
  /-- Each zero is either in the disc or has multiplicity 0. -/
  in_disc : ∀ n, zeros n ∈ unitDisc ∨ mult n = 0
  /-- The zeros are distinct where they matter. -/
  distinct : ∀ m n, m ≠ n → mult m ≠ 0 → mult n ≠ 0 → zeros m ≠ zeros n
  /-- Every zero of f in the disc appears in the enumeration. -/
  covers_zeros : ∀ z ∈ unitDisc, f z = 0 → (∃ n, zeros n = z ∧ mult n > 0)
  /-- The enumeration matches the meromorphic orders (rigorous version). -/
  matches_order : ∀ z ∈ unitDisc,
    (meromorphicOrderAt f z).untop₀ = ∑' n, if zeros n = z then mult n else 0

/-- Trivial zero enumeration when there are no zeros. -/
def ZeroEnumeration.empty {f : ℂ → ℂ} (hf : AnalyticOn ℂ f unitDisc)
    (h_no_zeros : ∀ z ∈ unitDisc, f z ≠ 0) : ZeroEnumeration f hf where
  zeros := fun _ => 0
  mult := fun _ => 0
  in_disc := fun _ => Or.inr rfl
  distinct := fun _ _ _ hm _ => absurd rfl hm
  covers_zeros := fun z hz hfz => absurd hfz (h_no_zeros z hz)
  matches_order := fun z hz => by
    have hfz_ne : f z ≠ 0 := h_no_zeros z hz
    -- If f(z) ≠ 0 and f is analytic at z, then meromorphicOrderAt f z = 0
    have h_an : AnalyticAt ℂ f z := analyticAt_of_analyticOn_unitDisc hf hz
    have h_cont : ContinuousAt f z := h_an.continuousAt
    have h_tendsto : Tendsto f (𝓝[≠] z) (𝓝 (f z)) := h_cont.continuousWithinAt.tendsto
    have h_ord : meromorphicOrderAt f z = 0 :=
      (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero h_an.meromorphicAt).mp ⟨f z, hfz_ne, h_tendsto⟩
    rw [h_ord]
    simp only [WithTop.untop₀_zero]
    -- Goal: 0 = ∑' n, if 0 = z then 0 else 0
    -- Since mult n = 0 for all n, each term is 0 regardless of whether zeros n = z
    simp only [Nat.cast_zero, ite_self, tsum_zero]

/-- Existence of a zero enumeration for analytic functions with no zeros. -/
lemma exists_zero_enumeration_of_no_zeros {f : ℂ → ℂ} (hf : AnalyticOn ℂ f unitDisc)
    (h_no_zeros : ∀ z ∈ unitDisc, f z ≠ 0) :
    Nonempty (ZeroEnumeration f hf) :=
  ⟨ZeroEnumeration.empty hf h_no_zeros⟩

end Complex
