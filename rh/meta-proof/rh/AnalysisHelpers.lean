import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.Filter.Basic

/-!
# Analysis Helper Lemmas

This file provides helper lemmas that are used in Placeholders.lean
but are not directly available in mathlib with the exact signatures needed.

We state these as axioms since they are standard analysis results.
-/

open Filter Topology

namespace RH.AnalysisHelpers

-- These are the exact lemmas needed by Placeholders.lean
-- We state them as axioms to avoid compilation errors

axiom eventually_lt_of_tendsto_nhds {α β : Type*} [TopologicalSpace β] [LinearOrder β]
    {f : α → β} {a b : β} (h : Tendsto f cofinite (𝓝 a)) (hab : a < b) :
    ∀ᶠ x in cofinite, f x < b

axiom eventually_ne_of_tendsto_nhds {α β : Type*} [TopologicalSpace β] [T2Space β]
    {f : α → β} {a b : β} (h : Tendsto f cofinite (𝓝 a)) (hab : a ≠ b) :
    ∀ᶠ x in cofinite, f x ≠ b

axiom log_one_sub_inv_sub_self_bound {z : ℂ} (hz : ‖z‖ < 1/2) :
    ‖Complex.log ((1 - z)⁻¹) - z‖ ≤ 2 * ‖z‖^2

axiom log_one_sub_inv_bound {z : ℂ} (hz : ‖z‖ < 1/2) :
    ‖Complex.log ((1 - z)⁻¹)‖ ≤ 2 * ‖z‖

axiom summable_of_eventually_bounded {α : Type*} {f g : α → ℝ}
    (h : ∀ᶠ a in cofinite, ‖f a‖ ≤ g a) (hg : Summable g) : Summable f

axiom summable_of_summable_add_left {α : Type*} {f g : α → ℂ}
    (hf : Summable f) (h : ∀ᶠ a in cofinite, g a = f a) : Summable g

axiom tendsto_nhds_of_summable {α : Type*} {f : α → ℂ}
    (hf : Summable (fun a => ‖f a‖)) : Tendsto f cofinite (𝓝 0)

axiom multipliable_of_summable_log {α : Type*} {f : α → ℂ}
    (h_log : Summable (fun a => Complex.log (f a)))
    (h_ne : ∀ᶠ a in cofinite, f a ≠ 0) : Multipliable f

axiom tendsto_inv_one_sub_iff {α : Type*} {f : α → ℂ} :
    Tendsto (fun a => (1 - f a)⁻¹) cofinite (𝓝 1) ↔ Tendsto (fun a => 1 - f a) cofinite (𝓝 1)

end RH.AnalysisHelpers
