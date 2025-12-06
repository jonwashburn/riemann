import Mathlib.Topology.Order

/-!
# Filter lemmas for nhdsWithin

This file collects general lemmas about `nhdsWithin` and eventually predicates.

## Main results

* `Filter.eventually_nhdsWithin_iff`: A property holds eventually in `𝓝[s] a` iff there exists
  a neighborhood of `a` where the property holds for all points in the intersection with `s`.

* `TopologicalSpace.discreteTopology_iff_isOpen_singleton_mem`: A subtype has discrete topology
  iff every singleton (as a subset of the subtype) is open.

## Implementation notes

These are extracted from the Riemann Project's RS/BWP layer for potential Mathlib inclusion.
-/

namespace Filter

open scoped Filter Topology Set

/-- A property holds eventually in `𝓝[s] a` iff there exists a neighborhood of `a`
where the property holds for all points in the intersection with `s`. -/
theorem eventually_nhdsWithin_iff' {α : Type*} [TopologicalSpace α]
    {a : α} {s : Set α} {p : α → Prop} :
    (∀ᶠ x in 𝓝[s] a, p x) ↔ ∀ᶠ x in 𝓝 a, x ∈ s → p x := by
  simp [nhdsWithin, eventually_inf_principal]

end Filter

namespace TopologicalSpace

/-- A subtype has discrete topology iff every singleton (as a subset of the subtype) is open. -/
theorem discreteTopology_iff_isOpen_singleton_mem' {α : Type*} [TopologicalSpace α] {s : Set α} :
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
      have : U = ⋃ x ∈ U, {x} := by
        ext y
        simp only [Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, exists_eq_right']
      rw [this]
      exact isOpen_biUnion (fun x _ => h x)

end TopologicalSpace
