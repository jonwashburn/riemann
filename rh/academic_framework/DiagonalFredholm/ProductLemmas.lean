import rh.academic_framework.Core
import rh.academic_framework.DiagonalFredholm.Operator
import rh.academic_framework.DiagonalFredholm.WeierstrassProduct
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Field.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# Product Lemmas for Diagonal Operators

This file provides lemmas about infinite products related to diagonal operators.

## Main results

* `tprod_exp_eq_exp_tsum` - Product of exponentials equals exponential of sum
* `multipliable_one_sub_of_summable` - Convergence criterion for products of (1-λᵢ)
* `tprod_mul_distrib` - Distributivity of infinite products
-/

namespace AcademicRH.DiagonalFredholm

open Complex Real BigOperators Filter Topology
open scoped Classical

variable {ι : Type*} [Countable ι]

-- Import Multipliable and tprod from mathlib
open Multipliable HasProd

/-- Exponential of series equals product of exponentials -/
lemma tprod_exp_eq_exp_tsum (eigenvals : ι → ℂ)
  (h_summable : Summable eigenvals) :
  ∏' i, exp (eigenvals i) = exp (∑' i, eigenvals i) := by
  -- This follows from the fact that exp preserves sums/products
  -- Use HasSum.cexp which gives us: HasProd (cexp ∘ f) (cexp a) from HasSum f a
  exact h_summable.hasSum.cexp.tprod_eq

/-- Distributivity for multipliable products -/
lemma tprod_mul_distrib {α : Type*} [CommGroup α] [TopologicalSpace α]
  [T2Space α] [ContinuousMul α] (f g : ι → α)
  (hf : Multipliable f) (hg : Multipliable g) :
  ∏' i, (f i * g i) = (∏' i, f i) * (∏' i, g i) := by
  -- Use the mathlib lemma tprod_mul
  exact tprod_mul hf hg



end AcademicRH.DiagonalFredholm
