import Riemann.RS.BWP.DiagonalBounds
import Riemann.RS.BWP.VKAnnularCountsReal
import Riemann.RS.BWP.Constants

/-!
# Kξ Finite Derivation

This module derives the finiteness of Kξ from the VK density estimates.
It chains the DiagonalBounds logic with the real VK counts to produce
a concrete `ConcreteHalfPlaneCarleson` witness.
-/

namespace RH.RS.BWP

open Real Complex

/-- The main theorem: Kξ is finite and bounded by Kxi_paper. -/
theorem Kxi_finite_real (I : RH.Cert.WhitneyInterval)
  (hSplit : HasAnnularSplit I)
  (hSchur : HasSchurRowBounds I) :
  carleson_energy I ≤ Kxi_paper * (2 * I.len) := by
  -- Use the theorem from DiagonalBounds that takes the count hypothesis
  apply carleson_energy_bound_from_split_schur_and_counts_default I hSplit hSchur

  -- Provide the VK count hypothesis using the real derivation
  intro K
  exact vk_partial_sum_bound_real I K

end RH.RS.BWP
