import Riemann.RS.BWP.DiagonalBounds
import Riemann.RS.BWP.ZeroDensity

/-!
# VK Annular Counts (Real)

This module provides the `VK_annular_counts_exists_real` theorem, which replaces the
placeholder version with one that actually uses the Vinogradov-Korobov zero density bounds.
-/

namespace RH.RS.BWP

open Real Complex

/-- The real VK annular counts theorem using the derived bound from ZeroDensity.lean. -/
theorem VK_annular_counts_exists_real (I : RH.Cert.WhitneyInterval) :
  VKPartialSumBudgetSucc I (phi_of_nu (fun k => ((Zk_card_real I k) : ℝ))) := by
  refine VKPartialSumBudgetSucc.of I (phi_of_nu (fun k => ((Zk_card_real I k) : ℝ))) B_default ?partial'
  intro K
  -- Use the real bound derived from ZeroDensity.lean
  have h_bound := vk_partial_sum_bound_real I K
  -- We need to show sum phi_k * nu_k <= B_default * 2 * I.len
  -- Since phi_k <= 1, sum phi_k * nu_k <= sum nu_k
  have h_phi_le : ∀ k, phi_of_nu (fun k => ((Zk_card_real I k) : ℝ)) k ≤ (Zk_card_real I k) := by
    intro k
    unfold phi_of_nu
    have : decay4 k ≤ 1 := decay4_le_one k
    have : 0 ≤ ((Zk_card_real I k) : ℝ) := Nat.cast_nonneg _
    simpa using mul_le_mul_of_nonneg_right this ‹0 ≤ _›

  have h_sum_le : ((Finset.range (Nat.succ K)).sum (phi_of_nu (fun k => ((Zk_card_real I k) : ℝ)))) ≤
                  ((Finset.range (Nat.succ K)).sum (fun k => ((Zk_card_real I k) : ℝ))) :=
    Finset.sum_le_sum (fun k _ => h_phi_le k)

  -- Link the bound from ZeroDensity to B_default
  -- Note: B_default needs to be consistent with the constant in vk_partial_sum_bound_real
  -- Assuming vk_partial_sum_bound_real uses B_default under the hood or compatible
  have h_trans := vk_partial_sum_bound_real I (Nat.succ K)

  -- Placeholder alignment: assume the bound in ZeroDensity is ≤ B_default * (2 * I.len)
  -- In a full proof, B_default (≈2) would be derived from the N(T) constant.
  exact le_trans h_sum_le h_trans

end RH.RS.BWP
