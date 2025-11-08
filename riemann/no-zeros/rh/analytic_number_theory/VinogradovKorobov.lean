import rh.RS.BoundaryWedgeProof

/-!
Vinogradov–Korobov formal counts re-exports.

This lightweight module surfaces the formal dyadic counts lemma and the
VK-style partial-sum budget builder for the canonical `ν_default` used in the
CR–Green/Whitney analysis. It introduces no axioms.
-/

namespace RH.AnalyticNumberTheory
namespace VinogradovKorobov

open RH.RS.BoundaryWedgeProof

/-! ## Short-interval VK count bound for `ν_default`

We package a library-friendly statement for the dyadic annular counts used in
the RS pipeline. The key quantitative claim is a linear partial-sum bound
  ∑_{k<K} ν_default(I,k) ≤ Cν · (2·I.len)
with explicit calibration 0 ≤ Cν ≤ 2. This relies only on the interface-level
facts already available in `BoundaryWedgeProof` about how ν_default is built
from residue bookkeeping and requires no analytic axioms here.

We also provide a ready-to-use bridge constructor that turns this counts bound
into a `VKPartialSumBudget` for the weighted sequence φ_k := (1/4)^k · ν_k.
-/

/-- Short-interval VK counts for the canonical `ν_default` witness. -/
theorem hVK_counts_default (I : RH.RS.WhitneyInterval) :
  ∃ Cν : ℝ, 0 ≤ Cν ∧ Cν ≤ 2 ∧
    (∀ K : ℕ,
      ((Finset.range K).sum (fun k => RH.RS.BoundaryWedgeProof.nu_default I k))
        ≤ Cν * (2 * I.len)) := by
  -- Reuse the formal counts witness exported by the RS module
  simpa using RH.RS.BoundaryWedgeProof.hVK_counts_default I

/-- VK partial‑sum budget for `φ_k = (1/4)^k · ν_default(k)` from the counts bound. -/
lemma VKPartialSumBudget_from_counts_default (I : RH.RS.WhitneyInterval) :
  ∃ (VD : RH.RS.BoundaryWedgeProof.VKPartialSumBudget I
        (RH.RS.BoundaryWedgeProof.phi_of_nu (RH.RS.BoundaryWedgeProof.nu_default I))),
    0 ≤ VD.Cν ∧ VD.Cν ≤ 2 := by
  classical
  -- Obtain the counts bound and calibrations
  rcases hVK_counts_default I with ⟨Cν, hCν0, hCν2, hPS⟩
  -- Build the VK partial-sum budget via the standard adapter
  refine ⟨RH.RS.BoundaryWedgeProof.VKPartialSumBudget.from_counts I
            (RH.RS.BoundaryWedgeProof.nu_default I) Cν
            (RH.RS.BoundaryWedgeProof.nu_default_nonneg I)
            (by intro K; simpa using hPS K), hCν0, hCν2⟩

end VinogradovKorobov
end RH.AnalyticNumberTheory
