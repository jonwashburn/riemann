import rh.RS.sealed.BoundaryWedgeProofCore

/-
# Boundary wedge proof – public API

This file intentionally keeps the Route B dependency surface small.  The full
arithmetical proof of `(P+)` along with all intermediate Whitney/VK machinery
now lives in `rh/RS/sealed/BoundaryWedgeProofCore.lean`.  Here we re-export only
the handful of declarations that the rest of the pipeline consumes:

* the calibrated constants (`A_default`, `B_default`, …),
* the dyadic bookkeeping helpers (`phi_of_nu`, `nu_default`, …),
* the VK partial-sum budget interface,
* the final `(P+)` theorem `PPlus_from_constants`.

Downstream stages should import this file (not the sealed core) so that the
analytic payload remains fenced off from the AF/RS build targets.
-/

namespace RH.RS.BoundaryWedgeProof

export RH.RS.BoundaryWedgeProof.Sealed
  (A_default B_default Cdiag_default C_cross_default
   phi_of_nu nu_default nu_default_nonneg
   VKPartialSumBudget VKPartialSumBudget.from_counts
   hVK_counts_default
   PPlus_from_constants)

end RH.RS.BoundaryWedgeProof
