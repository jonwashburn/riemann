import Riemann.RS.BWP.CRGreenReal
import Riemann.RS.BWP.Constants

/-!
# CR-Green Constant Verification

This module verifies that the window bound constant works with Kξ = 0.16.
-/

namespace RH.RS.BWP

open Real

/-- Verification that the effective window constant is compatible with the paper's C_ψ. -/
lemma C_psi_verification :
  C_psi_H1 * Real.sqrt (Kxi_paper + K0_paper) ≤ 0.2 := by
  -- 0.24 * sqrt(0.16 + 0.035) ≈ 0.24 * 0.44 ≈ 0.105 ≤ 0.2
  have hK : Kxi_paper + K0_paper ≤ 0.2 := by
    rw [Kxi_paper, K0_paper]
    norm_num
  have hSqrt : Real.sqrt (Kxi_paper + K0_paper) ≤ 0.45 := by
    rw [Kxi_paper, K0_paper]
    -- 0.19486808... sqrt is ~0.4414...
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · norm_num
  rw [C_psi_H1]
  nlinarith

end RH.RS.BWP
