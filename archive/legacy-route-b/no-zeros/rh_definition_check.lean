import Mathlib.NumberTheory.LSeries.RiemannZeta
import rh.Proof.Active

/-!
Verify the RiemannHypothesis is mathlib's standard definition.
-/

#eval IO.println "\n=== RIEMANN HYPOTHESIS DEFINITION CHECK ===\n"

#eval IO.println "Mathlib's RiemannHypothesis definition:"
#check RiemannHypothesis
#print RiemannHypothesis

#eval IO.println "\n=== VERIFY PROOF CONNECTION ===\n"

#eval IO.println "The final theorem proves RiemannHypothesis:"
#check RH.Proof.Final.RiemannHypothesis_mathlib_from_pinch_ext_assign
#check @RH.Proof.Final.RiemannHypothesis_mathlib_from_pinch_ext_assign

#eval IO.println "\n=== END CHECK ===\n"
