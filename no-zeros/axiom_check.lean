import rh.Proof.Main

/-!
Axiom audit for the main RH proof.
-/

#eval IO.println "\n=== MAIN PROOF PATH AXIOM AUDIT ===\n"

-- Core RH theorem
#eval IO.println "1. RH_core (symmetry + no-right-zeros → RH):"
#print axioms RH.Proof.RH_core

#eval IO.println "\n2. RH_riemannXi (RH for arbitrary riemannXi):"
#print axioms RH.Proof.RH_riemannXi

-- Assembly layer
#eval IO.println "\n3. nonvanishing_of_factor (factorization transfer):"
#print axioms RH.Proof.Assembly.nonvanishing_of_factor

#eval IO.println "\n4. RH_riemannXi_from_RS_offZeros:"
#print axioms RH.Proof.Assembly.RH_riemannXi_from_RS_offZeros

#eval IO.println "\n5. RH_riemannXi_from_RS_offZeros_localEq:"
#print axioms RH.Proof.Assembly.RH_riemannXi_from_RS_offZeros_localEq

-- Pinch route
#eval IO.println "\n6. no_right_zeros_from_pinch_assign:"
#print axioms RH.Proof.poissonIntegralinch.no_right_zeros_from_pinch_assign

#eval IO.println "\n7. RH_from_pinch_assign:"
#print axioms RH.Proof.poissonIntegralinch.RH_from_pinch_assign

-- Final export
#eval IO.println "\n8. RH_mathlib_from_xi_ext (export to mathlib):"
#print axioms RH.Proof.Final.RH_mathlib_from_xi_ext

#eval IO.println "\n9. RiemannHypothesis_from_pinch_ext_assign:"
#print axioms RH.Proof.Final.RiemannHypothesis_from_pinch_ext_assign

#eval IO.println "\n10. RiemannHypothesis_mathlib_from_pinch_ext_assign (FINAL):"
#print axioms RH.Proof.Final.RiemannHypothesis_mathlib_from_pinch_ext_assign

#eval IO.println "\n11. RH (top-level theorem from certificate):"
#print axioms RH

#eval IO.println "\n12. RiemannHypothesis_final (consuming pinch certificate):"
#print axioms RiemannHypothesis_final

#eval IO.println "\n=== END AXIOM AUDIT ===\n"
