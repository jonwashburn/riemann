import rh.RS.PinchCertificate
import rh.RS.PinchIngredients
import rh.RS.Cayley
import rh.RS.SchurGlobalization

/-!
Axiom checker for CERTIFICATE ROUTE core components.

This checks the building blocks that make up the certificate route,
avoiding Main.lean which has CR-outer dependencies.

Run with:
  lake env lean --run rh/Proof/AxiomsCheckCertificate.lean
-/

#eval IO.println "\n=== CERTIFICATE ROUTE CORE COMPONENTS - AXIOM CHECK ===\n"

#eval IO.println "1. Certificate builder (certificate_from_pinch_ingredients):"
#print axioms RH.RS.certificate_from_pinch_ingredients

#eval IO.println "\n2. Pinch certificate structure builder (buildPinchCertificate):"
#print axioms RH.RS.buildPinchCertificate

#eval IO.println "\n3. Schur globalization (core pinch lemma):"
#print axioms RH.RS.GlobalizeAcrossRemovable

#eval IO.println "\n4. J_pinch analyticity:"
#print axioms RH.RS.J_pinch_analytic_on_offXi

#eval IO.println "\n5. Certificate Theta Schur bound:"
#print axioms RH.RS.Θ_cert_Schur_offXi

#eval IO.println "\n=== CERTIFICATE CORE COMPONENTS CHECK COMPLETE ===\n"
#eval IO.println "These are the building blocks of the certificate route."
#eval IO.println "The final RH theorem assembly is in Main.lean (blocked by Whitney).\n"
