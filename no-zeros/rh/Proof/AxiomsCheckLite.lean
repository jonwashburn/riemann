import rh.Proof.Export

/-!
Minimal axioms printer for final export theorems.
Run with:
  lake env lean rh/Proof/AxiomsCheckLite.lean
-/

#eval IO.println "Axioms: RH.Proof.Export.pipeline_ready_unconditional"
#print axioms RH.Proof.Export.pipeline_ready_unconditional

#eval IO.println "Axioms: RH.Proof.Export.RiemannHypothesis_final"
#print axioms RH.Proof.Export.RiemannHypothesis_final

#eval IO.println "Axioms: RH.Proof.Export.RH"
#print axioms RH.Proof.Export.RH

#eval IO.println "Axioms: RH.Proof.Export.RiemannHypothesis_from_certificate_route"
#print axioms RH.Proof.Export.RiemannHypothesis_from_certificate_route

#eval IO.println "Axioms: RH.Proof.Export.RiemannHypothesis_from_certificate_rep_on_via_cov"
#print axioms RH.Proof.Export.RiemannHypothesis_from_certificate_rep_on_via_cov

#eval IO.println "Axioms: RH.Proof.Export.RiemannHypothesis_mathlib_from_CR_outer_ext"
#print axioms RH.Proof.Export.RiemannHypothesis_mathlib_from_CR_outer_ext
