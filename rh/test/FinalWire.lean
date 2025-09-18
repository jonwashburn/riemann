/-!
Non-build tests: check final theorem symbols exist once PRs land.
This file is under `test/` and not part of the `rh` build; it can be used locally.
-/

import rh.Proof.Main

/- If all components are present, the following names should resolve:
 - RH.Proof.Final.RH_xi_from_outer_and_local
 - RH.Proof.Final.RH_xi_from_outer_and_local_oneSafe
 - RH.Proof.Assembly.RH_riemannXi_from_RS_offZeros_oneSafe
 - RH.AcademicFramework.CompletedXi.zero_symmetry_from_fe
 - RH.AcademicFramework.CompletedXi.G_nonzero_on_Ω_away_from_one
 - RH.RS.OuterData
 - RH.RS.Θ_of
 - RH.RS.OffZeros.LocalData
-/

#check RH.Proof.Final.RH_xi_from_outer_and_local
#check RH.Proof.Final.RH_xi_from_outer_and_local_oneSafe
#check RH.Proof.Assembly.RH_riemannXi_from_RS_offZeros_oneSafe
#check RH.AcademicFramework.CompletedXi.zero_symmetry_from_fe
#check RH.AcademicFramework.CompletedXi.G_nonzero_on_Ω_away_from_one
#check RH.RS.OuterData
#check RH.RS.Θ_of
#check RH.RS.OffZeros.LocalData

/-!
Demo scaffolding: provide a stub `assignPinned` witness (as an axiom here, since
`test/` is not part of the `rh` build) and invoke the ext-based one-safe route
to synthesize mathlib's `RiemannHypothesis`.

This file is non-build and can be used locally to wire end-to-end once a real
`assignPinned` is available.
-/

open Complex Set

noncomputable section

namespace Demo

-- Stub: pinned-removable local data at each ζ-zero in Ω for Θ := Θ_of CRGreenOuterData
axiom assignPinned_stub : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
  ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
    (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
    ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ EqOn (RH.RS.Θ_of RH.RS.CRGreenOuterData) g (U \ {ρ}) ∧
      g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1

-- Demo: derive mathlib's RiemannHypothesis from the stub
def RH_from_stub : RiemannHypothesis :=
  RH.Proof.Final.RH_mathlib_from_CR_outer_oneSafe_ext_final assignPinned_stub

#check RH_from_stub

end Demo

end
