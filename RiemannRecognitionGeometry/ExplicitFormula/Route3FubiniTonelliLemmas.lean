/-
# Route 3: Fubini/Tonelli obligation lemmas (concrete instance)

This file exposes the individual obligations in `Route3FubiniTonelliObligations` as named lemmas
for the concrete Route 3 target (`Route3.F := ℝ → ℂ`).

Right now these lemmas are *proved* by projecting fields out of the hypothesis bundle
`Route3HypBundle.Route3.fubini_tonelli`; later, each lemma can be replaced by a real proof while
keeping the downstream API stable.
-/

import RiemannRecognitionGeometry.ExplicitFormula.Route3HypBundle

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open MeasureTheory
open scoped BigOperators

namespace Route3

-- `Assumptions` depends on an explicit `TestSpace F` instance.
variable [TestSpace F]

/- Fix a Route 3 assumption package. -/
variable (A : Assumptions)

/-- The key integrability obligation for the Route 3 sesquilinear integrand. -/
theorem integrable_integrand (f g : F) :
    Integrable (A.fubini_tonelli.integrand f g) volume := by
  simpa using A.fubini_tonelli.integrable_integrand f g

/-- Integrability of the corresponding product-measure integrand used for Fubini/Tonelli. -/
theorem integrable_integrand₂ (f g : F) :
    Integrable (A.fubini_tonelli.integrand₂ f g) (volume.prod volume) := by
  simpa using A.fubini_tonelli.integrable_integrand₂ f g

/-- The Fubini/Tonelli integral-swap identity for the Route 3 product integrand. -/
theorem integral_integral_swap (f g : F) :
    (∫ t : ℝ, ∫ u : ℝ, A.fubini_tonelli.integrand₂ f g (t, u) ∂ volume ∂ volume) =
      (∫ u : ℝ, ∫ t : ℝ, A.fubini_tonelli.integrand₂ f g (t, u) ∂ volume ∂ volume) := by
  simpa using A.fubini_tonelli.integral_integral_swap f g

/-- Almost-everywhere summability of the first “series under the integral” family. -/
theorem summable_term₀ (f g : F) :
    ∀ᵐ t : ℝ ∂ volume,
      Summable (fun i : A.fubini_tonelli.ι₀ => A.fubini_tonelli.term₀ i f g t) := by
  simpa using A.fubini_tonelli.summable_term₀ f g

/-- Integrability of the a.e.-summed first “series under the integral”. -/
theorem integrable_tsum_term₀ (f g : F) :
    Integrable (fun t : ℝ => ∑' i : A.fubini_tonelli.ι₀, A.fubini_tonelli.term₀ i f g t) volume := by
  simpa using A.fubini_tonelli.integrable_tsum_term₀ f g

/-- Interchange of integral and infinite sum for the first “series under the integral”. -/
theorem integral_tsum_term₀ (f g : F) :
    (∫ t : ℝ, (∑' i : A.fubini_tonelli.ι₀, A.fubini_tonelli.term₀ i f g t) ∂ volume) =
      ∑' i : A.fubini_tonelli.ι₀, ∫ t : ℝ, A.fubini_tonelli.term₀ i f g t ∂ volume := by
  simpa using A.fubini_tonelli.integral_tsum_term₀ f g

/-- Almost-everywhere summability of the second “series under the integral” family. -/
theorem summable_term₁ (f g : F) :
    ∀ᵐ t : ℝ ∂ volume,
      Summable (fun i : A.fubini_tonelli.ι₁ => A.fubini_tonelli.term₁ i f g t) := by
  simpa using A.fubini_tonelli.summable_term₁ f g

/-- Integrability of the a.e.-summed second “series under the integral”. -/
theorem integrable_tsum_term₁ (f g : F) :
    Integrable (fun t : ℝ => ∑' i : A.fubini_tonelli.ι₁, A.fubini_tonelli.term₁ i f g t) volume := by
  simpa using A.fubini_tonelli.integrable_tsum_term₁ f g

/-- Interchange of integral and infinite sum for the second “series under the integral”. -/
theorem integral_tsum_term₁ (f g : F) :
    (∫ t : ℝ, (∑' i : A.fubini_tonelli.ι₁, A.fubini_tonelli.term₁ i f g t) ∂ volume) =
      ∑' i : A.fubini_tonelli.ι₁, ∫ t : ℝ, A.fubini_tonelli.term₁ i f g t ∂ volume := by
  simpa using A.fubini_tonelli.integral_tsum_term₁ f g

/-- Integrability of each truncation in the dominated-convergence step. -/
theorem integrable_trunc (N : ℕ) (f g : F) :
    Integrable (fun t : ℝ => A.fubini_tonelli.trunc N f g t) volume := by
  simpa using A.fubini_tonelli.integrable_trunc N f g

/-- Convergence of the truncation integrals to the target integral. -/
theorem tendsto_integral_trunc (f g : F) :
    Filter.Tendsto
      (fun N : ℕ => ∫ t : ℝ, A.fubini_tonelli.trunc N f g t ∂ volume)
      Filter.atTop
      (nhds (∫ t : ℝ, A.fubini_tonelli.integrand f g t ∂ volume)) := by
  simpa using A.fubini_tonelli.tendsto_integral_trunc f g

end Route3

end ExplicitFormula
end RiemannRecognitionGeometry
