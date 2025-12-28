/-
# Route 3: sesquilinear integral-identity hypothesis bundle (concrete target)

This file instantiates `Route3SesqIntegralHypBundle` for the concrete target

- `Route3.F := ℝ → ℂ`
- `Route3.L : LagariasFramework Route3.F` (still abstract)

All genuinely analytic content (Plancherel/spectral identity, boundary limits, and Fubini/Tonelli
interchanges) remains *axiomatized* here, in one place.
-/

import RiemannRecognitionGeometry.ExplicitFormula.HilbertRealization
import RiemannRecognitionGeometry.ExplicitFormula.ArithmeticJ
import RiemannRecognitionGeometry.ExplicitFormula.CompletedJ
import RiemannRecognitionGeometry.ExplicitFormula.Route3Targets

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open MeasureTheory
open scoped BigOperators
open scoped InnerProductSpace

namespace Route3

-- We keep the concrete target type `F := ℝ → ℂ`, but the `TestSpace F` structure is an explicit
-- parameter (no global instance/axiom).
variable [TestSpace F]

/--
Route 3 candidate “transfer field” producing the spectral weight `weightOfJ J`.

We keep the *ζ-only* choice available as `Jζ`, but the contour/spectral derivation naturally
produces the logarithmic derivative of the **completed** ξ-function. Accordingly, the default
Route 3 weight is built from `CompletedJ.J`.
-/
def Jζ : ℂ → ℂ := ArithmeticJ.J

/-- The default Route 3 transfer field: the completed-channel `Jξ`. -/
def J : ℂ → ℂ := CompletedJ.J

/-- We take the abstract weight `w` to be the canonical one, so `boundary_limits` is definitional. -/
abbrev w : ℝ → ℝ := weightOfJ J

/--
All Route 3 analytic content needed to build the sesquilinear integral identity.

This is the “hard blocker” packaged as a single structure, so downstream theorems can be stated as
`Assumptions → ...` rather than introducing global axioms.
-/
structure Assumptions where
  /-- The Lagarias explicit-formula framework (`W¹`, etc.). -/
  L : LagariasFramework F
  /-- Route 3 boundary transform (assumed ℂ-linear). -/
  transform : F →ₗ[ℂ] (ℝ → ℂ)
  /-- (Normalization) `transform` agrees with the critical-line Mellin transform. -/
  transform_eq_mellinOnCriticalLine :
    ∀ f : F, transform f = fun t : ℝ => mellinOnCriticalLine (F := F) f t
  /-- Pointwise nonnegativity of the canonical weight. -/
  weight_nonneg : ∀ t : ℝ, 0 ≤ weightOfJ J t
  /-- L² admissibility for the concrete weighted transform. -/
  memL2 :
    ∀ f : F,
      MeasureTheory.Memℒp
        (fun t : ℝ => ((Real.sqrt (weightOfJ J t) : ℝ) : ℂ) * transform f t) 2 volume
  /-- (Step 1) The sesquilinear spectral identity with weight `w`. -/
  normalization_match :
    ∀ f g : F,
      L.W1 (pair (F := F) f g) =
        ∫ t : ℝ,
          ((w t : ℝ) : ℂ) * ((starRingEnd ℂ (transform f t)) * (transform g t)) ∂ volume
  /-- (Step 2) Explicit Fubini/Tonelli / dominated convergence obligations used in the derivation. -/
  fubini_tonelli :
    Route3FubiniTonelliObligations (F := F) (μ := volume) (w := w) (transform := transform)

/-!
## Measure-first Route 3 hypothesis bundle (preferred)

For the completed ξ-channel, the naive pointwise density `t ↦ Re(2·J(1/2+it))` is zero a.e. on the
critical line (away from zeros). The correct Route‑3 target is therefore **measure-first**:
package the Weil form as an `L²(μ)` inner product against some boundary measure `μ`.

This structure records exactly that statement, without mentioning a pointwise weight.
-/

structure AssumptionsMeasure where
  /-- The Lagarias explicit-formula framework (`W¹`, etc.). -/
  L : LagariasFramework F
  /-- Boundary measure (need not be absolutely continuous). -/
  μ : Measure ℝ := volume
  /-- Route 3 boundary transform (assumed ℂ-linear). -/
  transform : F →ₗ[ℂ] (ℝ → ℂ)
  /-- (Normalization) `transform` agrees with the critical-line Mellin transform. -/
  transform_eq_mellinOnCriticalLine :
    ∀ f : F, transform f = fun t : ℝ => mellinOnCriticalLine (F := F) f t
  /-- L² admissibility: the transformed functions lie in `L²(μ)`. -/
  memL2 : ∀ f : F, MeasureTheory.Memℒp (transform f) 2 μ
  /-- The measure-first sesquilinear identity (Hilbert-space form). -/
  identity :
    ∀ f g : F,
      L.W1 (pair (F := F) f g) =
        ⟪(memL2 f).toLp (transform f), (memL2 g).toLp (transform g)⟫_ℂ

/--
Measure-first Route 3 hypotheses (Bochner-integral form).

This is the same content as `AssumptionsMeasure`, but stated as the classical integral pairing
`∫ conj(F_f) · F_g dμ`. It converts mechanically to the Hilbert-space form using
`SesqMeasureIntegralIdentity.toSesqMeasureIdentity`.
-/
structure AssumptionsMeasureIntegral where
  /-- The Lagarias explicit-formula framework (`W¹`, etc.). -/
  L : LagariasFramework F
  /-- Boundary measure (need not be absolutely continuous). -/
  μ : Measure ℝ := volume
  /-- Route 3 boundary transform (assumed ℂ-linear). -/
  transform : F →ₗ[ℂ] (ℝ → ℂ)
  /-- (Normalization) `transform` agrees with the critical-line Mellin transform. -/
  transform_eq_mellinOnCriticalLine :
    ∀ f : F, transform f = fun t : ℝ => mellinOnCriticalLine (F := F) f t
  /-- L² admissibility: the transformed functions lie in `L²(μ)`. -/
  memL2 : ∀ f : F, MeasureTheory.Memℒp (transform f) 2 μ
  /-- The measure-first sesquilinear identity as an integral pairing against `μ`. -/
  identity_integral :
    ∀ f g : F,
      L.W1 (pair (F := F) f g) =
        ∫ t : ℝ, (starRingEnd ℂ (transform f t)) * (transform g t) ∂ μ

/-- Convert Bochner-form measure assumptions into Hilbert-form measure assumptions. -/
def AssumptionsMeasureIntegral.toAssumptionsMeasure (A : AssumptionsMeasureIntegral) : AssumptionsMeasure where
  L := A.L
  μ := A.μ
  transform := A.transform
  transform_eq_mellinOnCriticalLine := A.transform_eq_mellinOnCriticalLine
  memL2 := A.memL2
  identity := by
    intro f g
    let S : SesqMeasureIntegralIdentity (F := F) (L := A.L) :=
      { μ := A.μ
        transform := A.transform
        memL2 := A.memL2
        identity_integral := A.identity_integral }
    simpa using (SesqMeasureIntegralIdentity.toSesqMeasureIdentity (F := F) (L := A.L) S).identity f g

/-- Concrete Route 3 hypothesis bundle value, built from `Assumptions`. -/
def H (A : Assumptions) : Route3SesqIntegralHypBundle (F := F) A.L where
  μ := volume
  J := J
  transform := A.transform
  transform_eq_mellinOnCriticalLine := A.transform_eq_mellinOnCriticalLine
  weight_nonneg := A.weight_nonneg
  memL2 := A.memL2
  w := w
  normalization_match := A.normalization_match
  fubini_tonelli := A.fubini_tonelli
  boundary_limits := by
    intro t
    rfl

/-- Package the Route 3 hypotheses as a `SesqIntegralIdentity`. -/
def S (A : Assumptions) : SesqIntegralIdentity (F := F) (L := A.L) :=
  Route3SesqIntegralHypBundle.toSesqIntegralIdentity (F := F) (L := A.L) (H A)

/-- Route 3: the sesquilinear spectral identity yields a reflection-positivity realization. -/
theorem reflectionPositivityRealization (A : Assumptions) :
    OptionalTargets.ReflectionPositivityRealization (F := F) (L := A.L) := by
  classical
  exact SesqIntegralIdentity.reflectionPositivityRealization (F := F) (L := A.L) (S A)

/-- Route 3: reflection-positivity realization implies the Weil gate `WeilGate`. -/
theorem WeilGate (A : Assumptions) : A.L.WeilGate :=
  OptionalTargets.WeilGate_of_reflectionPositivityRealization (F := F) (L := A.L)
    (reflectionPositivityRealization A)

/-- Route 3: the Weil gate implies `RiemannHypothesis` (Lagarias Thm 3.2, packaged). -/
theorem RH (A : Assumptions) : RiemannHypothesis :=
  LagariasFramework.WeilGate_implies_RH (L := A.L) (WeilGate A)

/-! ### Measure-first Route 3 pipeline -/

/-- Package measure-first assumptions as a `SesqMeasureIdentity`. -/
def Sμ (A : AssumptionsMeasure) : SesqMeasureIdentity (F := F) (L := A.L) where
  μ := A.μ
  transform := A.transform
  memL2 := A.memL2
  identity := A.identity

/-- Route 3 (measure-first): sesquilinear identity yields a reflection-positivity realization. -/
theorem reflectionPositivityRealizationμ (A : AssumptionsMeasure) :
    OptionalTargets.ReflectionPositivityRealization (F := F) (L := A.L) := by
  classical
  exact SesqMeasureIdentity.reflectionPositivityRealization (F := F) (L := A.L) (Sμ A)

/-- Route 3 (measure-first): reflection positivity implies the Weil gate `WeilGate`. -/
theorem WeilGateμ (A : AssumptionsMeasure) : A.L.WeilGate :=
  OptionalTargets.WeilGate_of_reflectionPositivityRealization (F := F) (L := A.L)
    (reflectionPositivityRealizationμ A)

/-- Route 3 (measure-first): the Weil gate implies `RiemannHypothesis`. -/
theorem RHμ (A : AssumptionsMeasure) : RiemannHypothesis :=
  LagariasFramework.WeilGate_implies_RH (L := A.L) (WeilGateμ A)

/-- Route 3 (measure-first, integral form): Bochner identity implies RH (via conversion to `AssumptionsMeasure`). -/
theorem RHμ_integral (A : AssumptionsMeasureIntegral) : RiemannHypothesis :=
  RHμ (A := AssumptionsMeasureIntegral.toAssumptionsMeasure A)

end Route3

end ExplicitFormula
end RiemannRecognitionGeometry
