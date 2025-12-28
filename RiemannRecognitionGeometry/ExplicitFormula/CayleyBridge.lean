import RiemannRecognitionGeometry.ExplicitFormula.Cayley
import RiemannRecognitionGeometry.ExplicitFormula.MainRoute3

/-!
# Route 3: “Cayley bridge” (precise hypothesis package)

This file exists to make the common *strategy sentence* precise:

> “If we can build an arithmetic/outer field `J` with `Re(2·J) ≥ 0`, then by Cayley we get a Schur
> function `Θ`, hence positivity, hence the Weil gate.”

Only the **first** implication (real-part nonnegativity ⇒ Schur bound for the Cayley transform) is
pure algebra and is proved in `ExplicitFormula/Cayley.lean`.

Everything that would connect such a `J` to the **actual Route 3 Weil quadratic form**

`f ↦ Re (W¹ (f ⋆ₘ ˜ₘ (⋆ₜ f)))`

is additional analytic input. Here we package *exactly* what that extra input would have to look
like, without claiming it holds for ζ.

The cleanest classical-math target is the `ReflectionPositivityRealization` already recorded in
`MainRoute3.lean`: a Hilbert-space representation of the Weil form as an inner product.
-/

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open Complex

section

variable {F : Type} [TestSpace F] [AddCommGroup F] [Module ℂ F]
variable (L : LagariasFramework F)

/--
`CayleyBridgeAssumptions` = the **precise missing hypotheses** needed to turn a candidate “positivity
field” `J` into the Route 3 Weil gate.

What it contains:

- `J` and a domain `S` on which we can assert the right-half-plane condition `Re(2·J) ≥ 0`;
- a *single* bridge axiom `bridge_to_reflection` saying that this right-half-plane condition implies
  a `ReflectionPositivityRealization` of the Weil form.

Once `bridge_to_reflection` is available, Route 3 positivity follows immediately (by
`WeilGate_of_reflectionPositivityRealization`).

**Interpretation:** proving `bridge_to_reflection` for ζ is where genuinely new mathematics would
have to enter; it is essentially a positive-definiteness / GNS statement for the explicit-formula
kernel and is RH-equivalent in known formulations. -/
structure CayleyBridgeAssumptions (L : LagariasFramework F) where
  /-- Candidate arithmetic/outer field. -/
  J : ℂ → ℂ
  /-- Domain where the right-half-plane condition is asserted. -/
  S : Set ℂ
  /-- Positivity input: `Re(2·J) ≥ 0` on `S`. -/
  hRe : ∀ z ∈ S, 0 ≤ (((2 : ℂ) * J z).re)
  /--
  The *entire* analytic bridge: from `Re(2·J) ≥ 0` on `S` to a Hilbert-space (reflection positivity)
  realization of the Weil form.
  -/
  bridge_to_reflection :
    (∀ z ∈ S, 0 ≤ (((2 : ℂ) * J z).re)) →
      OptionalTargets.ReflectionPositivityRealization (F := F) (L := L)

/-!
## Measure-first bridge variant (preferred)

The original `CayleyBridgeAssumptions` packages the Route‑3 bottleneck as:

`Re(2·J) ≥ 0` ⇒ `ReflectionPositivityRealization`.

After the “weight is 0 a.e.” correction for the completed ξ-channel, the cleaner intermediate target
is **measure-first**: produce a `SesqMeasureIdentity` (an `L²(μ)` representation of the Weil form)
and then obtain reflection positivity mechanically.

This structure records that measure-first formulation of the same bottleneck.
-/

/--
`CayleyMeasureBridgeAssumptions` = a measure-first version of the Route‑3 bridge.

It asks for a single bridge axiom producing a `SesqMeasureIdentity` from the half-plane condition
`Re(2·J) ≥ 0` on a domain `S`.

Once such a `SesqMeasureIdentity` exists, `ReflectionPositivityRealization` follows immediately by
`SesqMeasureIdentity.reflectionPositivityRealization`.
-/
structure CayleyMeasureBridgeAssumptions (L : LagariasFramework F) where
  /-- Candidate arithmetic/outer field. -/
  J : ℂ → ℂ
  /-- Domain where the right-half-plane condition is asserted. -/
  S : Set ℂ
  /-- Positivity input: `Re(2·J) ≥ 0` on `S`. -/
  hRe : ∀ z ∈ S, 0 ≤ (((2 : ℂ) * J z).re)
  /--
  The analytic bridge (measure-first): from `Re(2·J) ≥ 0` on `S` to a `SesqMeasureIdentity` for the
  Weil form.
  -/
  bridge_to_measure :
    (∀ z ∈ S, 0 ≤ (((2 : ℂ) * J z).re)) →
      SesqMeasureIdentity (F := F) (L := L)

/-- A measure-bridge package yields a reflection-positivity realization by `L²(μ)` construction. -/
theorem reflectionPositivityRealization_of_measureBridge (B : CayleyMeasureBridgeAssumptions (L := L)) :
    OptionalTargets.ReflectionPositivityRealization (F := F) (L := L) := by
  classical
  have Sμ : SesqMeasureIdentity (F := F) (L := L) := B.bridge_to_measure B.hRe
  exact SesqMeasureIdentity.reflectionPositivityRealization (F := F) (L := L) Sμ

/-- Measure-bridge ⇒ Weil gate (via reflection positivity). -/
theorem WeilGate_of_measureBridge (B : CayleyMeasureBridgeAssumptions (L := L)) :
    L.WeilGate := by
  exact OptionalTargets.WeilGate_of_reflectionPositivityRealization (L := L)
    (h := reflectionPositivityRealization_of_measureBridge (L := L) B)

/-- A Cayley bridge assumption yields a reflection-positivity realization (by applying its bridge). -/
theorem reflectionPositivityRealization_of_bridge (B : CayleyBridgeAssumptions (L := L)) :
    OptionalTargets.ReflectionPositivityRealization (F := F) (L := L) :=
  B.bridge_to_reflection B.hRe

/--
Main “bridge → gate” theorem: if you can supply a `CayleyBridgeAssumptions` package, then the Route 3
Weil gate holds.

Note: the Cayley/Schur step itself is not used here — it is *conceptually* part of what one would
use to prove `bridge_to_reflection`, but the formal bottleneck is exactly `bridge_to_reflection`.
-/
theorem WeilGate_of_cayleyBridge (B : CayleyBridgeAssumptions (L := L)) :
    L.WeilGate := by
  -- Reduce to the already-recorded “reflection positivity ⇒ Weil gate”.
  exact OptionalTargets.WeilGate_of_reflectionPositivityRealization (L := L)
    (h := reflectionPositivityRealization_of_bridge (L := L) B)

/--
Optional helper: the Cayley transform of `2·J` is Schur (unit-disk bounded) on the asserted domain.

This is the purely algebraic part of the story, already proven in `ExplicitFormula/Cayley.lean`.
-/
theorem Theta_isSchurOn_of_bridge (B : CayleyBridgeAssumptions (L := L)) :
    Cayley.IsSchurOn (Cayley.thetaOfJ B.J) B.S :=
  Cayley.Theta_Schur_of_Re_nonneg_on (J := B.J) (S := B.S) B.hRe

end

end ExplicitFormula
end RiemannRecognitionGeometry
