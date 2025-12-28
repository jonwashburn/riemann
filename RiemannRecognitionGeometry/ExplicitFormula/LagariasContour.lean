import RiemannRecognitionGeometry.ExplicitFormula.Lagarias
import RiemannRecognitionGeometry.ExplicitFormula.ContourW1

/-!
# Route 3: Lagarias framework with a contour definition of `W¹`

`LagariasFramework` keeps the genuinely hard analytic definition/convergence of `W¹` abstract.
For the identity-part grind, it is useful to *package* (as data) the statement that `W¹` is the
`T → ∞` limit of the standard rectangular contour integral.

This file introduces a small wrapper structure that:
- carries a `LagariasFramework`, and
- additionally records a contour definition of `W¹` via `ContourW1.W1LimitAssumptions`.

No residue/argument-principle theorems are proved here; this is just scaffolding so later proofs
can target a concrete, conventional definition.
-/

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open TestSpace

/-- A `LagariasFramework` together with a contour-limit definition of the `W¹` functional. -/
structure LagariasContourFramework (F : Type) [TestSpace F] where
  /-- The underlying Lagarias skeleton (explicit formula + Weil criterion). -/
  L : LagariasFramework F
  /-- The completed entire function whose zeros define the spectral side (intended: `xiLagarias`). -/
  xi : ℂ → ℂ
  /-- The usual vertical-line parameter `c > 1` for the explicit-formula rectangle. -/
  c : ℝ
  /-- Contour-limit definition of `W¹` for this `xi`. -/
  contourW1 : ContourW1.W1LimitAssumptions (F := F) xi c
  /-- Compatibility: the framework’s `W1` is the contour-limit functional. -/
  W1_eq : L.W1 = contourW1.W1

namespace LagariasContourFramework

variable {F : Type} [TestSpace F] (LC : LagariasContourFramework F)

/-- Projection to the plain Lagarias framework. -/
def toLagariasFramework : LagariasFramework F := LC.L

@[simp] lemma W1_eq_contour : LC.L.W1 = LC.contourW1.W1 := LC.W1_eq

end LagariasContourFramework

end ExplicitFormula
end RiemannRecognitionGeometry
