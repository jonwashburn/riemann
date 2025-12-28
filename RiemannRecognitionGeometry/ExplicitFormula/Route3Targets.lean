/-
# Route 3: concrete targets (F and L)

This file fixes a concrete ambient test-function type `F` to target for Route 3, together with the
corresponding `LagariasFramework F` (still abstract at the `W¹` / explicit-formula level).

We intentionally keep the genuinely hard analytic content (zero-sum definition, convergence,
explicit formula) isolated in the `LagariasFramework` value `Route3.L`.
-/

import Mathlib.Analysis.MellinTransform
import RiemannRecognitionGeometry.ExplicitFormula.Defs
import RiemannRecognitionGeometry.ExplicitFormula.Lagarias
import RiemannRecognitionGeometry.ExplicitFormula.MathlibBridge
import RiemannRecognitionGeometry.ExplicitFormula.MulConvolution

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open MeasureTheory Set
open scoped BigOperators

namespace Route3

/-- Concrete Route 3 test-function type: functions `ℝ → ℂ` (supported on `(0,∞)` in integrals). -/
abbrev F : Type := ℝ → ℂ

/-!
## Note on the concrete `TestSpace` instance

For the Route 3 *skeleton* we keep the test-space operations abstract (via `[TestSpace F]`).

Instantiating `TestSpace` on `F := ℝ → ℂ` with `Mellin := mellin` and `conv := mulConv` is
mathematically correct **under explicit Fubini/Tonelli hypotheses**, but it is not true for *all*
functions `ℝ → ℂ` without integrability assumptions.

Accordingly, we do **not** provide a global `TestSpace F` instance here (and hence no global axiom);
the required analytic hypotheses are carried by `Route3HypBundle.Assumptions.fubini_tonelli`.
-/

end Route3

end ExplicitFormula
end RiemannRecognitionGeometry
