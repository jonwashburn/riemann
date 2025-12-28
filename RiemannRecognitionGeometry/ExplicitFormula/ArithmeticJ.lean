import Mathlib.NumberTheory.LSeries.Dirichlet
import RiemannRecognitionGeometry.ExplicitFormula.Cayley

/-!
# Route 3 (auxiliary): the “arithmetic J” from the von Mangoldt L-series

This file does **not** prove RH. It simply pins down, in classical Lean/Mathlib terms,
the natural analytic-number-theory candidate that appears in “arithmetic-side” discussions:

`J_arith(s) := -ζ'(s)/ζ(s)`.

On `Re(s) > 1` this equals the L-series of the von Mangoldt function `Λ`:

`∑ Λ(n) / n^s`.

This is useful if one wants to explore “Cayley/Schur” style transforms of an arithmetic object.
It is intentionally independent of the old Carleson/BMO/Whitney infrastructure.
-/

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open Complex

namespace ArithmeticJ

open LSeries ArithmeticFunction

open scoped LSeries.notation

/-- The canonical arithmetic-side analytic function: `J_arith(s) := - ζ'(s) / ζ(s)`. -/
def J (s : ℂ) : ℂ :=
  - deriv riemannZeta s / riemannZeta s

/--
On `Re(s) > 1`, `J_arith` agrees with the von Mangoldt L-series (Dirichlet series).

This is Mathlib’s theorem `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`,
rearranged to match our `J` definition.
-/
lemma J_eq_LSeries_vonMangoldt {s : ℂ} (hs : 1 < s.re) :
    J s = L (↗Λ) s := by
  -- Mathlib states `L ↗Λ s = - deriv ζ(s) / ζ(s)`; we just rewrite.
  have h := (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := s) hs)
  simpa [J] using h.symm

/--
The Cayley transform of the arithmetic J-field, in the common “2·J” normalization:
`Θ(s) := ((2·J(s)) - 1) / ((2·J(s)) + 1)`.

Note: without additional input, we do *not* know any unit-disk bound for this Θ on any region.
-/
def Theta (s : ℂ) : ℂ :=
  Cayley.thetaOfJ J s

end ArithmeticJ

end ExplicitFormula
end RiemannRecognitionGeometry

