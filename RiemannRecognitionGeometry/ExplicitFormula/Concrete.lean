/-
# Route 3: concrete `TestSpace` instances

This file provides concrete instances of the abstract Route 3 `TestSpace`.

We start with a *Mellin-domain* instance (functions on `ℂ`), which is fully
algebraic and supports the involution `s ↦ 1 - s` exactly.

Separately (in `MathlibBridge.lean`) we connect the Mellin transform on
functions `(0,∞) → ℂ` to Mathlib's `mellin`, and we will later build a true
function-space instance once multiplicative convolution is defined (U3).
-/

import Mathlib.Analysis.Complex.Basic
import RiemannRecognitionGeometry.ExplicitFormula.Defs

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

/--
A purely algebraic test space: elements are functions on the Mellin side.

This is useful as a *target* for rewriting and for stating positivity gates
without yet committing to analytic convergence details.
-/
abbrev MellinSide := ℂ → ℂ

namespace MellinSide

open ComplexConjugate

/-- Involution on the Mellin side: `f(s) ↦ f(1 - s)`. -/
def tilde (F : MellinSide) : MellinSide := fun s => F (1 - s)

  /-- Conjugation on the Mellin side: `F*(s) = conj(F(conj s))`. -/
  def star (F : MellinSide) : MellinSide := fun s => conj (F (conj s))

/-- Convolution on the Mellin side is pointwise multiplication (so Mellin is identity). -/
def conv (F G : MellinSide) : MellinSide := fun s => F s * G s

instance : TestSpace MellinSide where
  Mellin := fun F s => F s
  conv := conv
  tilde := tilde
  star := star
  mellin_conv := by
    intro f g s
    rfl
  mellin_tilde := by
    intro f s
    rfl
    mellin_star := by
      intro f s
      rfl

end MellinSide

end ExplicitFormula
end RiemannRecognitionGeometry
