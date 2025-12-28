/-
# Route 3 (major rebuild): explicit-formula infrastructure

This folder intentionally does **not** import any of the existing
Carleson/BMO/Whitney Recognition-Geometry infrastructure.

It provides a mechanically-checkable skeleton for the Lagarias/Weil/Li
explicit-formula route.
-/

import Mathlib.Data.Complex.Basic

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

universe u

/--
An abstract test-function space in the sense of Lagarias' Mellin-transform
normalization.

We keep this abstract on purpose: the Route 3 skeleton is about wiring the
logical implications correctly, while isolating analytic convergence issues
as explicit assumptions.
-/
class TestSpace (F : Type u) where
  /-- Mellin transform `M[f](s)`. -/
  Mellin : F → ℂ → ℂ
  /-- Multiplicative convolution `f * g`. -/
  conv : F → F → F
  /-- Involution `\widetilde f(x) = x^{-1} f(x^{-1})`. -/
  tilde : F → F
  /-- Complex conjugation on the test side (used in `\widetilde{\overline f}`). -/
  star : F → F
  /-- Mellin turns convolution into multiplication. -/
  mellin_conv : ∀ (f g : F) (s : ℂ),
    Mellin (conv f g) s = Mellin f s * Mellin g s
  /-- Mellin intertwines the involution by `s ↦ 1 - s`. -/
  mellin_tilde : ∀ (f : F) (s : ℂ),
    Mellin (tilde f) s = Mellin f (1 - s)
  /-- Mellin intertwines conjugation by `s ↦ conj s` (M[f*](s) = conj(M[f](conj s))). -/
  mellin_star : ∀ (f : F) (s : ℂ),
    Mellin (star f) s = starRingEnd ℂ (Mellin f (starRingEnd ℂ s))

attribute [simp] TestSpace.mellin_conv TestSpace.mellin_tilde TestSpace.mellin_star

namespace TestSpace

variable {F : Type u} [TestSpace F]

notation "M[" f "](" s ")" => TestSpace.Mellin f s
infixl:70 " ⋆ₘ " => TestSpace.conv
notation "˜ₘ" f => TestSpace.tilde f
notation "⋆ₜ" f => TestSpace.star f

/-- The quadratic-form test `f * \widetilde{\overline f}` (abstractly). -/
def quad (f : F) : F := f ⋆ₘ ˜ₘ (⋆ₜ f)

end TestSpace

end ExplicitFormula
end RiemannRecognitionGeometry
