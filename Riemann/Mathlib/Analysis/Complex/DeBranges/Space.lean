-- Mathlib/Analysis/Complex/DeBranges/Space.lean
import Riemann.Mathlib.Analysis.Complex.DeBranges.Basic
import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna
import Riemann.Mathlib.Analysis.Complex.ConjugateReflection
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# de Branges spaces

This file defines, for a Hermite–Biehler function `E`, the de Branges space `B(E)`
as a space of entire functions satisfying suitable admissibility and `L²` conditions.

The Hilbert space structure will be added in subsequent files.
-/

open Complex HermiteBiehlerFunction MeasureTheory Function
open scoped InnerProductSpace Topology

variable (E : HermiteBiehlerFunction)

namespace DeBranges

/-- The conditions for an entire function `F` to belong to the de Branges space `B(E)`. -/
structure MemSpace (F : ℂ → ℂ) : Prop where
  entire : Differentiable ℂ F
  /-- `F` restricted to `ℝ` belongs to `L²(μ_E)`. -/
  mem_L2 : MemLp (fun x : ℝ => (F x : ℂ)) 2 E.measure
  /-- `F / E` is admissible in the upper half-plane. -/
  admissible_F_over_E : IsDeBrangesAdmissible fun z => F z / E z
  /-- `F# / E` is admissible in the upper half-plane. -/
  admissible_F_sharp_over_E : IsDeBrangesAdmissible fun z =>
    Complex.conjugateReflection F z / E z

/-- The de Branges space `B(E)` associated with a Hermite–Biehler function `E`. -/
@[simp] def Space : Type _ := {F : ℂ → ℂ // MemSpace E F}

namespace Space

instance : CoeFun (Space E) (fun _ => ℂ → ℂ) := ⟨Subtype.val⟩

@[ext]
lemma ext {F G : Space E} (h : ∀ z, F z = G z) : F = G :=
  Subtype.ext (funext h)

/-- Members of `B(E)` are entire functions. -/
lemma entire (F : Space E) : Differentiable ℂ F :=
  F.property.entire

/-- Members of `B(E)` are continuous functions. -/
lemma continuous (F : Space E) : Continuous F :=
  F.property.entire.continuous

/-!
Further algebraic and Hilbert space structure on `Space E` will be developed in
subsequent lemmas and instances.
-/

end Space
end DeBranges
