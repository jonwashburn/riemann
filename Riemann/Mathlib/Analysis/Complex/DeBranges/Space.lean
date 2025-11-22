-- Mathlib/Analysis/Complex/DeBranges/Space.lean

import Riemann.Mathlib.Analysis.Complex.DeBranges.Basic
import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna
import Riemann.Mathlib.Analysis.Complex.ConjugateReflection

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# de Branges spaces

Given a Hermite–Biehler function `E : ℂ → ℂ`, we define the de Branges space `B(E)` as
the set of entire functions `F` such that

* `F` restricted to the real line belongs to `L²(μ_E)`, where `μ_E = |E(x)|⁻² dx`
  is the de Branges measure defined in `DeBranges.Basic`;
* the quotients `F / E` and `F# / E` are admissible in the sense of `IsDeBrangesAdmissible`.

These conditions match one of the standard characterizations of de Branges spaces in the
literature: `F/E` and `F#/E` are of bounded type and nonpositive mean type in the upper
half-plane, and `F/E` has square-integrable boundary values on `ℝ`. See, for example,
de Branges' *Hilbert spaces of entire functions* and subsequent expositions.
-/

open Complex HermiteBiehlerFunction MeasureTheory Function
open scoped Complex.ConjugateReflection InnerProductSpace Topology ENNReal

variable (E : HermiteBiehlerFunction)

namespace DeBranges

/-- Predicate expressing that an entire function `F : ℂ → ℂ` belongs to the de Branges
space associated with a Hermite–Biehler function `E`.

The conditions are:

* `entire`: `F` is entire (holomorphic on `ℂ`);
* `mem_L2`: `F` restricted to `ℝ` is in `L²(μ_E)`, where `μ_E = |E(x)|⁻² dx`;
* `admissible_F_over_E`: the quotient `F/E` is de Branges-admissible in the upper half-plane;
* `admissible_F_sharp_over_E`: the conjugate reflection `F#/E` is de Branges-admissible.

This matches the common analytic definition of the de Branges space `B(E)`. -/
structure MemSpace (F : ℂ → ℂ) : Prop where
  /-- `F` is entire. -/
  entire : Differentiable ℂ F
  /-- `F` restricted to `ℝ` belongs to `L²(μ_E)`. -/
  mem_L2 : MemLp (fun x : ℝ => (F x : ℂ)) (2 : ℝ≥0∞) E.measure
  /-- `F / E` is admissible in the upper half-plane. -/
  admissible_F_over_E :
    IsDeBrangesAdmissible fun z : ℂ => F z / E z
  /-- `F# / E` is admissible in the upper half-plane. -/
  admissible_F_sharp_over_E :
    IsDeBrangesAdmissible fun z : ℂ => (F#) z / E z

/-- The de Branges space `B(E)` associated with a Hermite–Biehler function `E`.

It is implemented as the subtype of entire functions `F : ℂ → ℂ` satisfying `MemSpace E F`. -/
def Space : Type _ := {F : ℂ → ℂ // MemSpace E F}

namespace Space

instance : CoeFun (Space E) (fun _ => ℂ → ℂ) :=
  ⟨Subtype.val⟩

@[ext] lemma ext {F G : Space E} (h : ∀ z, F z = G z) : F = G :=
  Subtype.ext (funext h)

/-- Members of the de Branges space `B(E)` are entire functions. -/
lemma entire (F : Space E) : Differentiable ℂ F :=
  F.property.entire

/-- Members of `B(E)` are continuous functions on `ℂ`. -/
lemma continuous (F : Space E) : Continuous F :=
  (Space.entire (E := E) F).continuous

/-- The restriction of a function in `B(E)` to `ℝ` belongs to `L²(μ_E)`. -/
lemma mem_L2 (F : Space E) :
    MemLp (fun x : ℝ => (F x : ℂ)) (2 : ℝ≥0∞) E.measure :=
  F.property.mem_L2

/-- For `F ∈ B(E)`, the quotient `F/E` is de Branges-admissible in the upper half-plane. -/
lemma admissible_F_over_E (F : Space E) :
    IsDeBrangesAdmissible (fun z : ℂ => F z / E z) :=
  F.property.admissible_F_over_E

/-- For `F ∈ B(E)`, the quotient `F#/E` is de Branges-admissible in the upper half-plane. -/
lemma admissible_F_sharp_over_E (F : Space E) :
    IsDeBrangesAdmissible (fun z : ℂ => (F#) z / E z) :=
  F.property.admissible_F_sharp_over_E

/-!
Further algebraic and Hilbert space structure on `Space E` will be developed in subsequent
files. In particular, once appropriate closure lemmas for `IsDeBrangesAdmissible` and
`Memℒp` are available, one can equip `Space E` with a canonical `ℂ`-vector space and
Hilbert space structure via the inner product
\[
  \langle F, G \rangle
    = \frac{1}{\pi} \int_\mathbb R \overline{F(x)}\,G(x)\,d\mu_E(x).
\]
-/

end Space
end DeBranges
