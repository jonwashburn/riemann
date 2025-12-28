/-
# Route 3 main file: explicit-formula gates → RH

This file exposes the Route 3 “gate” theorems:

- `WeilGate → RiemannHypothesis`
- `LiGate → RiemannHypothesis`

All analytic number theory content is isolated behind the Lagarias/Li framework
assumptions; this is a mechanically checkable proof *skeleton*.

Important non-goal (Conrey–Li): we do **not** target de Branges shift-positivity
(pointwise kernel-shift inequalities), which are known to fail for ζ.
The positivity target here is Weil/Li *averaged* positivity.
-/

import RiemannRecognitionGeometry.ExplicitFormula.Lagarias
import RiemannRecognitionGeometry.ExplicitFormula.Li
import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open TestSpace
open scoped InnerProductSpace

namespace LagariasFramework

variable {F : Type} [TestSpace F] (L : LagariasFramework F)

/-- Route 3 Weil gate: assuming the Weil positivity hypothesis yields RH. -/
theorem WeilGate_implies_RH : L.WeilGate → RiemannHypothesis := by
  intro hGate
  exact (L.weilPositivity).2 hGate

/-- Under RH, Weil positivity holds (the easy direction of Lagarias Thm 3.2). -/
theorem RH_implies_WeilGate : RiemannHypothesis → L.WeilGate := by
  intro hRH
  exact (L.weilPositivity).1 hRH

/-!
## Weil criterion (converse direction) as an explicit Lean proof plan

Lagarias Thm 3.2 asserts `RiemannHypothesis ↔ WeilGate`. In the mechanical Route 3 skeleton we
*package* that equivalence as the field `LagariasFramework.weilPositivity`.

For the **unconditional attempt**, it is useful to isolate the exact analytic sub-lemma needed for
the hard direction `WeilGate → RiemannHypothesis`:

> If there exists a nontrivial zero off the critical line, one can construct a test function `f`
> such that the explicit-formula quadratic form `Re(W¹(f ⋆ ~\bar f))` is strictly negative.

The structure below records this "off-line zero detector" as a single hypothesis; the resulting
Lean theorem then derives `WeilGate → RiemannHypothesis` without assuming the full equivalence.
-/

/-- A single analytic lemma that would prove the hard direction `WeilGate → RH`. -/
structure WeilConverseDetector where
  /--
  **Detector lemma** (contrapositive of Weil criterion):

  If `ζ(s)=0` is a nontrivial zero off the critical line, there exists a test function `f`
  with strictly negative quadratic form value `Re(W¹(f ⋆ ~\bar f))`.
  -/
  detect_offline_zero :
    ∀ s : ℂ,
      riemannZeta s = 0 →
      (¬ ∃ n : ℕ, s = -2 * (n + 1)) →  -- exclude trivial zeros
      s ≠ 1 →                       -- exclude the pole
      s.re ≠ (1 / 2 : ℝ) →          -- off the critical line
      ∃ f : F, (L.W1 (TestSpace.quad (F := F) f)).re < 0

/--
`WeilGate → RiemannHypothesis`, assuming only the "off-line zero detector" lemma `D`.

This is the exact proof plan for Lagarias Thm 3.2 (hard direction) inside Route 3.
-/
theorem WeilGate_implies_RH_of_detector (D : WeilConverseDetector (L := L)) :
    L.WeilGate → RiemannHypothesis := by
  intro hGate
  intro s hs0 htriv hs1
  by_contra hsRe
  rcases D.detect_offline_zero (s := s) hs0 htriv hs1 hsRe with ⟨f, hfneg⟩
  have hpos : 0 ≤ (L.W1 (TestSpace.quad (F := F) f)).re := hGate f
  exact (not_lt_of_ge hpos) hfneg

end LagariasFramework

namespace LiFramework

variable {F : Type} [TestSpace F] (L : LiFramework F)

/-- Route 3 Li gate: assuming Li-positivity yields RH. -/
theorem LiGate_implies_RH : L.LiGate → RiemannHypothesis := by
  intro hGate
  exact (L.liCriterion).2 hGate

/-- Under RH, Li positivity holds (the easy direction of Li's criterion). -/
theorem RH_implies_LiGate : RiemannHypothesis → L.LiGate := by
  intro hRH
  exact (L.liCriterion).1 hRH

/-!
## Li criterion as an explicit Lean proof plan (converse direction)

As with Weil, the mechanical Route 3 skeleton packages Li's criterion as the field
`LiFramework.liCriterion : RH ↔ LiGate`.

For the **unconditional attempt**, we isolate the exact analytic content needed for the hard
direction `(∀ n≥1, λₙ ≥ 0) → RH`:

> If there exists a nontrivial zero off the critical line, then *some* Li coefficient `λₙ` is
> strictly negative.

The structure below records this contrapositive as a single hypothesis; the resulting theorem then
derives `LiGate → RiemannHypothesis` without assuming the full equivalence.
-/

/-- A single analytic lemma that would prove the hard direction `LiGate → RH`. -/
structure LiConverseDetector where
  /--
  **Detector lemma** (contrapositive of Li's criterion):

  If `ζ(s)=0` is a nontrivial zero off the critical line, then there exists `n ≥ 1` with `λₙ < 0`.
  -/
  detect_offline_zero :
    ∀ s : ℂ,
      riemannZeta s = 0 →
      (¬ ∃ n : ℕ, s = -2 * (n + 1)) →  -- exclude trivial zeros
      s ≠ 1 →                       -- exclude the pole
      s.re ≠ (1 / 2 : ℝ) →          -- off the critical line
      ∃ n : ℕ, 1 ≤ n ∧ L.lambda n < 0

/--
`LiGate → RiemannHypothesis`, assuming only the "off-line zero detector" lemma `D`.

This is the exact proof plan for the hard direction of Li's criterion inside Route 3.
-/
theorem LiGate_implies_RH_of_detector (D : LiConverseDetector (L := L)) :
    L.LiGate → RiemannHypothesis := by
  intro hGate
  intro s hs0 htriv hs1
  by_contra hsRe
  rcases D.detect_offline_zero (s := s) hs0 htriv hs1 hsRe with ⟨n, hn1, hnneg⟩
  have hpos : 0 ≤ L.lambda n := hGate n hn1
  exact (not_lt_of_ge hpos) hnneg

end LiFramework

/-
## Optional intermediate targets (“attackability”)

These are **not** needed for the mechanical Route 3 skeleton. They simply record,
in Lean-typed form, two intermediate subtargets mentioned in
`renormalized_tail_bound.md` §8.8.
-/

namespace OptionalTargets

section DenseReduction

variable {F : Type} [TestSpace F] [TopologicalSpace F]
variable (L : LagariasFramework F)

/-- Target: reduce Weil positivity to a dense subclass, using continuity of the quadratic form. -/
def DenseSubclassReduction : Prop :=
  ∃ (S : Set F),
    Dense S ∧
    Continuous (fun f : F => (L.W1 (TestSpace.quad (F:=F) f)).re) ∧
      ((∀ f : F, f ∈ S → 0 ≤ (L.W1 (TestSpace.quad (F:=F) f)).re) →
        (∀ f : F, 0 ≤ (L.W1 (TestSpace.quad (F:=F) f)).re))

end DenseReduction

section LiEventualPositivity

variable {F : Type} [TestSpace F]
variable (L : LiFramework F)

/-- Target: a quantitative lower bound implying eventual Li positivity (hence a finite reduction). -/
def LiEventualPositivityTarget : Prop :=
  ∃ (N0 : ℕ) (c C θ : ℝ),
    θ < 1 ∧
    (∀ n : ℕ, N0 ≤ n →
      L.lambda n ≥ ((n : ℝ) / 2) * Real.log (n : ℝ) + c * (n : ℝ) - C * (n : ℝ) ^ θ)

end LiEventualPositivity

section ReflectionPositivity

variable {F : Type} [TestSpace F] [AddCommGroup F] [Module ℂ F]
variable (L : LagariasFramework F)

/--
Target: a Hilbert-space realization of the Weil form (reflection positivity / “sum over zeros is a
norm-square”).

This is the clean classical-math version of the heuristic “the explicit-formula quadratic form is a
physical cost (hence nonnegative)”: exhibit a complex Hilbert space `H` and a linear map `T : F → H`
such that the sesquilinear form

`(f,g) ↦ W¹(f ⋆ₘ ˜ₘ(⋆ₜ g))`

is literally the inner product `⟪T f, T g⟫`.

Once such a representation exists, Weil positivity `Re(W¹(f ⋆ₘ ˜ₘ(⋆ₜ f))) ≥ 0` is immediate.

Mathematically, proving existence of such a representation is equivalent to proving that the kernel
defined by the explicit formula is positive definite (a GNS/Bochner–Schwartz style statement). -/
def ReflectionPositivityRealization : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
    (T : F →ₗ[ℂ] H),
      ∀ f g : F, L.W1 (g ⋆ₘ ˜ₘ (⋆ₜ f)) = ⟪T f, T g⟫_ℂ

/-- A reflection-positivity realization implies the Route 3 Weil gate `WeilGate`. -/
theorem WeilGate_of_reflectionPositivityRealization
    (h : ReflectionPositivityRealization (L := L)) : L.WeilGate := by
  rcases h with ⟨H, _instNACG, _instIP, _instComplete, T, hW⟩
  classical
  -- register the existentially-provided structures as instances
  letI : NormedAddCommGroup H := _instNACG
  letI : InnerProductSpace ℂ H := _instIP
  letI : CompleteSpace H := _instComplete
  intro f
  have hEq : L.W1 (TestSpace.quad (F := F) f) = ⟪T f, T f⟫_ℂ := by
    simpa [TestSpace.quad] using (hW f f)
  have hpos : 0 ≤ (⟪T f, T f⟫_ℂ).re := by
    -- use the ℂ-specialization explicitly to avoid typeclass metavariables
    simpa using (inner_self_nonneg (𝕜 := ℂ) (x := T f))
  simpa [hEq] using hpos

end ReflectionPositivity

end OptionalTargets

end ExplicitFormula
end RiemannRecognitionGeometry
