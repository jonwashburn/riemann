/-
Faithful phase interface for Recognition Geometry.

Motivation:
The principal argument `Complex.arg : ℂ → ℝ` is discontinuous (branch cut), so treating
`argXi(t)` as a globally well-behaved harmonic conjugate is not faithful.

A standard way to model phase correctly is to work modulo `2π`, i.e. in `Real.Angle = ℝ/2πℤ`.
On intervals where ξ is nonzero, one can (in analysis) lift this to a continuous real-valued phase;
later milestones will add the needed hypotheses/lemmas for such lifts.
-/

import RiemannRecognitionGeometry.FeffermanStein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Normed.Group.AddCircle

noncomputable section

open Real Complex

namespace RiemannRecognitionGeometry

/-- Phase of ξ on the critical line as an element of `Real.Angle = ℝ/2πℤ`.

This is the argument **modulo 2π**, so branch cut jumps of `Complex.arg` are identified.
At zeros we still take the junk value coming from `arg 0 = 0`.
-/
def phaseXi (t : ℝ) : Real.Angle :=
  ((xiOnCriticalLine t).arg : Real.Angle)

/-- A real-valued continuous lift of `phaseXi` on an interval `[a, b]`.

This is a *hypothesis object*: we do **not** claim it exists without extra assumptions
(e.g. that `xiOnCriticalLine` is nonzero on `[a, b]`, so a continuous argument lift exists).
-/
structure PhaseLift (a b : ℝ) where
  /-- Ordering assumption so endpoints belong to `Icc a b`. -/
  hab : a ≤ b
  /-- The chosen real-valued lift. -/
  lift : ℝ → ℝ
  /-- The lift agrees with `phaseXi` modulo `2π` on `[a, b]`. -/
  coe_lift_eq : ∀ t : ℝ, t ∈ Set.Icc a b → (lift t : Real.Angle) = phaseXi t
  /-- Continuity of the chosen lift on `[a, b]`. -/
  continuousOn_lift : ContinuousOn lift (Set.Icc a b)

/-- The real phase change of a chosen lift on `[a, b]`. -/
def phaseLiftChange {a b : ℝ} (h : PhaseLift a b) : ℝ :=
  h.lift b - h.lift a

/-- Coercing the lift phase change to `Real.Angle` recovers the `Real.Angle` phase difference. -/
lemma coe_phaseLiftChange {a b : ℝ} (h : PhaseLift a b) :
    (phaseLiftChange h : Real.Angle) = phaseXi b - phaseXi a := by
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, h.hab⟩
  have hb : b ∈ Set.Icc a b := ⟨h.hab, le_rfl⟩
  unfold phaseLiftChange
  -- `((x - y : ℝ) : Real.Angle) = (x : Real.Angle) - (y : Real.Angle)`.
  simpa [Real.Angle.coe_sub, h.coe_lift_eq a ha, h.coe_lift_eq b hb]

/-- Phase change across a Whitney interval, valued in `Real.Angle` (i.e. modulo `2π`). -/
def xiPhaseChangeAngle (I : WhitneyInterval) : Real.Angle :=
  phaseXi (I.t0 + I.len) - phaseXi (I.t0 - I.len)

/-- The (real-valued) Blaschke phase on the critical line associated to a putative zero `ρ`.

This is the elementary arctan phase used in the RG argument.
-/
def rgBlaschkePhase (ρ : ℂ) (t : ℝ) : ℝ :=
  Real.arctan ((t - ρ.im) / (ρ.re - 1/2))

/-- The Blaschke phase change across a Whitney interval, as a real number.

This matches the `let blaschke := ...` expression in `Conjectures.weierstrass_tail_bound_axiom_statement`.
-/
def rgBlaschkePhaseChange (I : WhitneyInterval) (ρ : ℂ) : ℝ :=
  rgBlaschkePhase ρ (I.t0 - I.len) - rgBlaschkePhase ρ (I.t0 + I.len)

/-- The Blaschke phase change across a Whitney interval, valued in `Real.Angle` (modulo `2π`). -/
def rgBlaschkePhaseChangeAngle (I : WhitneyInterval) (ρ : ℂ) : Real.Angle :=
  (rgBlaschkePhaseChange I ρ : Real.Angle)

/-- The “cofactor phase” (modulo `2π`) obtained by subtracting the Blaschke phase.

If one can factor out the half-plane Blaschke inner factor corresponding to `ρ`, then this is
the boundary phase of the analytic cofactor.
-/
def rgCofactorPhaseAngle (ρ : ℂ) (t : ℝ) : Real.Angle :=
  phaseXi t + (rgBlaschkePhase ρ t : Real.Angle)

/-- Algebraic reduction: the Weierstrass tail angle is exactly the phase change of the cofactor phase.

This isolates the analytic content needed to prove the tail bound: a Green/Carleson phase bound for the
cofactor phase (with the *same* BMO/Carleson constant, since the Blaschke factor is unimodular on the boundary).
-/
lemma xiPhaseChangeAngle_sub_rgBlaschkePhaseChangeAngle (I : WhitneyInterval) (ρ : ℂ) :
    xiPhaseChangeAngle I - rgBlaschkePhaseChangeAngle I ρ =
      rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len) := by
  -- Unfold definitions and simplify in the additive group `Real.Angle`.
  simp [xiPhaseChangeAngle, rgBlaschkePhaseChangeAngle, rgBlaschkePhaseChange, rgCofactorPhaseAngle,
    rgBlaschkePhase, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

/-- Norm-level version of `xiPhaseChangeAngle_sub_rgBlaschkePhaseChangeAngle`. -/
lemma norm_xiPhaseChangeAngle_sub_rgBlaschkePhaseChangeAngle (I : WhitneyInterval) (ρ : ℂ) :
    ‖xiPhaseChangeAngle I - rgBlaschkePhaseChangeAngle I ρ‖ =
      ‖rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len)‖ := by
  simpa using congrArg (fun x : Real.Angle => ‖x‖) (xiPhaseChangeAngle_sub_rgBlaschkePhaseChangeAngle I ρ)

/-- A real-valued size of phase change: the norm on `Real.Angle`.

This is the shortest-distance representative in `[-π, π]`.
-/
def xiPhaseChange (I : WhitneyInterval) : ℝ :=
  ‖xiPhaseChangeAngle I‖

/-- Any angle has norm ≤ π. In particular, `xiPhaseChange I ≤ π`. -/
lemma xiPhaseChange_le_pi (I : WhitneyInterval) : xiPhaseChange I ≤ Real.pi := by
  -- General bound: for `AddCircle p`, ‖x‖ ≤ |p|/2.
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by
    nlinarith [Real.pi_pos]
  have h := (AddCircle.norm_le_half_period (p := (2 * Real.pi)) (x := xiPhaseChangeAngle I) hp)
  have hRHS : |(2 * Real.pi : ℝ)| / 2 = Real.pi := by
    have hpos : 0 < (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
    calc
      |(2 * Real.pi : ℝ)| / 2 = (2 * Real.pi) / 2 := by simp [abs_of_pos hpos]
      _ = Real.pi := by
            -- rewrite as `π * 2 / 2`
            simpa [mul_comm] using
              (mul_div_cancel_left₀ (Real.pi) (2 : ℝ) (two_ne_zero : (2 : ℝ) ≠ 0))
  -- `xiPhaseChange I = ‖xiPhaseChangeAngle I‖`.
  simpa [xiPhaseChange, hRHS] using h

end RiemannRecognitionGeometry
