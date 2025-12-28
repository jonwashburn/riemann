/-
Bundled assumptions used by the main theorems.

Goal: make dependencies explicit at the theorem signatures.

We separate:
- **Classical analysis assumptions** (expected true in standard analysis): e.g. Green/Cauchy–Schwarz.
- **RG-specific assumptions** (the bottleneck estimate(s) of the Recognition Geometry approach): e.g. the
  Weierstrass/Hadamard tail bound.

This file is intentionally lightweight: it packages existing statement-shapes without changing any proofs.
-/

import RiemannRecognitionGeometry.Phase
import RiemannRecognitionGeometry.DirichletEta

noncomputable section

open Real Complex Set MeasureTheory

namespace RiemannRecognitionGeometry

/-- Classical analysis assumptions used by the RG main chain. -/
structure ClassicalAnalysisAssumptions : Prop where
  /-- Green–Cauchy–Schwarz (phase change bounded by Carleson energy). -/
  green_identity_axiom_statement :
    ∀ (J : WhitneyInterval) (C : ℝ) (hC_pos : C > 0)
      (E : ℝ) (hE_pos : E > 0) (hE_le : E ≤ C),
      xiPhaseChange J ≤
        C_geom * Real.sqrt (E * (2 * J.len)) * (1 / Real.sqrt (2 * J.len))

  /-- Green–Cauchy–Schwarz for the **cofactor/unimodular boundary certificate**.

  Conceptually: if `w(t) = Arg 𝒥(1/2+it)` is the boundary phase of a unimodular analytic ratio,
  and `U = Re log 𝒥` has Carleson-box energy constant `E`, then phase changes across Whitney
  intervals are controlled by the same `C_geom` estimate.

  In our Lean development, the relevant “cofactor phase” is packaged as
  `rgCofactorPhaseAngle ρ t`, so we record the Green bound directly for its phase change.
  This is classical harmonic analysis / CR–Green bookkeeping (cf. `CPM.tex`). -/
  cofactor_green_identity_axiom_statement :
    ∀ (I : WhitneyInterval) (ρ : ℂ) (C : ℝ) (hC_pos : C > 0)
      (E : ℝ) (hE_pos : E > 0) (hE_le : E ≤ C),
      ‖rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len)‖ ≤
        C_geom * Real.sqrt (E * (2 * I.len)) * (1 / Real.sqrt (2 * I.len))

  /-- ζ(s) ≠ 0 for real `s ∈ (0, 1)`. (Used to rule out real zeros when `Im ρ = 0`.) -/
  zeta_ne_zero_of_real_in_unit_interval :
    ∀ s : ℝ, 0 < s → s < 1 → riemannZeta (s : ℂ) ≠ 0

/-- RG-specific bottleneck assumptions (not known to be true unconditionally). -/
structure RGAssumptions : Prop where
  /-- **CPM-form bottleneck** (Route 1 / boundary certificate):

  A uniform Carleson-box energy bound for the harmonic field `U = Re log 𝒥` (or equivalently,
  a uniform packing bound for the corresponding off-line zero measure).

  We record it in the minimal form needed by the RG chain:
  for each Whitney interval `I` containing `Im ρ`, the relevant Carleson-energy constant `E`
  can be taken `≤ K_tail M` for the same quantitative parameter `M` used downstream.

  The *tail phase bound* is then derived (classically) from:
  - this energy inequality, and
  - `ClassicalAnalysisAssumptions.cofactor_green_identity_axiom_statement`
    (CR–Green + Cauchy–Schwarz with the `|I|^{1/2}` cancellation).
  -/
  j_carleson_energy_axiom_statement :
    ∀ (I : WhitneyInterval) (ρ : ℂ) (M : ℝ),
      0 < M →
      completedRiemannZeta ρ = 0 → ρ.im ∈ I.interval →
      ∃ E : ℝ, E > 0 ∧ E ≤ K_tail M

/-- A single packaged hypothesis expressing “BMO/oscillation is small enough to close RG”. -/
def OscillationTarget : Prop :=
  ∃ M : ℝ, InBMOWithBound logAbsXi M ∧ M ≤ C_tail

/-- Oscillation/BMO smallness target needed to close the numeric contradiction.

This is the project’s current “unconditional bottleneck”: proving (or otherwise justifying)
that `logAbsXi` admits a *small enough* mean-oscillation bound.
-/
structure OscillationAssumptions : Prop where
  /-- There exists an explicit oscillation bound `M` with `M ≤ C_tail`. -/
  oscillationTarget : OscillationTarget

end RiemannRecognitionGeometry
