/-
Central registry for project-level conjectural / axiomatized results.

Goal: keep the “hard classical analysis” assumptions in one place so they are easy
to audit and (eventually) discharge.
-/

import RiemannRecognitionGeometry.Assumptions

noncomputable section

open Real Complex Set MeasureTheory

namespace RiemannRecognitionGeometry

namespace Conjectures

/-- **THEOREM (assumption wrapper)**: Phase change bounded by Carleson energy.

See `RiemannRecognitionGeometry/Axioms.lean` for the full mathematical discussion.
This bound is expected to be true in standard harmonic analysis, but is not yet
fully formalized in Mathlib.
-/
theorem green_identity_axiom_statement
    (hCA : ClassicalAnalysisAssumptions)
    (J : WhitneyInterval) (C : ℝ) (hC_pos : C > 0)
    (E : ℝ) (hE_pos : E > 0) (hE_le : E ≤ C) :
    xiPhaseChange J ≤
      C_geom * Real.sqrt (E * (2 * J.len)) * (1 / Real.sqrt (2 * J.len)) :=
  hCA.green_identity_axiom_statement J C hC_pos E hE_pos hE_le

/-- **THEOREM (assumption wrapper)**: The tail contribution to phase is bounded by `U_tail`.

See `RiemannRecognitionGeometry/Axioms.lean` for the full mathematical discussion.
This is the RG-specific bottleneck estimate.
-/
theorem weierstrass_tail_bound_axiom_statement
    (hCA : ClassicalAnalysisAssumptions)
    (hRG : RGAssumptions)
    (I : WhitneyInterval) (ρ : ℂ) (M : ℝ) (hM_pos : 0 < M)
    (hρ_zero : completedRiemannZeta ρ = 0) (hρ_im : ρ.im ∈ I.interval) :
    let d : ℝ := ρ.re - 1/2
    let y_hi : ℝ := I.t0 + I.len - ρ.im
    let y_lo : ℝ := I.t0 - I.len - ρ.im
    let blaschke := Real.arctan (y_lo / d) - Real.arctan (y_hi / d)
    ‖xiPhaseChangeAngle I - (blaschke : Real.Angle)‖ ≤ U_tail M := by
  intro d y_hi y_lo blaschke

  -- 1) Reduce the “Weierstrass tail angle” to the cofactor phase change.
  have h_reduce :
      ‖xiPhaseChangeAngle I - (blaschke : Real.Angle)‖ =
        ‖rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len)‖ := by
    -- `blaschke` is definitionally the real Blaschke phase change.
    have : (blaschke : Real.Angle) = rgBlaschkePhaseChangeAngle I ρ := by
      -- Expand both sides to the same `arctan` expression.
      simp [rgBlaschkePhaseChangeAngle, rgBlaschkePhaseChange, rgBlaschkePhase, d, y_hi, y_lo, blaschke]
    -- Now apply the algebraic reduction lemma from `Phase.lean`.
    simpa [this] using (norm_xiPhaseChangeAngle_sub_rgBlaschkePhaseChangeAngle I ρ)

  -- 2) Get an energy constant `E ≤ K_tail M` from the RG bottleneck assumption.
  obtain ⟨E, hE_pos, hE_le⟩ :=
    hRG.j_carleson_energy_axiom_statement I ρ M hM_pos hρ_zero hρ_im

  have hK_pos : (K_tail M) > 0 := K_tail_pos hM_pos

  -- 3) Green/CR bound for the cofactor phase in terms of `E`.
  have h_green :
      ‖rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len)‖ ≤
        C_geom * Real.sqrt (E * (2 * I.len)) * (1 / Real.sqrt (2 * I.len)) :=
    hCA.cofactor_green_identity_axiom_statement I ρ (K_tail M) hK_pos E hE_pos hE_le

  -- 4) Cancel the interval-length factor and bound `√E ≤ √(K_tail M)`.
  have h_cancel :
      Real.sqrt (E * (2 * I.len)) * (1 / Real.sqrt (2 * I.len)) = Real.sqrt E := by
    have hE_nonneg : 0 ≤ E := le_of_lt hE_pos
    have hL_pos : 0 < (2 * I.len) := by nlinarith [I.len_pos]
    simpa using (sqrt_energy_cancellation E (2 * I.len) hE_nonneg hL_pos)

  have h_green' : ‖rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len)‖ ≤
      C_geom * Real.sqrt E := by
    have h := h_green
    -- reassociate to rewrite the cancellation factor
    rw [mul_assoc] at h
    rw [h_cancel] at h
    exact h

  have h_sqrt : Real.sqrt E ≤ Real.sqrt (K_tail M) := Real.sqrt_le_sqrt hE_le

  have h_bound : C_geom * Real.sqrt E ≤ U_tail M := by
    unfold U_tail
    exact mul_le_mul_of_nonneg_left h_sqrt (le_of_lt C_geom_pos)

  -- 5) Conclude.
  have h_cofactor : ‖rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len)‖ ≤
      U_tail M :=
    le_trans h_green' h_bound

  -- Transport across the algebraic reduction.
  simpa [h_reduce] using h_cofactor

/-- **THEOREM (assumption wrapper)**: packaged small-oscillation target for `logAbsXi`. -/
theorem oscillationTarget (hOsc : OscillationAssumptions) :
    ∃ M : ℝ, InBMOWithBound logAbsXi M ∧ M ≤ C_tail :=
  hOsc.oscillationTarget

end Conjectures

end RiemannRecognitionGeometry
