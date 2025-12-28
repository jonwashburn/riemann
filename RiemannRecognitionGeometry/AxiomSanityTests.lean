/-
Axiom sanity tests (guardrails).

These lemmas are **not** mathematical proofs of the project axioms.
They are small checks that the *statement shapes* behave sensibly on trivial inputs
(e.g. the zero function), and that the main numeric constants are compatible with
basic bounds (e.g. `xiPhaseChange ≤ π`).
-/

import RiemannRecognitionGeometry.Conjectures
import RiemannRecognitionGeometry.PoissonExtension
import Mathlib.MeasureTheory.Integral.SetIntegral

noncomputable section

open Real Complex Set MeasureTheory
open scoped BigOperators MeasureTheory

namespace RiemannRecognitionGeometry

namespace AxiomSanityTests

open RiemannRecognitionGeometry.PoissonExtension

/-! ## Poisson/Carleson sanity checks -/

lemma gradient_conjugate_poisson_zero (z : ℝ × ℝ) :
    PoissonExtension.gradient_conjugate_poisson (fun _ : ℝ => 0) z = (0, 0) := by
  simp [PoissonExtension.gradient_conjugate_poisson, PoissonExtension.conjugate_poisson_integral]

lemma carleson_energy_zero (a b : ℝ) :
    PoissonExtension.carleson_energy (fun _ : ℝ => 0) a b = 0 := by
  simp [PoissonExtension.carleson_energy, gradient_conjugate_poisson_zero]

/-- The BMO→Carleson axiom is compatible with the zero function. -/
lemma bmo_carleson_embedding_zero (a b M : ℝ) (hM_pos : M > 0) :
    PoissonExtension.carleson_energy (fun _ : ℝ => 0) a b ≤ C_FS * M ^ 2 * (b - a) := by
  -- Provide the (trivial) BMO hypothesis for `w := 0`.
  refine
    PoissonExtension.bmo_carleson_embedding (w := fun _ : ℝ => 0) (a := a) (b := b) (M := M)
      hM_pos ?_
  intro a' b' hab
  -- The left side is definitionaly `0` for the zero function.
  have : (0 : ℝ) ≤ M := le_of_lt hM_pos
  simpa using this

/-! ## Phase axiom shape checks -/

/-- Instantiating the Green-identity axiom at `C = M = K_tail` yields the uniform bound
`xiPhaseChange J ≤ U_tail`.

This is the intended “phase is controlled by the Carleson constant” consequence.
-/
lemma green_identity_gives_U_tail (hCA : ClassicalAnalysisAssumptions)
    (J : WhitneyInterval) (M : ℝ) (hM_pos : 0 < M) :
    xiPhaseChange J ≤ U_tail M := by
  have hC_pos : 0 < K_tail M := K_tail_pos hM_pos
  have h :=
    Conjectures.green_identity_axiom_statement hCA J (K_tail M) hC_pos (K_tail M) hC_pos (le_rfl)
  -- Cancel the interval-length normalization.
  have h_cancel :
      Real.sqrt (K_tail M * (2 * J.len)) * (1 / Real.sqrt (2 * J.len)) = Real.sqrt (K_tail M) := by
    have hK : 0 ≤ K_tail M := K_tail_nonneg M
    have hL : 0 < (2 * J.len) := by nlinarith [J.len_pos]
    simpa using (sqrt_energy_cancellation (K_tail M) (2 * J.len) hK hL)
  have h1 := h
  rw [mul_assoc] at h1
  rw [h_cancel] at h1
  simpa [U_tail] using h1

/-- Numeric sanity: the main upper bound `U_tail` is strictly less than `π`.

This ensures a uniform bound like `xiPhaseChange ≤ U_tail` is compatible with the universal
angle-norm bound `xiPhaseChange ≤ π`.
-/
lemma U_tail_lt_pi : U_tail C_tail < Real.pi := by
  -- `U_tail C_tail ≈ 0.71 < 0.75 < 3 < π`.
  have h_pi : 3 < Real.pi := Real.pi_gt_three
  have h_utail : U_tail C_tail < (0.75 : ℝ) := by
    -- reuse the estimate from `Basic.zero_free_condition_C_tail`
    have h_sqrt : Real.sqrt (K_tail C_tail) < (1.5 : ℝ) := by
      have h : K_tail C_tail < (1.5 : ℝ) ^ 2 := by
        unfold K_tail C_FS C_tail
        norm_num
      have h0 : (0 : ℝ) ≤ K_tail C_tail := K_tail_nonneg C_tail
      have h15 : (0 : ℝ) ≤ (1.5 : ℝ) := by norm_num
      have hs : Real.sqrt (K_tail C_tail) < Real.sqrt ((1.5 : ℝ) ^ 2) := Real.sqrt_lt_sqrt h0 h
      simpa [Real.sqrt_sq h15] using hs
    unfold U_tail
    have : (C_geom : ℝ) = (1/2 : ℝ) := by
      unfold C_geom
      norm_num
    rw [this]
    nlinarith [Real.sqrt_nonneg (K_tail C_tail), h_sqrt]
  have h075_lt_3 : (0.75 : ℝ) < 3 := by norm_num
  linarith

end AxiomSanityTests

end RiemannRecognitionGeometry
