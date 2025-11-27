import Riemann.Mathlib.Analysis.Complex.DeBranges.Space
import Riemann.Mathlib.Analysis.Complex.DeBranges.ReproducingKernel.Defs
import Riemann.Mathlib.Analysis.Complex.DeBranges.Measure
import Riemann.Mathlib.Analysis.Complex.DeBranges.Zeros
import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna
import Riemann.Mathlib.Analysis.Complex.DeBranges.NevanlinnaClosure
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib
import PrimeNumberTheoremAnd
import StrongPNT

open Complex Real MeasureTheory Filter Topology Function Metric Set
open scoped Complex.ConjugateReflection BigOperators ENNReal Topology InnerProductSpace RealInnerProductSpace

variable (E : HermiteBiehlerFunction)

namespace DeBranges

/-- The de Branges–Cauchy kernel restricted to the real line, realized via the
reproducing kernel `kernel E w z` evaluated at real `t`. -/
noncomputable def kernel_Cauchy (w : ℂ) (t : ℝ) : ℂ :=
  kernel E w t

/-- Diagonal value of the Cauchy kernel on the real line `t = w ∈ ℝ`.

This is just `kernel_diag` specialized to real arguments, using that `star (w : ℂ) = w`
for real `w`. -/
lemma kernel_Cauchy_diag (x : ℝ) :
    kernel_Cauchy E x x =
      ((deriv E x) * (E#) x - (deriv (E#) x) * E x) /
        (-2 * π * Complex.I) := by
  -- `kernel_Cauchy E x x = kernel E x x`, and `kernel_diag` applies with `w := (x : ℂ)`.
  simpa [kernel_Cauchy] using
    (kernel_diag (E := E) (w := (x : ℂ)))

/-- Off-diagonal value of the Cauchy kernel on the real line `t ≠ \bar w`.

This is just `kernel_off_diag` specialized to `z := (t : ℂ)`. -/
lemma kernel_Cauchy_off_diag (w : ℂ) (t : ℝ) (ht : (t : ℂ) ≠ star w) :
    kernel_Cauchy E w t =
      kernelNum E w t / (2 * π * Complex.I * kernelDen w t) := by
  -- `kernel_Cauchy E w t = kernel E w t`, and `kernel_off_diag` applies with `z := (t : ℂ)`.
  simpa [kernel_Cauchy] using
    (kernel_off_diag (E := E) (w := w) (z := (t : ℂ)) ht)

/-- Uniqueness principle for de Branges–admissible functions:

If `f` is de Branges–admissible (analytic on the upper half-plane, of bounded type,
and of non-positive mean type), and its boundary values on `ℝ` vanish almost
everywhere with respect to the de Branges measure `E.measure`, then `f` vanishes
identically on `ℂ`.

The analytic input (Nevanlinna / Poisson theory) is still deferred as a TODO. -/
theorem admissible_zero_of_boundary_zero
    (f : ℂ → ℂ)
    (hf : IsDeBrangesAdmissible f)
    (hbdry :
      (fun t : ℝ => f t) =ᵐ[E.measure] fun _ : ℝ => (0 : ℂ)) :
    ∀ z : ℂ, f z = 0 := by
  classical

  -- Step 0: move the boundary a.e. condition from `E.measure` to Lebesgue measure.
  have hbdry_lebesgue :
      (fun t : ℝ => f t) =ᵐ[(volume : Measure ℝ)] fun _ : ℝ => (0 : ℂ) := by
    -- First see `hbdry` as an a.e. equality w.r.t. `volume.withDensity E.density`.
    have hbdry' :
        (fun t : ℝ => f t) =ᵐ[(volume : Measure ℝ).withDensity E.density]
          fun _ : ℝ => (0 : ℂ) := by
      simpa [HermiteBiehlerFunction.measure] using hbdry
    -- The density is a.e. positive, so `volume` and `volume.withDensity E.density`
    -- have the same a.e. equalities (by `withDensity_ae_eq`).
    have hdens_aemeas :
        AEMeasurable E.density (volume : Measure ℝ) :=
      (HermiteBiehlerFunction.measurable_density (E := E)).aemeasurable
    have hdens_pos :
        ∀ᵐ x ∂(volume : Measure ℝ), E.density x ≠ 0 := by
      -- Pointwise: `E.density x = ENNReal.ofReal (E.weight x)` and `E.weight x > 0`.
      have hpos_point : ∀ x : ℝ, E.density x ≠ 0 := by
        intro x
        have hpos : 0 < E.weight x :=
          HermiteBiehlerFunction.weight_pos (E := E) x
        have hOfReal :
            ENNReal.ofReal (E.weight x) ≠ 0 :=
          (ENNReal.ofReal_ne_zero_iff (r := E.weight x)).2 hpos
        simpa [HermiteBiehlerFunction.density] using hOfReal
      exact Filter.Eventually.of_forall hpos_point
    -- Transfer a.e. equality from `volume.withDensity E.density` to `volume`.
    exact
      (MeasureTheory.withDensity_ae_eq
        (μ := (volume : Measure ℝ))
        (d := E.density)
        (f := fun t : ℝ => f t)
        (g := fun _ : ℝ => (0 : ℂ))
        hdens_aemeas hdens_pos).1 hbdry'

  -- Now we know the boundary values of `f` vanish Lebesgue-a.e. on `ℝ`.
  have h_ae_zero_vol :
      ∀ᵐ t : ℝ ∂(volume : Measure ℝ), f t = 0 := by
    simpa using hbdry_lebesgue

  -- Step 1: the exceptional boundary set `{t ∈ ℝ | f(t) ≠ 0}` has Lebesgue measure zero.
  have h_zero_set_vol :
      (volume : Measure ℝ) {t : ℝ | f t ≠ 0} = 0 := by
    -- Translate `∀ᵐ t, f t = 0` into a statement about the measure
    -- of the complement of `{t | f t = 0}`.
    have := (MeasureTheory.ae_iff (μ := (volume : Measure ℝ))
      (p := fun t : ℝ => f t = 0)).1 h_ae_zero_vol
    -- `{t | ¬ (f t = 0)} = {t | f t ≠ 0}`.
    simpa [Classical.not_not] using this

  -- TODO (analytic core): use admissibility + boundary vanishing on a Lebesgue-null set
  -- to show `f ≡ 0` in the upper half-plane, then extend to all of `ℂ`.
  /- Analytic step (Nevanlinna / Poisson, to be implemented later):

     * Combine `hf.analytic_on_UHP`, `hf.is_bounded_type`, `hf.mean_type_nonpos`
       with the Lebesgue-a.e. boundary condition (encoded equivalently by
       `h_zero_set_vol`).
     * Use Nevanlinna/Poisson representation to deduce that `f` vanishes
       identically on the upper half-plane.
     * Then extend this vanishing to all of `ℂ` via the appropriate
       de Branges reflection/continuation principle.
  -/
  sorry

/-- Global Cauchy representation: we package the defect function and reduce to
proving that it vanishes identically. This is where the full de Branges
analysis (Thm. 11/19) will live. -/
theorem cauchy_representation_global (F : Space E) :
    ∀ z : ℂ, F z = ∫ t, kernel_Cauchy E z t * F t ∂E.measure := by
  classical
  -- Define the defect function `H(z) := F(z) - ∫ K(z,t) F(t) dμ_E(t)`.
  let H : ℂ → ℂ :=
    fun z => F z - ∫ t, kernel_Cauchy E z t * F t ∂E.measure

  -- Step 1 (to be proved later): `H` is entire in `z`.
  have h_entire : Differentiable ℂ H := by
    -- `F` is entire as an element of the de Branges space `B(E)`.
    have hF_entire : Differentiable ℂ F :=
      Space.entire (E := E) F
    -- The integral term should also be entire in `z`, by differentiating under
    -- the integral sign using the analyticity of the kernel and appropriate
    -- dominated-convergence / Nevanlinna bounds.
    have hI_entire :
        Differentiable ℂ fun z : ℂ =>
          ∫ t, kernel_Cauchy E z t * F t ∂E.measure := by
      /- TODO (analytic core):
         * For each fixed `t : ℝ`, use `kernel_entire (E := E) (w := z)` to see that
           `z ↦ kernel_Cauchy E z t` is entire on `ℂ`.
         * Show there is an integrable dominating function (in `t`) for the
           derivatives on suitable neighbourhoods in `z`, using the admissibility
           of `F/E`, `F#/E` and growth bounds from de Branges / Nevanlinna theory.
         * Apply a differentiation-under-the-integral theorem to conclude that
           `z ↦ ∫ kernel_Cauchy E z t * F t dμ_E(t)` is entire.
      -/
      sorry
    -- `H z = F z - ∫ K(z,t) F(t) dμ_E(t)`, so `H` is the difference of two entire functions.
    simpa [H] using hF_entire.sub hI_entire

  -- Step 2 (to be proved later): an admissibility estimate for `H/E`
  -- in the upper half-plane, using admissibility of `F/E` and `F#/E`.
  have h_admissible :
      IsDeBrangesAdmissible
        (fun z : ℂ => H z / E z) := by
    -- Decompose `H/E` as the difference of two quotients.
    let f1 : ℂ → ℂ := fun z => F z / E z
    let f2 : ℂ → ℂ := fun z =>
      (∫ t, kernel_Cauchy E z t * F t ∂E.measure) / E z

    -- First quotient `F/E` is admissible by the defining property of `Space E`.
    have h_f1 : IsDeBrangesAdmissible f1 :=
      DeBranges.Space.admissible_F_over_E (E := E) F

    -- Second quotient: analytic core (Cauchy integral term divided by `E`).
    have h_f2 : IsDeBrangesAdmissible f2 := by
      /- TODO (analytic core):
         * Use admissibility of `F/E` and `F#/E` together with
           Nevanlinna/Poisson estimates for the kernel slices
           `z ↦ kernel_Cauchy E z t` to show that
           `z ↦ (∫ kernel_Cauchy E z t * F t dμ_E(t)) / E z`
           satisfies the de Branges admissibility conditions.
      -/
      sorry

    -- Use closure of admissibility under subtraction.
    have h_sub :
        IsDeBrangesAdmissible (fun z : ℂ => f1 z - f2 z) :=
      Complex.IsDeBrangesAdmissible.sub h_f1 h_f2

    -- Rewrite `H/E` in terms of `f1` and `f2`.
    simpa [H, f1, f2, sub_eq_add_neg, div_eq_mul_inv, mul_add, add_mul,
           add_comm, add_left_comm, add_assoc,
           mul_comm, mul_left_comm, mul_assoc] using h_sub

  -- Step 3 (to be proved later): boundary values of `H/E` vanish a.e. on `ℝ`.
  have h_boundary_zero :
      (fun t : ℝ => H t / E t) =ᵐ[E.measure] fun _ => (0 : ℂ) := by
    /- TODO:
       * identify non-tangential boundary values of `H/E` on `ℝ`,
       * use the Cauchy / Poisson integral representation and the fact that the
         kernel is tuned to cancel `F` on the boundary.
    -/
    sorry

  -- Step 4: use the uniqueness principle for admissible functions.
  -- An admissible function with zero boundary values is identically zero.
  have h_zero : ∀ z : ℂ, H z = 0 := by
    -- Apply `admissible_zero_of_boundary_zero` to `f := H/E`.
    have h_flat : ∀ z : ℂ, H z / E z = 0 :=
      admissible_zero_of_boundary_zero (E := E)
        (f := fun z => H z / E z) h_admissible h_boundary_zero
    intro z
    by_cases hzE : E z = 0
    ·
      /- TODO: handle the case `E z = 0` using analyticity of `H` and
         the zero set of `E` (removable singularity argument). -/
      sorry
    ·
      -- If `E z ≠ 0`, then from `H z / E z = 0` we get `H z = 0`.
      have hz_div := h_flat z
      -- From `H z / E z = 0` and `E z ≠ 0`, deduce `H z = 0`.
      field_simp [hzE] at hz_div
      simp only [mul_zero, hz_div]

  -- Step 5: conclude the representation from `H ≡ 0`.
  intro z
  have hz : H z = 0 := h_zero z
  -- Unfold `H z = 0` and solve `F z = ∫ K(z,t) F(t) dμ_E` from `F z - ∫ … = 0`.
  unfold H at hz
  exact sub_eq_zero.mp hz

/-- **Cauchy representation for de Branges spaces**: pointwise version,
specialized from the global statement. -/
theorem cauchy_representation (F : Space E) (w : ℂ) :
    F w = ∫ t, kernel_Cauchy E w t * F t ∂E.measure :=
  cauchy_representation_global (E := E) F w

/-- Real-line version of the Cauchy representation, useful for boundary arguments. -/
lemma cauchy_representation_real (F : Space E) (x : ℝ) :
    F x = ∫ t, kernel_Cauchy E x t * F t ∂E.measure := by
  -- Just view `x : ℝ` as a complex number and apply the global result.
  simpa using
    (cauchy_representation (E := E) F (w := (x : ℂ)))

end DeBranges
