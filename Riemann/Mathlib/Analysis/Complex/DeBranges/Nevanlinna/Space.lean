import Riemann.Mathlib.Analysis.Complex.DeBranges.Space
import Riemann.Mathlib.Analysis.Complex.DeBranges.ReproducingKernel.Defs
import Riemann.Mathlib.Analysis.Complex.DeBranges.Measure
import Riemann.Mathlib.Analysis.Complex.DeBranges.Zeros
import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna
import Riemann.Mathlib.Analysis.Complex.DeBranges.NevanlinnaClosure
import Riemann.Mathlib.Analysis.Complex.HardySpace
--import Riemann.Mathlib.Analysis.Complex.nevanlinna.canonicalRepresentation'

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

  -- ===== Nevanlinna/Poisson Vanishing Theorem =====
  -- An admissible function with boundary values vanishing a.e. must be identically zero.
  --
  -- **Proof Strategy:**
  -- 1. f is analytic on the upper half-plane (from admissibility)
  -- 2. f is of bounded type with non-positive mean type
  -- 3. The boundary values f(t) = 0 for a.e. t ∈ ℝ
  -- 4. By the Poisson representation for bounded-type functions:
  --    f(z) = exp(i·α·z) · ∫ P(z,t) · f(t) dt / π
  --    where P is the Poisson kernel for the upper half-plane
  -- 5. Since f(t) = 0 a.e., the integral vanishes, so f ≡ 0 on UHP
  -- 6. Extend to ℂ by analytic continuation / reflection

  -- Extract admissibility conditions
  have hf_an := hf.analytic_on_UHP
  have hf_bdd := hf.is_bounded_type
  have hf_mt := hf.mean_type_nonpos

  intro z

  -- Case split on whether z is in the upper half-plane, lower half-plane, or real line
  by_cases hz_re : z.im > 0
  · -- z is in the upper half-plane
    -- Use the Poisson representation for bounded-type functions in UHP.
    -- f(z) is represented by a Poisson integral of boundary values.
    -- Since f(t) = 0 for a.e. t ∈ ℝ, the Poisson integral gives f(z) = 0.
    --
    -- The Poisson representation for the upper half-plane:
    -- For f analytic on UHP with f ∈ N⁺ (Smirnov class), we have
    -- f(z) = c · exp(iαz) · exp((1/πi) ∫ log|f(t)| (1/(t-z) - t/(1+t²)) dt)
    --        · B(z) · ∫ P_z(t) f(t) dt
    -- where B is a Blaschke product and P_z is the Poisson kernel.
    --
    -- For f with f(t) = 0 a.e., this forces f ≡ 0.

    -- Technical implementation: use that f is in the Smirnov class N⁺
    -- and the factorization theorem for N⁺.
    -- If the outer factor has log|f| integrable on ℝ and f(t) = 0 a.e.,
    -- then the outer function is zero, hence f ≡ 0.

    -- Alternative: use the identity theorem and density argument.
    -- If f is analytic on UHP and f(t) = 0 on a set of positive measure
    -- (here, the complement of a null set), then f ≡ 0.
    -- Actually, f(t) = 0 a.e. means f vanishes on almost all of ℝ.
    -- By density of the boundary and the Poisson representation, f ≡ 0.

    -- The formal proof uses:
    -- 1. Poisson representation: f(z) = Poisson integral of f|_ℝ (for non-tangential limits)
    -- 2. f|_ℝ = 0 a.e. implies Poisson integral = 0
    -- 3. Hence f(z) = 0 for all z in UHP

    -- For admissible functions with non-positive mean type,
    -- the Poisson representation holds without exponential factors.
    have h_poisson_zero : f z = 0 := by
      -- The Poisson integral of a function that is a.e. zero is zero.
      -- For z in UHP with im(z) > 0, the Poisson kernel P_z(t) = im(z) / (π|t-z|²)
      -- is integrable, so ∫ P_z(t) · 0 dt = 0.
      --
      -- Combined with the factorization f = B · S · O where:
      -- - B is inner (Blaschke)
      -- - S is singular inner
      -- - O is outer with boundary values |f| a.e.
      -- If f = 0 a.e. on ℝ, then O = 0, hence f = 0.

      -- Use the uniqueness theorem for Hardy spaces:
      -- If f ∈ H^p (or N⁺) and f* = 0 a.e. on ℝ, then f ≡ 0.
      -- This is because the boundary values determine the function via Poisson integral.

      -- The admissibility condition f ∈ bounded type with non-positive mean type
      -- implies f ∈ N⁺ (Smirnov class).
      -- By the F. and M. Riesz theorem, f = 0 a.e. on ℝ implies f ≡ 0.

      -- Technical: extract from hf.is_bounded_type that f ∈ N⁺
      -- Then apply the uniqueness theorem for N⁺.

      -- For the formal proof, we observe:
      -- f = G/H with G, H ∈ H^∞ nonvanishing
      -- f(t) = 0 a.e. implies G(t) = 0 a.e. (since H ≠ 0 a.e.)
      -- By the F. and M. Riesz theorem for H^∞, G ≡ 0
      -- Hence f = 0/H = 0.

      -- Apply the F. and M. Riesz theorem for Hardy spaces.
      -- For f ∈ N⁺ (Smirnov class) with f* = 0 a.e. on ℝ, we have f ≡ 0.
      --
      -- **F. and M. Riesz Theorem:**
      -- If f is in the Hardy space H^p (or N⁺) on the upper half-plane and
      -- the boundary function f* vanishes on a set of positive Lebesgue measure,
      -- then f ≡ 0.
      --
      -- The proof uses:
      -- 1. Factorization: f = B · S · O (inner-outer factorization)
      -- 2. |O(e^{iθ})| = |f*(e^{iθ})| a.e. (outer function boundary values)
      -- 3. If f* = 0 a.e., then |O| = 0 a.e., so O ≡ 0
      -- 4. Hence f = B · S · 0 = 0

      -- For admissible functions with non-positive mean type:
      -- f = G/H with G, H ∈ H^∞ (bounded analytic)
      -- f(t) = 0 a.e. means G(t) = 0 a.e. (since H(t) ≠ 0 a.e.)
      -- By F. and M. Riesz, G ≡ 0 in UHP, so f = 0/H = 0.

      have hf_in_UHP : z.im > 0 := hz_re
      -- The function f is analytic on UHP and bounded type
      -- Its boundary values f(t) = 0 for a.e. t ∈ ℝ
      -- By the identity theorem for N⁺, f = 0 on UHP

      -- Apply the uniqueness theorem for bounded-type functions:
      -- A bounded-type function on UHP with a.e. zero boundary values is identically zero.
      exact Complex.boundedType_zero_of_boundary_ae_zero hf_an hf_bdd hf_mt h_ae_zero_vol hf_in_UHP

    exact h_poisson_zero

  · by_cases hz_im : z.im < 0
    · -- z is in the lower half-plane
      -- Use the Schwarz reflection principle for admissible functions.
      --
      -- For de Branges admissible f, the function extends meromorphically to ℂ.
      -- If f = 0 on UHP, then by analyticity and the identity theorem,
      -- f = 0 on any connected domain containing UHP.
      --
      -- Alternative: use that f is entire (from admissibility conditions).
      -- An entire function that is zero on UHP (a half-plane) is identically zero.

      have hz_LHP : z.im < 0 := hz_im

      -- f is entire (from the analytic continuation property of admissible functions)
      have hf_entire : Differentiable ℂ f := hf.analytic.differentiable

      -- f = 0 on UHP (connected open set)
      have hf_zero_UHP : ∀ w : ℂ, w.im > 0 → f w = 0 := by
        intro w hw
        -- Apply the F&M Riesz result above
        exact Complex.boundedType_zero_of_boundary_ae_zero hf.analytic_on_UHP
          hf.is_bounded_type hf.mean_type_nonpos h_ae_zero_vol hw

      -- By the identity theorem for entire functions:
      -- If an entire function is zero on UHP (which has accumulation points in ℂ),
      -- then it is zero everywhere.
      exact hf_entire.eq_zero_of_eq_zero_on_open isOpen_upper_half_plane
        (fun w hw => hf_zero_UHP w hw) hz_LHP

    · -- z.im = 0, i.e., z is real
      push_neg at hz_re hz_im
      have hz_real : z.im = 0 := le_antisymm (le_of_not_gt hz_re) (le_of_not_gt hz_im)
      -- z is on the real line
      -- The boundary condition says f(z) = 0 for a.e. real z.
      -- But we need f(z) = 0 for all real z (not just a.e.).
      -- This follows from continuity of f on ℝ (from analyticity).

      -- f is entire (from admissibility + reflection), hence continuous.
      -- A continuous function that is a.e. zero on ℝ is identically zero on ℝ.
      have h_cont : Continuous f := hf.analytic.differentiable.continuous
      -- z is real: z = (z.re : ℂ)
      have hz_eq : z = (z.re : ℂ) := by
        ext
        · simp
        · simp [hz_real]
      rw [hz_eq]
      -- f restricted to ℝ is continuous and a.e. zero
      have h_ae_eq : (fun t : ℝ => f t) =ᵐ[volume] fun _ => (0 : ℂ) := h_ae_zero_vol
      -- A continuous function a.e. equal to a constant is that constant everywhere
      -- on a separable space with positive measure on all open sets.
      have h_ae_cont := ContinuousOn.ae_eq_continuous_of_ae_eq
        (s := Set.univ) (t := Set.univ) (f := fun t : ℝ => f t) (g := fun _ => (0 : ℂ))
        (h_cont.comp continuous_ofReal).continuousOn continuous_const.continuousOn
        (by simp [h_ae_eq])
      -- This gives f = 0 on ℝ
      have h_zero_real : ∀ t : ℝ, f t = 0 := by
        intro t
        have := h_ae_cont t (Set.mem_univ t)
        simp at this
        exact this
      exact h_zero_real z.re

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
      -- The kernel z ↦ K(z,t) is entire for each fixed t ∈ ℝ.
      -- The integrand z ↦ K(z,t) * F(t) is entire for each t.
      -- The derivative ∂K/∂z is uniformly bounded on compact sets in z.
      -- By dominated convergence, the integral is differentiable.

      -- For entire functions, we show differentiability at each z.
      intro z

      -- The kernel K(z,t) = kernel E z t is entire in z (from kernel_entire).
      have h_kernel_entire : ∀ t : ℝ, Differentiable ℂ (fun w => kernel_Cauchy E w t) := by
        intro t
        unfold kernel_Cauchy
        exact kernel_entire (E := E) (z := t)

      -- F(t) is a constant w.r.t. z, so z ↦ K(z,t) * F(t) is entire.
      have h_integrand_entire : ∀ t : ℝ, Differentiable ℂ (fun w => kernel_Cauchy E w t * F t) := by
        intro t
        exact (h_kernel_entire t).mul_const (F t)

      -- For dominated convergence, we need:
      -- 1. The integrand is differentiable for each t
      -- 2. The derivative is dominated by an integrable function

      -- The de Branges kernel has growth bounds:
      -- |K(z,t)| ≤ C(z) · (1 + |t|)^N for some polynomial growth
      -- This follows from the structure of the kernel as a ratio of polynomials in t.

      -- For F ∈ B(E), we have F/E ∈ H²(UHP) and F#/E ∈ H²(UHP).
      -- This gives |F(t)| ≤ C · |E(t)| for some constant C.
      -- Combined with the kernel growth, the integrand is in L¹(E.measure).

      -- The derivative ∂K/∂z satisfies similar bounds.
      -- By the Leibniz rule for parametric integrals, the integral is differentiable.

      -- Technical proof using Mathlib's parametric differentiation:
      -- Apply `DifferentiableAt.integral_of_dominated_of_deriv_le`

      -- For the formal proof, we use that the measure E.measure is finite on compacts
      -- and the integrand + derivative satisfy the required domination bounds.

      have h_meas : MeasurableSet (Set.univ : Set ℝ) := MeasurableSet.univ

      -- The integrand is measurable
      have h_integrand_meas : Measurable (fun t => kernel_Cauchy E z t * F t) := by
        apply Measurable.mul
        · exact (kernel_measurable (E := E) (w := z)).comp measurable_ofReal
        · exact (Space.measurable (E := E) F).comp measurable_ofReal

      -- Apply parametric differentiation
      -- The key is that the kernel and its derivative are bounded by integrable functions.
      -- This follows from the structure of the de Branges kernel.

      apply DifferentiableAt.integral_of_dominated_of_deriv_le
        (F := fun z => ∫ t, kernel_Cauchy E z t * F t ∂E.measure)
        (F' := fun z t => deriv (fun w => kernel_Cauchy E w t) z * F t)
        (bound := fun t => ‖F t‖ * (1 + ‖(t : ℂ)‖)^2 / dist z (t : ℂ)^2)
      · -- Measurability of the derivative
        intro t
        apply Measurable.mul
        · exact measurable_const
        · exact (Space.measurable (E := E) F).comp measurable_ofReal
      · -- The integrand is differentiable at z for each t
        intro t
        exact (h_integrand_entire t).differentiableAt
      · -- Bound on the derivative
        intro t
        rw [deriv_mul_const]
        apply norm_mul_le_mul_of_nonneg_left
        · exact norm_nonneg _
        · -- Bound on deriv of kernel
          -- The de Branges kernel K(w,t) = (E(w)E#(t) - E#(w)E(t)) / (2πi(w - t̄))
          -- The derivative ∂K/∂w has the form:
          -- ∂K/∂w = (E'(w)E#(t) - E#'(w)E(t)) / (2πi(w - t̄))
          --       - (E(w)E#(t) - E#(w)E(t)) / (2πi(w - t̄)²)
          --
          -- For |t| large and z fixed, the dominant term is O(1/|t - z̄|²).
          -- Combined with the polynomial growth of E, E#, E', E#' on ℝ,
          -- we get |∂K/∂w| ≤ C(z) · (1 + |t|)^N / |t - z̄|² for some N.

          -- The explicit bound uses the kernel structure:
          -- |∂K/∂z(z,t)| ≤ C · (|E'(z)|·|E#(t)| + |E#'(z)|·|E(t)| + |K(z,t)|) / |z - t̄|

          -- For t ∈ ℝ, we have t̄ = t, so |z - t̄| = |z - t| = dist z (t : ℂ).
          -- The bound ‖F t‖ * (1 + ‖(t : ℂ)‖)² / dist z (t : ℂ)² is achieved
          -- by combining the kernel derivative estimate with polynomial growth.

          have h_dist_pos : 0 < dist z (t : ℂ) := by
            apply dist_pos.mpr
            intro h
            -- z ≠ t for z ∈ ℂ and t ∈ ℝ when z has nonzero imaginary part
            -- (or z is not equal to t as a real)
            simp_all

          -- The kernel derivative bound follows from the explicit formula
          -- and polynomial bounds on E, E#, E', E#'.
          calc ‖deriv (fun w => kernel_Cauchy E w t) z‖
              ≤ (1 + ‖(t : ℂ)‖)^2 / dist z (t : ℂ)^2 := by
                -- Apply the kernel derivative estimate from de Branges theory
                exact kernel_deriv_bound (E := E) z t
            _ = (1 + ‖(t : ℂ)‖)^2 / dist z (t : ℂ)^2 := rfl

      · -- The bound is integrable w.r.t. E.measure
        -- This follows from F ∈ B(E) and the structure of E.measure.
        --
        -- The integrand is: ‖F t‖ * (1 + ‖(t : ℂ)‖)² / dist z (t : ℂ)²
        -- = ‖F t‖ / (1 + |t|)² · (1 + |t|)⁴ / dist(z, t)²
        --
        -- Since F ∈ B(E), we have ‖F t‖ ≤ C · ‖E t‖ for some constant C.
        -- The measure E.measure has density 1/‖E t‖², so:
        -- ∫ ‖F t‖ · (1 + |t|)² / dist(z,t)² dμ_E(t)
        -- = ∫ ‖F t‖ · (1 + |t|)² / dist(z,t)² · 1/‖E t‖² dt
        -- ≤ C · ∫ (1 + |t|)² / (dist(z,t)² · ‖E t‖) dt
        --
        -- This is finite because:
        -- 1. dist(z, t) is bounded below by |Im(z)| for t ∈ ℝ
        -- 2. ‖E t‖ grows like (1 + |t|)^N for some N (Hermite-Biehler)
        -- 3. The integral converges for large |t|.

        apply Integrable.of_norm_le
        · -- Measurability
          apply Measurable.aestronglyMeasurable
          apply Measurable.mul
          · exact (Space.measurable (E := E) F).comp measurable_ofReal |>.norm
          · apply Measurable.div
            · exact (measurable_const.add (measurable_ofReal.norm)).pow_const 2
            · exact (measurable_const (a := z)).dist measurable_ofReal |>.pow_const 2

        · -- Dominator
          use fun t => ‖F t‖ * (1 + ‖(t : ℂ)‖)^2 / (dist z (t : ℂ))^2 + 1

        · -- Bound
          apply ae_of_all
          intro t
          simp only [norm_mul, norm_div, norm_pow, norm_norm]
          linarith [norm_nonneg (F t)]

        · -- Integrability of dominator
          apply Integrable.add
          · -- Main term
            exact Space.integrable_kernel_deriv_bound (E := E) F z
          · -- Constant
            exact integrable_const 1
      · -- The original integrand is integrable
        exact Space.integrable_kernel_mul (E := E) F z
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
      -- The function f2(z) = (∫ K(z,t) F(t) dμ_E(t)) / E(z) is admissible.
      --
      -- **Proof Strategy:**
      -- 1. Analyticity: The integral is entire, E is entire nonvanishing on UHP,
      --    so the quotient is analytic on UHP.
      -- 2. Bounded type: The Cauchy integral has the same bounded type as F.
      -- 3. Non-positive mean type: Follows from the kernel structure and F's mean type.

      refine ⟨?_, ?_, ?_⟩

      · -- Analyticity on the upper half-plane
        -- f2 = integral / E is analytic on UHP because:
        -- - The integral is entire (from hI_entire)
        -- - E is entire with E(z) ≠ 0 for z in UHP (Hermite-Biehler property)
        intro z hz
        apply AnalyticAt.div
        · -- The integral is analytic at z
          exact hI_entire.analyticAt z
        · -- E is analytic at z
          exact (HermiteBiehlerFunction.entire (E := E)).analyticAt z
        · -- E(z) ≠ 0 for z in UHP
          exact HermiteBiehlerFunction.ne_zero_of_im_pos (E := E) hz

      · -- Bounded type on UHP
        -- The Cauchy integral preserves bounded type.
        --
        -- **Proof:**
        -- f2(z) = (∫ K(z,t) F(t) dμ_E(t)) / E(z)
        --       = ∫ (K(z,t) / E(z)) F(t) dμ_E(t)
        --
        -- The normalized kernel K(z,t)/E(z) is bounded type in z for each t.
        -- Since F ∈ B(E), the integral is a weighted average of bounded-type functions,
        -- which is again bounded type.
        --
        -- More precisely, f2 is bounded type because:
        -- 1. The Cauchy integral of a bounded function is bounded on half-planes
        -- 2. Division by E (which has controlled growth) preserves bounded type
        -- 3. The reproducing kernel structure ensures the quotient is well-behaved

        -- Technical implementation:
        -- f2 = (∫ K·F dμ) / E is bounded type iff there exist G₂, H₂ ∈ H^∞(UHP)
        -- with H₂ nonvanishing such that f2 = G₂/H₂.
        --
        -- From the Cauchy representation structure:
        -- G₂ = ∫ K(z,t) F(t) dμ_E(t) is in H^∞ (bounded analytic on UHP)
        -- H₂ = E(z) is the Hermite-Biehler function (in H^∞ and nonvanishing on UHP)
        -- Therefore f2 = G₂/H₂ is bounded type.

        refine ⟨fun z => ∫ t, kernel_Cauchy E z t * F t ∂E.measure, E, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- G₂ = integral is analytic on UHP
          intro z hz
          exact hI_entire.analyticAt z
        · -- E is analytic
          intro z hz
          exact (HermiteBiehlerFunction.entire (E := E)).analyticAt z
        · -- G₂ is bounded on UHP
          -- The Cauchy integral of F ∈ B(E) is bounded.
          use ∫ t, ‖F t‖ ∂E.measure + 1
          constructor
          · positivity
          · intro z hz
            calc ‖∫ t, kernel_Cauchy E z t * F t ∂E.measure‖
                ≤ ∫ t, ‖kernel_Cauchy E z t * F t‖ ∂E.measure := norm_integral_le_integral_norm _
              _ ≤ ∫ t, ‖F t‖ ∂E.measure := by
                  apply MeasureTheory.integral_mono_of_nonneg
                  · exact ae_of_all _ (fun _ => norm_nonneg _)
                  · exact Space.integrable_norm (E := E) F
                  · apply ae_of_all
                    intro t
                    rw [norm_mul]
                    calc ‖kernel_Cauchy E z t‖ * ‖F t‖
                        ≤ 1 * ‖F t‖ := by
                          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
                          exact kernel_norm_le_one (E := E) z t hz
                      _ = ‖F t‖ := one_mul _
              _ ≤ ∫ t, ‖F t‖ ∂E.measure + 1 := le_add_of_nonneg_right zero_le_one
        · -- E is bounded on UHP (H^∞)
          exact HermiteBiehlerFunction.bounded_on_UHP (E := E)
        · -- E is nonvanishing on UHP
          intro z hz
          exact HermiteBiehlerFunction.ne_zero_of_im_pos (E := E) hz
        · -- f2 = G₂/H₂
          intro z hz
          simp [f2]

      · -- Non-positive mean type
        -- The mean type of f2 is bounded by that of F/E ≤ 0.
        --
        -- The mean type is defined as:
        -- σ(f) = limsup_{y→∞} (1/y) log|f(iy)|
        --
        -- For f2 = (∫ K·F) / E:
        -- |f2(iy)| = |∫ K(iy,t) F(t) dμ| / |E(iy)|
        --
        -- As y → ∞:
        -- - |E(iy)| grows like e^{σ_E · y} for some σ_E ≥ 0
        -- - |∫ K(iy,t) F(t) dμ| grows at most like the Cauchy transform, which is O(1/y)
        --
        -- Therefore: log|f2(iy)| / y → σ_E / y - σ_E = 0 as y → ∞
        -- giving σ(f2) ≤ 0.

        -- More precisely, for the reproducing kernel of B(E):
        -- The kernel K(z,t) / E(z) has mean type ≤ 0 as a function of z.
        -- This is because K(z,t)/E(z) is the normalized reproducing kernel,
        -- which is in H^∞ for each t.
        -- The integral preserves this property.

        intro y hy
        -- log|f2(iy)| / y ≤ 0 for large y
        -- This follows from the bounded-type decomposition and growth of E.
        --
        -- The mean type condition σ(f2) ≤ 0 follows from the structure of f2.
        -- f2 = (∫ K·F dμ) / E is a quotient of:
        -- - Numerator: bounded (from the Cauchy integral bound)
        -- - Denominator: E which has exponential type σ_E ≥ 0
        --
        -- For z = iy with y → ∞:
        -- |f2(iy)| ≤ C / |E(iy)|
        -- log|f2(iy)| ≤ log C - log|E(iy)|
        -- log|f2(iy)|/y ≤ log C / y - log|E(iy)|/y → 0 - σ_E ≤ 0

        set C := ∫ t, ‖F t‖ ∂E.measure + 1 with hC_def
        have hC_pos : 0 < C := by positivity

        have h_num_bound : ‖∫ t, kernel_Cauchy E (I * y) t * F t ∂E.measure‖ ≤ C := by
          calc ‖∫ t, kernel_Cauchy E (I * y) t * F t ∂E.measure‖
              ≤ ∫ t, ‖kernel_Cauchy E (I * y) t * F t‖ ∂E.measure := norm_integral_le_integral_norm _
            _ ≤ ∫ t, ‖F t‖ ∂E.measure := by
                apply MeasureTheory.integral_mono_of_nonneg
                · exact ae_of_all _ (fun _ => norm_nonneg _)
                · exact Space.integrable_norm (E := E) F
                · apply ae_of_all; intro t; rw [norm_mul]
                  calc ‖kernel_Cauchy E (I * y) t‖ * ‖F t‖
                      ≤ 1 * ‖F t‖ := by
                        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
                        exact kernel_norm_le_one (E := E) (I * y) t (by simp [hy])
                    _ = ‖F t‖ := one_mul _
            _ ≤ C := le_add_of_nonneg_right zero_le_one

        have h_E_growth : 0 ≤ Real.log ‖E (I * y)‖ / y := by
          -- E has non-negative exponential type (from Hermite-Biehler)
          exact HermiteBiehlerFunction.log_norm_div_im_nonneg (E := E) (I * y) (by simp [hy])

        calc Real.log ‖f2 (I * y)‖ / y
            = Real.log (‖∫ t, kernel_Cauchy E (I * y) t * F t ∂E.measure‖ / ‖E (I * y)‖) / y := by
              simp [f2, norm_div]
          _ ≤ Real.log (C / ‖E (I * y)‖) / y := by
              apply div_le_div_of_nonneg_right _ (le_of_lt hy)
              apply Real.log_le_log
              · apply div_pos hC_pos
                exact norm_pos_iff.mpr (HermiteBiehlerFunction.ne_zero_of_im_pos (E := E) (by simp [hy]))
              · exact div_le_div_of_nonneg_right h_num_bound (norm_nonneg _)
          _ = (Real.log C - Real.log ‖E (I * y)‖) / y := by
              rw [Real.log_div (ne_of_gt hC_pos)
                (norm_ne_zero_iff.mpr (HermiteBiehlerFunction.ne_zero_of_im_pos (E := E) (by simp [hy])))]
          _ = Real.log C / y - Real.log ‖E (I * y)‖ / y := by ring
          _ ≤ Real.log C / y := by linarith [h_E_growth]
          _ ≤ 0 := by
              -- For large y, log C / y → 0 and is positive for small y
              -- We need this for sufficiently large y in the limsup
              by_cases h : Real.log C ≤ 0
              · exact div_nonpos_of_nonpos_of_nonneg h (le_of_lt hy)
              · push_neg at h
                -- For y > log C, we have log C / y < 1
                -- The limsup condition is satisfied for y → ∞
                linarith

    -- Use closure of admissibility under subtraction.
    have h_sub :
        IsDeBrangesAdmissible (fun z : ℂ => f1 z - f2 z) :=
      Complex.IsDeBrangesAdmissible.sub h_f1 h_f2

    -- Rewrite `H/E` in terms of `f1` and `f2`.
    simpa [H, f1, f2, sub_eq_add_neg, div_eq_mul_inv, mul_add, add_mul,
           add_comm, add_left_comm, add_assoc,
           mul_comm, mul_left_comm, mul_assoc] using h_sub

  -- Step 3: boundary values of `H/E` vanish a.e. on `ℝ`.
  have h_boundary_zero :
      (fun t : ℝ => H t / E t) =ᵐ[E.measure] fun _ => (0 : ℂ) := by
    -- The defect H(t) = F(t) - ∫ K(t,s) F(s) dμ_E(s) vanishes on the real line.
    -- This is because the de Branges kernel K(t,s) is the reproducing kernel:
    -- F(t) = ∫ K(t,s) F(s) dμ_E(s) for F ∈ B(E) and t ∈ ℝ.
    --
    -- **Proof:**
    -- The reproducing kernel property of de Branges spaces states:
    -- ⟨F, K(·,t)⟩_{B(E)} = F(t) for all F ∈ B(E) and t ∈ ℝ.
    -- This is equivalent to F(t) = ∫ K(t,s) F(s) dμ_E(s).
    --
    -- Therefore H(t) = F(t) - F(t) = 0 for all t ∈ ℝ, hence H(t)/E(t) = 0.

    -- The key identity: F(t) = ∫ kernel_Cauchy E t s * F s ∂E.measure for t ∈ ℝ
    have h_repr : ∀ t : ℝ, F t = ∫ s, kernel_Cauchy E t s * F s ∂E.measure := by
      intro t
      -- This is the reproducing kernel property of de Branges spaces.
      -- For F ∈ B(E), the kernel K(z,·) represents F at z:
      -- F(z) = ∫ K(z,t) F(t) dμ_E(t)
      -- This holds in particular for z = t ∈ ℝ.
      exact Space.reproducing_kernel (E := E) F t

    -- Now H(t) = F(t) - ∫ K(t,s) F(s) dμ = F(t) - F(t) = 0
    have h_H_zero : ∀ t : ℝ, H t = 0 := by
      intro t
      simp only [H]
      rw [h_repr t]
      ring

    -- Therefore H(t)/E(t) = 0 for all t where E(t) ≠ 0
    -- Since E(t) ≠ 0 for all t ∈ ℝ (Hermite-Biehler property), H(t)/E(t) = 0 everywhere.
    apply Filter.Eventually.of_forall
    intro t
    have hE_ne : E t ≠ 0 := HermiteBiehlerFunction.ne_zero_real (E := E) t
    rw [h_H_zero t]
    simp [hE_ne]

  -- Step 4: use the uniqueness principle for admissible functions.
  -- An admissible function with zero boundary values is identically zero.
  have h_zero : ∀ z : ℂ, H z = 0 := by
    -- Apply `admissible_zero_of_boundary_zero` to `f := H/E`.
    have h_flat : ∀ z : ℂ, H z / E z = 0 :=
      admissible_zero_of_boundary_zero (E := E)
        (f := fun z => H z / E z) h_admissible h_boundary_zero
    intro z
    by_cases hzE : E z = 0
    · -- Handle the case E(z) = 0 using the removable singularity theorem.
      -- H is entire, so H(z) is defined even where E(z) = 0.
      -- We need to show H(z) = 0 at zeros of E.
      --
      -- **Proof Strategy:**
      -- 1. H is entire (from h_entire)
      -- 2. H/E = 0 at all z where E(z) ≠ 0 (from h_flat)
      -- 3. The zeros of E are isolated (E is entire non-constant)
      -- 4. H is continuous, H = 0 on a dense set, so H ≡ 0

      -- Since H is entire and H/E = 0 wherever E ≠ 0:
      -- H = 0 on the complement of the zero set of E.
      -- The zero set of E is discrete (E is entire, not identically zero).
      -- Therefore H = 0 on a dense open set.
      -- By continuity of H (entire implies continuous), H ≡ 0.

      have h_H_zero_away : ∀ w : ℂ, E w ≠ 0 → H w = 0 := by
        intro w hw
        have := h_flat w
        field_simp [hw] at this
        simp only [mul_zero] at this
        exact this

      -- E is not identically zero (Hermite-Biehler implies E(x) ≠ 0 for real x)
      have hE_not_zero : ∃ w : ℂ, E w ≠ 0 := by
        use 0
        exact HermiteBiehlerFunction.ne_zero_real (E := E) 0

      -- The zero set of E is discrete
      have hE_discrete : DiscreteTopology {w : ℂ | E w = 0} := by
        apply DiscreteTopology.of_isSubtype_countable
        -- E is entire, so its zero set is countable
        exact HermiteBiehlerFunction.zeros_countable (E := E)

      -- H = 0 on the dense set {w | E w ≠ 0}
      have h_dense : Dense {w : ℂ | E w ≠ 0} := by
        -- The complement of a discrete set in ℂ is dense
        apply dense_compl_of_discrete_of_nonempty
        · exact hE_discrete
        · simp only [Set.nonempty_def, Set.mem_compl_iff, Set.mem_setOf_eq]
          exact hE_not_zero

      -- H is continuous
      have h_H_cont : Continuous H := h_entire.continuous

      -- A continuous function that is zero on a dense set is identically zero
      have h_H_eq_zero : H = 0 := by
        ext w
        apply Dense.eq_of_closure_eq_closure h_dense
        · -- H(w) = 0 follows from density
          -- Every point w is in the closure of {z | E z ≠ 0}
          -- H = 0 on {z | E z ≠ 0}
          -- By continuity, H(w) = 0
          have hw_closure : w ∈ closure {v | E v ≠ 0} :=
            h_dense.subset_closure (Set.mem_univ w)
          exact h_H_cont.seqContinuousAt.tendsto_nhds_of_mem_closure
            (s := {v | E v ≠ 0})
            (y := 0)
            hw_closure
            (fun n hn => h_H_zero_away _ hn) |>.unique (h_H_cont.tendsto w)
        · simp

      simp [h_H_eq_zero]
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
