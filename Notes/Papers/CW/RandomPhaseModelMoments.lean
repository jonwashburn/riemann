import Notes.Papers.CW.RandomPhaseMoments
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Probability.Independence.Integration

open MeasureTheory ProbabilityTheory Real Complex BigOperators
open scoped BigOperators Interval

namespace ZetaSpinGlass

section

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable (params : ModelParams) (rnd : RandomPhases Ω)

/-! ### Pushforward-to-uniform transfer lemmas -/

lemma integral_theta_eq_uniform (p : ℕ) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ ω, f (rnd.theta p ω) ∂ (ℙ : Measure Ω)) = ∫ x, f x ∂ uniformIcc0TwoPi := by
  have hmap :=
    (MeasureTheory.integral_map (μ := (ℙ : Measure Ω)) (φ := rnd.theta p)
      (hφ := (rnd.measurable p).aemeasurable) (f := f) (hfm := hf.aestronglyMeasurable))
  have hΩ :
      (∫ ω, f (rnd.theta p ω) ∂ (ℙ : Measure Ω))
        = ∫ x, f x ∂ Measure.map (rnd.theta p) (ℙ : Measure Ω) := by
    simpa using hmap.symm
  rw [hΩ, rnd.dist p]
  rfl

lemma integral_cos_theta_sub (p : ℕ) (a : ℝ) :
    (∫ ω, Real.cos (rnd.theta p ω - a) ∂ (ℙ : Measure Ω)) = 0 := by
  have h :=
    integral_theta_eq_uniform (rnd := rnd) (p := p) (f := fun x : ℝ => Real.cos (x - a))
      (hf := by fun_prop)
  simpa [h] using (integral_cos_sub (a := a))

lemma integral_cos_two_mul_theta_sub (p : ℕ) (a : ℝ) :
    (∫ ω, Real.cos (2 * (rnd.theta p ω - a)) ∂ (ℙ : Measure Ω)) = 0 := by
  have h :=
    integral_theta_eq_uniform (rnd := rnd) (p := p) (f := fun x : ℝ => Real.cos (2 * (x - a)))
      (hf := by fun_prop)
  simpa [h] using (integral_cos_two_mul_sub (a := a))

lemma integral_cos_theta_sub_mul_cos_theta_sub (p : ℕ) (a b : ℝ) :
    (∫ ω, Real.cos (rnd.theta p ω - a) * Real.cos (rnd.theta p ω - b) ∂ (ℙ : Measure Ω))
      = (1 / 2 : ℝ) * Real.cos (b - a) := by
  have h :=
    integral_theta_eq_uniform (rnd := rnd) (p := p)
      (f := fun x : ℝ => Real.cos (x - a) * Real.cos (x - b)) (hf := by fun_prop)
  simpa [h] using (integral_cos_sub_mul_cos_sub (a := a) (b := b))

lemma integral_cos_theta_sub_mul_cos_theta_sub_of_ne {p q : ℕ} (hpq : p ≠ q) (a b : ℝ) :
    (∫ ω, Real.cos (rnd.theta p ω - a) * Real.cos (rnd.theta q ω - b) ∂ (ℙ : Measure Ω)) = 0 := by
  -- independence of `theta p` and `theta q`, pushed through `cos (· - a)` and `cos (· - b)`
  have hindθ : rnd.theta p ⟂ᵢ[(ℙ : Measure Ω)] rnd.theta q := rnd.indep.indepFun hpq
  have hmeasA : Measurable (fun x : ℝ => Real.cos (x - a)) := by fun_prop
  have hmeasB : Measurable (fun x : ℝ => Real.cos (x - b)) := by fun_prop
  have hind :
      (fun ω => Real.cos (rnd.theta p ω - a)) ⟂ᵢ[(ℙ : Measure Ω)]
        (fun ω => Real.cos (rnd.theta q ω - b)) := by
    simpa [Function.comp] using hindθ.comp hmeasA hmeasB
  have hX : AEStronglyMeasurable (fun ω => Real.cos (rnd.theta p ω - a)) (ℙ : Measure Ω) := by
    exact (hmeasA.comp (rnd.measurable p)).aestronglyMeasurable
  have hY : AEStronglyMeasurable (fun ω => Real.cos (rnd.theta q ω - b)) (ℙ : Measure Ω) := by
    exact (hmeasB.comp (rnd.measurable q)).aestronglyMeasurable
  -- factorization, then each mean vanishes by the uniform computation
  have hmul :
      (∫ ω, Real.cos (rnd.theta p ω - a) * Real.cos (rnd.theta q ω - b) ∂ (ℙ : Measure Ω))
        = (∫ ω, Real.cos (rnd.theta p ω - a) ∂ (ℙ : Measure Ω))
            * (∫ ω, Real.cos (rnd.theta q ω - b) ∂ (ℙ : Measure Ω)) := by
    simpa using (IndepFun.integral_fun_mul_eq_mul_integral (μ := (ℙ : Measure Ω)) hind hX hY)
  -- finish
  simp [hmul, integral_cos_theta_sub (rnd := rnd)]  -- both factors are `0`

/-! ### Random-phase trigonometric reduction -/

private lemma exp_I_mul_re (t : ℝ) : (Complex.exp (Complex.I * (t : ℂ))).re = Real.cos t := by
  have hmul : (Complex.I * (t : ℂ)) = ((t : ℂ) * Complex.I) := by ring
  rw [hmul]
  simpa using (Complex.exp_ofReal_mul_I_re t)

private lemma exp_I_mul_sq (t : ℝ) :
    (Complex.exp (Complex.I * (t : ℂ))) ^ 2 = Complex.exp (Complex.I * ((2 * t : ℝ) : ℂ)) := by
  simp [pow_two]
  have hprod :
      Complex.exp (Complex.I * (t : ℂ)) * Complex.exp (Complex.I * (t : ℂ))
        = Complex.exp (Complex.I * (t : ℂ) + Complex.I * (t : ℂ)) := by
    simpa using (Complex.exp_add (Complex.I * (t : ℂ)) (Complex.I * (t : ℂ))).symm
  rw [hprod]
  congr 1
  ring_nf

lemma random_phase_re (p : ℕ) (h : ℝ) (ω : Ω) :
    (random_phase params rnd p h ω).re = Real.cos (rnd.theta p ω - h * Real.log p) := by
  unfold random_phase
  set t : ℝ := rnd.theta p ω - h * Real.log p
  have hcast :
      (↑(rnd.theta p ω) - (↑h : ℂ) * (↑(Real.log p) : ℂ)) = (t : ℂ) := by
    simp [t, Complex.ofReal_sub, Complex.ofReal_mul]
  rw [hcast]
  simpa [t] using (exp_I_mul_re (t := t))

lemma random_phase_sq_re (p : ℕ) (h : ℝ) (ω : Ω) :
    ((random_phase params rnd p h ω) ^ 2).re = Real.cos (2 * (rnd.theta p ω - h * Real.log p)) := by
  unfold random_phase
  set t : ℝ := rnd.theta p ω - h * Real.log p
  have hcast :
      (↑(rnd.theta p ω) - (↑h : ℂ) * (↑(Real.log p) : ℂ)) = (t : ℂ) := by
    simp [t, Complex.ofReal_sub, Complex.ofReal_mul]
  rw [hcast]
  rw [exp_I_mul_sq (t := t)]
  simpa [t] using (exp_I_mul_re (t := 2 * t))

/-! ### Centering of the random blocks -/

lemma integrable_cos_theta_sub (p : ℕ) (a : ℝ) :
    Integrable (fun ω : Ω => Real.cos (rnd.theta p ω - a)) (ℙ : Measure Ω) := by
  refine Integrable.of_bound (μ := (ℙ : Measure Ω)) ?_ (C := (1 : ℝ)) ?_
  · have hθ : Measurable (rnd.theta p) := rnd.measurable p
    have : Measurable (fun ω : Ω => Real.cos (rnd.theta p ω - a)) :=
      (Real.continuous_cos.measurable.comp (hθ.sub measurable_const))
    exact this.aestronglyMeasurable
  · filter_upwards with ω
    simpa using (Real.abs_cos_le_one (rnd.theta p ω - a))

lemma integrable_cos_two_mul_theta_sub (p : ℕ) (a : ℝ) :
    Integrable (fun ω : Ω => Real.cos (2 * (rnd.theta p ω - a))) (ℙ : Measure Ω) := by
  refine Integrable.of_bound (μ := (ℙ : Measure Ω)) ?_ (C := (1 : ℝ)) ?_
  · have hθ : Measurable (rnd.theta p) := rnd.measurable p
    have : Measurable (fun ω : Ω => Real.cos (2 * (rnd.theta p ω - a))) :=
      Real.continuous_cos.measurable.comp ((measurable_const.mul (hθ.sub measurable_const)))
    exact this.aestronglyMeasurable
  · filter_upwards with ω
    simpa using (Real.abs_cos_le_one (2 * (rnd.theta p ω - a)))

lemma integrable_block_term_random_phase (p : ℕ) (h : ℝ) :
    Integrable (fun ω : Ω => block_term p (random_phase params rnd p h ω)) (ℙ : Measure Ω) := by
  -- rewrite to a sum of two bounded cosine terms
  have hblock :
      (fun ω : Ω => block_term p (random_phase params rnd p h ω))
        = fun ω : Ω =>
            (Real.rpow (p : ℝ) (-(1 / 2 : ℝ))) * Real.cos (rnd.theta p ω - h * Real.log p)
              + (1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ)) * Real.cos (2 * (rnd.theta p ω - h * Real.log p)) := by
    funext ω
    simp [block_term, random_phase_re, random_phase_sq_re, mul_assoc, mul_left_comm, mul_comm]
  -- integrability of each term
  have hInt1 :
      Integrable (fun ω : Ω =>
          (Real.rpow (p : ℝ) (-(1 / 2 : ℝ))) * Real.cos (rnd.theta p ω - h * Real.log p)) (ℙ : Measure Ω) :=
    (integrable_cos_theta_sub (rnd := rnd) (p := p) (a := h * Real.log p)).const_mul _
  have hInt2 :
      Integrable (fun ω : Ω =>
          (1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ)) * Real.cos (2 * (rnd.theta p ω - h * Real.log p)))
        (ℙ : Measure Ω) :=
    (integrable_cos_two_mul_theta_sub (rnd := rnd) (p := p) (a := h * Real.log p)).const_mul
      ((1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ)))
  refine (hInt1.add hInt2).congr ?_
  filter_upwards with ω
  -- `hblock` is a pointwise identity after applying `congrArg`
  simpa using (congrArg (fun f => f ω) hblock).symm

lemma integral_block_term_random_phase (p : ℕ) (h : ℝ) :
    (∫ ω, block_term p (random_phase params rnd p h ω) ∂ (ℙ : Measure Ω)) = 0 := by
  classical
  -- expand the block term and rewrite the phases to cosines
  have h1 :
      (∫ ω,
            (Real.rpow (p : ℝ) (-(1 / 2 : ℝ)))
                * Real.cos (rnd.theta p ω - h * Real.log p) ∂ (ℙ : Measure Ω))
        = 0 := by
    -- pull out the constant, then use the uniform cosine integral
    simp [MeasureTheory.integral_const_mul, integral_cos_theta_sub (rnd := rnd) (p := p) (a := h * Real.log p)]
  have h2 :
      (∫ ω,
            (1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ))
                * Real.cos (2 * (rnd.theta p ω - h * Real.log p)) ∂ (ℙ : Measure Ω))
        = 0 := by
    -- constants again
    simp [MeasureTheory.integral_const_mul, integral_cos_two_mul_theta_sub (rnd := rnd) (p := p) (a := h * Real.log p),
      mul_assoc, mul_left_comm, mul_comm]
  -- now combine the two pieces
  -- (we supply integrability to use `integral_add`).
  have hInt1 :
      Integrable (fun ω : Ω =>
          (Real.rpow (p : ℝ) (-(1 / 2 : ℝ))) * Real.cos (rnd.theta p ω - h * Real.log p)) (ℙ : Measure Ω) := by
    simpa using (integrable_cos_theta_sub (rnd := rnd) (p := p) (a := h * Real.log p)).const_mul
      (Real.rpow (p : ℝ) (-(1 / 2 : ℝ)))
  have hInt2 :
      Integrable (fun ω : Ω =>
          (1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ)) * Real.cos (2 * (rnd.theta p ω - h * Real.log p)))
        (ℙ : Measure Ω) := by
    simpa using (integrable_cos_two_mul_theta_sub (rnd := rnd) (p := p) (a := h * Real.log p)).const_mul
      ((1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ)))
  -- finish by rewriting `block_term` and using the two zero integrals
  have hre :
      (fun ω : Ω => (random_phase params rnd p h ω).re) =
        fun ω : Ω => Real.cos (rnd.theta p ω - h * Real.log p) := by
    funext ω
    simpa using (random_phase_re (params := params) (rnd := rnd) (p := p) (h := h) (ω := ω))
  have hre2 :
      (fun ω : Ω => ((random_phase params rnd p h ω) ^ 2).re) =
        fun ω : Ω => Real.cos (2 * (rnd.theta p ω - h * Real.log p)) := by
    funext ω
    simpa using (random_phase_sq_re (params := params) (rnd := rnd) (p := p) (h := h) (ω := ω))
  -- now compute
  have hblock :
      (fun ω : Ω => block_term p (random_phase params rnd p h ω))
        = fun ω : Ω =>
            (Real.rpow (p : ℝ) (-(1 / 2 : ℝ))) * Real.cos (rnd.theta p ω - h * Real.log p)
              + (1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ)) * Real.cos (2 * (rnd.theta p ω - h * Real.log p)) := by
    funext ω
    simp [block_term, random_phase_re, random_phase_sq_re, mul_assoc, mul_left_comm, mul_comm]
  -- apply linearity
  have hrewrite :
      (∫ ω, block_term p (random_phase params rnd p h ω) ∂ (ℙ : Measure Ω))
        = ∫ ω,
            (Real.rpow (p : ℝ) (-(1 / 2 : ℝ))) * Real.cos (rnd.theta p ω - h * Real.log p)
              + (1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ)) * Real.cos (2 * (rnd.theta p ω - h * Real.log p))
            ∂ (ℙ : Measure Ω) := by
    simpa [hblock]
  rw [hrewrite]
  -- split the integral and use `h1`, `h2`
  -- `simp` can introduce `rpow`-notation (`^`) for real exponents, so we normalize explicitly.
  rw [MeasureTheory.integral_add hInt1 hInt2]
  -- each term vanishes by the uniform cosine integrals
  simp [MeasureTheory.integral_const_mul,
    integral_cos_theta_sub (rnd := rnd) (p := p) (a := h * Real.log p),
    integral_cos_two_mul_theta_sub (rnd := rnd) (p := p) (a := h * Real.log p),
    mul_assoc, mul_left_comm, mul_comm]

lemma mean_Y_rand_k (k : ℕ) (h : ℝ) :
    mean (Y_rand_k (params := params) rnd k h) (ℙ : Measure Ω) = 0 := by
  classical
  -- unfold `mean` and `Y_rand_k`
  simp [ZetaSpinGlass.mean, Y_rand_k]
  -- swap integral and finite sum
  have hInt :
      (∫ ω, ∑ p ∈ P_k params k, block_term p (random_phase params rnd p h ω) ∂ (ℙ : Measure Ω))
        = ∑ p ∈ P_k params k, ∫ ω, block_term p (random_phase params rnd p h ω) ∂ (ℙ : Measure Ω) := by
    refine MeasureTheory.integral_finset_sum (μ := (ℙ : Measure Ω)) (s := P_k params k)
      (f := fun p ω => block_term p (random_phase params rnd p h ω)) ?_
    intro p hp
    exact integrable_block_term_random_phase (params := params) (rnd := rnd) (p := p) (h := h)
  -- each summand integral is zero
  rw [hInt]
  simp [integral_block_term_random_phase (params := params) (rnd := rnd) (h := h)]

end

end ZetaSpinGlass
