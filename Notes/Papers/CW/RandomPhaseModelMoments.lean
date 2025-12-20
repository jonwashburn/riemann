import Notes.Papers.CW.RandomPhaseMoments
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Probability.Independence.Integration

open MeasureTheory ProbabilityTheory Real Complex BigOperators
open scoped BigOperators Interval

set_option linter.unusedSectionVars false
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

lemma integral_cos_theta_sub_mul_cos_two_mul_theta_sub_eq_zero (p : ℕ) (a b : ℝ) :
    (∫ ω, Real.cos (rnd.theta p ω - a) * Real.cos (2 * (rnd.theta p ω - b)) ∂ (ℙ : Measure Ω)) = 0 := by
  have h :=
    integral_theta_eq_uniform (rnd := rnd) (p := p)
      (f := fun x : ℝ => Real.cos (x - a) * Real.cos (2 * (x - b))) (hf := by fun_prop)
  simpa [h] using (integral_cos_sub_mul_cos_two_mul_sub_eq_zero (a := a) (b := b))

lemma integral_cos_two_mul_theta_sub_mul_cos_two_mul_theta_sub (p : ℕ) (a b : ℝ) :
    (∫ ω, Real.cos (2 * (rnd.theta p ω - a)) * Real.cos (2 * (rnd.theta p ω - b)) ∂ (ℙ : Measure Ω))
      = (1 / 2 : ℝ) * Real.cos (2 * (b - a)) := by
  have h :=
    integral_theta_eq_uniform (rnd := rnd) (p := p)
      (f := fun x : ℝ => Real.cos (2 * (x - a)) * Real.cos (2 * (x - b))) (hf := by fun_prop)
  simpa [h] using (integral_cos_two_mul_sub_mul_cos_two_mul_sub (a := a) (b := b))

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
  simp

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

lemma block_term_random_phase_eq (p : ℕ) (h : ℝ) :
    (fun ω : Ω => block_term p (random_phase params rnd p h ω))
      = fun ω : Ω =>
          (Real.rpow (p : ℝ) (-(1 / 2 : ℝ))) * Real.cos (rnd.theta p ω - h * Real.log p)
            + (1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ)) * Real.cos (2 * (rnd.theta p ω - h * Real.log p)) := by
  funext ω
  simp [block_term, random_phase_re, random_phase_sq_re, mul_assoc, mul_comm]

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
    simp [block_term, random_phase_re, random_phase_sq_re, mul_assoc, mul_comm]
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
      mul_assoc, mul_comm]
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
    simp [block_term, random_phase_re, random_phase_sq_re, mul_assoc, mul_comm]
  -- apply linearity
  have hrewrite :
      (∫ ω, block_term p (random_phase params rnd p h ω) ∂ (ℙ : Measure Ω))
        = ∫ ω,
            (Real.rpow (p : ℝ) (-(1 / 2 : ℝ))) * Real.cos (rnd.theta p ω - h * Real.log p)
              + (1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ)) * Real.cos (2 * (rnd.theta p ω - h * Real.log p))
            ∂ (ℙ : Measure Ω) := by
    simp [hblock]
  rw [hrewrite]
  -- split the integral and use `h1`, `h2`
  -- `simp` can introduce `rpow`-notation (`^`) for real exponents, so we normalize explicitly.
  rw [MeasureTheory.integral_add hInt1 hInt2]
  -- each term vanishes by the uniform cosine integrals
  simp [MeasureTheory.integral_const_mul,
    integral_cos_theta_sub (rnd := rnd) (p := p) (a := h * Real.log p),
    integral_cos_two_mul_theta_sub (rnd := rnd) (p := p) (a := h * Real.log p),
    mul_assoc, mul_comm]

lemma integral_block_term_random_phase_mul (p : ℕ) (hp : p ≠ 0) (h₁ h₂ : ℝ) :
    (∫ ω, block_term p (random_phase params rnd p h₁ ω) * block_term p (random_phase params rnd p h₂ ω)
        ∂ (ℙ : Measure Ω))
      =
      (1 / 2 : ℝ) * ((p : ℝ)⁻¹) * Real.cos ((h₁ - h₂) * Real.log p)
        + (1 / 8 : ℝ) * ((p : ℝ)⁻¹) ^ 2 * Real.cos (2 * ((h₁ - h₂) * Real.log p)) := by
  classical
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hp

  -- cosine expansions of the two block terms
  have hblock₁ := block_term_random_phase_eq (params := params) (rnd := rnd) (p := p) (h := h₁)
  have hblock₂ := block_term_random_phase_eq (params := params) (rnd := rnd) (p := p) (h := h₂)

  -- abbreviate coefficients and shifts
  set A : ℝ := Real.rpow (p : ℝ) (-(1 / 2 : ℝ))
  set B : ℝ := (1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ))
  set a : ℝ := h₁ * Real.log p
  set b : ℝ := h₂ * Real.log p

  have hA : A ^ 2 = (p : ℝ)⁻¹ := by
    -- `p^(-1/2)` squared is `p^(-1)` (requires `p>0` for the add law)
    have hmul :
        ((p : ℝ) ^ (-( (2 : ℝ)⁻¹))) * ((p : ℝ) ^ (-( (2 : ℝ)⁻¹))) = (p : ℝ) ^ (-1 : ℝ) := by
      have h := (Real.rpow_add hp0 (-( (2 : ℝ)⁻¹)) (-( (2 : ℝ)⁻¹))).symm
      simpa [show (-( (2 : ℝ)⁻¹) + -( (2 : ℝ)⁻¹)) = (-1 : ℝ) by ring] using h
    -- unfold `A` and conclude
    -- (`simp` turns `-(1/2)` into `-(2:ℝ)⁻¹`.)
    simp [A, pow_two, hmul, Real.rpow_neg_one]

  have hB : B ^ 2 = (1 / 4 : ℝ) * ((p : ℝ)⁻¹) ^ 2 := by
    -- expand the square and rewrite `p^(-1)` as `p⁻¹`
    simp [B, pow_two, Real.rpow_neg_one]
    ring

  -- rewrite the original integral via the cosine expansions
  have hrewrite :
      (∫ ω, block_term p (random_phase params rnd p h₁ ω) * block_term p (random_phase params rnd p h₂ ω)
          ∂ (ℙ : Measure Ω))
        =
        ∫ ω,
          (A * Real.cos (rnd.theta p ω - a) + B * Real.cos (2 * (rnd.theta p ω - a)))
            *
          (A * Real.cos (rnd.theta p ω - b) + B * Real.cos (2 * (rnd.theta p ω - b)))
          ∂ (ℙ : Measure Ω) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with ω
    have h1ω :
        block_term p (random_phase params rnd p h₁ ω)
          = A * Real.cos (rnd.theta p ω - a) + B * Real.cos (2 * (rnd.theta p ω - a)) := by
      -- `hblock₁` already has the right shape; we just rename `a`
      simpa [A, B, a] using congrArg (fun f => f ω) hblock₁
    have h2ω :
        block_term p (random_phase params rnd p h₂ ω)
          = A * Real.cos (rnd.theta p ω - b) + B * Real.cos (2 * (rnd.theta p ω - b)) := by
      simpa [A, B, b] using congrArg (fun f => f ω) hblock₂
    simp [h1ω, h2ω]

  -- pointwise expansion into four integrals
  let t11 : Ω → ℝ := fun ω =>
    (A * Real.cos (rnd.theta p ω - a)) * (A * Real.cos (rnd.theta p ω - b))
  let t12 : Ω → ℝ := fun ω =>
    (A * Real.cos (rnd.theta p ω - a)) * (B * Real.cos (2 * (rnd.theta p ω - b)))
  let t21 : Ω → ℝ := fun ω =>
    (B * Real.cos (2 * (rnd.theta p ω - a))) * (A * Real.cos (rnd.theta p ω - b))
  let t22 : Ω → ℝ := fun ω =>
    (B * Real.cos (2 * (rnd.theta p ω - a))) * (B * Real.cos (2 * (rnd.theta p ω - b)))

  have hpoint :
      (fun ω : Ω =>
          (A * Real.cos (rnd.theta p ω - a) + B * Real.cos (2 * (rnd.theta p ω - a)))
            * (A * Real.cos (rnd.theta p ω - b) + B * Real.cos (2 * (rnd.theta p ω - b))))
        = fun ω => t11 ω + t12 ω + t21 ω + t22 ω := by
    funext ω
    simp [t11, t12, t21, t22]
    ring

  -- measurability helpers for `theta`-cosine composites
  have hθ : Measurable (rnd.theta p) := rnd.measurable p
  have hcos (c : ℝ) : Measurable fun ω : Ω => Real.cos (rnd.theta p ω - c) :=
    (Real.continuous_cos.measurable.comp (hθ.sub measurable_const))
  have hcos2 (c : ℝ) : Measurable fun ω : Ω => Real.cos (2 * (rnd.theta p ω - c)) := by
    have : Measurable fun ω : Ω => (2 : ℝ) * (rnd.theta p ω - c) :=
      measurable_const.mul (hθ.sub measurable_const)
    exact (Real.continuous_cos.measurable.comp this)

  -- integrability of the four terms (bounded on a probability space)
  have ht11 : Integrable t11 (ℙ : Measure Ω) := by
    refine Integrable.of_bound (μ := (ℙ : Measure Ω)) ?_ (C := |A| * |A|) ?_
    ·
      have h1 : Measurable fun ω : Ω => A * Real.cos (rnd.theta p ω - a) :=
        measurable_const.mul (hcos a)
      have h2 : Measurable fun ω : Ω => A * Real.cos (rnd.theta p ω - b) :=
        measurable_const.mul (hcos b)
      have : Measurable t11 := by
        dsimp [t11]
        exact h1.mul h2
      exact this.aestronglyMeasurable
    · filter_upwards with ω
      have hAcos : |A * Real.cos (rnd.theta p ω - a)| ≤ |A| := by
        -- `|A*cos| ≤ |A|`
        calc
          |A * Real.cos (rnd.theta p ω - a)|
              = |A| * |Real.cos (rnd.theta p ω - a)| := by simp [abs_mul]
          _ ≤ |A| * (1 : ℝ) := by
                gcongr
                simpa using Real.abs_cos_le_one (rnd.theta p ω - a)
          _ = |A| := by ring
      have hBcos : |A * Real.cos (rnd.theta p ω - b)| ≤ |A| := by
        calc
          |A * Real.cos (rnd.theta p ω - b)|
              = |A| * |Real.cos (rnd.theta p ω - b)| := by simp [abs_mul]
          _ ≤ |A| * (1 : ℝ) := by
                gcongr
                simpa using Real.abs_cos_le_one (rnd.theta p ω - b)
          _ = |A| := by ring
      have : |t11 ω| ≤ |A| * |A| := by
        -- product bound
        simpa [t11, abs_mul] using
          (mul_le_mul hAcos hBcos (abs_nonneg _) (abs_nonneg A))
      simpa [Real.norm_eq_abs] using this
  have ht12 : Integrable t12 (ℙ : Measure Ω) := by
    refine Integrable.of_bound (μ := (ℙ : Measure Ω)) ?_ (C := |A| * |B|) ?_
    ·
      have h1 : Measurable fun ω : Ω => A * Real.cos (rnd.theta p ω - a) :=
        measurable_const.mul (hcos a)
      have h2 : Measurable fun ω : Ω => B * Real.cos (2 * (rnd.theta p ω - b)) :=
        measurable_const.mul (hcos2 b)
      have : Measurable t12 := by
        dsimp [t12]
        exact h1.mul h2
      exact this.aestronglyMeasurable
    · filter_upwards with ω
      have hAcos : |A * Real.cos (rnd.theta p ω - a)| ≤ |A| := by
        calc
          |A * Real.cos (rnd.theta p ω - a)|
              = |A| * |Real.cos (rnd.theta p ω - a)| := by simp [abs_mul]
          _ ≤ |A| * (1 : ℝ) := by
                gcongr
                simpa using Real.abs_cos_le_one (rnd.theta p ω - a)
          _ = |A| := by ring
      have hBcos : |B * Real.cos (2 * (rnd.theta p ω - b))| ≤ |B| := by
        calc
          |B * Real.cos (2 * (rnd.theta p ω - b))|
              = |B| * |Real.cos (2 * (rnd.theta p ω - b))| := by simp [abs_mul]
          _ ≤ |B| * (1 : ℝ) := by
                gcongr
                simpa using Real.abs_cos_le_one (2 * (rnd.theta p ω - b))
          _ = |B| := by ring
      have : |t12 ω| ≤ |A| * |B| := by
        simpa [t12, abs_mul] using
          (mul_le_mul hAcos hBcos (abs_nonneg _) (abs_nonneg A))
      simpa [Real.norm_eq_abs] using this
  have ht21 : Integrable t21 (ℙ : Measure Ω) := by
    -- symmetric to `ht12`
    refine Integrable.of_bound (μ := (ℙ : Measure Ω)) ?_ (C := |B| * |A|) ?_
    ·
      have h1 : Measurable fun ω : Ω => B * Real.cos (2 * (rnd.theta p ω - a)) :=
        measurable_const.mul (hcos2 a)
      have h2 : Measurable fun ω : Ω => A * Real.cos (rnd.theta p ω - b) :=
        measurable_const.mul (hcos b)
      have : Measurable t21 := by
        dsimp [t21]
        exact h1.mul h2
      exact this.aestronglyMeasurable
    · filter_upwards with ω
      have hBcos : |B * Real.cos (2 * (rnd.theta p ω - a))| ≤ |B| := by
        calc
          |B * Real.cos (2 * (rnd.theta p ω - a))|
              = |B| * |Real.cos (2 * (rnd.theta p ω - a))| := by simp [abs_mul]
          _ ≤ |B| * (1 : ℝ) := by
                gcongr
                simpa using Real.abs_cos_le_one (2 * (rnd.theta p ω - a))
          _ = |B| := by ring
      have hAcos : |A * Real.cos (rnd.theta p ω - b)| ≤ |A| := by
        calc
          |A * Real.cos (rnd.theta p ω - b)|
              = |A| * |Real.cos (rnd.theta p ω - b)| := by simp [abs_mul]
          _ ≤ |A| * (1 : ℝ) := by
                gcongr
                simpa using Real.abs_cos_le_one (rnd.theta p ω - b)
          _ = |A| := by ring
      have : |t21 ω| ≤ |B| * |A| := by
        simpa [t21, abs_mul] using
          (mul_le_mul hBcos hAcos (abs_nonneg _) (abs_nonneg B))
      simpa [Real.norm_eq_abs] using this
  have ht22 : Integrable t22 (ℙ : Measure Ω) := by
    refine Integrable.of_bound (μ := (ℙ : Measure Ω)) ?_ (C := |B| * |B|) ?_
    ·
      have h1 : Measurable fun ω : Ω => B * Real.cos (2 * (rnd.theta p ω - a)) :=
        measurable_const.mul (hcos2 a)
      have h2 : Measurable fun ω : Ω => B * Real.cos (2 * (rnd.theta p ω - b)) :=
        measurable_const.mul (hcos2 b)
      have : Measurable t22 := by
        dsimp [t22]
        exact h1.mul h2
      exact this.aestronglyMeasurable
    · filter_upwards with ω
      have hBcos1 : |B * Real.cos (2 * (rnd.theta p ω - a))| ≤ |B| := by
        calc
          |B * Real.cos (2 * (rnd.theta p ω - a))|
              = |B| * |Real.cos (2 * (rnd.theta p ω - a))| := by simp [abs_mul]
          _ ≤ |B| * (1 : ℝ) := by
                gcongr
                simpa using Real.abs_cos_le_one (2 * (rnd.theta p ω - a))
          _ = |B| := by ring
      have hBcos2 : |B * Real.cos (2 * (rnd.theta p ω - b))| ≤ |B| := by
        calc
          |B * Real.cos (2 * (rnd.theta p ω - b))|
              = |B| * |Real.cos (2 * (rnd.theta p ω - b))| := by simp [abs_mul]
          _ ≤ |B| * (1 : ℝ) := by
                gcongr
                simpa using Real.abs_cos_le_one (2 * (rnd.theta p ω - b))
          _ = |B| := by ring
      have : |t22 ω| ≤ |B| * |B| := by
        simpa [t22, abs_mul] using
          (mul_le_mul hBcos1 hBcos2 (abs_nonneg _) (abs_nonneg B))
      simpa [Real.norm_eq_abs] using this

  -- expand the integral
  have hsum :
      (∫ ω,
          (A * Real.cos (rnd.theta p ω - a) + B * Real.cos (2 * (rnd.theta p ω - a)))
            * (A * Real.cos (rnd.theta p ω - b) + B * Real.cos (2 * (rnd.theta p ω - b)))
        ∂ (ℙ : Measure Ω))
        =
        (∫ ω, t11 ω ∂ (ℙ : Measure Ω))
          + (∫ ω, t12 ω ∂ (ℙ : Measure Ω))
          + (∫ ω, t21 ω ∂ (ℙ : Measure Ω))
          + (∫ ω, t22 ω ∂ (ℙ : Measure Ω)) := by
    -- rewrite integrand, then use `integral_add` repeatedly
    rw [MeasureTheory.integral_congr_ae (ae_of_all _ (fun ω => by
      simpa using congrArg (fun f => f ω) hpoint))]
    -- reassociate as ((t11+t12) + (t21+t22))
    have ht12' : Integrable (fun ω => t11 ω + t12 ω) (ℙ : Measure Ω) := ht11.add ht12
    have ht34' : Integrable (fun ω => t21 ω + t22 ω) (ℙ : Measure Ω) := ht21.add ht22
    -- first split
    have hsplit1 :
        (∫ ω, (t11 ω + t12 ω) + (t21 ω + t22 ω) ∂ (ℙ : Measure Ω))
          =
          (∫ ω, (t11 ω + t12 ω) ∂ (ℙ : Measure Ω))
            + (∫ ω, (t21 ω + t22 ω) ∂ (ℙ : Measure Ω)) := by
      simpa using (MeasureTheory.integral_add (μ := (ℙ : Measure Ω)) ht12' ht34')
    -- and split each of the two sums
    have hsplit12 :
        (∫ ω, t11 ω + t12 ω ∂ (ℙ : Measure Ω))
          = (∫ ω, t11 ω ∂ (ℙ : Measure Ω)) + (∫ ω, t12 ω ∂ (ℙ : Measure Ω)) := by
      simpa using (MeasureTheory.integral_add (μ := (ℙ : Measure Ω)) ht11 ht12)
    have hsplit34 :
        (∫ ω, t21 ω + t22 ω ∂ (ℙ : Measure Ω))
          = (∫ ω, t21 ω ∂ (ℙ : Measure Ω)) + (∫ ω, t22 ω ∂ (ℙ : Measure Ω)) := by
      simpa using (MeasureTheory.integral_add (μ := (ℙ : Measure Ω)) ht21 ht22)
    -- combine
    -- start from the LHS and rewrite step-by-step
    -- (the only non-trivial reassociation is handled by `ring_nf`)
    calc
      (∫ ω : Ω, t11 ω + t12 ω + t21 ω + t22 ω ∂ (ℙ : Measure Ω))
          = (∫ ω : Ω, (t11 ω + t12 ω) + (t21 ω + t22 ω) ∂ (ℙ : Measure Ω)) := by
              refine MeasureTheory.integral_congr_ae ?_
              filter_upwards with ω
              ring
      _ = (∫ ω : Ω, t11 ω + t12 ω ∂ (ℙ : Measure Ω))
            + (∫ ω : Ω, t21 ω + t22 ω ∂ (ℙ : Measure Ω)) := by
              simpa using hsplit1
      _ = ((∫ ω : Ω, t11 ω ∂ (ℙ : Measure Ω)) + (∫ ω : Ω, t12 ω ∂ (ℙ : Measure Ω)))
            + ((∫ ω : Ω, t21 ω ∂ (ℙ : Measure Ω)) + (∫ ω : Ω, t22 ω ∂ (ℙ : Measure Ω))) := by
              rw [hsplit12, hsplit34]
      _ = (∫ ω : Ω, t11 ω ∂ (ℙ : Measure Ω))
            + (∫ ω : Ω, t12 ω ∂ (ℙ : Measure Ω))
            + (∫ ω : Ω, t21 ω ∂ (ℙ : Measure Ω))
            + (∫ ω : Ω, t22 ω ∂ (ℙ : Measure Ω)) := by ring

  -- evaluate the four integrals
  have I11 :
      (∫ ω, t11 ω ∂ (ℙ : Measure Ω))
        = (A ^ 2) * ((1 / 2 : ℝ) * Real.cos (b - a)) := by
    calc
      (∫ ω, t11 ω ∂ (ℙ : Measure Ω))
          = ∫ ω, (A * A) * (Real.cos (rnd.theta p ω - a) * Real.cos (rnd.theta p ω - b)) ∂ (ℙ : Measure Ω) := by
              refine MeasureTheory.integral_congr_ae ?_
              filter_upwards with ω
              simp [t11]
              ring
      _ = (A * A) * (∫ ω, Real.cos (rnd.theta p ω - a) * Real.cos (rnd.theta p ω - b) ∂ (ℙ : Measure Ω)) := by
              simpa using
                (MeasureTheory.integral_const_mul (μ := (ℙ : Measure Ω)) (r := A * A)
                  (f := fun ω => Real.cos (rnd.theta p ω - a) * Real.cos (rnd.theta p ω - b)))
      _ = (A * A) * ((1 / 2 : ℝ) * Real.cos (b - a)) := by
              simp [integral_cos_theta_sub_mul_cos_theta_sub (rnd := rnd) (p := p) (a := a) (b := b)]
      _ = (A ^ 2) * ((1 / 2 : ℝ) * Real.cos (b - a)) := by
              simp [pow_two, mul_assoc]

  have I12 : (∫ ω, t12 ω ∂ (ℙ : Measure Ω)) = 0 := by
    calc
      (∫ ω, t12 ω ∂ (ℙ : Measure Ω))
          = ∫ ω, (A * B) * (Real.cos (rnd.theta p ω - a) * Real.cos (2 * (rnd.theta p ω - b)))
              ∂ (ℙ : Measure Ω) := by
              refine MeasureTheory.integral_congr_ae ?_
              filter_upwards with ω
              simp [t12]
              ring
      _ = (A * B) * (∫ ω, Real.cos (rnd.theta p ω - a) * Real.cos (2 * (rnd.theta p ω - b))
              ∂ (ℙ : Measure Ω)) := by
              simpa using
                (MeasureTheory.integral_const_mul (μ := (ℙ : Measure Ω)) (r := A * B)
                  (f := fun ω => Real.cos (rnd.theta p ω - a) * Real.cos (2 * (rnd.theta p ω - b))))
      _ = (A * B) * 0 := by
              simp [integral_cos_theta_sub_mul_cos_two_mul_theta_sub_eq_zero (rnd := rnd) (p := p) (a := a) (b := b)]
      _ = 0 := by simp

  have I21 : (∫ ω, t21 ω ∂ (ℙ : Measure Ω)) = 0 := by
    calc
      (∫ ω, t21 ω ∂ (ℙ : Measure Ω))
          = ∫ ω, (B * A) * (Real.cos (2 * (rnd.theta p ω - a)) * Real.cos (rnd.theta p ω - b))
              ∂ (ℙ : Measure Ω) := by
              refine MeasureTheory.integral_congr_ae ?_
              filter_upwards with ω
              simp [t21]
              ring
      _ = (B * A) * (∫ ω, Real.cos (2 * (rnd.theta p ω - a)) * Real.cos (rnd.theta p ω - b)
              ∂ (ℙ : Measure Ω)) := by
              simpa using
                (MeasureTheory.integral_const_mul (μ := (ℙ : Measure Ω)) (r := B * A)
                  (f := fun ω => Real.cos (2 * (rnd.theta p ω - a)) * Real.cos (rnd.theta p ω - b)))
      _ = (B * A) * 0 := by
              -- prove the inner integral is `0` by commuting and applying the mixed-frequency lemma
              have hmix :
                  (∫ ω, Real.cos (2 * (rnd.theta p ω - a)) * Real.cos (rnd.theta p ω - b)
                      ∂ (ℙ : Measure Ω)) = 0 := by
                calc
                  (∫ ω, Real.cos (2 * (rnd.theta p ω - a)) * Real.cos (rnd.theta p ω - b)
                      ∂ (ℙ : Measure Ω))
                      =
                      (∫ ω, Real.cos (rnd.theta p ω - b) * Real.cos (2 * (rnd.theta p ω - a))
                        ∂ (ℙ : Measure Ω)) := by
                        refine MeasureTheory.integral_congr_ae ?_
                        filter_upwards with ω
                        ring
                  _ = 0 := by
                        simpa using
                          (integral_cos_theta_sub_mul_cos_two_mul_theta_sub_eq_zero
                            (rnd := rnd) (p := p) (a := b) (b := a))
              simp [hmix]
      _ = 0 := by simp

  have I22 :
      (∫ ω, t22 ω ∂ (ℙ : Measure Ω))
        = (B ^ 2) * ((1 / 2 : ℝ) * Real.cos (2 * (b - a))) := by
    calc
      (∫ ω, t22 ω ∂ (ℙ : Measure Ω))
          = ∫ ω, (B * B) * (Real.cos (2 * (rnd.theta p ω - a)) * Real.cos (2 * (rnd.theta p ω - b)))
              ∂ (ℙ : Measure Ω) := by
              refine MeasureTheory.integral_congr_ae ?_
              filter_upwards with ω
              simp [t22]
              ring
      _ = (B * B) * (∫ ω, Real.cos (2 * (rnd.theta p ω - a)) * Real.cos (2 * (rnd.theta p ω - b))
              ∂ (ℙ : Measure Ω)) := by
              simpa using
                (MeasureTheory.integral_const_mul (μ := (ℙ : Measure Ω)) (r := B * B)
                  (f := fun ω => Real.cos (2 * (rnd.theta p ω - a)) * Real.cos (2 * (rnd.theta p ω - b))))
      _ = (B * B) * ((1 / 2 : ℝ) * Real.cos (2 * (b - a))) := by
              simp [integral_cos_two_mul_theta_sub_mul_cos_two_mul_theta_sub (rnd := rnd) (p := p) (a := a) (b := b)]
      _ = (B ^ 2) * ((1 / 2 : ℝ) * Real.cos (2 * (b - a))) := by
              simp [pow_two, mul_assoc]
  -- assemble and rewrite `b-a` as `-(h₁-h₂)*log p`
  rw [hrewrite, hsum]
  -- substitute the four computed values
  simp [I11, I12, I21, I22]
  -- normalize cosine arguments and coefficients
  have hcos1 : Real.cos (b - a) = Real.cos ((h₁ - h₂) * Real.log p) := by
    have : b - a = -((h₁ - h₂) * Real.log p) := by
      simp [a, b]; ring
    simp [this]
  have hcos2 : Real.cos (2 * (b - a)) = Real.cos (2 * ((h₁ - h₂) * Real.log p)) := by
    have : 2 * (b - a) = -(2 * ((h₁ - h₂) * Real.log p)) := by
      simp [a, b]; ring
    simp [this]
  -- rewrite `A^2` and `B^2`
  -- and finish by ring-like normalization
  -- (we keep `((p : ℝ)⁻¹)^2` as requested by the statement).
  simp [hA, hB, hcos1, hcos2]
  ring_nf

lemma integral_block_term_random_phase_mul_of_ne {p q : ℕ} (hpq : p ≠ q) (h₁ h₂ : ℝ) :
    (∫ ω,
        block_term p (random_phase params rnd p h₁ ω) * block_term q (random_phase params rnd q h₂ ω)
        ∂ (ℙ : Measure Ω))
      = 0 := by
  classical
  -- package each block term as a measurable function of the corresponding phase
  let φ (p : ℕ) (h : ℝ) : ℝ → ℝ :=
    fun x : ℝ =>
      (Real.rpow (p : ℝ) (-(1 / 2 : ℝ))) * Real.cos (x - h * Real.log p)
        + (1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ)) * Real.cos (2 * (x - h * Real.log p))
  have hφ_meas (p : ℕ) (h : ℝ) : Measurable (φ p h) := by
    -- measurability from continuity of cosine and algebraic operations
    have hsub : Measurable fun x : ℝ => x - h * Real.log p := (measurable_id.sub measurable_const)
    have hcos : Measurable fun x : ℝ => Real.cos (x - h * Real.log p) :=
      (Real.continuous_cos.measurable.comp hsub)
    have hcos2 : Measurable fun x : ℝ => Real.cos (2 * (x - h * Real.log p)) := by
      have harg : Measurable fun x : ℝ => (2 : ℝ) * (x - h * Real.log p) := measurable_const.mul hsub
      exact (Real.continuous_cos.measurable.comp harg)
    -- combine (keep the coefficients explicit to avoid `simp` turning `rpow` into `^`)
    have h1 :
        Measurable fun x : ℝ => (Real.rpow (p : ℝ) (-(1 / 2 : ℝ))) * Real.cos (x - h * Real.log p) :=
      measurable_const.mul hcos
    have h2 :
        Measurable fun x : ℝ =>
          (1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ)) * Real.cos (2 * (x - h * Real.log p)) := by
      -- rewrite as a constant multiple of `cos(2*(...))`
      simpa [mul_assoc] using (measurable_const.mul hcos2 : Measurable fun x : ℝ =>
        ((1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ))) * Real.cos (2 * (x - h * Real.log p)))
    simpa [φ] using h1.add h2

  have hcomp (p : ℕ) (h : ℝ) :
      (fun ω : Ω => block_term p (random_phase params rnd p h ω)) = (φ p h) ∘ (rnd.theta p) := by
    funext ω
    -- expand `block_term` through cosine identities
    have hω := congrArg (fun f => f ω)
      (block_term_random_phase_eq (params := params) (rnd := rnd) (p := p) (h := h))
    simpa [φ, Function.comp, mul_assoc, mul_left_comm, mul_comm] using hω

  -- independence of the two phases implies independence of the two block terms
  have hindθ : (rnd.theta p) ⟂ᵢ[(ℙ : Measure Ω)] (rnd.theta q) := rnd.indep.indepFun hpq
  have hind :
      ((fun ω : Ω => block_term p (random_phase params rnd p h₁ ω)) ⟂ᵢ[(ℙ : Measure Ω)]
        (fun ω : Ω => block_term q (random_phase params rnd q h₂ ω))) := by
    -- rewrite as compositions and apply `IndepFun.comp`
    -- (measurability of the composing maps is handled above)
    simpa [hcomp p h₁, hcomp q h₂, Function.comp] using
      (IndepFun.comp hindθ (hφ_meas p h₁) (hφ_meas q h₂))

  -- now factor the expectation of the product
  have hmeas_p :
      AEStronglyMeasurable (fun ω : Ω => block_term p (random_phase params rnd p h₁ ω)) (ℙ : Measure Ω) := by
    -- measurability from the cosine expansion and measurability of `theta`
    have : Measurable (fun ω : Ω => block_term p (random_phase params rnd p h₁ ω)) := by
      -- `block_term_random_phase_eq` reduces to measurable cos-composites
      -- and `rnd.measurable p` supplies measurability of `theta`.
      have hθ : Measurable (rnd.theta p) := rnd.measurable p
      have hcos : Measurable fun ω : Ω => Real.cos (rnd.theta p ω - h₁ * Real.log p) :=
        (Real.continuous_cos.measurable.comp (hθ.sub measurable_const))
      have hcos2 : Measurable fun ω : Ω => Real.cos (2 * (rnd.theta p ω - h₁ * Real.log p)) := by
        have harg : Measurable fun ω : Ω => (2 : ℝ) * (rnd.theta p ω - h₁ * Real.log p) :=
          measurable_const.mul (hθ.sub measurable_const)
        exact (Real.continuous_cos.measurable.comp harg)
      -- finish using the explicit cosine expansion
      have h1 :
          Measurable fun ω : Ω =>
            (Real.rpow (p : ℝ) (-(1 / 2 : ℝ))) * Real.cos (rnd.theta p ω - h₁ * Real.log p) :=
        measurable_const.mul hcos
      have h2 :
          Measurable fun ω : Ω =>
            (1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ))
              * Real.cos (2 * (rnd.theta p ω - h₁ * Real.log p)) := by
        simpa [mul_assoc] using (measurable_const.mul hcos2 : Measurable fun ω : Ω =>
          ((1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ)))
            * Real.cos (2 * (rnd.theta p ω - h₁ * Real.log p)))
      -- rewrite `block_term` as the sum of these two measurable terms
      simpa [block_term_random_phase_eq (params := params) (rnd := rnd) (p := p) (h := h₁),
        mul_assoc, add_assoc] using h1.add h2
    exact this.aestronglyMeasurable

  have hmeas_q :
      AEStronglyMeasurable (fun ω : Ω => block_term q (random_phase params rnd q h₂ ω)) (ℙ : Measure Ω) := by
    have : Measurable (fun ω : Ω => block_term q (random_phase params rnd q h₂ ω)) := by
      have hθ : Measurable (rnd.theta q) := rnd.measurable q
      have hcos : Measurable fun ω : Ω => Real.cos (rnd.theta q ω - h₂ * Real.log q) :=
        (Real.continuous_cos.measurable.comp (hθ.sub measurable_const))
      have hcos2 : Measurable fun ω : Ω => Real.cos (2 * (rnd.theta q ω - h₂ * Real.log q)) := by
        have harg : Measurable fun ω : Ω => (2 : ℝ) * (rnd.theta q ω - h₂ * Real.log q) :=
          measurable_const.mul (hθ.sub measurable_const)
        exact (Real.continuous_cos.measurable.comp harg)
      have h1 :
          Measurable fun ω : Ω =>
            (Real.rpow (q : ℝ) (-(1 / 2 : ℝ))) * Real.cos (rnd.theta q ω - h₂ * Real.log q) :=
        measurable_const.mul hcos
      have h2 :
          Measurable fun ω : Ω =>
            (1 / 2 : ℝ) * Real.rpow (q : ℝ) (-(1 : ℝ))
              * Real.cos (2 * (rnd.theta q ω - h₂ * Real.log q)) := by
        simpa [mul_assoc] using (measurable_const.mul hcos2 : Measurable fun ω : Ω =>
          ((1 / 2 : ℝ) * Real.rpow (q : ℝ) (-(1 : ℝ)))
            * Real.cos (2 * (rnd.theta q ω - h₂ * Real.log q)))
      simpa [block_term_random_phase_eq (params := params) (rnd := rnd) (p := q) (h := h₂),
        mul_assoc, add_assoc] using h1.add h2
    exact this.aestronglyMeasurable

  have hfactor :=
    IndepFun.integral_fun_mul_eq_mul_integral (μ := (ℙ : Measure Ω)) hind hmeas_p hmeas_q
  -- both means are zero
  have hmean_p :
      (∫ ω, block_term p (random_phase params rnd p h₁ ω) ∂ (ℙ : Measure Ω)) = 0 := by
    simpa using (integral_block_term_random_phase (params := params) (rnd := rnd) (p := p) (h := h₁))
  have hmean_q :
      (∫ ω, block_term q (random_phase params rnd q h₂ ω) ∂ (ℙ : Measure Ω)) = 0 := by
    simpa using (integral_block_term_random_phase (params := params) (rnd := rnd) (p := q) (h := h₂))
  -- conclude
  -- `hfactor` gives the product integral as product of integrals
  -- and both integrals vanish.
  simpa [hmean_p, hmean_q] using hfactor

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

lemma norm_block_term_random_phase_le (p : ℕ) (h : ℝ) :
    ∀ ω : Ω,
      ‖block_term p (random_phase params rnd p h ω)‖
        ≤ |Real.rpow (p : ℝ) (-(1 / 2 : ℝ))|
          + |(1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ))| := by
  intro ω
  -- cosine expansion at `ω`
  have hrepr := congrArg (fun f => f ω)
    (block_term_random_phase_eq (params := params) (rnd := rnd) (p := p) (h := h))
  -- bound each term by its coefficient using `|cos| ≤ 1`
  have hA :
      ‖(Real.rpow (p : ℝ) (-(1 / 2 : ℝ))) * Real.cos (rnd.theta p ω - h * Real.log p)‖
        ≤ |Real.rpow (p : ℝ) (-(1 / 2 : ℝ))| := by
    -- `‖c * cos t‖ = |c| * |cos t| ≤ |c|`
    calc
      ‖(Real.rpow (p : ℝ) (-(1 / 2 : ℝ))) * Real.cos (rnd.theta p ω - h * Real.log p)‖
          = |Real.rpow (p : ℝ) (-(1 / 2 : ℝ))| * |Real.cos (rnd.theta p ω - h * Real.log p)| := by
            simp [Real.norm_eq_abs]
      _ ≤ |Real.rpow (p : ℝ) (-(1 / 2 : ℝ))| * (1 : ℝ) := by
            gcongr
            simpa using Real.abs_cos_le_one (rnd.theta p ω - h * Real.log p)
      _ = |Real.rpow (p : ℝ) (-(1 / 2 : ℝ))| := by ring
  have hB :
      ‖(1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ)) * Real.cos (2 * (rnd.theta p ω - h * Real.log p))‖
        ≤ |(1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ))| := by
    -- same bound, with the combined constant in front
    calc
      ‖(1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ))
            * Real.cos (2 * (rnd.theta p ω - h * Real.log p))‖
          = |(1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ))|
              * |Real.cos (2 * (rnd.theta p ω - h * Real.log p))| := by
            simp [Real.norm_eq_abs, abs_mul, mul_assoc]
      _ ≤ |(1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ))| * (1 : ℝ) := by
            gcongr
            simpa using Real.abs_cos_le_one (2 * (rnd.theta p ω - h * Real.log p))
      _ = |(1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ))| := by ring
  -- triangle inequality
  have htri :
      ‖block_term p (random_phase params rnd p h ω)‖
        ≤ ‖(Real.rpow (p : ℝ) (-(1 / 2 : ℝ))) * Real.cos (rnd.theta p ω - h * Real.log p)‖
          + ‖(1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ))
              * Real.cos (2 * (rnd.theta p ω - h * Real.log p))‖ := by
    simpa [hrepr] using
      (norm_add_le
        ((Real.rpow (p : ℝ) (-(1 / 2 : ℝ))) * Real.cos (rnd.theta p ω - h * Real.log p))
        ((1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ))
          * Real.cos (2 * (rnd.theta p ω - h * Real.log p))))
  exact htri.trans (add_le_add hA hB)

lemma integrable_block_term_random_phase_mul (p q : ℕ) (h₁ h₂ : ℝ) :
    Integrable
      (fun ω : Ω =>
        block_term p (random_phase params rnd p h₁ ω) * block_term q (random_phase params rnd q h₂ ω))
      (ℙ : Measure Ω) := by
  -- boundedness gives integrability on a probability space
  refine Integrable.of_bound (μ := (ℙ : Measure Ω)) ?_ (C :=
    (|Real.rpow (p : ℝ) (-(1 / 2 : ℝ))| + |(1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ))|)
      * (|Real.rpow (q : ℝ) (-(1 / 2 : ℝ))| + |(1 / 2 : ℝ) * Real.rpow (q : ℝ) (-(1 : ℝ))|)) ?_
  · -- AE-strong measurability of the product
    have hp : Integrable (fun ω : Ω => block_term p (random_phase params rnd p h₁ ω)) (ℙ : Measure Ω) :=
      integrable_block_term_random_phase (params := params) (rnd := rnd) (p := p) (h := h₁)
    have hq : Integrable (fun ω : Ω => block_term q (random_phase params rnd q h₂ ω)) (ℙ : Measure Ω) :=
      integrable_block_term_random_phase (params := params) (rnd := rnd) (p := q) (h := h₂)
    exact hp.1.mul hq.1
  · filter_upwards with ω
    have hp := norm_block_term_random_phase_le (params := params) (rnd := rnd) (p := p) (h := h₁) ω
    have hq := norm_block_term_random_phase_le (params := params) (rnd := rnd) (p := q) (h := h₂) ω
    have hmul :
        ‖block_term p (random_phase params rnd p h₁ ω) *
            block_term q (random_phase params rnd q h₂ ω)‖
          ≤
          ‖block_term p (random_phase params rnd p h₁ ω)‖
            * ‖block_term q (random_phase params rnd q h₂ ω)‖ := by
      simp
    have hmul' :
        ‖block_term p (random_phase params rnd p h₁ ω)‖
            * ‖block_term q (random_phase params rnd q h₂ ω)‖
          ≤
          (|Real.rpow (p : ℝ) (-(1 / 2 : ℝ))| + |(1 / 2 : ℝ) * Real.rpow (p : ℝ) (-(1 : ℝ))|)
            * (|Real.rpow (q : ℝ) (-(1 / 2 : ℝ))| + |(1 / 2 : ℝ) * Real.rpow (q : ℝ) (-(1 : ℝ))|) := by
      exact mul_le_mul hp hq (by positivity) (by positivity)
    exact hmul.trans hmul'

lemma integral_Y_rand_k_mul (k : ℕ) (h₁ h₂ : ℝ) :
    (∫ ω,
        Y_rand_k (params := params) rnd k h₁ ω * Y_rand_k (params := params) rnd k h₂ ω
        ∂ (ℙ : Measure Ω))
      =
      ∑ p ∈ P_k params k,
        ((1 / 2 : ℝ) * ((p : ℝ)⁻¹) * Real.cos ((h₁ - h₂) * Real.log p)
          + (1 / 8 : ℝ) * ((p : ℝ)⁻¹) ^ 2 * Real.cos (2 * ((h₁ - h₂) * Real.log p))) := by
  classical
  -- abbreviate the block terms
  let X₁ : ℕ → Ω → ℝ := fun p ω => block_term p (random_phase params rnd p h₁ ω)
  let X₂ : ℕ → Ω → ℝ := fun p ω => block_term p (random_phase params rnd p h₂ ω)
  have hInt :
      (∫ ω,
          Y_rand_k (params := params) rnd k h₁ ω * Y_rand_k (params := params) rnd k h₂ ω
          ∂ (ℙ : Measure Ω))
        =
        ∫ ω,
          (∑ p ∈ P_k params k, X₁ p ω) * (∑ q ∈ P_k params k, X₂ q ω)
          ∂ (ℙ : Measure Ω) := by
    simp [Y_rand_k, X₁, X₂]
  rw [hInt]
  -- expand into a double finite sum and swap integral/sum
  have hmul :
      (fun ω : Ω => (∑ p ∈ P_k params k, X₁ p ω) * (∑ q ∈ P_k params k, X₂ q ω))
        =
        fun ω : Ω => ∑ p ∈ P_k params k, ∑ q ∈ P_k params k, (X₁ p ω) * (X₂ q ω) := by
    funext ω
    simpa using
      (Finset.sum_mul_sum (P_k params k) (P_k params k) (fun p : ℕ => X₁ p ω) (fun q : ℕ => X₂ q ω))
  rw [MeasureTheory.integral_congr_ae (ae_of_all _ (fun ω => by
    simpa using congrArg (fun f => f ω) hmul))]
  -- integrability of each summand (bounded product of block terms)
  have hIntPQ :
      ∀ p ∈ P_k params k, ∀ q ∈ P_k params k,
        Integrable (fun ω : Ω => (X₁ p ω) * (X₂ q ω)) (ℙ : Measure Ω) := by
    intro p hp q hq
    simpa [X₁, X₂] using
      (integrable_block_term_random_phase_mul (params := params) (rnd := rnd) (p := p) (q := q) (h₁ := h₁)
        (h₂ := h₂))

  have hswap1 :
      (∫ ω : Ω, ∑ p ∈ P_k params k, ∑ q ∈ P_k params k, X₁ p ω * X₂ q ω ∂ (ℙ : Measure Ω))
        =
        ∑ p ∈ P_k params k,
          ∫ ω : Ω, ∑ q ∈ P_k params k, X₁ p ω * X₂ q ω ∂ (ℙ : Measure Ω) := by
    refine MeasureTheory.integral_finset_sum (μ := (ℙ : Measure Ω)) (s := P_k params k)
      (f := fun p ω => ∑ q ∈ P_k params k, X₁ p ω * X₂ q ω) ?_
    intro p hp
    -- inner sum integrable by `integral_finset_sum`
    refine (MeasureTheory.integrable_finset_sum (μ := (ℙ : Measure Ω)) (s := P_k params k)
      (f := fun q ω => X₁ p ω * X₂ q ω) ?_)  -- gives Integrable of the sum
    intro q hq
    exact hIntPQ p hp q hq

  rw [hswap1]
  -- swap the second sum
  have hswap2 :
      ∀ p ∈ P_k params k,
        (∫ ω : Ω, ∑ q ∈ P_k params k, X₁ p ω * X₂ q ω ∂ (ℙ : Measure Ω))
          =
          ∑ q ∈ P_k params k, ∫ ω : Ω, X₁ p ω * X₂ q ω ∂ (ℙ : Measure Ω) := by
    intro p hp
    refine MeasureTheory.integral_finset_sum (μ := (ℙ : Measure Ω)) (s := P_k params k)
      (f := fun q ω => X₁ p ω * X₂ q ω) ?_
    intro q hq
    exact hIntPQ p hp q hq
  -- rewrite each outer summand using `hswap2`
  have hswap2' :
      (∑ p ∈ P_k params k,
          ∫ ω : Ω, ∑ q ∈ P_k params k, X₁ p ω * X₂ q ω ∂ (ℙ : Measure Ω))
        =
        ∑ p ∈ P_k params k,
          ∑ q ∈ P_k params k, ∫ ω : Ω, X₁ p ω * X₂ q ω ∂ (ℙ : Measure Ω) := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    simpa using hswap2 p hp
  rw [hswap2']

  -- kill the off-diagonal terms using independence/centering
  have hdiag :
      ∀ p ∈ P_k params k,
        (∑ q ∈ P_k params k, ∫ ω : Ω, X₁ p ω * X₂ q ω ∂ (ℙ : Measure Ω))
          =
          ∫ ω : Ω, X₁ p ω * X₂ p ω ∂ (ℙ : Measure Ω) := by
    intro p hp
    refine Finset.sum_eq_single_of_mem p hp (fun q hq hqp => ?_)
    -- off-diagonal integral vanishes
    have : (∫ ω : Ω, X₁ p ω * X₂ q ω ∂ (ℙ : Measure Ω)) = 0 := by
      simpa [X₁, X₂] using
        (integral_block_term_random_phase_mul_of_ne (params := params) (rnd := rnd) (p := p) (q := q)
          (hpq := hqp.symm) (h₁ := h₁) (h₂ := h₂))
    simp [this]

  -- apply `hdiag` to collapse the double sum
  have hdiag' :
      (∑ p ∈ P_k params k,
          ∑ q ∈ P_k params k, ∫ ω : Ω, X₁ p ω * X₂ q ω ∂ (ℙ : Measure Ω))
        =
        ∑ p ∈ P_k params k, ∫ ω : Ω, X₁ p ω * X₂ p ω ∂ (ℙ : Measure Ω) := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    simpa using hdiag p hp
  rw [hdiag']

  -- finally insert the diagonal covariance formula
  refine Finset.sum_congr rfl (fun p hp => ?_)
  -- `p` is prime hence nonzero
  have hp0 : p ≠ 0 := ((Finset.mem_filter.1 hp).2).1.ne_zero
  -- unfold `X₁`, `X₂` and use the same-prime lemma
  simpa [X₁, X₂, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
    using (integral_block_term_random_phase_mul (params := params) (rnd := rnd) (p := p) hp0 h₁ h₂)

/-!
### Covariance matrices for the random prime-phase blocks

`Sigma_k` in `ZetaSpinGlassDefs` records the *leading* covariance kernel (the `p⁻¹` term).  The
random model `Y_rand_k` also contains a smaller `p⁻²` contribution coming from the `z^2` term in
`block_term`.  We package this as a correction matrix `Sigma2_k`, so that the covariance matrix is
exactly `Sigma_k + Sigma2_k`.
-/

variable {m : ℕ} (pts : ConfigPoints m)

/-- The `p⁻²` correction to the covariance kernel coming from the quadratic term in `block_term`. -/
noncomputable def Sigma2_k (k : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun i j =>
    let h_i := pts.val i
    let h_j := pts.val j
    ∑ p ∈ P_k params k,
      (1 / 8 : ℝ) * ((p : ℝ)⁻¹) ^ 2 * Real.cos (2 * ((h_i - h_j) * Real.log p))

lemma covarianceMatrix_Y_rand_k_eq (k : ℕ) :
    ProbabilityTheory.covarianceMatrix
        (X := fun ω : Ω => fun i : Fin (m + 1) => Y_rand_k (params := params) rnd k (pts.val i) ω)
        (ℙ : Measure Ω)
      =
      Sigma_k params pts k + Sigma2_k (params := params) pts k := by
  classical
  ext i j
  -- mean-zero simplifies the covariance matrix to an expectation of products
  have hmean :
      ∀ i : Fin (m + 1),
        (∫ ω, Y_rand_k (params := params) rnd k (pts.val i) ω ∂ (ℙ : Measure Ω)) = 0 := by
    intro i
    simpa [ZetaSpinGlass.mean] using (mean_Y_rand_k (params := params) (rnd := rnd) (k := k) (h := pts.val i))
  -- unfold covariance and rewrite with `integral_Y_rand_k_mul`
  simp [ProbabilityTheory.covarianceMatrix, hmean, Matrix.add_apply, Sigma_k, Sigma2_k,
    integral_Y_rand_k_mul (params := params) (rnd := rnd) (k := k) (h₁ := pts.val i) (h₂ := pts.val j),
    Finset.sum_add_distrib, mul_assoc, mul_comm]

lemma abs_Sigma2_k_le (k : ℕ) (i j : Fin (m + 1)) :
    |Sigma2_k (params := params) pts k i j|
      ≤ ∑ p ∈ P_k params k, (1 / 8 : ℝ) * ((p : ℝ)⁻¹) ^ 2 := by
  classical
  -- expand and use `|cos| ≤ 1`
  dsimp [Sigma2_k]
  -- apply `abs_sum_le_sum_abs`, then bound each summand by dropping the cosine
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum (fun p hp => ?_)
  set c : ℝ := (1 / 8 : ℝ) * ((p : ℝ)⁻¹) ^ 2
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hcos : |Real.cos (2 * ((pts.val i - pts.val j) * Real.log p))| ≤ (1 : ℝ) := by
    simpa using Real.abs_cos_le_one (2 * ((pts.val i - pts.val j) * Real.log p))
  calc
    |(1 / 8 : ℝ) * ((p : ℝ)⁻¹) ^ 2 * Real.cos (2 * ((pts.val i - pts.val j) * Real.log p))|
        = |c * Real.cos (2 * ((pts.val i - pts.val j) * Real.log p))| := by
            simp [c, mul_assoc]
    _ = |c| * |Real.cos (2 * ((pts.val i - pts.val j) * Real.log p))| := by
          simp [abs_mul]
    _ = c * |Real.cos (2 * ((pts.val i - pts.val j) * Real.log p))| := by
          simp [abs_of_nonneg hc]
    _ ≤ c * (1 : ℝ) := by
          gcongr
    _ = c := by ring
    _ = (1 / 8 : ℝ) * ((p : ℝ)⁻¹) ^ 2 := by
          simp [c]

/-!
#### A more general “index family” covariance statement

For many downstream uses (blockwise Lindeberg, Guerra interpolation, etc.) it is convenient to
package the covariance computation for an arbitrary finite index type `ι` and a label function
`h : ι → ℝ`.  The `ConfigPoints` version above is the specialization `ι = Fin (m+1)` and
`h = pts.val`.
-/

section GeneralIndex

variable {ι : Type*} [Fintype ι] (h : ι → ℝ)

noncomputable def SigmaLead_k (k : ℕ) : Matrix ι ι ℝ :=
  fun i j =>
    ∑ p ∈ P_k params k, (1 / 2 : ℝ) * ((p : ℝ)⁻¹) * Real.cos ((h i - h j) * Real.log p)

noncomputable def Sigma2_k_fun (k : ℕ) : Matrix ι ι ℝ :=
  fun i j =>
    ∑ p ∈ P_k params k, (1 / 8 : ℝ) * ((p : ℝ)⁻¹) ^ 2 * Real.cos (2 * ((h i - h j) * Real.log p))

lemma covarianceMatrix_Y_rand_k_fun_eq (k : ℕ) :
    ProbabilityTheory.covarianceMatrix
        (X := fun ω : Ω => fun i : ι => Y_rand_k (params := params) rnd k (h i) ω)
        (ℙ : Measure Ω)
      =
      SigmaLead_k (params := params) (h := h) k + Sigma2_k_fun (params := params) (h := h) k := by
  classical
  ext i j
  have hmean :
      ∀ i : ι, (∫ ω, Y_rand_k (params := params) rnd k (h i) ω ∂ (ℙ : Measure Ω)) = 0 := by
    intro i
    simpa [ZetaSpinGlass.mean] using (mean_Y_rand_k (params := params) (rnd := rnd) (k := k) (h := h i))
  simp [ProbabilityTheory.covarianceMatrix, hmean, Matrix.add_apply, SigmaLead_k, Sigma2_k_fun,
    integral_Y_rand_k_mul (params := params) (rnd := rnd) (k := k) (h₁ := h i) (h₂ := h j),
    Finset.sum_add_distrib, mul_assoc, mul_left_comm, mul_comm]

end GeneralIndex

end

end ZetaSpinGlass
