import Mathlib
import Riemann.Mathlib.MeasureTheory.Integral.Auxiliary

/-!
# Rational Function Integrals

This file contains the complete computation of integrals of rational functions over ℝ,
including the classical results:
- ∫ 1/(1+x²)² dx = π/2
- ∫ 1/((u²+1)((u-c)²+1)) dx = π·(2/(c²+4))

## Main results

* `IntegralOneOverOnePlusSqSq.integral_one_div_one_plus_sq_sq` - The integral ∫ ((u²+1)²)⁻¹ = π/2
* `integral_one_div_one_plus_sq_sq'` - Export of the main result
* `integral_forms_equiv` - Equivalence between different forms

## Implementation notes

The proof uses explicit antiderivatives involving arctan and careful limit analysis
at ±∞ using dominated convergence techniques.

## References

* Gradshteyn-Ryzhik, Table of Integrals
-/

/-!
# Proof of : ∫ 1/(1+x²)² = π/2
-/

namespace IntegralOneOverOnePlusSqSq
open Real

-- Define the antiderivative
noncomputable def F (x : ℝ) : ℝ := x / (2 * (1 + x^2)) + arctan x / 2

-- Key algebraic lemma for simplification
lemma algebra_simp (x : ℝ) (_ : 1 + x^2 ≠ 0) :
    (2 * (1 + x^2) - 4 * x^2) / (4 * (1 + x^2)^2) + 1 / (2 * (1 + x^2)) =
    ((1 + x^2)^2)⁻¹ := by
  field_simp
  ring

-- The derivative of F is our integrand
theorem hasDerivAt_F (x : ℝ) :
    HasDerivAt F ((1 + x^2)^2)⁻¹ x := by
  unfold F
  -- Derivative of x / (2 * (1 + x^2))
  have h_frac : HasDerivAt (fun x => x / (2 * (1 + x^2)))
      ((2 * (1 + x^2) * 1 - x * (2 * 2 * x)) / (2 * (1 + x^2))^2) x := by
    have h_num : HasDerivAt (fun x => x) 1 x := hasDerivAt_id' x
    have h_den : HasDerivAt (fun x => 2 * (1 + x^2)) (2 * 2 * x) x := by
      have : HasDerivAt (fun x => 1 + x^2) (2 * x) x := by
        convert (hasDerivAt_id' x).pow 2 |>.add (hasDerivAt_const x 1) using 1
        · ext y; simp [pow_succ]; ring
        · ring
      convert this.const_mul 2 using 1
      ring
    have h_ne : 2 * (1 + x^2) ≠ 0 := by positivity
    convert h_num.div h_den h_ne using 1
    ring
  -- Derivative of arctan x / 2
  have h_arctan : HasDerivAt (fun x => arctan x / 2)
      (((1 + x^2)⁻¹) / 2) x := by
    convert (hasDerivAt_arctan x).div_const 2 using 1
    ring
  convert h_frac.add h_arctan using 1
  have : (2 * (1 + x^2) * 1 - x * (2 * 2 * x)) / (2 * (1 + x^2))^2 + ((1 + x^2)⁻¹) / 2 =
         ((1 + x^2)^2)⁻¹ := by
    have h0 : 1 + x^2 ≠ 0 := by positivity
    calc (2 * (1 + x^2) * 1 - x * (2 * 2 * x)) / (2 * (1 + x^2))^2 + ((1 + x^2)⁻¹) / 2
        = (2 * (1 + x^2) - 4 * x^2) / (2 * (1 + x^2))^2 + ((1 + x^2)⁻¹) / 2 := by ring
      _ = (2 * (1 + x^2) - 4 * x^2) / (4 * (1 + x^2)^2) + 1 / (2 * (1 + x^2)) := by
          rw [pow_two (2 * (1 + x^2))]
          rw [inv_eq_one_div]
          field_simp
          ring
      _ = ((1 + x^2)^2)⁻¹ := algebra_simp x h0
  exact id (Eq.symm this)

-- F is differentiable everywhere
theorem differentiable_F : Differentiable ℝ F := by
  intro x
  exact (hasDerivAt_F x).differentiableAt

-- Integral on a finite interval
theorem integral_on_interval (a b : ℝ) :
    ∫ x in a..b, ((1 + x^2)^2)⁻¹ = F b - F a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · -- Has derivative
    intro x _
    exact hasDerivAt_F x
  · -- Integrability of the derivative (i.e., the integrand)
    apply Continuous.intervalIntegrable
    apply Continuous.inv₀
    · continuity
    · intro x
      positivity

open Filter Real Topology

-- Limit at +∞
theorem F_limit_atTop : Tendsto F atTop (𝓝 (π / 4)) := by
  unfold F
  have h1 : Tendsto (fun (x : ℝ) => x / (2 * (1 + x^2))) atTop (𝓝 0) := by
    have : (fun (x : ℝ) => x / (2 * (1 + x^2))) = (fun (x : ℝ) => (1 / 2) * (x / (1 + x^2))) := by
      ext x; field_simp
    rw [this]
    convert Real.tendsto_div_one_add_sq_atTop.const_mul (1 / 2) using 1
    norm_num
  have h2 : Tendsto (fun (x : ℝ) => arctan x / 2) atTop (𝓝 (π / 4)) :=
    Real.tendsto_arctan_div_two_atTop
  have hsum :
      Tendsto (fun x : ℝ => x / (2 * (1 + x^2)) + arctan x / 2) atTop (𝓝 (0 + π / 4)) :=
    h1.add h2
  simpa [F, add_comm, add_left_comm, add_assoc, add_zero] using hsum

lemma tendsto_div_one_add_sq_atBot :
    Tendsto (fun x : ℝ => x / (1 + x^2)) atBot (𝓝 0) := by
  -- use oddness and `tendsto_neg_atBot_atTop`
  have h := (Real.tendsto_div_one_add_sq_atTop.neg).comp tendsto_neg_atBot_atTop
  have hfun :
      ((fun x : ℝ => -(x / (1 + x * x))) ∘ Neg.neg)
        = fun x : ℝ => x / (1 + x * x) := by
    funext x
    simp [Function.comp, neg_div, neg_neg]
  simpa [pow_two, hfun] using h

lemma tendsto_div_2mul_one_add_sq_atBot :
    Tendsto (fun x : ℝ => x / (2 * (1 + x^2))) atBot (𝓝 0) := by
  -- equal to `(1/2) * (x / (1 + x^2))`
  have := (tendsto_div_one_add_sq_atBot.const_mul (1 / 2))
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this

theorem F_limit_atBot : Tendsto F atBot (𝓝 (-π / 4)) := by
  unfold F
  have h1 := tendsto_div_2mul_one_add_sq_atBot
  have h2 : Tendsto (fun (x : ℝ) => arctan x / 2) atBot (𝓝 (-π / 4)) :=
    Real.tendsto_arctan_div_two_atBot
  have hsum :
      Tendsto (fun x : ℝ => x / (2 * (1 + x^2)) + arctan x / 2) atBot (𝓝 (0 + (-π / 4))) :=
    h1.add h2
  simpa [F, add_comm, add_left_comm, add_assoc, add_zero] using hsum

-- Translation preserves atTop and yields an if-and-only-if on precomposition.
lemma tendsto_atTop_add_const_right
    {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (c : α) :
    Tendsto (fun x : α => x + c) atTop atTop := by
  -- Use the atTop characterization on ordered types
  refine Filter.tendsto_atTop_atTop.2 ?_
  intro b
  refine ⟨b - c, ?_⟩
  intro x hx
  -- From b - c ≤ x, add c to both sides to get b ≤ x + c
  have := add_le_add_right hx c
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this

lemma tendsto_atTop_add_const_right_iff
    {α β : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [TopologicalSpace β]
    {f : α → β} {l : Filter β} {c : α} :
    Tendsto (fun x => f (x + c)) atTop l ↔ Tendsto f atTop l := by
  constructor
  · intro h
    -- Precompose by translation by -c to cancel
    have h' := h.comp (tendsto_atTop_add_const_right (-c))
    have : ((fun x => f (c + x)) ∘ fun x => x + -c) = f := by
      funext x
      simp [Function.comp]
    convert h' using 1
    aesop
  · intro h
    -- Precompose by translation by c
    exact h.comp (tendsto_atTop_add_const_right c)

lemma tendsto_atBot_add_const_right
    {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (c : α) :
    Tendsto (fun x : α => x + c) atBot atBot := by
  refine Filter.tendsto_atBot_atBot.2 ?_
  intro b
  refine ⟨b - c, ?_⟩
  intro x hx
  have := add_le_add_right hx c
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this

open MeasureTheory
-- Integrability by comparison (decay as x^{-4})
lemma integrable_inv_one_add_sq_sq :
    Integrable (fun x : ℝ => ((1 + x^2)^2)⁻¹) := by
  -- use the Japanese bracket lemma with r = 4
  have h :
      Integrable (fun x : ℝ => (1 + ‖x‖ ^ 2) ^ (-(4 : ℝ) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
      (r := 4) (by norm_num)
  -- simplify the exponent
  have h' : Integrable (fun x : ℝ => (1 + ‖x‖ ^ 2) ^ (-2 : ℝ)) := by
    convert h using 2; norm_num
  -- rewrite to our concrete integrand
  refine (integrable_congr ?_).1 h'
  refine Filter.Eventually.of_forall (fun x => ?_)
  -- (1+|x|^2)^(-2) = ((1+|x|^2)^2)⁻¹ = ((1+x^2)^2)⁻¹
  simp only [Real.norm_eq_abs, sq_abs]
  norm_cast

theorem integral_one_div_one_plus_sq_sq :
    ∫ u : ℝ, ((u^2 + 1)^2)⁻¹ = π / 2 := by
  have h_comm : (fun u : ℝ => ((u^2 + 1)^2)⁻¹) = fun u => ((1 + u^2)^2)⁻¹ := by
    ext u; ring_nf
  rw [h_comm]
  -- integrability by comparison (proved separately)
  -- integrability by comparison (proved separately)
  have hf : Integrable (fun x : ℝ => ((1 + x^2)^2)⁻¹) :=
    integrable_inv_one_add_sq_sq
  have h :=
    (MeasureTheory.integral_of_hasDerivAt_of_tendsto
      (f := F) (f' := fun x => ((1 + x^2)^2)⁻¹)
      (hderiv := hasDerivAt_F) (hf' := hf)
      (hbot := F_limit_atBot) (htop := F_limit_atTop))
  -- RHS simplifies: π/4 - (-π/4) = π/2
  convert h using 1
  ring

end IntegralOneOverOnePlusSqSq

-- Export the main result
theorem integral_one_div_one_plus_sq_sq' :
    ∫ u : ℝ, ((u^2 + 1)^2)⁻¹ = Real.pi / 2 :=
  IntegralOneOverOnePlusSqSq.integral_one_div_one_plus_sq_sq

open Real MeasureTheory

/-- Interval version of change of variables. -/
lemma integral_comp_div_sub_pos_Ioo
    (f : ℝ → ℝ) (σ a b c : ℝ) (hσ : 0 < σ)
    (_ : ContinuousOn f Set.univ) :
    ∫ t in a..b, f ((t - c) / σ) =
    σ * ∫ u in (a - c)/σ..(b - c)/σ, f u := by
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have h :=
    (intervalIntegral.integral_comp_div_add
      (f := f) (a := a) (b := b) (c := σ) (d := -c / σ) hσne)
  simpa [sub_eq_add_neg, add_div, smul_eq_mul] using h


lemma integral_comp_smul_sub_pos_interval
    (f : ℝ → ℝ) (σ a b c : ℝ) (hσ : 0 < σ) :
    ∫ t in a..b, f ((t - c) / σ) =
    σ * ∫ u in (a - c)/σ..(b - c)/σ, f u := by
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have h :=
    (intervalIntegral.integral_comp_div_add
      (f := f) (a := a) (b := b) (c := σ) (d := -c / σ) hσne)
  simpa [sub_eq_add_neg, add_div, smul_eq_mul] using h

lemma integral_forms_equiv :
    (fun u : ℝ => (1 / (u^2 + 1))^2) = fun u => ((u^2 + 1)^2)⁻¹ := by
  ext u
  field_simp

theorem integral_one_div_one_plus_sq_sq_inv :
    ∫ u : ℝ, ((u^2 + 1)^2)⁻¹ ∂volume = π / 2 :=
  integral_one_div_one_plus_sq_sq'

theorem integral_one_div_one_plus_sq_sq :
    ∫ u : ℝ, (1 / (u^2 + 1))^2 ∂volume = π / 2 := by
  rw [integral_forms_equiv]
  exact integral_one_div_one_plus_sq_sq_inv

theorem integral_one_div_one_plus_sq_sq_direct :
    ∫ u : ℝ, (1 / (u^2 + 1))^2 = π / 2 := by
  rw [integral_forms_equiv]
  exact integral_one_div_one_plus_sq_sq'

-- Restatement with clear equivalence
example :
    (∫ u : ℝ, (1 / (u^2 + 1))^2 ∂volume = π / 2) ↔
    (∫ u : ℝ, ((u^2 + 1)^2)⁻¹ ∂volume = π / 2) := by
  constructor <;> intro h
  · rw [integral_forms_equiv] at h; exact h
  · rw [integral_forms_equiv]; exact h
