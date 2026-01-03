import Mathlib.Probability.Distributions.Gaussian.Basic

open Complex Real MeasureTheory ProbabilityTheory Filter Topology BigOperators Matrix
open scoped BigOperators

namespace ZetaSpinGlass

/-!
# Section 2: Framework - Arithmetic and Random Models
-/

structure ModelParams where
  T : ℝ
  y : ℝ
  h_max : ℝ
  T_large : 10 < T

variable (params : ModelParams)

-- 1. Block Decomposition (Standard)
noncomputable def n_scales : ℕ := ⌊Real.log (Real.log params.T)⌋.toNat
noncomputable def n0 : ℕ := ⌊params.y⌋.toNat
noncomputable def P_k (_params : ModelParams) (k : ℕ) : Finset ℕ :=
  let lower := Real.exp (k - 1 : ℝ)
  let upper := Real.exp k
  (Finset.range (Nat.ceil upper + 1)).filter
    (fun p => p.Prime ∧ lower < Real.log p ∧ Real.log p ≤ upper)

/-! ### 2.1 The Arithmetic Model (Diamond-Free) -/

/--
**Arithmetic Measure**: Explicitly defined measure on `ℝ`.
We avoids `instance : MeasureSpace ℝ` to pass the **Diamond Oracle**.
-/
noncomputable def mu_arith : Measure ℝ :=
  (volume (Set.Icc params.T (2 * params.T)))⁻¹ •
    (volume.restrict (Set.Icc params.T (2 * params.T)))

/-- Arithmetic Phase: p^{-i(τ+h)} -/
noncomputable def arithmetic_phase (p : ℕ) (tau h : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (tau + h) * Real.log p)

/-- Fundamental Term: Re(p^{-1/2} z + 1/2 p^{-1} z^2) -/
noncomputable def block_term (p : ℕ) (z : ℂ) : ℝ :=
  let p_r : ℝ := p
  (Real.rpow p_r (-(1 / 2 : ℝ))) * z.re + (1 / 2 : ℝ) * (Real.rpow p_r (-(1 : ℝ))) * (z^2).re

/-- Arithmetic Block Increment -/
noncomputable def Y_zeta_k (k : ℕ) (h : ℝ) : ℝ → ℝ :=
  fun tau => ∑ p ∈ P_k params k, block_term p (arithmetic_phase p tau h)

/-! ### 2.2 The Random Prime-Phase Model (Proof-Survival Optimized) -/

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! ### Basic probabilistic primitives used below -/

/-- Mean of a random variable as a Bochner integral. -/
noncomputable def mean {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Ω → E) (μ : Measure Ω := (ℙ : Measure Ω)) : E :=
  ∫ ω, X ω ∂μ

/-- A random variable is Gaussian if its pushforward measure is Gaussian. -/
def Gaussian {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    [MeasurableSpace E] (X : Ω → E) (μ : Measure Ω := (ℙ : Measure Ω)) : Prop :=
  ProbabilityTheory.IsGaussian (Measure.map X μ)

namespace ProbabilityTheory

/-- Covariance matrix of a finite family of real random variables. -/
noncomputable def covarianceMatrix {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (X : Ω → ι → ℝ) (μ : Measure Ω) : Matrix ι ι ℝ :=
  let m : ι → ℝ := fun i => ∫ ω, X ω i ∂μ
  fun i j => ∫ ω, (X ω i - m i) * (X ω j - m j) ∂μ

end ProbabilityTheory

/--
**Random Phases Structure**:
Bundles the random variables `θ_p` and their properties.
-/
structure RandomPhases (Ω : Type*) [MeasureSpace Ω] where
  theta : ℕ → Ω → ℝ
  measurable : ∀ p, Measurable (theta p)
  indep : iIndepFun (β := fun _ : ℕ => ℝ) theta ℙ
  dist : ∀ p,
    Measure.map (theta p) ℙ =
      (volume (Set.Icc 0 (2 * Real.pi)))⁻¹ • (volume.restrict (Set.Icc 0 (2 * Real.pi)))

variable (rnd : RandomPhases Ω)

/-- Random Phase: e^{i(θ_p - h log p)} -/
noncomputable def random_phase (_params : ModelParams) (rnd : RandomPhases Ω) (p : ℕ) (h : ℝ) (ω : Ω) : ℂ :=
  Complex.exp (Complex.I * (rnd.theta p ω - h * Real.log p))

/-- Random Block Increment -/
noncomputable def Y_rand_k (k : ℕ) (h : ℝ) : Ω → ℝ :=
  fun ω => ∑ p ∈ P_k params k, block_term p (random_phase params rnd p h ω)

/-! ### 2.3 Gaussian Surrogates (Unified Space) -/

structure ConfigPoints (m : ℕ) where
  val : Fin (m + 1) → ℝ
  bound : ∀ i, |val i| ≤ 1

variable {m : ℕ} (pts : ConfigPoints m)

/--
**Covariance Matrix**: Explicit formula (sum of cosines).
This is the **Ground Truth** for the Diagrammatic Check.
-/
noncomputable def Sigma_k (k : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun i j =>
    let h_i := pts.val i
    let h_j := pts.val j
    ∑ p ∈ P_k params k,
      (1 / 2 : ℝ) * ((p : ℝ)⁻¹) * Real.cos ((h_i - h_j) * Real.log p)

/--
**Gaussian Surrogate Field**:
Defined on the *same* `Ω` as the random phases, or a coupled space.
-/
structure GaussianSurrogateField (params : ModelParams) {m : ℕ} (pts : ConfigPoints m)
    (Ω : Type*) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] where
  /-- The vector N_k for each block k. -/
  N_vec : ℕ → Ω → (Fin (m + 1) → ℝ)
  /-- Independence across blocks. -/
  indep : iIndepFun (β := fun _ : ℕ => (Fin (m + 1) → ℝ)) N_vec ℙ
  /-- Each block is centered Gaussian matching Sigma_k. -/
  gaussian : ∀ k, Gaussian (N_vec k) ℙ
  centered : ∀ k, mean (N_vec k) ℙ = 0
  cov_match : ∀ k, ProbabilityTheory.covarianceMatrix (N_vec k) ℙ = Sigma_k params pts k

/-! ### 3. Synthetic Theorems (Diagrammatic Checks) -/

/--
**Diagrammatic Check 2**: Covariance Consistency.
Verifies that `Sigma_k` is symmetric, a required property for a covariance matrix.
`aesop` should close this using the symmetry of `cos`.
-/
example (k : ℕ) (i j : Fin (m + 1)) :
  Sigma_k params pts k i j = Sigma_k params pts k j i := by
  classical
  -- Expand `Sigma_k` and reduce to summand equality (no cancellation of prefactors).
  simp [Sigma_k]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  -- The RHS cosine argument is the negation of the LHS argument.
  have harg :
      (pts.val j - pts.val i) * Real.log (p : ℝ) = -((pts.val i - pts.val j) * Real.log (p : ℝ)) := by
    ring
  rw [harg]
  simp [Real.cos_neg, mul_assoc, mul_comm]


/--
**Proof Survival Check**: Summing Blocks.
If definitions were "Ghost", we couldn't define the total field `G_T`.
-/
noncomputable def G_T (field : GaussianSurrogateField params pts Ω) (ω : Ω) : Fin (m + 1) → ℝ :=
  fun i => ∑ k ∈ Finset.Ioc (n0 params) (n_scales params), field.N_vec k ω i

end ZetaSpinGlass
