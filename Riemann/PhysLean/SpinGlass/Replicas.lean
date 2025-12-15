import Riemann.PhysLean.SpinGlass.SKModel
import Riemann.PhysLean.SpinGlass.GuerraBound
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory ProbabilityTheory Real BigOperators SpinGlass SpinGlass.Algebra
open PhysLean.Probability.GaussianIBP

namespace SpinGlass

/-!
# Section 1.4: General Replica Calculus and Latala's Argument

To prove concentration, we must manage functions of `n` replicas.
Differentiation increases the number of replicas by 2.

**Terminology:** this file implements the **interpolation / smart path** machinery
(Talagrand Vol. I, §§1.3–1.4). It is *not* the cavity method (Talagrand Vol. I, §1.6),
which is an induction on `N`.
-/

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable (N : ℕ) (β h q : ℝ)
variable (sk : SKDisorder (Ω := Ω) N β h) (sim : SimpleDisorder (Ω := Ω) N β q)

section ReplicaCalculus

variable (n : ℕ)

/-- The space of `n` replicas: (Fin n → Config N). -/
abbrev ReplicaSpace := Fin n → Config N

/-- A function of `n` replicas. -/
abbrev ReplicaFun := ReplicaSpace N n → ℝ

/-- A generic two-replica interaction kernel `U(σ,τ)` (Talagrand’s `U_{ℓ,ℓ'}`). -/
abbrev InteractionKernel := Config N → Config N → ℝ

/--
Interpolated Hamiltonian (Guerra):
\[
H_t = \sqrt{t}\,U + \sqrt{1-t}\,V + H_{\text{field}}.
\]

The external field term uses the **magnetization-dependent** energy
`magnetic_field_vector` (not a constant shift).
-/
noncomputable def H_gauss (t : ℝ) : Ω → EnergySpace N :=
  fun w =>
    (Real.sqrt t) • sk.U w
      + (Real.sqrt (1 - t)) • sim.V w

noncomputable def H_field : EnergySpace N :=
  magnetic_field_vector (N := N) h

noncomputable def H_t (t : ℝ) : Ω → EnergySpace N :=
  fun w =>
    H_gauss (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w
      + H_field (N := N) (h := h)

/--
**Equation (1.17)**: The Gibbs average of a function of `n` replicas.
⟨f⟩ = (1/Z^n) ∑_{σ^1...σ^n} f(σ) exp(-∑ H(σ^l))
-/
noncomputable def gibbs_average_n (t : ℝ) (f : ReplicaFun N n) : Ω → ℝ :=
  fun w =>
    let H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w
    ∑ σs : ReplicaSpace N n, f σs * ∏ l, gibbs_pmf N H (σs l)

/-- Expected Gibbs average: ν_t(f) = E[ ⟨f⟩_t ]. -/
noncomputable def nu (t : ℝ) (f : ReplicaFun N n) : ℝ :=
  ∫ w, gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w ∂ℙ

/-- Lift a function of `n` replicas to `n + k` replicas by ignoring the last `k`. -/
def liftReplicaFun (k : ℕ) (f : ReplicaFun N n) : ReplicaFun N (n + k) :=
  fun σs => f (fun i => σs (Fin.castAdd k i))

/--
The product Gibbs weights on `n` replicas sum to `1`.

This is the finite-dimensional fact that the `n`-replica Gibbs measure is the product of `n`
copies of the one-replica Gibbs measure.
-/
lemma sum_prod_gibbs_pmf_eq_one (H : EnergySpace N) :
    (∑ σs : ReplicaSpace N n, ∏ l, gibbs_pmf N H (σs l)) = 1 := by
  classical
  -- Induction on `n`, splitting `Fin (n+1) → Config N` into head/tail via `Fin.consEquiv`.
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let p : Config N → ℝ := gibbs_pmf N H
      have hs1 : (∑ σ : Config N, p σ) = 1 := by
        simpa [p] using (SpinGlass.sum_gibbs_pmf (N := N) (H := H))
      let e : (Config N × (Fin n → Config N)) ≃ (Fin (n + 1) → Config N) :=
        Fin.consEquiv (fun _ : Fin (n + 1) => Config N)
      have hrew :
          (∑ σs : (Fin (n + 1) → Config N), ∏ l : Fin (n + 1), p (σs l))
            = ∑ x : (Config N × (Fin n → Config N)), ∏ l : Fin (n + 1), p (e x l) := by
        -- `Fintype.sum_equiv` lets us change variables along the equivalence `e`.
        simpa using
          (Fintype.sum_equiv e
              (f := fun x => ∏ l : Fin (n + 1), p (e x l))
              (g := fun σs => ∏ l : Fin (n + 1), p (σs l))
              (h := fun x => rfl)).symm
      -- Compute the RHS by iterating sums over `(σ₀, σtail)` and factoring.
      calc
        (∑ σs : (Fin (n + 1) → Config N), ∏ l : Fin (n + 1), p (σs l))
            = ∑ x : (Config N × (Fin n → Config N)), ∏ l : Fin (n + 1), p (e x l) := hrew
        _ = ∑ σ₀ : Config N, ∑ σtail : (Fin n → Config N),
              p σ₀ * (∏ i : Fin n, p (σtail i)) := by
              -- Expand the sum over the product type, then split the `Fin (n+1)` product.
              classical
              -- First rewrite the sum over pairs as an iterated sum.
              simp [Fintype.sum_prod_type, e, p, Fin.prod_univ_succ]
        _ = ∑ σ₀ : Config N, p σ₀ * (∑ σtail : (Fin n → Config N), ∏ i : Fin n, p (σtail i)) := by
              classical
              -- Pull out the constant scalar `p σ₀` from the inner sum.
              simp [Finset.mul_sum]
        _ = ∑ σ₀ : Config N, p σ₀ * 1 := by
              -- Use the induction hypothesis for the tail sum.
              simpa [p] using congrArg (fun r => ∑ σ₀ : Config N, p σ₀ * r) ih
        _ = ∑ σ₀ : Config N, p σ₀ := by simp
        _ = 1 := hs1

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/--
Uniform bound on the n-replica Gibbs average:
\[
|\langle f\rangle_{t,n}| \le \max_{\sigma^1,\dots,\sigma^n} |f(\sigma^1,\dots,\sigma^n)|.
\]
-/
lemma abs_gibbs_average_n_le (t : ℝ) (f : ReplicaFun N n) (w : Ω) :
    |gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w|
      ≤ ∑ σs : ReplicaSpace N n, |f σs| := by
  classical
  -- crude but sufficient: triangle inequality and `0 ≤ ∏ l, gibbs_pmf ...`.
  have hnonneg :
      ∀ σs : ReplicaSpace N n,
        0 ≤ ∏ l, gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) :=
    fun σs => by
      classical
      -- product of nonnegative terms
      have : ∀ l : Fin n,
          0 ≤ gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) :=
        fun l => SpinGlass.gibbs_pmf_nonneg (N := N) (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σ := σs l)
      -- move to finset product
      simpa using Finset.prod_nonneg (fun l _hl => this l)
  -- triangle inequality
  calc
    |gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w|
        = |∑ σs : ReplicaSpace N n,
            f σs * ∏ l,
              gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)| := by
            rfl
    _ ≤ ∑ σs : ReplicaSpace N n,
          |f σs * ∏ l,
              gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)| := by
          classical
          -- Apply the finset triangle inequality on `univ`.
          simpa using
            (Finset.abs_sum_le_sum_abs
              (f := fun σs : ReplicaSpace N n =>
                f σs * ∏ l, gibbs_pmf N
                  (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))
              (s := (Finset.univ : Finset (ReplicaSpace N n))))
    _ = ∑ σs : ReplicaSpace N n,
          (|f σs| * |∏ l,
              gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)|) := by
          refine Finset.sum_congr rfl ?_
          intro σs _hσs
          simp [abs_mul]
    _ ≤ ∑ σs : ReplicaSpace N n, |f σs| := by
          -- use `|∏ ...| = ∏ ... ≤ 1`, but we only need a crude bound by `1`.
          -- Since each factor is a probability, it is ≤ 1.
          classical
          -- compare termwise on the finset `univ` and `simp` back to the `Fintype` sum.
          simpa using
            (Finset.sum_le_sum (s := (Finset.univ : Finset (ReplicaSpace N n))) (fun σs _hσs => by
              have hle1 : |∏ l,
                  gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)| ≤ 1 := by
                -- crude: each factor `gibbs_pmf` is ≤ 1, hence product ≤ 1
                have hfac : ∀ l : Fin n,
                    gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) ≤ 1 := by
                  intro l
                  have hZpos :
                      0 < Z N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) :=
                    SpinGlass.Z_pos (N := N)
                      (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
                  have hterm_le :
                      Real.exp (-(H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))
                        ≤ Z N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) := by
                    -- a single term is bounded by the sum `Z`
                    classical
                    -- use `Finset.single_le_sum` on `s = univ`, `f = exp(-H)`
                    have :=
                      Finset.single_le_sum
                        (s := (Finset.univ : Finset (Config N)))
                        (f := fun τ =>
                          Real.exp (-(H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ))
                        (hf := fun τ _hτ => (Real.exp_pos _).le)
                        (a := (σs l)) (h := Finset.mem_univ (σs l))
                    simpa [Z] using this
                  have := (div_le_one hZpos).2 hterm_le
                  simpa [SpinGlass.gibbs_pmf] using this
                -- absolute value is redundant since factors are nonnegative
                have habs :
                    |∏ l,
                        gibbs_pmf N
                          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)|
                      =
                    ∏ l,
                        gibbs_pmf N
                          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) := by
                  have hnonneg' : 0 ≤ ∏ l,
                      gibbs_pmf N
                        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) :=
                    hnonneg σs
                  simp [abs_of_nonneg hnonneg']
                have hprod :
                    ∏ l,
                        gibbs_pmf N
                          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)
                      ≤ (1 : ℝ) := by
                  -- `∏ l, a_l ≤ 1` if each `0 ≤ a_l` and `a_l ≤ 1`.
                  classical
                  simpa using
                    (Finset.prod_le_one (s := (Finset.univ : Finset (Fin n)))
                      (f := fun l =>
                        gibbs_pmf N
                          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))
                      (fun l _hl => SpinGlass.gibbs_pmf_nonneg (N := N)
                        (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
                        (σ := σs l))
                      (fun l _hl => hfac l))
                simpa [habs] using hprod
              -- finish the termwise inequality: `|f| * |w| ≤ |f|`
              have : |f σs| * |∏ l,
                  gibbs_pmf N
                    (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)|
                    ≤ |f σs| := by
                -- multiply the bound `|w| ≤ 1` by the nonnegative factor `|f|`
                simpa using (mul_le_mul_of_nonneg_left hle1 (abs_nonneg (f σs)))
              -- close
              simpa [mul_assoc] using this))

-- From the above crude bound, integrability under the probability measure is immediate.
lemma integrable_gibbs_average_n (t : ℝ) (f : ReplicaFun N n) :
    Integrable (fun w => gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w) := by
  classical
  -- A uniform (in `w`) bound, hence an a.e. bound.
  have hbound :
      ∀ w, ‖gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w‖
        ≤ ∑ σs : ReplicaSpace N n, ‖f σs‖ := by
    intro w
    simpa [Real.norm_eq_abs] using
      (abs_gibbs_average_n_le (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) (n := n) (t := t) (f := f) w)

  -- Measurability of the Gibbs average is by finite sums/products of measurable functions.
  have hU_meas : Measurable (sk.U) := sk.hU.repr_measurable
  have hV_meas : Measurable (sim.V) := sim.hV.repr_measurable
  have hHt_meas :
      Measurable (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t) := by
    -- linear combination of measurable maps + constant
    have h1 : Measurable (fun w => (Real.sqrt t) • sk.U w) := hU_meas.const_smul (Real.sqrt t)
    have h2 : Measurable (fun w => (Real.sqrt (1 - t)) • sim.V w) := hV_meas.const_smul (Real.sqrt (1 - t))
    have h3 : Measurable (fun _w : Ω => H_field (N := N) (h := h)) := measurable_const
    -- Keep the addition parenthesization aligned with the definition of `H_t`:
    -- `H_t = (√t • U + √(1-t) • V) + H_field`.
    simpa [H_t, H_gauss] using ((h1.add h2).add h3)

  have h_gibbs_pmf_meas :
      ∀ (σ : Config N),
        Measurable fun w =>
          gibbs_pmf N
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) σ := by
    intro σ
    -- unfold `gibbs_pmf` and use measurability of evaluation, exp, the finite sum `Z`, and division.
    have hEval : Measurable fun w =>
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) σ :=
      (evalCLM (N := N) σ).measurable.comp hHt_meas
    have hNum : Measurable fun w =>
        Real.exp (-
          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) σ) :=
      (Real.continuous_exp.measurable.comp (measurable_neg.comp hEval))
    have hZ : Measurable fun w =>
        Z N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) := by
      classical
      -- `Z` is a finite sum of exponentials of measurable evaluations.
      have hterm : ∀ τ : Config N,
          Measurable fun w =>
            Real.exp (-
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ) := by
        intro τ
        have hEvalτ : Measurable fun w =>
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ :=
          (evalCLM (N := N) τ).measurable.comp hHt_meas
        exact (Real.continuous_exp.measurable.comp (measurable_neg.comp hEvalτ))
      -- now apply `Finset.measurable_sum` on `Finset.univ`.
      simpa [Z] using
        (Finset.measurable_sum (s := (Finset.univ : Finset (Config N)))
          (f := fun τ w =>
            Real.exp (-
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ))
          (hf := by intro τ _hτ; simpa using hterm τ))
    -- division is measurable
    simpa [SpinGlass.gibbs_pmf] using hNum.div hZ

  have hMeas :
      Measurable (fun w =>
        gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w) := by
    classical
    -- Expand the finite sum over replica configurations.
    -- We work with the `Finset.univ` presentation to use `Finset.measurable_sum/prod`.
    have hterm :
        ∀ σs : ReplicaSpace N n,
          Measurable fun w =>
            f σs * ∏ l : Fin n,
              gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) := by
      intro σs
      -- measurability of the product over replicas
      have hprod :
          Measurable fun w =>
            ∏ l : Fin n,
              gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) := by
        -- rewrite as a finset product and use `Finset.measurable_prod`
        classical
        simpa using
          (Finset.measurable_prod (s := (Finset.univ : Finset (Fin n)))
            (f := fun l w =>
              gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))
            (hf := by
              intro l _hl
              simpa using h_gibbs_pmf_meas (σs l)))
      simpa [mul_assoc] using (measurable_const.mul hprod)
    -- sum over `σs`
    simpa [gibbs_average_n] using
      (Finset.measurable_sum (s := (Finset.univ : Finset (ReplicaSpace N n)))
        (f := fun σs w =>
          f σs * ∏ l : Fin n,
            gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))
        (hf := by intro σs _hσs; simpa using hterm σs))

  have hAESM :
      AEStronglyMeasurable
        (fun w =>
          gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w) ℙ :=
    hMeas.aestronglyMeasurable

  -- Finish by boundedness on a finite measure space.
  have hBoundAE :
      ∀ᵐ w ∂ℙ, ‖gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w‖
        ≤ ∑ σs : ReplicaSpace N n, ‖f σs‖ :=
    Filter.Eventually.of_forall hbound
  exact Integrable.of_bound (μ := (ℙ : Measure Ω)) hAESM _ hBoundAE

/--
The Covariance function U(σ^l, σ^l') appearing in the derivative.
U_{l,l'} = E[u(σ^l)u(σ^l')] - E[v(σ^l)v(σ^l')].
For SK: U_{l,l'} = (β²/2)(R_{l,l'}^2 - q).
-/
def U_interaction (U : InteractionKernel (N := N)) (l l' : Fin n) (σs : ReplicaSpace N n) : ℝ :=
  U (σs l) (σs l')

noncomputable def U_kernel_SK : InteractionKernel (N := N) :=
  fun σ τ =>
    let R := overlap N σ τ
    (β^2 / 2) * (R^2 - q)

noncomputable def U_interaction_SK (l l' : Fin n) (σs : ReplicaSpace N n) : ℝ :=
  U_interaction (N := N) (n := n) (U := U_kernel_SK (N := N) (β := β) (q := q)) l l' σs

end ReplicaCalculus

end SpinGlass
