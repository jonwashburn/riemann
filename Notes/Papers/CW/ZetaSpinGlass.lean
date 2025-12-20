import Notes.Papers.CW.ZetaSpinGlassDefs
import Notes.Papers.CW.ArithmeticSpinGlass
import Riemann.PhysLean.SpinGlass.Defs

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
open scoped BigOperators

namespace ZetaSpinGlass

/-!
# Zeta Spin Glass: Guerra interpolation layer

This file builds the Guerra interpolation/free-energy functional on top of the
number-theoretic “signal/noise” framework in `ZetaSpinGlass''` and reuses the
abstract differentiation theorem `ArithmeticSpinGlass.asymmetric_guerra_derivative`.

We deliberately avoid constructing an `IsGaussianHilbert` witness from a matrix
covariance (which would require spectral data). Instead, we assume:
- a Gaussian Hilbert model `hG : IsGaussianHilbert G`, and
- a **covariance matching** hypothesis identifying `covOp` matrix elements with the
  explicit arithmetic kernel `Sigma_T_kernel`.

This matches the IDS protocol: no fragile “heap” structures, no diamonds, and no
duplicate ad-hoc APIs.
-/

section Framework

variable (params : ModelParams)

/-!
## 1. Configuration points (as a label on SpinGlass configurations)

`SpinGlass.Config N` is our canonical finite configuration type from the existing
SpinGlass framework. We attach “positions” \(h(\sigma)\in[-1,1]\) to each configuration.
-/

open SpinGlass

variable {N : ℕ}

/-- A labeling of spin-glass configurations by points in `[-1,1]`. -/
structure SpinConfigPoints (N : ℕ) where
  val : Config N → ℝ
  bound : ∀ σ, |val σ| ≤ 1

variable (pts : SpinConfigPoints N)

/-!
## 2. Arithmetic signal as an energy function
-/

/-- Total arithmetic field at scale `T` (sum over blocks and primes). -/
noncomputable def X_zeta_T (tau h : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc (n0 params) (n_scales params),
    ∑ p ∈ P_k params k, block_term p (arithmetic_phase p tau h)

/-- Vectorized arithmetic Hamiltonian in the SpinGlass energy space. -/
noncomputable def H_arith (tau : ℝ) : EnergySpace N :=
  WithLp.toLp 2 (fun σ : Config N => X_zeta_T params tau (pts.val σ))

/-!
## 3. Explicit covariance kernel (number theory side)

We keep this as a kernel `Config N → Config N → ℝ` so it can be used directly as
matrix elements of the abstract covariance operator `covOp` in the standard basis.
-/

/-- Block covariance kernel Σ_k(σ,τ). -/
noncomputable def Sigma_k_kernel (k : ℕ) (σ τ : Config N) : ℝ :=
  ∑ p ∈ P_k params k,
    (1 / 2 : ℝ) * ((p : ℝ)⁻¹) * Real.cos ((pts.val σ - pts.val τ) * Real.log p)

/-- Total covariance kernel Σ_T(σ,τ) = ∑_k Σ_k(σ,τ). -/
noncomputable def Sigma_T_kernel (σ τ : Config N) : ℝ :=
  ∑ k ∈ Finset.Ioc (n0 params) (n_scales params), Sigma_k_kernel params pts k σ τ

lemma Sigma_k_kernel_symm (k : ℕ) (σ τ : Config N) :
    Sigma_k_kernel params pts k σ τ = Sigma_k_kernel params pts k τ σ := by
  classical
  -- Avoid cancelling prefactors (which can introduce irrelevant case splits).
  simp [Sigma_k_kernel]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have harg :
      (pts.val τ - pts.val σ) * Real.log (p : ℝ) =
        -((pts.val σ - pts.val τ) * Real.log (p : ℝ)) := by
    ring
  rw [harg]
  simp [Real.cos_neg, mul_assoc, mul_comm]

lemma Sigma_T_kernel_symm (σ τ : Config N) :
    Sigma_T_kernel params pts σ τ = Sigma_T_kernel params pts τ σ := by
  classical
  simp [Sigma_T_kernel, Sigma_k_kernel_symm (params := params) (pts := pts)]

end Framework

section Guerra

open SpinGlass PhysLean.Probability.GaussianIBP ArithmeticSpinGlass

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {N : ℕ}
variable {β : ℝ}
variable (params : ModelParams) (pts : SpinConfigPoints N)

/-!
## 4. Gaussian field assumptions and Guerra interpolation

We assume we are given a Gaussian Hilbert model for the *noise field* `G` and a
covariance matching hypothesis identifying `covOp` matrix elements with the explicit
kernel `Sigma_T_kernel`.
-/

structure GaussianField (Ω : Type*) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] where
  G : Ω → EnergySpace N
  hG : IsGaussianHilbert G
  cov_match :
    ∀ σ τ : Config N,
      inner ℝ (covOp hG (SpinGlass.std_basis N σ)) (SpinGlass.std_basis N τ)
        = Sigma_T_kernel params pts σ τ

variable (field : GaussianField (params := params) (pts := pts) Ω)

/-- The interpolated free energy functional \( \phi(t) \) for fixed `tau`. -/
noncomputable def phi (tau : ℝ) (t : ℝ) : ℝ :=
  ArithmeticSpinGlass.phi (M := N) (β := β) (H_arith := H_arith (params := params) (pts := pts) tau)
    (G := field.G) t

lemma phi_t0 (tau : ℝ) :
    phi (β := β) (params := params) (pts := pts) (field := field) tau 0
      =
      SpinGlass.free_energy_density (N := N) ((-β) • H_arith (params := params) (pts := pts) tau) := by
  -- `sqrt 0 = 0` and the integral of a constant is itself.
  classical
  simp [phi, ArithmeticSpinGlass.phi, Real.sqrt_zero]

/-!
## 5. The Guerra derivative in the zeta model

This is obtained by instantiating `ArithmeticSpinGlass.asymmetric_guerra_derivative` and then
rewriting the abstract covariance kernel `Cov` using `field.cov_match`.
-/

theorem guerra_derivative_zeta (tau : ℝ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (phi (β := β) (params := params) (pts := pts) (field := field) tau)
      ((β^2 / (2 * (N : ℝ))) *
        ∫ ω,
          let H := (-β) • (H_arith (params := params) (pts := pts) tau + (Real.sqrt t) • field.G ω)
          let μ : Config N → ℝ := fun σ => SpinGlass.gibbs_pmf N H σ
          let Sigma : Config N → Config N → ℝ := Sigma_T_kernel (params := params) (pts := pts)
          (∑ σ, μ σ * Sigma σ σ) - (∑ σ, ∑ τ, μ σ * μ τ * Sigma σ τ)
        ∂ℙ) t := by
  classical
  -- Start from the abstract derivative theorem (in terms of `covOp`).
  have h0 :=
    ArithmeticSpinGlass.asymmetric_guerra_derivative (M := N) (β := β)
      (H_arith := H_arith (params := params) (pts := pts) tau)
      (G := field.G) (hG := field.hG) t ht
  -- Rewrite the integrand pointwise using `field.cov_match`.
  have hRHS :
      ((β^2 / (2 * (N : ℝ))) *
          ∫ ω,
            let H := (-β) • (H_arith (params := params) (pts := pts) tau + (Real.sqrt t) • field.G ω)
            let μ : Config N → ℝ := fun σ => SpinGlass.gibbs_pmf N H σ
            let Cov : Config N → Config N → ℝ :=
              fun σ τ =>
                inner ℝ (covOp field.hG (SpinGlass.std_basis N σ)) (SpinGlass.std_basis N τ)
            (∑ σ, μ σ * Cov σ σ) - (∑ σ, ∑ τ, μ σ * μ τ * Cov σ τ)
          ∂ℙ)
        =
        ((β^2 / (2 * (N : ℝ))) *
          ∫ ω,
            let H := (-β) • (H_arith (params := params) (pts := pts) tau + (Real.sqrt t) • field.G ω)
            let μ : Config N → ℝ := fun σ => SpinGlass.gibbs_pmf N H σ
            let Sigma : Config N → Config N → ℝ := Sigma_T_kernel (params := params) (pts := pts)
            (∑ σ, μ σ * Sigma σ σ) - (∑ σ, ∑ τ, μ σ * μ τ * Sigma σ τ)
          ∂ℙ) := by
    -- The two integrands are equal for all ω after rewriting `Cov` by `field.cov_match`.
    refine congrArg (fun x => (β^2 / (2 * (N : ℝ))) * x) ?_
    refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
    -- Unfold the `let`s (without unfolding `covOp`) and rewrite covariances by `field.cov_match`.
    dsimp
    -- `simp_rw` rewrites only using the provided lemmas, avoiding `covOp_apply` expansions.
    simp_rw [field.cov_match]
  -- Finish: unfold our `phi`, rewrite the RHS using `hRHS`, and apply `h0`.
  dsimp [phi]
  -- Rewrite the derivative value to the form provided by `h0`.
  rw [← hRHS]
  exact h0

end Guerra

end ZetaSpinGlass
