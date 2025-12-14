import Riemann.Mathlib.Probability.Distributions.Gaussian_IBP_Hilbert
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv


open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology

namespace SpinGlass

variable (N : ℕ) (β h q : ℝ)

/-! ### Basic Definitions -/

abbrev Config := Fin N → Bool

def spin (σ : Config N) (i : Fin N) : ℝ := if σ i then 1 else -1

abbrev EnergySpace := PiLp 2 (fun _ : Config N => ℝ)

noncomputable instance : InnerProductSpace ℝ (EnergySpace N) :=
  PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Config N => ℝ)

noncomputable instance : FiniteDimensional ℝ (EnergySpace N) := by
  classical
  -- `EnergySpace N` is a type synonym of the finite product `∀ σ : Config N, ℝ`.
  infer_instance

def std_basis (σ : Config N) : EnergySpace N :=
  WithLp.toLp 2 (fun τ => if σ = τ then 1 else 0)

noncomputable section

def overlap (σ τ : Config N) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, (spin N σ i) * (spin N τ i)

/-! ### Covariance Kernels -/

def sk_cov_kernel (σ τ : Config N) : ℝ :=
  (N * β^2 / 2) * (overlap N σ τ)^2

def simple_cov_kernel (σ τ : Config N) : ℝ :=
  N * β^2 * q * (overlap N σ τ)

/-! ### Thermodynamic Quantities -/

def Z (H : EnergySpace N) : ℝ := ∑ σ, Real.exp (- H σ)

def gibbs_pmf (H : EnergySpace N) (σ : Config N) : ℝ :=
  Real.exp (- H σ) / Z N H

/-! ### Free energy density and its abstract (Fréchet) Hessian -/

/-- Free energy density \(F_N(H) := \frac1N \log Z_N(H)\). -/
noncomputable def free_energy_density (H : EnergySpace N) : ℝ :=
  (1 / (N : ℝ)) * Real.log (Z N H)

/--
The Hessian of the free energy density, defined abstractly as the second Fréchet derivative
`fderiv ℝ (fun H' => fderiv ℝ (free_energy_density N) H') H`.

This is the object that interfaces directly with Gaussian IBP statements.
-/
noncomputable def hessian_free_energy_fderiv (H : EnergySpace N) :
    EnergySpace N →L[ℝ] EnergySpace N →L[ℝ] ℝ :=
  fderiv ℝ (fun H' => fderiv ℝ (free_energy_density (N := N)) H') H

lemma Z_pos (H : EnergySpace N) : 0 < Z N H := by
  classical
  have : 0 < ∑ σ : Config N, Real.exp (- H σ) := by
    refine Finset.sum_pos ?_ Finset.univ_nonempty
    intro σ _hσ
    exact Real.exp_pos _
  simpa [Z] using this

lemma Z_ne_zero (H : EnergySpace N) : Z N H ≠ 0 :=
  (ne_of_gt (Z_pos (N := N) (H := H)))

lemma gibbs_pmf_pos (H : EnergySpace N) (σ : Config N) : 0 < gibbs_pmf N H σ := by
  have hZ : 0 < Z N H := Z_pos (N := N) (H := H)
  simpa [gibbs_pmf] using (div_pos (Real.exp_pos _) hZ)

lemma gibbs_pmf_nonneg (H : EnergySpace N) (σ : Config N) : 0 ≤ gibbs_pmf N H σ :=
  le_of_lt (gibbs_pmf_pos (N := N) (H := H) σ)

lemma sum_gibbs_pmf (H : EnergySpace N) : (∑ σ, gibbs_pmf N H σ) = 1 := by
  classical
  have hZ : Z N H ≠ 0 := Z_ne_zero (N := N) (H := H)
  calc
    (∑ σ, gibbs_pmf N H σ) = ∑ σ, Real.exp (- H σ) / Z N H := by rfl
    _ = ∑ σ, Real.exp (- H σ) * (Z N H)⁻¹ := by
      simp [div_eq_mul_inv]
    _ = (∑ σ, Real.exp (- H σ)) * (Z N H)⁻¹ := by
      -- factor the constant `(Z N H)⁻¹` out of the sum
      simpa using
        (Finset.sum_mul (s := (Finset.univ : Finset (Config N)))
          (f := fun σ => Real.exp (- H σ)) (a := (Z N H)⁻¹)).symm
    _ = (Z N H) * (Z N H)⁻¹ := by
      simp [Z]
    _ = 1 := by simp [hZ]

/-! ### Differentiation formulas (Fréchet derivatives) -/

noncomputable abbrev evalCLM (σ : Config N) : EnergySpace N →L[ℝ] ℝ :=
  PiLp.proj (p := (2 : ENNReal)) (fun _ : Config N => ℝ) σ

lemma hasFDerivAt_Z (H : EnergySpace N) :
    HasFDerivAt (fun H : EnergySpace N => Z N H)
      (∑ σ : Config N, (-(Real.exp (-H σ))) • evalCLM (N := N) σ) H := by
  classical
  -- Differentiate termwise in the finite sum defining `Z`.
  -- Each term is `H ↦ exp(- H σ)`, a composition of evaluation, negation, and `exp`.
  have hterm :
      ∀ σ : Config N,
        HasFDerivAt (fun H : EnergySpace N => Real.exp (-H σ))
          ((-(Real.exp (-H σ))) • evalCLM (N := N) σ) H := by
    intro σ
    have heval :
        HasFDerivAt (fun H : EnergySpace N => H σ) (evalCLM (N := N) σ) H := by
      simpa [evalCLM] using
        (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := (2 : ENNReal))
          (E := fun _ : Config N => ℝ) (f := H) σ)
    have hneg :
        HasFDerivAt (fun H : EnergySpace N => -(H σ)) (-(evalCLM (N := N) σ)) H := by
      simpa using heval.neg
    have hexp : HasDerivAt Real.exp (Real.exp (-H σ)) (-H σ) :=
      Real.hasDerivAt_exp (-H σ)
    have hcomp :
        HasFDerivAt (fun H : EnergySpace N => Real.exp (-(H σ)))
          ((Real.exp (-H σ)) • (-(evalCLM (N := N) σ))) H :=
      by
        simpa [Function.comp] using
          (HasDerivAt.comp_hasFDerivAt (x := H) hexp hneg)
    -- Rewrite the derivative into the more convenient `(-exp(-Hσ)) • evalCLM σ` form.
    simpa [smul_neg, neg_smul] using hcomp
  -- Now sum the derivatives.
  -- `Z N H = ∑ σ, exp(-H σ)` as a `Finset` sum over `Finset.univ`.
  simpa [Z] using
    (HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Config N)))
      (A := fun σ : Config N => fun H : EnergySpace N => Real.exp (-H σ))
      (A' := fun σ : Config N => (-(Real.exp (-H σ))) • evalCLM (N := N) σ)
      (x := H)
      (fun σ _hσ => hterm σ))

lemma fderiv_Z_apply (H h : EnergySpace N) :
    fderiv ℝ (fun H : EnergySpace N => Z N H) H h =
      - ∑ σ : Config N, Real.exp (-H σ) * h σ := by
  classical
  -- Use the explicit derivative from `hasFDerivAt_Z` and evaluate it on `h`.
  have hZ' := (hasFDerivAt_Z (N := N) (H := H)).fderiv
  -- Expand the CLM sum application.
  simp [hZ', evalCLM, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]

lemma fderiv_free_energy_density_apply (H h : EnergySpace N) :
    fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H) H h =
      -(1 / (N : ℝ)) * ∑ σ : Config N, (gibbs_pmf N H σ) * h σ := by
  classical
  -- Differentiate `H ↦ (1/N) * log(Z(H))` using the chain rule.
  have hZ : HasFDerivAt (fun H : EnergySpace N => Z N H)
      (∑ σ : Config N, (-(Real.exp (-H σ))) • evalCLM (N := N) σ) H :=
    hasFDerivAt_Z (N := N) (H := H)
  have hlog :
      HasFDerivAt (fun H : EnergySpace N => Real.log (Z N H))
        ((Z N H)⁻¹ • (∑ σ : Config N, (-(Real.exp (-H σ))) • evalCLM (N := N) σ)) H :=
    (hZ.log (Z_ne_zero (N := N) (H := H)))
  have hF :
      HasFDerivAt (fun H : EnergySpace N => free_energy_density (N := N) H)
        ((1 / (N : ℝ)) • ((Z N H)⁻¹ • (∑ σ : Config N, (-(Real.exp (-H σ))) • evalCLM (N := N) σ))) H := by
    -- `free_energy_density` is a constant scalar multiple of `log ∘ Z`.
    simpa [free_energy_density, smul_eq_mul, mul_assoc] using (hlog.const_smul (c := (1 / (N : ℝ))))
  -- Now evaluate the derivative on direction `h` and rewrite in Gibbs form.
  have hF' := hF.fderiv
  -- Unfold the linear-map expression and simplify, then rearrange products inside the finite sum.
  -- (We keep the steps explicit to avoid any accidental `Nat`-division coercions.)
  have : fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H) H h =
        (1 / (N : ℝ)) * ((Z N H)⁻¹ * (-∑ σ : Config N, Real.exp (-H σ) * h σ)) := by
    -- Evaluate the derivative coming from `hF'`.
    -- The only content here is unfolding the `Finset`-sum of CLMs and `evalCLM`.
    simp [hF', evalCLM, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      mul_comm]
  -- Substitute the explicit formula for `fderiv Z` and rewrite into Gibbs form.
  -- `fderiv Z` already gave us the sum `-∑ exp(-Hσ) * hσ`.
  -- Finally, move the scalar `(Z N H)⁻¹` inside the sum and recognize `gibbs_pmf`.
  calc
    fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H) H h
        = (1 / (N : ℝ)) * ((Z N H)⁻¹ * (-∑ σ : Config N, Real.exp (-H σ) * h σ)) := this
    _ = -(1 / (N : ℝ)) * ∑ σ : Config N, (Real.exp (-H σ) / Z N H) * h σ := by
          -- push constants inside and rewrite `/` as `* (·)⁻¹`
          -- note: `a / b = a * b⁻¹` and `-(c) * s = c * (-s)`.
          simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm,
            Finset.mul_sum, Finset.sum_neg_distrib]
    _ = -(1 / (N : ℝ)) * ∑ σ : Config N, (gibbs_pmf N H σ) * h σ := by
          simp [gibbs_pmf]

def hessian_free_energy (H : EnergySpace N) (h k : EnergySpace N) : ℝ :=
  (1 / (N : ℝ)) * (
    (∑ σ, gibbs_pmf N H σ * h σ * k σ) -
    (∑ σ, gibbs_pmf N H σ * h σ) * (∑ τ, gibbs_pmf N H τ * k τ)
  )

/-! ### Trace Formulae and Proofs -/

/--
The trace of the product of a covariance operator `Cov` and the Hessian of the free energy.
Algebraically reduces to variance-like terms of the Gibbs measure.
-/
theorem trace_formula (H : EnergySpace N) (Cov : Config N → Config N → ℝ) :
    (∑ σ, ∑ τ, Cov σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ)) =
    (1 / (N : ℝ)) * (
      (∑ σ, (gibbs_pmf N H σ) * Cov σ σ) -
      (∑ σ, ∑ τ, (gibbs_pmf N H σ) * (gibbs_pmf N H τ) * Cov σ τ)
    ) := by
  classical
  -- Abbreviate the Gibbs weights to keep the algebra readable.
  let g : Config N → ℝ := fun σ => gibbs_pmf N H σ

  have hb : ∀ σ, (∑ ρ, g ρ * std_basis N σ ρ) = g σ := by
    intro σ
    simp [g, std_basis]

  have hc :
      ∀ σ τ, (∑ ρ, g ρ * std_basis N σ ρ * std_basis N τ ρ) = if σ = τ then g σ else 0 := by
    intro σ τ
    by_cases hστ : σ = τ
    · subst hστ
      simp [g, std_basis]
    · simp [g, std_basis, hστ]
  have hHess :
      ∀ σ τ,
        hessian_free_energy N H (std_basis N σ) (std_basis N τ)
        = (1 / (N : ℝ)) * ((if σ = τ then g σ else 0) - g σ * g τ) := by
    intro σ τ
    simp [hessian_free_energy, hb, hc, g]
  -- First simplify the `std_basis`-evaluated Hessian, then split diagonal/off-diagonal pieces.
  have h_diag :
      (∑ σ, ∑ τ, Cov σ τ * (if σ = τ then g σ else 0))
        = ∑ σ, (gibbs_pmf N H σ) * Cov σ σ := by
    classical
    -- Evaluate the inner sum over `τ` using the Kronecker delta.
    refine Finset.sum_congr rfl ?_
    intro σ _hσ
    -- only the term `τ = σ` survives
    rw [Finset.sum_eq_single σ]
    · simp [g, mul_comm]
    · intro τ _hτ hτσ
      have hστ : σ ≠ τ := by simpa [eq_comm] using hτσ
      simp [g, hστ]
    · intro hmem
      exfalso
      exact hmem (Finset.mem_univ σ)
  have h_prod :
      (∑ σ, ∑ τ, Cov σ τ * (g σ * g τ))
        = ∑ σ, ∑ τ, (gibbs_pmf N H σ) * (gibbs_pmf N H τ) * Cov σ τ := by
    classical
    simp [g, mul_comm]
  calc
    (∑ σ, ∑ τ, Cov σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ))
        = ∑ σ, ∑ τ, Cov σ τ * ((1 / (N : ℝ)) * ((if σ = τ then g σ else 0) - g σ * g τ)) := by
            simp [hHess]
    _ = ∑ σ, ∑ τ, (1 / (N : ℝ)) * (Cov σ τ * ((if σ = τ then g σ else 0) - g σ * g τ)) := by
            refine Finset.sum_congr rfl ?_
            intro σ _hσ
            refine Finset.sum_congr rfl ?_
            intro τ _hτ
            simp [mul_left_comm]
    _ = (1 / (N : ℝ)) * ∑ σ, ∑ τ, Cov σ τ * ((if σ = τ then g σ else 0) - g σ * g τ) := by
            -- factor `(1/N)` out of the double sum (first over `τ`, then over `σ`)
            simp [Finset.mul_sum]
    _ = (1 / (N : ℝ)) * (
          (∑ σ, (gibbs_pmf N H σ) * Cov σ σ) -
          (∑ σ, ∑ τ, (gibbs_pmf N H σ) * (gibbs_pmf N H τ) * Cov σ τ)
        ) := by
            -- split the double sum using `mul_sub`/`sum_sub_distrib`, then use `h_diag`/`h_prod`
            have hsplit :
                (∑ σ, ∑ τ, Cov σ τ * ((if σ = τ then g σ else 0) - g σ * g τ))
                  =
                (∑ σ, ∑ τ, Cov σ τ * (if σ = τ then g σ else 0))
                  -
                (∑ σ, ∑ τ, Cov σ τ * (g σ * g τ)) := by
              simp [mul_sub, Finset.sum_sub_distrib]
            simp [hsplit, h_prod, g, mul_comm]

/--
Self-overlap is always 1.
-/
theorem overlap_self (hN : 0 < N) (σ : Config N) : overlap N σ σ = 1 := by
  classical
  unfold overlap
  have hterm : ∀ i : Fin N, spin N σ i * spin N σ i = (1 : ℝ) := by
    intro i
    cases hσ : σ i <;> simp [spin, hσ]
  have hsum : (∑ i : Fin N, spin N σ i * spin N σ i) = (N : ℝ) := by
    calc
      (∑ i : Fin N, spin N σ i * spin N σ i)
          = ∑ _i : Fin N, (1 : ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              exact hterm i
      _ = (N : ℝ) := by simp
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  -- `(1 / (N : ℝ)) * N = 1` for `N ≠ 0`
  simp [hsum, hN0, div_eq_mul_inv]

/--
Trace calculation for the SK model covariance.
Result: (β²/2) * (1 - ⟨R₁₂²⟩ - 1/N + 1/N) = (β²/2) * (1 - ⟨R₁₂²⟩)
-/
theorem trace_sk (hN : 0 < N) (H : EnergySpace N) :
    (∑ σ, ∑ τ, sk_cov_kernel N β σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ)) =
    (β^2 / 2) * (1 - ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ)^2) := by
  classical
  let E_R2 : ℝ :=
    ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ)^2
  have hs1 : (∑ σ, gibbs_pmf N H σ) = 1 := sum_gibbs_pmf (N := N) (H := H)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  -- Apply the general trace formula.
  rw [trace_formula (N := N) (H := H) (Cov := sk_cov_kernel N β)]
  -- Diagonal contribution.
  have hdiag :
      (∑ σ, gibbs_pmf N H σ * sk_cov_kernel N β σ σ)
        = (N * β^2 / 2) := by
    have hover : ∀ σ : Config N, (overlap N σ σ)^2 = (1 : ℝ) := by
      intro σ
      simp [overlap_self (N := N) (hN := hN) σ]
    calc
      (∑ σ, gibbs_pmf N H σ * sk_cov_kernel N β σ σ)
          = ∑ σ, gibbs_pmf N H σ * (N * β^2 / 2) := by
              refine Finset.sum_congr rfl ?_
              intro σ _hσ
              simp [sk_cov_kernel, hover, mul_comm]
      _ = (∑ σ, gibbs_pmf N H σ) * (N * β^2 / 2) := by
              simpa using
                (Finset.sum_mul (s := (Finset.univ : Finset (Config N)))
                  (f := fun σ => gibbs_pmf N H σ) (a := (N * β^2 / 2))).symm
      _ = (N * β^2 / 2) := by simp [hs1]
  -- Off-diagonal contribution.
  have hoff :
      (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * sk_cov_kernel N β σ τ)
        = (N * β^2 / 2) * E_R2 := by
    -- factor out the constant `(N * β^2 / 2)` and use the definition of `E_R2`
    simp [sk_cov_kernel, E_R2, Finset.mul_sum, mul_assoc, mul_left_comm]
  -- Final assembly and cancellation of the prefactor `(1/N)`.
  have hcancel : (1 / (N : ℝ)) * (N * β^2 / 2) = (β^2 / 2) := by
    field_simp [hN0]
  -- Finish by rewriting the two trace terms and simplifying.
  calc
    (1 / (N : ℝ)) *
        ((∑ σ, gibbs_pmf N H σ * sk_cov_kernel N β σ σ) -
          (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * sk_cov_kernel N β σ τ))
        = (1 / (N : ℝ)) * ((N * β^2 / 2) - ((N * β^2 / 2) * E_R2)) := by
            simp [hdiag, hoff]
    _ = (1 / (N : ℝ)) * ((N * β^2 / 2) * (1 - E_R2)) := by ring
    _ = ((1 / (N : ℝ)) * (N * β^2 / 2)) * (1 - E_R2) := by
            simp [mul_assoc]
    _ = (β^2 / 2) * (1 - E_R2) := by
            simpa [mul_assoc] using congrArg (fun z => z * (1 - E_R2)) hcancel
    _ = (β^2 / 2) * (1 - ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ)^2) := by
            simp [E_R2]

/--
Trace calculation for Simple Model.
Result: β² q (1 - ⟨R₁₂⟩)
-/
theorem trace_simple (hN : 0 < N) (H : EnergySpace N) :
    (∑ σ, ∑ τ, simple_cov_kernel N β q σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ)) =
    (β^2 * q) * (1 - ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * overlap N σ τ) := by
  classical
  let E_R : ℝ :=
    ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * overlap N σ τ
  have hs1 : (∑ σ, gibbs_pmf N H σ) = 1 := sum_gibbs_pmf (N := N) (H := H)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  -- Apply the general trace formula.
  rw [trace_formula (N := N) (H := H) (Cov := simple_cov_kernel N β q)]
  have hdiag :
      (∑ σ, gibbs_pmf N H σ * simple_cov_kernel N β q σ σ) = N * β^2 * q := by
    have hover : ∀ σ : Config N, overlap N σ σ = (1 : ℝ) := by
      intro σ
      simpa using overlap_self (N := N) (hN := hN) σ
    -- simplify the diagonal kernel and use `∑ gibbs_pmf = 1`
    calc
      (∑ σ, gibbs_pmf N H σ * simple_cov_kernel N β q σ σ)
          = ∑ σ, gibbs_pmf N H σ * (N * β^2 * q) := by
              simp [simple_cov_kernel, hover, mul_assoc, mul_comm]
      _ = (∑ σ, gibbs_pmf N H σ) * (N * β^2 * q) := by
              simpa using
                (Finset.sum_mul (s := (Finset.univ : Finset (Config N)))
                  (f := fun σ => gibbs_pmf N H σ) (a := (N * β^2 * q))).symm
      _ = N * β^2 * q := by simp [hs1]
  have hoff :
      (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * simple_cov_kernel N β q σ τ)
        = (N * β^2 * q) * E_R := by
    -- just factor out the constant and use the definition of `E_R`
    simp [simple_cov_kernel, E_R, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

  have hcancel : (1 / (N : ℝ)) * (N * β^2 * q) = (β^2 * q) := by
    field_simp [hN0]

  calc
    (1 / (N : ℝ)) *
        ((∑ σ, gibbs_pmf N H σ * simple_cov_kernel N β q σ σ) -
          (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * simple_cov_kernel N β q σ τ))
        = (1 / (N : ℝ)) * ((N * β^2 * q) - ((N * β^2 * q) * E_R)) := by
            simp [hdiag, hoff]
    _ = (1 / (N : ℝ)) * ((N * β^2 * q) * (1 - E_R)) := by ring
    _ = ((1 / (N : ℝ)) * (N * β^2 * q)) * (1 - E_R) := by
            simp [mul_assoc]
    _ = (β^2 * q) * (1 - E_R) := by
            simpa [mul_assoc] using congrArg (fun z => z * (1 - E_R)) hcancel
    _ = (β^2 * q) * (1 - ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * overlap N σ τ) := by
            simp [E_R]

/--
**Proof of Guerra's Derivative Bound**

Combinations of the trace formulas imply:
φ'(t) = (β²/4) * (1 - 2q + q² - ⟨(R-q)²⟩) ≤ (β²/4) * (1-q)²
-/
theorem guerra_derivative_bound_algebra
    (hN : 0 < N) (H : EnergySpace N) :
    let term_sk := (∑ σ, ∑ τ, sk_cov_kernel N β σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ))
    let term_simple := (∑ σ, ∑ τ, simple_cov_kernel N β q σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ))
    (1 / 2) * (term_sk - term_simple) ≤ (β^2 / 4) * (1 - q)^2 := by
  dsimp
  rw [trace_sk (N := N) (β := β) (hN := hN) (H := H),
      trace_simple (N := N) (β := β) (q := q) (hN := hN) (H := H)]
  -- Define Expectation notation for readability
  let E_R := ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * overlap N σ τ
  let E_R2 := ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ)^2
  -- Target inequality:
  -- (1/2) * [ (β²/2)(1 - E_R2) - (β² q)(1 - E_R) ] ≤ (β²/4)(1-q)²
  -- Multiply by 4/β² to simplify:
  -- [ (1 - E_R2) - 2q(1 - E_R) ] ≤ (1-q)²
  -- 1 - E_R2 - 2q + 2q E_R ≤ 1 - 2q + q²
  -- - E_R2 + 2q E_R ≤ q²
  -- 0 ≤ E_R2 - 2q E_R + q²
  -- 0 ≤ E [ (R - q)² ]
  have h_main : (1 / 2) * ((β^2 / 2) * (1 - E_R2) - (β^2 * q) * (1 - E_R)) =
                (β^2 / 4) * ((1 - q)^2 - (E_R2 - 2 * q * E_R + q^2)) := by
    ring
  rw [h_main]
  -- Now we just need to show E_R2 - 2q E_R + q² ≥ 0
  -- This expression is exactly ∑ G(σ)G(τ) (R(σ,τ) - q)²
  have h_pos : (E_R2 - 2 * q * E_R + q^2) =
               ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ - q)^2 := by
    classical
    have hs1 : (∑ x : Config N, gibbs_pmf N H x) = 1 := sum_gibbs_pmf (N := N) (H := H)
    have hs2 : (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ) = 1 := by
      have h :=
        (Fintype.sum_mul_sum (f := fun σ : Config N => gibbs_pmf N H σ)
          (g := fun τ : Config N => gibbs_pmf N H τ))
      calc
        (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ)
            = (∑ σ, gibbs_pmf N H σ) * (∑ τ, gibbs_pmf N H τ) := by
                simpa using h.symm
        _ = 1 := by simp [hs1]
    -- Expand the square pointwise and sum.
    have h_expand :
        (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ - q)^2)
          =
        E_R2 - 2 * q * E_R + q^2 := by
      -- `Finset`-sum of the pointwise identity `(a-q)^2 = a^2 - 2aq + q^2`
      calc
        (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ - q)^2)
            =
            (∑ σ, ∑ τ,
              gibbs_pmf N H σ * gibbs_pmf N H τ *
                ((overlap N σ τ)^2 - 2 * (overlap N σ τ) * q + q^2)) := by
              refine Finset.sum_congr rfl ?_
              intro σ _hσ
              refine Finset.sum_congr rfl ?_
              intro τ _hτ
              simp [sub_sq, mul_assoc, mul_comm]
        _ =
            (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ)^2)
              - (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * (2 * (overlap N σ τ) * q))
              + (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * q^2) := by
              -- distribute the outer multiplication over `a^2 - 2aq + q^2`
              simp [mul_add, sub_eq_add_neg, add_comm,
                Finset.sum_add_distrib, mul_assoc, mul_left_comm, mul_comm]
        _ =
            E_R2 - 2 * q * E_R + q^2 := by
              -- identify the three sums with `E_R2`, `E_R`, and `hs2`
              have hQ :
                  (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * (2 * (overlap N σ τ) * q))
                    =
                  (2 * q) * E_R := by
                -- pull out `q` and `2` from the double sum
                -- first rewrite the integrand
                have :
                    (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * (2 * (overlap N σ τ) * q))
                      =
                    ∑ σ, ∑ τ, (2 * q) * (gibbs_pmf N H σ * gibbs_pmf N H τ * overlap N σ τ) := by
                  refine Finset.sum_congr rfl ?_
                  intro σ _hσ
                  refine Finset.sum_congr rfl ?_
                  intro τ _hτ
                  ring_nf
                -- now factor `(2*q)` out of the double sum
                calc
                  (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * (2 * (overlap N σ τ) * q))
                      = ∑ σ, ∑ τ, (2 * q) * (gibbs_pmf N H σ * gibbs_pmf N H τ * overlap N σ τ) := this
                  _ = (2 * q) * (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * overlap N σ τ) := by
                        simp [Finset.mul_sum, mul_assoc]
                  _ = (2 * q) * E_R := by simp [E_R]
              have hQ2 :
                  (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * q^2) = q^2 := by
                -- the weights sum to 1 on the product space
                calc
                  (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * q^2)
                      = (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ) * q^2 := by
                          simp [Finset.sum_mul, mul_assoc]
                  _ = q^2 := by simp [hs2]
              simp [E_R, E_R2, hQ, hQ2]
    simp [h_expand]
  rw [h_pos]
  -- The term subtracted is non-negative
  have h_nonneg : 0 ≤ ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ - q)^2 := by
    apply Finset.sum_nonneg; intro σ _; apply Finset.sum_nonneg; intro τ _
    apply mul_nonneg
    · apply mul_nonneg
      · exact le_of_lt (div_pos (Real.exp_pos _) (Z_pos N H))
      · exact le_of_lt (div_pos (Real.exp_pos _) (Z_pos N H))
    · apply sq_nonneg
  -- X - Y ≤ X if Y ≥ 0
  -- Use monotonicity of subtraction: `a - b ≤ a` for `0 ≤ b`,
  -- then scale by the nonnegative factor `(β^2 / 4)`.
  have hβ : 0 ≤ (β^2 / 4 : ℝ) := by nlinarith
  have hsub : (1 - q)^2 - (∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ - q)^2)
      ≤ (1 - q)^2 := sub_le_self _ h_nonneg
  have := mul_le_mul_of_nonneg_left hsub hβ
  simpa [mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using this

end
end SpinGlass
