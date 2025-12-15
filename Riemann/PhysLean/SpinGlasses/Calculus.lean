import Riemann.PhysLean.SpinGlasses.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology

open scoped ContDiff

namespace SpinGlass

variable {N : ℕ}

/-!
## Calculus bridge for the free energy (Talagrand)

This file packages the **calculus layer** needed to connect:

- the *abstract* Fréchet-derivative API used by the Gaussian IBP library; and
- the *explicit* Gibbs-average / covariance formulas used in the SK algebra.

The key statement is `hessian_free_energy_eq_variance`, asserting that the (abstract)
Hessian of the free energy density is exactly the Gibbs covariance bilinear form.

### References
- M. Talagrand, *Mean Field Models for Spin Glasses*, Vol. I, Ch. 1, §1.3 (differentiation of
  \(\log Z\) and the Gibbs covariance/Hessian identity used in the Guerra interpolation).
-/

section Derivatives

/-!
### Smoothness of the partition function and free energy

These are the (finite-dimensional) smoothness facts used to justify the Fréchet derivatives.
They correspond to standard computations in Talagrand’s Appendix on differentiation of
the free energy functional.
-/

/--
`Z` is smooth (`C^∞`) as a finite sum of exponentials of linear forms.

This is the finite-volume regularity input behind Talagrand’s differentiation of the free energy
functional (Vol. I, Ch. 1, §1.3).
-/
lemma contDiff_Z (N : ℕ) : ContDiff ℝ (∞) (fun H : EnergySpace N => Z N H) := by
  classical
  -- `Z(H) = ∑σ exp(-H σ)`. Each summand is smooth and the index set is finite.
  have hterm :
      ∀ σ : Config N, ContDiff ℝ (∞) (fun H : EnergySpace N => Real.exp (-H σ)) := by
    intro σ
    -- `H ↦ H σ` is smooth (continuous linear), so `H ↦ exp(-H σ)` is smooth by composition.
    simpa using (contDiff_exp.comp (contDiff_neg.comp (evalCLM (N := N) σ).contDiff))
  simpa [Z] using
    (ContDiff.sum (𝕜 := ℝ) (n := (∞))
      (s := (Finset.univ : Finset (Config N)))
      (f := fun σ : Config N => fun H : EnergySpace N => Real.exp (-H σ))
      (fun σ hσ => hterm σ))

/--
`Z(H) > 0` for every Hamiltonian `H`.

This is the positivity condition needed to differentiate `log (Z H)` (as in Talagrand, Vol. I,
Ch. 1, §1.3).
-/
lemma Z_pos_everywhere (H : EnergySpace N) : 0 < Z N H :=
  Z_pos (N := N) (H := H)

/--
The free energy density `H ↦ (1/N) log Z(H)` is smooth.

Reference: Talagrand, Vol. I, Ch. 1, §1.3 (differentiation of the free energy).
-/
lemma contDiff_free_energy_density (N : ℕ) :
    ContDiff ℝ (∞) (fun H : EnergySpace N => free_energy_density (N := N) H) := by
  classical
  -- Smoothness of `log ∘ Z` uses that `Z` never vanishes.
  have hZ : ContDiff ℝ (∞) (fun H : EnergySpace N => Z N H) := contDiff_Z (N := N)
  have hlog : ContDiff ℝ (∞) (fun H : EnergySpace N => Real.log (Z N H)) :=
    (hZ.log (fun H => (Z_pos_everywhere (N := N) (H := H)).ne'))
  -- Multiply by the constant `1/N`.
  simpa [free_energy_density, smul_eq_mul, mul_assoc] using
    (ContDiff.const_smul (𝕜 := ℝ) (n := (∞)) (R := ℝ) (c := (1 / (N : ℝ))) hlog)

/-!
### First and second Fréchet derivatives (Talagrand: Gibbs averages and covariances)

These are the formal counterparts of the standard identities:

* \(D(\log Z)(h) = -\langle h \rangle\),
* \(D^2(\log Z)(h,k) = \langle hk \rangle - \langle h \rangle \langle k \rangle\).
-/

/--
**First derivative of the free energy density.**

This is Talagrand’s “\(D\log Z = -\langle \cdot\rangle\)” identity for the Gibbs measure,
with the extra \(1/N\) normalization of the free energy density.

Reference: Talagrand, Vol. I, Ch. 1, §1.3 (first derivative of \(\log Z\)).
-/
lemma fderiv_free_energy_apply (H h : EnergySpace N) :
    fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H) H h =
      -(1 / (N : ℝ)) * ∑ σ : Config N, (gibbs_pmf N H σ) * h σ :=
  fderiv_free_energy_density_apply (N := N) (H := H) (h := h)

/--
**Second derivative / Hessian equals Gibbs covariance** (Talagrand).

This is the key “bridge” identity: the abstract Hessian (Fréchet second derivative)
agrees with the explicit Gibbs covariance formula.

In Talagrand’s notation, this is the identification of \(D^2 \log Z\) with the Gibbs
variance/covariance (used implicitly throughout the Guerra interpolation).

Reference: Talagrand, Vol. I, Ch. 1, §1.3 (second derivative of \(\log Z\) as a covariance).
-/
lemma hessian_free_energy_eq_variance (H h k : EnergySpace N) :
    (hessian_logZ (N := N) H) h k
      = (1 / (N : ℝ)) *
          ((∑ σ : Config N, gibbs_pmf N H σ * h σ * k σ) -
            (∑ σ : Config N, gibbs_pmf N H σ * h σ) * (∑ τ : Config N, gibbs_pmf N H τ * k τ)) := by
  -- This is exactly `hessian_eq_covariance` plus unfolding the explicit covariance definition.
  simpa [gibbs_covariance, hessian_free_energy] using
    (hessian_eq_covariance (N := N) (H := H) (h := h) (k := k))

end Derivatives

end SpinGlass
