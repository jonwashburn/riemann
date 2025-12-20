import Riemann.Mathlib.Probability.Distributions.Gaussian_IBP_Hilbert
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Riemann.PhysLean.SpinGlass.Replicas

open scoped Filter BigOperators Topology ProbabilityTheory ENNReal InnerProductSpace NNReal
open MeasureTheory Filter Set
open SpinGlass
noncomputable section

namespace PhysLean.Probability.GaussianIBP

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [MeasurableSpace H] [BorelSpace H]

-- Expectation notation
local notation3 (prettyPrint := false) "𝔼[" e "]" => ∫ ω, e ∂ℙ


attribute [instance] IsGaussianHilbert.fintype_ι



/-! ## Real Gaussian Integration by Parts (Operator Form) -/

/-- **Operator form (coordinate‑free).**
  `𝔼[⟪g, h⟫ F(g)] = 𝔼[(fderiv ℝ F (g)) (Σ h)]`.
-/
theorem gaussian_integration_by_parts_hilbert_cov_op
    {g : Ω → H} (hg : IsGaussianHilbert g)
    (h : H)
    {F : H → ℝ} (hF_diff : ContDiff ℝ 1 F) (hF_growth : HasModerateGrowth F) :
    𝔼[(fun ω => ⟪g ω, h⟫_ℝ * F (g ω))]
      = 𝔼[(fun ω => (fderiv ℝ F (g ω)) ((covOp (g := g) hg) h))] :=
        ProbabilityTheory.gaussian_integration_by_parts_hilbert_cov_op hg h hF_diff hF_growth

variable (N : ℕ) (β h q : ℝ)

/-- **Operator form (coordinate‑free).** Applying the Gaussian IBP in `EnergySpace`
  for any `H,V`, we can then write
  `𝔼[⟪H, V⟫ F(H)] = 𝔼[(fderiv ℝ F (H)) (Σ V)]`.

  Reference: Talagrand, Vol. I, Ch. 1, §1.3 (second derivative of \(\log Z\) as a Gibbs covariance),
  formula (1.65) in the article.
-/
theorem gaussian_integration_by_parts_hilbert_cov_op'
    (H : Ω → EnergySpace N) (hH : IsGaussianHilbert H)
    (V : EnergySpace N)
    {F : EnergySpace N → ℝ} (hF_diff : ContDiff ℝ 1 F) (hF_growth : HasModerateGrowth F) :
    𝔼[(fun ω => ⟪H ω, V⟫_ℝ * F (H ω))] = 𝔼[(fun ω => (fderiv ℝ F (H ω)) ((covOp (g := H) hH) V))] :=
  gaussian_integration_by_parts_hilbert_cov_op hH V hF_diff hF_growth
