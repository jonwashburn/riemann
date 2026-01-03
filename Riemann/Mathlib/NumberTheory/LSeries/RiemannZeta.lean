import Mathlib.NumberTheory.LSeries.RiemannZeta
import Riemann    -- for academic framework & Mellin/Theta


open Filter Complex
open scoped Topology

namespace LSeries

-- 1. Holomorphy off 1: imported from your analytic zeta file
lemma analyticOn_riemannZeta_compl_one :
  AnalyticOn ℂ riemannZeta {1}ᶜ :=
  RiemannZetaAnalytic.analyticOn_riemannZeta_compl_one

lemma differentiableOn_riemannZeta :
  DifferentiableOn ℂ riemannZeta {1}ᶜ :=
  analyticOn_riemannZeta_compl_one.differentiableOn

-- 2. Use mathlib's completedRiemannZeta and functional equation directly
export Mathlib.NumberTheory.LSeries.RiemannZeta
  (completedRiemannZeta completedRiemannZeta_one_sub)

-- 3. Residue at 1: imported from the analytic zeta file
lemma tendsto_sub_one_mul_riemannZeta_one :
  Tendsto (fun s : ℂ ↦ (s - 1) * riemannZeta s) (𝓝 1) (𝓝 1) :=
  RiemannZetaAnalytic.tendsto_sub_one_mul_riemannZeta_one

lemma riemannZeta_residue_one :
  Tendsto (fun s : ℂ ↦ (s - 1) * riemannZeta s) (𝓝 1) (𝓝 1) :=
  tendsto_sub_one_mul_riemannZeta_one

noncomputable def zetaMinusPrincipal (s : ℂ) : ℂ :=
  riemannZeta s - (1 / (s - 1))

end LSeries

#min_imports
