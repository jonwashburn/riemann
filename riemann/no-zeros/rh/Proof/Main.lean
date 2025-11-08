import rh.academic_framework.Certificate
import rh.RS.SchurGlobalization
-- Import of the heavy boundary wedge module is avoided here to keep the active
-- proof track isolated from placeholder-bearing modules; we consume only the
-- classical boundary positivity exported via RouteB_Final.
import rh.Cert.KxiWhitney
import Mathlib.Topology.Defs.Filter
import rh.academic_framework.EulerProductMathlib
import rh.academic_framework.CompletedXi
import rh.academic_framework.CompletedXiSymmetry
import rh.RS.OffZerosBridge
import rh.RS.Cayley
import rh.RS.PinchCertificate
import rh.RS.XiExtBridge
-- (CR-outer import removed from Proof layer)
-- CompletedXi import deferred until formalization lands
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.Basic
import rh.RS.PinchIngredients
--import rh.dev.upstream.lemmas.PreconnectedBallComplex
import Mathlib

set_option maxRecDepth 4096
set_option diagnostics true
open Metric

namespace AnalyticOn

/-- Identity principle (globalization) for an open, preconnected domain:
if `g` is analytic on `U` and equals the constant `1` on a nonempty open
subset `U' ⊆ U`, then `g = 1` on all of `U`. -/
lemma eqOn_of_isPreconnected_of_open_subset
    {g : ℂ → ℂ} {U U' : Set ℂ}
    (hg : AnalyticOn ℂ g U) (hUconn : IsPreconnected U) (hUopen : IsOpen U)
    (hU'open : IsOpen U') (hU'sub : U' ⊆ U) (hU'ne : U'.Nonempty)
    (hEq : ∀ z ∈ U', g z = (1 : ℂ)) :
    Set.EqOn g (fun _ => (1 : ℂ)) U := by
  classical
  rcases hU'ne with ⟨z0, hz0U'⟩
  have hz0U : z0 ∈ U := hU'sub hz0U'
  have hgN : AnalyticOnNhd ℂ g U :=
    (IsOpen.analyticOn_iff_analyticOnNhd (𝕜 := ℂ) (f := g) hUopen).1 hg
  have h1N : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) U :=
    (IsOpen.analyticOn_iff_analyticOnNhd (𝕜 := ℂ) (f := fun _ : ℂ => (1 : ℂ)) hUopen).1
      (by
        simpa using
          (analyticOn_const (𝕜 := ℂ) (E := ℂ) (F := ℂ) (s := U) (v := (1 : ℂ))))
  have hEv : g =ᶠ[nhds z0] (fun _ => (1 : ℂ)) := by
    refine Filter.eventually_of_mem (hU'open.mem_nhds hz0U') ?_
    intro z hz; simpa using hEq z hz
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hgN h1N hUconn hz0U hEv

end AnalyticOn

namespace RH.Proof

/-!
Lemma: open balls in `ℂ` are preconnected (generic Mathlib-style statement).
This is a good upstream candidate when not already covered by an existing lemma.
-/

open Metric

lemma isPreconnected_ball_complex (z : ℂ) (r : ℝ) : IsPreconnected (Metric.ball z r) := by
  -- Convex sets in real topological vector spaces are path connected, hence preconnected
  have hconv : Convex ℝ (Metric.ball z r) := by
    simpa using (convex_ball z r)
  exact Convex.isPreconnected hconv

/-/ Proof-layer alias for certificate readiness. -/
def PipelineReady : Prop := RH.AcademicFramework.Certificate.Ready

/-- Bridge: certificate readiness implies proof‑layer readiness. -/
theorem pipeline_ready_of_certificate_ready
    (h : RH.AcademicFramework.Certificate.Ready) : PipelineReady := h

/-- Unconditional pipeline readiness, delegated to the certificate layer. -/
theorem pipeline_ready_unconditional : PipelineReady := by
  exact pipeline_ready_of_certificate_ready
    (RH.AcademicFramework.Certificate.Ready_unconditional)

end RH.Proof

-- Specialized wrappers are placed after `theorem RH` below

namespace RH.Proof.Assembly

/-- Boundary nonvanishing from an RS off‑zeros boundary hypothesis. -/
theorem boundary_nonvanishing_from_offzeros
    {Θ N : ℂ → ℂ}
    (h : RH.RS.OffZerosBoundaryHypothesis Θ N) :
    ∀ z, z.re = 1 → riemannZeta z ≠ 0 :=
  RH.RS.ZetaNoZerosOnRe1_from_offZerosAssignmentStatement h

/-- Pointwise boundary nonvanishing on `Re = 1` from the same hypothesis. -/
theorem boundary_nonvanishing_from_offzeros_pointwise
    {Θ N : ℂ → ℂ}
    (h : RH.RS.OffZerosBoundaryHypothesis Θ N)
    (z : ℂ) (hz : z.re = 1) :
    riemannZeta z ≠ 0 :=
  RH.AcademicFramework.EPM.zeta_nonzero_re_eq_one_from_offZerosAssignmentStatement h z hz

end RH.Proof.Assembly

namespace RH.Proof.Assembly

/-- Data bundle to relay RS off‑zeros inputs for a supplied `riemannXi`. -/
structure XiOffZerosBridge where
  riemannXi : ℂ → ℂ
  G : ℂ → ℂ
  symXi : ∀ ρ, riemannXi ρ = 0 → riemannXi (1 - ρ) = 0
  hXiEq : ∀ s, riemannXi s = G s * riemannZeta s
  hGnz : ∀ ρ ∈ RH.RS.Ω, G ρ ≠ 0
  Θ : ℂ → ℂ
  hSchur : RH.RS.IsSchurOn Θ (RH.RS.Ω \ {z | riemannZeta z = 0})
  assign : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
      (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
      ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
        Set.EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1

end RH.Proof.Assembly

namespace RH.Proof

open Complex Set Filter

-- Avoid global simp loops from the functional equation inside this file
attribute [-simp] RH.AcademicFramework.CompletedXi.xi_ext_functional_equation

/-- Core symmetry step: from zero‑symmetry and right‑half‑plane nonvanishing
for `Ξ`, conclude zeros lie on `Re = 1/2`. -/
theorem RH_core
    {Ξ : ℂ → ℂ}
    (noRightZeros : ∀ ρ ∈ RH.RS.Ω, Ξ ρ ≠ 0)
    (sym : ∀ ρ, Ξ ρ = 0 → Ξ (1 - ρ) = 0) :
    ∀ ρ, Ξ ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  intro ρ h0
  -- Trichotomy on Re ρ
  rcases lt_trichotomy ρ.re (1 / 2 : ℝ) with hlt | heq | hgt
  · -- Re ρ < 1/2 ⇒ Re (1 - ρ) > 1/2, so 1-ρ lies in Ω and carries a zero by symmetry
    have hgt' : (1 / 2 : ℝ) < 1 - ρ.re := by linarith
    -- membership in Ω for σ := 1 - ρ
    have hΩσ : (1 - ρ) ∈ RH.RS.Ω := by
      -- Ω = {s | 1/2 < Re s}
      have : (1 / 2 : ℝ) < (1 - ρ).re := by
        simpa [Complex.sub_re, Complex.one_re] using hgt'
      -- unfold Ω membership explicitly
      simpa [RH.RS.Ω, Set.mem_setOf_eq] using this
    -- symmetry transports the zero to 1-ρ
    have h0σ : Ξ (1 - ρ) = 0 := sym ρ h0
    -- contradict no-zero in Ω
    exfalso
    exact (noRightZeros (1 - ρ) hΩσ) h0σ
  · -- Re ρ = 1/2
    exact heq
  · -- Re ρ > 1/2 contradicts noRightZeros on Ω
    have hΩ : ρ ∈ RH.RS.Ω := by simpa [RH.RS.Ω, Set.mem_setOf_eq] using hgt
    exact False.elim ((noRightZeros ρ hΩ) h0)

end RH.Proof

-- Specialized RH wrappers (defined after the core RH theorem)
namespace RH.Proof

/-- RH specialized to an arbitrary function `Ξ` under the standard inputs. -/
theorem RH_for
    (Ξ : ℂ → ℂ)
    (noRightZeros : ∀ ρ ∈ RH.RS.Ω, Ξ ρ ≠ 0)
    (sym : ∀ ρ, Ξ ρ = 0 → Ξ (1 - ρ) = 0) :
    ∀ ρ, Ξ ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  exact (RH_core (Ξ := Ξ) noRightZeros sym)

/-- RH specialized to a `riemannXi` with the standard two assumptions. -/
theorem RH_riemannXi
    (riemannXi : ℂ → ℂ)
    (noRightZeros : ∀ ρ ∈ RH.RS.Ω, riemannXi ρ ≠ 0)
    (sym : ∀ ρ, riemannXi ρ = 0 → riemannXi (1 - ρ) = 0) :
    ∀ ρ, riemannXi ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  exact (RH_core (Ξ := riemannXi) noRightZeros sym)

end RH.Proof

namespace RH.Proof.Assembly

/-- Transfer nonvanishing across a product factorization `Ξ = G·Z` on a set. -/
theorem nonvanishing_of_factor
    (Ω : Set ℂ) (Ξ Z G : ℂ → ℂ)
    (hEq : ∀ s, Ξ s = G s * Z s)
    (hG : ∀ ρ ∈ Ω, G ρ ≠ 0)
    (hZ : ∀ ρ ∈ Ω, Z ρ ≠ 0) :
    ∀ ρ ∈ Ω, Ξ ρ ≠ 0 := by
  intro ρ hΩ
  have hGρ := hG ρ hΩ
  have hZρ := hZ ρ hΩ
  have : G ρ * Z ρ ≠ 0 := mul_ne_zero hGρ hZρ
  have hxieq := hEq ρ
  intro hXi0; rw [hxieq] at hXi0; exact this hXi0

/-- Assemble RH for `riemannXi` from FE, factorization `Ξ = G·ζ`,
Schur bound on `Ω \ {ζ = 0}`, and an RS removable‑extension assignment. -/
theorem RH_riemannXi_from_RS_offZeros
    (riemannXi : ℂ → ℂ)
    (symXi : ∀ ρ, riemannXi ρ = 0 → riemannXi (1 - ρ) = 0)
    (G : ℂ → ℂ)
    (hXiEq : ∀ s, riemannXi s = G s * riemannZeta s)
    (hGnz : ∀ ρ ∈ RH.RS.Ω, G ρ ≠ 0)
    (Θ : ℂ → ℂ)
    (hSchur : RH.RS.IsSchurOn Θ (RH.RS.Ω \ {z | riemannZeta z = 0}))
    (assign : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          Set.EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1) :
    ∀ ρ, riemannXi ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  -- ζ has no zeros on Ω by the RS off‑zeros Schur–pinch route
  have hζnz : ∀ ρ ∈ RH.RS.Ω, riemannZeta ρ ≠ 0 :=
    RH.RS.no_offcritical_zeros_from_schur Θ hSchur assign
  -- Transfer to Ξ via the factorization Ξ = G·ζ with G nonzero on Ω
  have hΞnz : ∀ ρ ∈ RH.RS.Ω, riemannXi ρ ≠ 0 :=
    nonvanishing_of_factor (Ω := RH.RS.Ω)
      (Ξ := riemannXi) (Z := riemannZeta) (G := G) hXiEq hGnz hζnz
  -- Conclude RH for Ξ by symmetry wrapper
  exact RH_riemannXi riemannXi hΞnz symXi

end RH.Proof.Assembly
namespace RH.Proof.Assembly

/-- Local‑equality variant: assume `Ξ = G·ζ` only on Ω. -/
theorem RH_riemannXi_from_RS_offZeros_localEq
    (riemannXi : ℂ → ℂ)
    (symXi : ∀ ρ, riemannXi ρ = 0 → riemannXi (1 - ρ) = 0)
    (G : ℂ → ℂ)
    (hXiEqΩ : ∀ ρ ∈ RH.RS.Ω, riemannXi ρ = G ρ * riemannZeta ρ)
    (hGnz : ∀ ρ ∈ RH.RS.Ω, G ρ ≠ 0)
    (Θ : ℂ → ℂ)
    (hSchur : RH.RS.IsSchurOn Θ (RH.RS.Ω \ {z | riemannZeta z = 0}))
    (assign : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          Set.EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1) :
    ∀ ρ, riemannXi ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  -- ζ has no zeros on Ω by the RS off‑zeros Schur–pinch route
  have hζnz : ∀ ρ ∈ RH.RS.Ω, riemannZeta ρ ≠ 0 :=
    RH.RS.no_offcritical_zeros_from_schur Θ hSchur assign
  -- Nonvanishing of Ξ on Ω via local factorization
  have hΞnz : ∀ ρ ∈ RH.RS.Ω, riemannXi ρ ≠ 0 := by
    intro ρ hΩ
    have hEq : riemannXi ρ = G ρ * riemannZeta ρ := hXiEqΩ ρ hΩ
    have hG := hGnz ρ hΩ
    have hZ := hζnz ρ hΩ
    have : G ρ * riemannZeta ρ ≠ 0 := mul_ne_zero hG hZ
    intro hXi0; rw [hEq] at hXi0; exact this hXi0
  -- Conclude RH for Ξ by symmetry wrapper
  exact RH_riemannXi riemannXi hΞnz symXi

end RH.Proof.Assembly

namespace RH.Proof.Assembly

/-- One‑safe variant: allow `G ≠ 0` on `Ω \ {1}` with a separate value at `1`. -/
theorem RH_riemannXi_from_RS_offZeros_oneSafe
    (riemannXi : ℂ → ℂ)
    (symXi : ∀ ρ, riemannXi ρ = 0 → riemannXi (1 - ρ) = 0)
    (G : ℂ → ℂ)
    (hXiEq : ∀ s, riemannXi s = G s * riemannZeta s)
    (hGnzAway : ∀ ρ ∈ RH.RS.Ω, ρ ≠ (1 : ℂ) → G ρ ≠ 0)
    (hXiOne : riemannXi 1 ≠ 0)
    (Θ : ℂ → ℂ)
    (hSchur : RH.RS.IsSchurOn Θ (RH.RS.Ω \ {z | riemannZeta z = 0}))
    (assign : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          Set.EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1) :
    ∀ ρ, riemannXi ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  -- ζ has no zeros on Ω
  have hζnz : ∀ ρ ∈ RH.RS.Ω, riemannZeta ρ ≠ 0 :=
    RH.RS.no_offcritical_zeros_from_schur Θ hSchur assign
  -- Build Ξ nonvanishing on Ω pointwise using the one-safe guard at 1
  have hΞnz : ∀ ρ ∈ RH.RS.Ω, riemannXi ρ ≠ 0 := by
    intro ρ hΩ
    by_cases h1 : ρ = (1 : ℂ)
    · simpa [h1] using hXiOne
    · have hG : G ρ ≠ 0 := hGnzAway ρ hΩ h1
      have hZ : riemannZeta ρ ≠ 0 := hζnz ρ hΩ
      have hEq : riemannXi ρ = G ρ * riemannZeta ρ := hXiEq ρ
      have : G ρ * riemannZeta ρ ≠ 0 := mul_ne_zero hG hZ
      intro hXi0; rw [hEq] at hXi0; exact this hXi0
  -- Conclude RH for Ξ by symmetry wrapper
  exact RH_riemannXi riemannXi hΞnz symXi

end RH.Proof.Assembly

namespace RH.Proof.Assembly

/-- One‑safe local‑equality variant: assume `Ξ = G·ζ` only away from `1`. -/
theorem RH_riemannXi_from_RS_offZeros_oneSafe_localEq
    (riemannXi : ℂ → ℂ)
    (symXi : ∀ ρ, riemannXi ρ = 0 → riemannXi (1 - ρ) = 0)
    (G : ℂ → ℂ)
    (hXiEqAway : ∀ ρ ∈ RH.RS.Ω, ρ ≠ (1 : ℂ) → riemannXi ρ = G ρ * riemannZeta ρ)
    (hGnzAway : ∀ ρ ∈ RH.RS.Ω, ρ ≠ (1 : ℂ) → G ρ ≠ 0)
    (hXiOne : riemannXi 1 ≠ 0)
    (Θ : ℂ → ℂ)
    (hSchur : RH.RS.IsSchurOn Θ (RH.RS.Ω \ {z | riemannZeta z = 0}))
    (assign : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          Set.EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1) :
    ∀ ρ, riemannXi ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  -- ζ has no zeros on Ω by the RS off‑zeros Schur–pinch route
  have hζnz : ∀ ρ ∈ RH.RS.Ω, riemannZeta ρ ≠ 0 :=
    RH.RS.no_offcritical_zeros_from_schur Θ hSchur assign
  -- Build Ξ nonvanishing on Ω pointwise using the one-safe guard at 1
  have hΞnz : ∀ ρ ∈ RH.RS.Ω, riemannXi ρ ≠ 0 := by
    intro ρ hΩ
    by_cases h1 : ρ = (1 : ℂ)
    · simpa [h1] using hXiOne
    · have hG : G ρ ≠ 0 := hGnzAway ρ hΩ h1
      have hZ : riemannZeta ρ ≠ 0 := hζnz ρ hΩ
      have hEq : riemannXi ρ = G ρ * riemannZeta ρ := hXiEqAway ρ hΩ h1
      have : G ρ * riemannZeta ρ ≠ 0 := mul_ne_zero hG hZ
      intro hXi0; rw [hEq] at hXi0; exact this hXi0
  -- Conclude RH for Ξ by symmetry wrapper
  exact RH_riemannXi riemannXi hΞnz symXi

end RH.Proof.Assembly

namespace RH.Proof.Final

open RH.AcademicFramework.CompletedXi

/-- Disjunction transport at `1-ρ`: if `Ξ(ρ)=0` and `Ξ=G·ζ`, then `G(1-ρ)=0 ∨ ζ(1-ρ)=0`. -/
lemma disj_at_one_sub_of_xi_zero
    (riemannXi G : ℂ → ℂ)
    (hXiEq : ∀ s, riemannXi s = G s * riemannZeta s)
    (symXi : ∀ s, riemannXi s = 0 → riemannXi (1 - s) = 0)
    (ρ : ℂ) (hXi0 : riemannXi ρ = 0)
    : G (1 - ρ) = 0 ∨ riemannZeta (1 - ρ) = 0 := by
  have h1 : riemannXi (1 - ρ) = 0 := symXi ρ hXi0
  have hfac := hXiEq (1 - ρ)
  -- exact transport of zero across factorization
  have := h1; simpa [hfac] using this

/-- RH for a supplied `riemannXi` using FE, Schur bound, assignment, and `G ≠ 0` on Ω. -/
theorem RH_xi_from_supplied_RS
    (riemannXi G : ℂ → ℂ)
    (fe : ∀ s, riemannXi s = riemannXi (1 - s))
    (Θ : ℂ → ℂ)
    (hSchur : RH.RS.IsSchurOn Θ (RH.RS.Ω \ {z | riemannZeta z = 0}))
    (assign : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          Set.EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
    (hXiEq : ∀ s, riemannXi s = G s * riemannZeta s)
    (hGnz : ∀ ρ ∈ RH.RS.Ω, G ρ ≠ 0)
    : ∀ ρ, riemannXi ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  -- Derive zero-symmetry from the supplied functional equation locally
  have symXi : ∀ ρ, riemannXi ρ = 0 → riemannXi (1 - ρ) = 0 :=
    RH.AcademicFramework.CompletedXi.zero_symmetry_from_fe riemannXi fe
  -- ζ has no zeros on Ω by the RS off‑zeros Schur–pinch route
  have hζnz : ∀ ρ ∈ RH.RS.Ω, riemannZeta ρ ≠ 0 :=
    RH.RS.no_offcritical_zeros_from_schur Θ hSchur assign
  -- Ξ nonvanishing on Ω via factorization
  have hΞnz : ∀ ρ ∈ RH.RS.Ω, riemannXi ρ ≠ 0 := by
    intro ρ hΩ
    have hG := hGnz ρ hΩ
    have hZ := hζnz ρ hΩ
    have hEq : riemannXi ρ = G ρ * riemannZeta ρ := hXiEq ρ
    simpa [hEq] using mul_ne_zero hG hZ
  -- Conclude RH for Ξ by symmetry wrapper
  exact RH_riemannXi riemannXi hΞnz symXi

end RH.Proof.Final

namespace RH.Proof.Final

open RH.AcademicFramework.CompletedXi

/-- Nonvanishing of `Γℝ(s)` away from its poles. -/
lemma GammaR_ne_zero_of_not_pole {s : ℂ} (h : ∀ n : ℕ, s / 2 ≠ - (n : ℂ)) : s.Gammaℝ ≠ 0 := by
  have hπ0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hpow : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl hπ0
  have hΓ : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero h
  rw [Complex.Gammaℝ_def]
  exact mul_ne_zero hpow hΓ

/-- Export: convert `Hxi` (zeros of `Ξ_ext` lie on `Re = 1/2`) to mathlib's RH. -/
theorem RH_mathlib_from_xi_ext
    (Hxi : ∀ ρ, RH.AcademicFramework.CompletedXi.riemannXi_ext ρ = 0 → ρ.re = (1 / 2 : ℝ))
    : RiemannHypothesis := by
  intro s hζ _hneTriv _
  have hne0 : s ≠ 0 := by
    intro h0
    simpa [h0, riemannZeta_zero] using hζ
  have hζdef : riemannZeta s = completedRiemannZeta s / s.Gammaℝ :=
    riemannZeta_def_of_ne_zero hne0
  have hNoPole : ∀ n : ℕ, s / 2 ≠ - (n : ℂ) := by
    intro n hn
    have two_ne_zero : (2 : ℂ) ≠ 0 := by norm_num
    have hs : s = -2 * (n : ℂ) := by
      -- from s/2 = -n, multiply by 2
      have : s = (s / 2) * 2 := by
        rw [div_mul_cancel₀ _ two_ne_zero]
      rw [this, hn]
      ring
    apply _hneTriv
    cases n with
      | zero =>
        -- n = 0 case: s/2 = -0 = 0, so s = 0, contradicting hne0
        have h_zero : s / 2 = 0 := by
          simp at hn ⊢
          exact hn
        have : s = 0 := by
          calc s = (s / 2) * 2 := by rw [div_mul_cancel₀ _ two_ne_zero]
               _ = 0 * 2 := by rw [h_zero]
               _ = 0 := by simp
        exact absurd this hne0
      | succ m =>
        -- n = succ m, so n = m + 1
        use m
        rw [hs]
        simp [Nat.succ_eq_add_one]
  have hΓR_ne : s.Gammaℝ ≠ 0 := GammaR_ne_zero_of_not_pole hNoPole
  have hΛeq' : riemannZeta s * s.Gammaℝ = completedRiemannZeta s := by
    -- from ζ = Λ / Γℝ, get ζ * Γℝ = Λ
    calc
      riemannZeta s * s.Gammaℝ = (completedRiemannZeta s / s.Gammaℝ) * s.Gammaℝ := by rw [hζdef]
      _ = completedRiemannZeta s := div_mul_cancel₀ _ hΓR_ne
  have hΛ0 : completedRiemannZeta s = 0 := by
    rw [<- hΛeq', hζ, zero_mul]
  have hXi0 : riemannXi_ext s = 0 := by
    rw [riemannXi_ext, hΛ0]
  exact Hxi s hXi0

-- (CR-outer routes and assign-based wrapper referencing CRGreenOuterData removed)

/-
Pinch route scaffolding (paper-aligned): abstract pinch lemmas that avoid the
LocalData/removable-extension chooser. These provide a direct contradiction
structure using: Schur on Ω \ Z(Ξ), right-edge normalization (Θ → -1), and
local pole behavior at zeros (Θ → 1), plus symmetry to conclude RH.
-/
namespace RH.Proof.poissonIntegralinch
-- (skeleton pinch lemmas removed in favor of the assign-based route below)
end RH.Proof.poissonIntegralinch

-- Assign-based pinch route (no sorries): use RS removable globalization directly.
namespace RH.Proof.poissonIntegralinch

open RH.RS Complex Set

/-- No‑right‑zeros from a removable‑extension assignment on Ω \ {Ξ=0}. -/
theorem no_right_zeros_from_pinch_assign
    (Ξ Θ : ℂ → ℂ)
    (hSchur : RH.RS.IsSchurOn Θ (RH.RS.Ω \ {z | Ξ z = 0}))
    (assign : ∀ ρ, ρ ∈ RH.RS.Ω → Ξ ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | Ξ z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          Set.EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
    : ∀ ρ ∈ RH.RS.Ω, Ξ ρ ≠ 0 := by
  intro ρ hΩ hΞρ
  rcases assign ρ hΩ hΞρ with
    ⟨U, hUopen, hUconn, hUsub, hρU, hUZeq, g, hg, hΘU, hExt, hval, z0, hz0U, hneq⟩
  -- Globalize across the removable point using Schur bound on Ω \ {Ξ=0}
  have hρZ : ρ ∈ ({z | Ξ z = 0} : Set ℂ) := by simpa [Set.mem_setOf_eq] using hΞρ
  have hUminusSub : (U \ {ρ}) ⊆ (RH.RS.Ω \ ({z | Ξ z = 0})) := by
    intro x hx
    have hxU : x ∈ U := hx.1
    have hxNe : x ≠ ρ := by
      intro h; exact hx.2 (by simp [h])
    have hxNotZ : x ∉ ({z | Ξ z = 0} : Set ℂ) := by
      intro hxZ
      have hxInCap : x ∈ (U ∩ {z | Ξ z = 0}) := ⟨hxU, hxZ⟩
      have hxSingleton : x ∈ ({ρ} : Set ℂ) := by simpa [hUZeq] using hxInCap
      have : x = ρ := by simpa using hxSingleton
      exact hxNe this
    exact ⟨hUsub hxU, hxNotZ⟩
  have hg_one : ∀ w ∈ U, g w = 1 :=
    RH.RS.GlobalizeAcrossRemovable ({z | Ξ z = 0}) Θ hSchur
      U hUopen hUconn hUsub ρ hΩ hρU hρZ g hg hΘU hUminusSub hExt hval
  -- Contradiction with the nontriviality witness
  have : g z0 = 1 := hg_one z0 hz0U
  exact (hneq this).elim

/-- RH from the assign‑based pinch route. -/
theorem RH_from_pinch_assign
    (Ξ Θ : ℂ → ℂ)
    (sym : ∀ ρ, Ξ ρ = 0 → Ξ (1 - ρ) = 0)
    (hSchur : RH.RS.IsSchurOn Θ (RH.RS.Ω \ {z | Ξ z = 0}))
    (assign : ∀ ρ, ρ ∈ RH.RS.Ω → Ξ ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | Ξ z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          Set.EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
    : ∀ ρ, Ξ ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  have noRightZeros : ∀ ρ ∈ RH.RS.Ω, Ξ ρ ≠ 0 :=
    no_right_zeros_from_pinch_assign Ξ Θ hSchur assign
  exact RH.Proof.RH_core (Ξ := Ξ) noRightZeros sym

end RH.Proof.poissonIntegralinch

namespace RH.Proof.Final
open RH.AcademicFramework.CompletedXi
-- (skeleton pinch exports removed; we use the assign-based exports below)
-- keep namespace open for subsequent wrappers

namespace RH.Proof.Final

open RH.AcademicFramework.CompletedXi

/-- Assign‑based pinch specialized to `riemannXi_ext`. -/
theorem RiemannHypothesis_from_pinch_ext_assign
    (Θ : ℂ → ℂ)
    (hSchur_offXi : RH.RS.IsSchurOn Θ RH.AcademicFramework.HalfPlaneOuterV2.offXi)
    (assign : ∀ ρ, ρ ∈ RH.RS.Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          Set.EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
    : ∀ ρ, riemannXi_ext ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  -- FE for Ξ_ext and symmetry
  have fe : ∀ s, riemannXi_ext s = riemannXi_ext (1 - s) :=
    fun s => RH.AcademicFramework.CompletedXi.xi_ext_functional_equation s
  have symXi : ∀ ρ, riemannXi_ext ρ = 0 → riemannXi_ext (1 - ρ) = 0 :=
    RH.AcademicFramework.CompletedXi.zero_symmetry_from_fe riemannXi_ext fe
  -- Prove no-right-zeros using the assign-based pinch with Schur on offXi.
  have noRightZeros : ∀ ρ ∈ RH.RS.Ω, riemannXi_ext ρ ≠ 0 := by
    intro ρ hΩ hXiρ
    rcases assign ρ hΩ hXiρ with
      ⟨U, hUopen, hUconn, hUsub, hρU, hUZeq, g, hg, hΘU, hExt, hval, z0, hz0U, hneq⟩
    -- Shrink to a ball around ρ contained in Ω ∩ U, and in the ρ ≠ 1 case also avoiding 1
    have hΩ_open : IsOpen RH.RS.Ω := RH.RS.isOpen_Ω
    obtain ⟨εΩ, hεΩpos, hεΩsubset⟩ :=
      Metric.mem_nhds_iff.mp (hΩ_open.mem_nhds (hUsub hρU))
    obtain ⟨εU, hεUpos, hεUsubset⟩ :=
      Metric.mem_nhds_iff.mp (hUopen.mem_nhds hρU)
    by_cases hρ1 : ρ = (1 : ℂ)
    · -- Pick a small ball in Ω ∩ U; removing ρ ensures z ≠ 1 on the puncture
      let t : ℝ := min εΩ εU
      have htpos : 0 < t := lt_min hεΩpos hεUpos
      have hBall_sub_Ω : Metric.ball ρ t ⊆ RH.RS.Ω := by
        intro z hz
        have hzlt : dist z ρ < εΩ := lt_of_lt_of_le hz (min_le_left _ _)
        have : z ∈ Metric.ball ρ εΩ := by simpa [Metric.mem_ball] using hzlt
        exact hεΩsubset this
      have hBall_sub_U : Metric.ball ρ t ⊆ U := by
        intro z hz
        have hzlt : dist z ρ < εU := lt_of_lt_of_le hz (min_le_right _ _)
        have : z ∈ Metric.ball ρ εU := by simpa [Metric.mem_ball] using hzlt
        exact hεUsubset this
      -- Define U'
      let U' : Set ℂ := Metric.ball ρ t
      have hU'open : IsOpen U' := isOpen_ball
      have hU'subΩ : U' ⊆ RH.RS.Ω := hBall_sub_Ω
      have hρU' : ρ ∈ U' := by simpa [U', Metric.mem_ball, dist_self] using htpos
      -- Isolation persists
      have hIso' : (U' ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) := by
        apply Set.Subset.antisymm
        · intro z hz
          have hzU : z ∈ U := hBall_sub_U hz.1
          have hzpair : z ∈ U ∩ {z | riemannXi_ext z = 0} := ⟨hzU, hz.2⟩
          have : z ∈ ({ρ} : Set ℂ) := by simpa [hUZeq] using hzpair
          simpa using this
        · intro z hz; obtain rfl : z = ρ := by simpa [Set.mem_singleton_iff] using hz
          refine ⟨?_, ?_⟩
          · have : dist z z < t := by simpa [dist_self] using htpos
            simpa [U', Metric.mem_ball] using this
          · simp [hXiρ]
      -- Build Schur on U'\{ρ} via offXi inclusion
      have hUminusSub_offXi : (U' \ {ρ}) ⊆ RH.AcademicFramework.HalfPlaneOuterV2.offXi := by
        intro z hz
        have hzU' : z ∈ U' := hz.1
        have hzNeρ : z ≠ ρ := hz.2
        have hzΩ : z ∈ RH.RS.Ω := hU'subΩ hzU'
        have hzXi : riemannXi_ext z ≠ 0 := by
          intro h0
          have : z ∈ (U' ∩ {w | riemannXi_ext w = 0}) := ⟨hzU', by simpa [Set.mem_setOf_eq] using h0⟩
          have : z ∈ ({ρ} : Set ℂ) := by simpa [hIso'] using this
          exact hzNeρ (by simpa using this)
        have hzNe1 : z ≠ (1 : ℂ) := by
          -- since ρ = 1 and z ≠ ρ
          simpa [hρ1] using hzNeρ
        exact ⟨hzΩ, hzNe1, hzXi⟩
      have hSchur_U' : RH.RS.IsSchurOn Θ (U' \ {ρ}) := by
        intro z hz; exact hSchur_offXi z (hUminusSub_offXi hz)
      have hΘU' : AnalyticOn ℂ Θ (U' \ {ρ}) :=
        hΘU.mono (by intro z hz; exact ⟨hBall_sub_U hz.1, hz.2⟩)
      have hEqOn' : Set.EqOn Θ g (U' \ {ρ}) := by
        intro w hw; exact hExt ⟨hBall_sub_U hw.1, hw.2⟩
      have hPF := RH.RS.PinchFromExtension U' hU'open (isPreconnected_ball_complex ρ t) ρ hρU' Θ hΘU' hSchur_U'
        g (hg.mono (by intro w hw; exact hBall_sub_U hw)) hEqOn' hval
      have hAllOne : ∀ w ∈ U', g w = 1 := hPF.1
      have : g z0 = 1 := by
        -- Prove 1-avoidance on U \ {ρ} using ρ = 1 and isolation, then globalize on U
        have hUminusSub_offXi_U : (U \ {ρ}) ⊆ RH.AcademicFramework.HalfPlaneOuterV2.offXi := by
          intro w hw
          have hwU : w ∈ U := hw.1
          have hwNeρ : w ≠ ρ := hw.2
          have hwΩ : w ∈ RH.RS.Ω := hUsub hwU
          have hwXi : riemannXi_ext w ≠ 0 := by
            intro h0
            have : w ∈ (U ∩ {z | riemannXi_ext z = 0}) := ⟨hwU, by simpa [Set.mem_setOf_eq] using h0⟩
            have : w ∈ ({ρ} : Set ℂ) := by simpa [hUZeq] using this
            exact hwNeρ (by simpa using this)
          have hwNe1 : w ≠ (1 : ℂ) := by simpa [hρ1] using hwNeρ
          exact ⟨hwΩ, hwNe1, hwXi⟩
        have hSchur_U : RH.RS.IsSchurOn Θ (U \ {ρ}) := by
          intro w hw; exact hSchur_offXi w (hUminusSub_offXi_U hw)
        have hPFU := RH.RS.PinchFromExtension U hUopen hUconn ρ hρU Θ hΘU hSchur_U
          g hg hExt hval
        have hAllOneU : ∀ w ∈ U, g w = 1 := hPFU.1
        exact hAllOneU z0 hz0U
      exact (hneq this).elim
    · -- ρ ≠ 1: choose a ball that also avoids 1
      let δ : ℝ := dist ρ 1 / 2
      have hδpos : 0 < δ := by
        have : 0 < dist ρ 1 := by exact dist_pos.mpr hρ1
        exact half_pos this
      let t : ℝ := min εΩ (min εU δ)
      have htpos : 0 < t := lt_min (hεΩpos) (lt_min hεUpos hδpos)
      have hBall_sub_Ω : Metric.ball ρ t ⊆ RH.RS.Ω := by
        intro z hz
        have hzlt : dist z ρ < εΩ := lt_of_lt_of_le hz (min_le_left _ _)
        have : z ∈ Metric.ball ρ εΩ := by simpa [Metric.mem_ball] using hzlt
        exact hεΩsubset this

      have hBall_sub_U : Metric.ball ρ t ⊆ U := by
        intro z hz
        have hzlt : dist z ρ < εU :=
          lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_left _ _))
        have : z ∈ Metric.ball ρ εU := by simpa [Metric.mem_ball] using hzlt
        exact hεUsubset this
      -- 1 ∉ ball ρ t since t ≤ δ = dist ρ 1 / 2
      have hBall_avoids1 : (1 : ℂ) ∉ Metric.ball ρ t := by
        intro h1
        have ht_le_δ : t ≤ δ := by
          have : min εU δ ≤ δ := min_le_right _ _
          exact le_trans (min_le_right _ _) this
        -- From membership, get a strict inequality and push it to δ
        have hlt : dist ρ 1 < dist ρ 1 / 2 := by
          have h1' : dist 1 ρ < t := by simpa [Metric.mem_ball, dist_comm] using h1
          have : dist 1 ρ < δ := lt_of_lt_of_le h1' ht_le_δ
          simpa [δ, dist_comm] using this
        -- But x/2 < x for x > 0, contradiction
        have : ¬ dist ρ 1 ≤ dist ρ 1 / 2 := by
          have : 0 < dist ρ 1 := dist_pos.mpr hρ1
          exact not_le_of_gt (half_lt_self this)
        exact this (le_of_lt hlt)
      -- Define U' := ball ρ t and proceed as in the previous case
      let U' : Set ℂ := Metric.ball ρ t
      have hU'open : IsOpen U' := isOpen_ball
      have hU'subΩ : U' ⊆ RH.RS.Ω := hBall_sub_Ω
      have hρU' : ρ ∈ U' := by simpa [U', Metric.mem_ball, dist_self] using htpos
      have hIso' : (U' ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) := by
        apply Set.Subset.antisymm
        · intro z hz
          have hzU : z ∈ U := hBall_sub_U hz.1
          have hzpair : z ∈ U ∩ {z | riemannXi_ext z = 0} := ⟨hzU, hz.2⟩
          have : z ∈ ({ρ} : Set ℂ) := by simpa [hUZeq] using hzpair
          simpa using this
        · intro z hz; obtain rfl : z = ρ := by simpa [Set.mem_singleton_iff] using hz
          refine ⟨?_, ?_⟩
          · have : dist z z < t := by simpa [dist_self] using htpos
            simpa [U', Metric.mem_ball] using this
          · simp [hXiρ]
      have hUminusSub_offXi : (U' \ {ρ}) ⊆ RH.AcademicFramework.HalfPlaneOuterV2.offXi := by
        intro z hz
        have hzU' : z ∈ U' := hz.1
        have hzNeρ : z ≠ ρ := hz.2
        have hzΩ : z ∈ RH.RS.Ω := hU'subΩ hzU'
        have hzXi : riemannXi_ext z ≠ 0 := by
          intro h0
          have : z ∈ (U' ∩ {w | riemannXi_ext w = 0}) := ⟨hzU', by simpa [Set.mem_setOf_eq] using h0⟩
          have : z ∈ ({ρ} : Set ℂ) := by simpa [hIso'] using this
          exact hzNeρ (by simpa using this)
        have hzNe1 : z ≠ (1 : ℂ) := by
          intro h1
          have : (1 : ℂ) ∈ U' := by
            simpa [U', Metric.mem_ball, dist_comm, h1] using hzU'
          exact hBall_avoids1 this
        exact ⟨hzΩ, hzNe1, hzXi⟩
      have hSchur_U' : RH.RS.IsSchurOn Θ (U' \ {ρ}) := by
        intro z hz; exact hSchur_offXi z (hUminusSub_offXi hz)
      have hΘU' : AnalyticOn ℂ Θ (U' \ {ρ}) :=
        hΘU.mono (by intro z hz; exact ⟨hBall_sub_U hz.1, hz.2⟩)
      have hEqOn' : Set.EqOn Θ g (U' \ {ρ}) := by
        intro w hw; exact hExt ⟨hBall_sub_U hw.1, hw.2⟩
      have hPF := RH.RS.PinchFromExtension U' hU'open (isPreconnected_ball_complex ρ t) ρ hρU' Θ hΘU' hSchur_U'
        g (hg.mono (by intro w hw; exact hBall_sub_U hw)) hEqOn' hval
      -- g = 1 on U' and g analytic on U ⇒ g = 1 on all of U (identity theorem)
      have hEqOnU :
          Set.EqOn g (fun _ => (1 : ℂ)) U :=
        AnalyticOn.eqOn_of_isPreconnected_of_open_subset
          (hg)               -- g analytic on U
          hUconn             -- U is preconnected
          hUopen             -- U is open
          hU'open            -- U' is open
          (by
            -- U' ⊆ U
            intro x hx; exact hBall_sub_U hx)
          ⟨ρ, hρU'⟩           -- U' nonempty
          (by
            -- g = 1 on U'
            intro w hw; exact hPF.1 w hw)
      have hAllOneU : ∀ w ∈ U, g w = 1 := by
        intro w hw; simpa using hEqOnU hw
      have : g z0 = 1 := hAllOneU z0 hz0U
      exact (hneq this).elim
    -- Done
  -- Conclude via symmetry
  exact RH.Proof.RH_core (Ξ := riemannXi_ext) noRightZeros symXi

/-- Export to mathlib from the assign‑based pinch route. -/
theorem RiemannHypothesis_mathlib_from_pinch_ext_assign
    (Θ : ℂ → ℂ)
    (hSchur_offXi : RH.RS.IsSchurOn Θ RH.AcademicFramework.HalfPlaneOuterV2.offXi)
    (assign : ∀ ρ, ρ ∈ RH.RS.Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          Set.EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
    : RiemannHypothesis := by
  have Hxi : ∀ ρ, riemannXi_ext ρ = 0 → ρ.re = (1 / 2 : ℝ) :=
    RiemannHypothesis_from_pinch_ext_assign Θ hSchur_offXi assign
  exact RH_mathlib_from_xi_ext Hxi

end RH.Proof.Final

/-- Final theorem: build the `Ξ` assignment from a certificate and conclude RH. -/
theorem RH_from_pinch_certificate (C : RH.RS.PinchCertificateExt) : RiemannHypothesis := by
  -- Θ from certificate and its Schur bound off Z(Ξ_ext)
  have hSchur : RH.RS.IsSchurOn (RH.RS.Θ_cert C)
      RH.AcademicFramework.HalfPlaneOuterV2.offXi :=
    RH.RS.Θ_cert_Schur_offXi C
  -- Xi-assign from the certificate's removable existence
  let assignXi : ∀ ρ, ρ ∈ RH.RS.Ω → RH.AcademicFramework.CompletedXi.riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ (RH.RS.Θ_cert C) (U \ ({ρ} : Set ℂ)) ∧
          Set.EqOn (RH.RS.Θ_cert C) g (U \ ({ρ} : Set ℂ)) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1 :=
    fun ρ hΩ hXi => C.existsRemXi ρ hΩ hXi
  -- Conclude via the assign-based pinch on Ξ_ext
  exact RH.Proof.Final.RiemannHypothesis_mathlib_from_pinch_ext_assign
      (Θ := RH.RS.Θ_cert C) hSchur assignXi

-- Final unconditional entry will instantiate `RH_from_pinch_certificate` once
-- `J_pinch` is certified without axioms.

/-!
## Final Export Theorems

These provide the top-level interface for the Riemann Hypothesis proof.
-/

/-- Final Riemann Hypothesis theorem consuming a pinch certificate. -/
theorem RiemannHypothesis_final (C : RH.RS.PinchCertificateExt) : RiemannHypothesis :=
  RH_from_pinch_certificate C

/-- Convenience alias of the final theorem. -/
theorem RH (C : RH.RS.PinchCertificateExt) : RiemannHypothesis :=
  RiemannHypothesis_final C

/-- Clean pinch‑ingredients route from outer existence, interior positivity, and pinned data. -/
theorem RiemannHypothesis_from_pinch_ingredients
    (hOuter : ∃ O : ℂ → ℂ, _root_.RH.RS.OuterHalfPlane O ∧
        _root_.RH.RS.BoundaryModulusEq O (fun s => _root_.RH.RS.det2 s / riemannXi_ext s))
    (hRe_offXi : ∀ z ∈ RH.AcademicFramework.HalfPlaneOuterV2.offXi,
        0 ≤ ((2 : ℂ) * (_root_.RH.RS.J_pinch _root_.RH.RS.det2 (Classical.choose hOuter) z)).re)
    (hRemXi : ∀ ρ, ρ ∈ _root_.RH.RS.Ω → riemannXi_ext ρ = 0 →
        ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ _root_.RH.RS.Ω ∧ ρ ∈ U ∧
          (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
          ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧
            AnalyticOn ℂ (_root_.RH.RS.Θ_pinch_of _root_.RH.RS.det2 (Classical.choose hOuter)) (U \ {ρ}) ∧
            Set.EqOn (_root_.RH.RS.Θ_pinch_of _root_.RH.RS.det2 (Classical.choose hOuter)) g (U \ {ρ}) ∧
            g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
    : RiemannHypothesis := by
  exact RH_from_pinch_certificate
    (RH.RS.certificate_from_pinch_ingredients hOuter hRe_offXi hRemXi)

/-- Poisson+pinned route producing the pinch ingredients and concluding RH. -/
theorem RiemannHypothesis_from_poisson_and_pinned'
    (hOuter : ∃ O : ℂ → ℂ, _root_.RH.RS.OuterHalfPlane O ∧
        _root_.RH.RS.BoundaryModulusEq O (fun s => _root_.RH.RS.det2 s / riemannXi_ext s))
    (hPoisson : ∀ z ∈ RH.RS.Ω,
        0 ≤ ((2 : ℂ) * (_root_.RH.RS.J_pinch _root_.RH.RS.det2 (Classical.choose hOuter) z)).re)
    (hPinned : ∀ ρ, ρ ∈ RH.RS.Ω → riemannXi_ext ρ = 0 →
        ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
          (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
          AnalyticOn ℂ (_root_.RH.RS.Θ_pinch_of _root_.RH.RS.det2 (Classical.choose hOuter)) (U \ {ρ}) ∧
          ∃ u : ℂ → ℂ,
            Set.EqOn (_root_.RH.RS.Θ_pinch_of _root_.RH.RS.det2 (Classical.choose hOuter))
              (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
            Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) ∧
            ∃ z, z ∈ U ∧ z ≠ ρ ∧ (_root_.RH.RS.Θ_pinch_of _root_.RH.RS.det2 (Classical.choose hOuter)) z ≠ 1)
    : RiemannHypothesis := by
  classical
  -- Ingredient 1: restrict Poisson positivity to the AF `offXi` set
  let hRe_offXi : ∀ z ∈ RH.AcademicFramework.HalfPlaneOuterV2.offXi,
        0 ≤ ((2 : ℂ) * (_root_.RH.RS.J_pinch _root_.RH.RS.det2 (Classical.choose hOuter) z)).re :=
    fun z hz => hPoisson z (RH.AcademicFramework.HalfPlaneOuterV2.offXi_subset_Ω hz)
  -- Ingredient 2: package pinned data into a removable-extension assignment
  let hRemXi : ∀ ρ, ρ ∈ RH.RS.Ω → riemannXi_ext ρ = 0 →
        ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
          (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
          ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧
            AnalyticOn ℂ (_root_.RH.RS.Θ_pinch_of _root_.RH.RS.det2 (Classical.choose hOuter)) (U \ {ρ}) ∧
            Set.EqOn (_root_.RH.RS.Θ_pinch_of _root_.RH.RS.det2 (Classical.choose hOuter)) g (U \ {ρ}) ∧
            g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1 := by
    intro ρ hΩ hXi0
    rcases hPinned ρ hΩ hXi0 with
      ⟨U, hUopen, hUconn, hUsub, hρU, hIso,
       hΘU, u, hEq, hu0, z_nontrivial⟩
    let Θ : ℂ → ℂ := _root_.RH.RS.Θ_pinch_of _root_.RH.RS.det2 (Classical.choose hOuter)
    -- Eventual equality on the punctured neighborhood
    have hEq_ev : (fun w => Θ w) =ᶠ[nhdsWithin ρ (U \ {ρ})]
        (fun w => (1 - u w) / (1 + u w)) :=
      Set.EqOn.eventuallyEq_nhdsWithin (s := U \ {ρ}) hEq
    -- Limit Θ → 1 along the punctured approach (u → 0)
    have _hΘ_lim1 : Filter.Tendsto Θ (nhdsWithin ρ (U \ {ρ})) (nhds (1 : ℂ)) :=
      RH.RS.Theta_pinned_limit_from_N2 (U := U \ {ρ}) (ρ := ρ) (Θ := Θ) (u := u) hEq_ev hu0
    -- Define the removable extension g as an update at ρ
    let g : ℂ → ℂ := Function.update Θ ρ (1 : ℂ)
    have hEqOn : Set.EqOn Θ g (U \ {ρ}) := by
      intro w hw; simpa only [g, Function.update_noteq hw.2] using rfl
    have hval : g ρ = 1 := by
      classical
      simp [g]
    -- Analyticity of g on U via the pinned removable-update lemma
    have hgU : AnalyticOn ℂ g U := by
      exact RH.RS.analyticOn_update_from_pinned (U := U) (ρ := ρ) (Θ := Θ) (u := u)
        hUopen hρU hΘU hEq hu0
    -- Package the witness: provide a point where g ≠ 1 inherited from Θ ≠ 1
    rcases z_nontrivial with ⟨z0, hz0U, hz0ne, hΘz0⟩
    refine ⟨U, hUopen, hUconn, hUsub, hρU, hIso,
      ⟨g, hgU, hΘU, hEqOn, hval, z0, hz0U, ?nz⟩⟩
    intro hg1
    have : Θ z0 = 1 := by
      -- z0 ≠ ρ, so update leaves value unchanged
      have : g z0 = Θ z0 := by
        change Function.update Θ ρ (1 : ℂ) z0 = Θ z0
        simp [g, hz0ne]
      simpa [this] using hg1
    exact hΘz0 this
  -- Build certificate and conclude
  let C : RH.RS.PinchCertificateExt :=
    RH.RS.buildPinchCertificate hOuter hRe_offXi hRemXi
  exact RH_from_pinch_certificate C

-- (Cayley-transport variant omitted pending dedicated transport identities.)
