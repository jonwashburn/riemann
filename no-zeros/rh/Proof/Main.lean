import rh.academic_framework.Certificate
import rh.RS.SchurGlobalization
import rh.RS.BoundaryWedgeProof
import rh.Cert.KxiWhitney
import Mathlib.Topology.Defs.Filter
import rh.academic_framework.EulerProductMathlib
import rh.academic_framework.CompletedXi
import rh.academic_framework.CompletedXiSymmetry
import rh.academic_framework.Theta
import rh.RS.OffZerosBridge
import rh.RS.Cayley
import rh.RS.PinchCertificate
import rh.RS.XiExtBridge
import rh.RS.SchurGlobalization
import rh.RS.CRGreenOuter
-- CompletedXi import deferred until formalization lands
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Topology.Basic
import rh.RS.PinchIngredients

set_option maxRecDepth 4096
set_option diagnostics true

namespace RH.Proof

/-/ Proof-layer alias for certificate readiness. -/
def PipelineReady : Prop := RH.AcademicFramework.Certificate.Ready

/-- Bridge: certificate readiness implies proof-layer readiness. -/
theorem pipeline_ready_of_certificate_ready
    (h : RH.AcademicFramework.Certificate.Ready) : PipelineReady := h

/-- Unconditional pipeline readiness, delegated to the certificate layer. -/
theorem pipeline_ready_unconditional : PipelineReady := by
  exact pipeline_ready_of_certificate_ready
    (RH.AcademicFramework.Certificate.Ready_unconditional)

end RH.Proof

-- Specialized wrappers are placed after `theorem RH` below

namespace RH.Proof.Assembly

/-- Boundary nonvanishing from the RS off-zeros boundary hypothesis (statement-level). -/
theorem boundary_nonvanishing_from_offzeros
    {Θ N : ℂ → ℂ}
    (h : RH.RS.OffZerosBoundaryHypothesis Θ N) :
    ∀ z, z.re = 1 → riemannZeta z ≠ 0 :=
  RH.RS.ZetaNoZerosOnRe1_from_offZerosAssignmentStatement h

/-- EPM-facing pointwise wrapper for the same statement. -/
theorem boundary_nonvanishing_from_offzeros_pointwise
    {Θ N : ℂ → ℂ}
    (h : RH.RS.OffZerosBoundaryHypothesis Θ N)
    (z : ℂ) (hz : z.re = 1) :
    riemannZeta z ≠ 0 :=
  RH.AcademicFramework.EPM.zeta_nonzero_re_eq_one_from_offZerosAssignmentStatement h z hz

end RH.Proof.Assembly

namespace RH.Proof.Assembly

/-- Pack the RS data needed to drive RH for a supplied `riemannXi`. -/
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

/-- RH symmetry wrapper (statement-level, generic function Ξ):
If `Ξ` has no zeros in the open right half‑plane `Ω = {Re > 1/2}` and its zeros
are symmetric under `s ↦ 1 - s`, then every zero of `Ξ` lies on the critical
line `Re = 1/2`.

This is the abstract symmetry pinching step; consumers can instantiate `Ξ` with
a completed zeta–type function that satisfies the functional equation. -/
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

/-- RH specialized to an arbitrary function `Ξ` under the standard two hypotheses. -/
theorem RH_for
    (Ξ : ℂ → ℂ)
    (noRightZeros : ∀ ρ ∈ RH.RS.Ω, Ξ ρ ≠ 0)
    (sym : ∀ ρ, Ξ ρ = 0 → Ξ (1 - ρ) = 0) :
    ∀ ρ, Ξ ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  exact (RH_core (Ξ := Ξ) noRightZeros sym)

/-- RH specialized to a provided symbol `riemannXi` (completed zeta),
    assuming no zeros on Ω and symmetry of zeros. -/
theorem RH_riemannXi
    (riemannXi : ℂ → ℂ)
    (noRightZeros : ∀ ρ ∈ RH.RS.Ω, riemannXi ρ ≠ 0)
    (sym : ∀ ρ, riemannXi ρ = 0 → riemannXi (1 - ρ) = 0) :
    ∀ ρ, riemannXi ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  exact (RH_core (Ξ := riemannXi) noRightZeros sym)

end RH.Proof

namespace RH.Proof.Assembly

/-- Factorization transfer: if `Ξ = G · Z` on a set `Ω` and both `G` and `Z`
    are nonvanishing on `Ω`, then `Ξ` is nonvanishing on `Ω`. -/
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

/-- Route assembly: assuming
    1) symmetry of zeros for a provided `riemannXi`,
    2) a factorization `riemannXi = G · ζ` with `G` zero‑free on `Ω`, and
    3) an RS Schur–pinch off‑zeros assignment excluding ζ‑zeros in `Ω`,
    we obtain RH for `riemannXi`. -/
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

/-- Local-equality variant: `riemannXi = G·ζ` only on Ω suffices. -/
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

/-- Route assembly (one-safe variant): allow `G ≠ 0` on `Ω \ {1}` and a separate
    nonvanishing fact `riemannXi 1 ≠ 0`. -/
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

/-- Route assembly (one-safe, local equality variant): allow
    1) zero-symmetry for a provided `riemannXi`,
    2) factorization `riemannXi = G · ζ` only on `Ω \ {1}`,
    3) nonvanishing of `G` on `Ω \ {1}` plus a separate center value `riemannXi 1 ≠ 0`, and
    4) RS Schur–pinch off‑zeros assignment excluding ζ‑zeros in `Ω`.

    Concludes RH for the provided `riemannXi`. -/
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

/-- Transport disjunction to 1−ρ from zero-symmetry and factorization. -/
lemma disj_at_one_sub_of_xi_zero
    (hXiEq : ∀ s, riemannXi s = G s * riemannZeta s)
    (symXi : ∀ s, riemannXi s = 0 → riemannXi (1 - s) = 0)
    (ρ : ℂ) (hXi0 : riemannXi ρ = 0)
    : G (1 - ρ) = 0 ∨ riemannZeta (1 - ρ) = 0 := by
  have h1 : riemannXi (1 - ρ) = 0 := symXi ρ hXi0
  have hfac := hXiEq (1 - ρ)
  -- exact transport of zero across factorization
  have := h1; simpa [hfac] using this

/-- RH for `riemannXi` from supplied FE, Schur map Θ, assignment, and nonvanishing of G on Ω. -/
theorem RH_xi_from_supplied_RS
    (fe : ∀ s, riemannXi s = riemannXi (1 - s))
    (Θ : ℂ → ℂ)
    (hSchur : RH.RS.IsSchurOn Θ (RH.RS.Ω \ {z | riemannZeta z = 0}))
    (assign : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          Set.EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
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
    simpa [xi_factorization ρ] using mul_ne_zero hG hZ
  -- Conclude RH for Ξ by symmetry wrapper
  exact RH_riemannXi riemannXi hΞnz symXi

end RH.Proof.Final

namespace RH.Proof.Final

open RH.AcademicFramework.CompletedXi

/-- Nonvanishing of Γℝ(s) away from poles. -/
lemma GammaR_ne_zero_of_not_pole {s : ℂ} (h : ∀ n : ℕ, s / 2 ≠ - (n : ℂ)) : s.Gammaℝ ≠ 0 := by
  have hπ0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hpow : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl hπ0
  have hΓ : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero h
  rw [Complex.Gammaℝ_def]
  exact mul_ne_zero hpow hΓ

/-- Convert Hxi for the ext variant to mathlib's `RiemannZeta.RiemannHypothesis`. -/
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

/-- CR-outer full route for the ext variant. -/
theorem RiemannHypothesis_from_CR_outer_ext
    (fe : ∀ s, RH.AcademicFramework.CompletedXi.riemannXi_ext s = RH.AcademicFramework.CompletedXi.riemannXi_ext (1 - s))
    (choose : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      RH.RS.OffZeros.LocalData (riemannZeta := riemannZeta)
        (Θ := RH.RS.Θ_of RH.RS.CRGreenOuterData) (ρ := ρ))
    (hGnz : ∀ ρ ∈ RH.RS.Ω, RH.AcademicFramework.CompletedXi.G_ext ρ ≠ 0)
    : ∀ ρ, RH.AcademicFramework.CompletedXi.riemannXi_ext ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  -- Build Θ and Schur bound from outer data
  let Θ : ℂ → ℂ := RH.RS.Θ_of RH.RS.CRGreenOuterData
  have hSchur : RH.RS.IsSchurOn Θ (RH.RS.Ω \ {z | riemannZeta z = 0}) :=
    RH.RS.Θ_Schur_of RH.RS.CRGreenOuterData
  let assign := RH.RS.OffZeros.assign_fromLocal (Θ := Θ) (choose := choose)
  -- zero symmetry for Ξ_ext from FE
  have symXi : ∀ ρ, riemannXi_ext ρ = 0 → riemannXi_ext (1 - ρ) = 0 :=
    RH.AcademicFramework.CompletedXi.zero_symmetry_from_fe riemannXi_ext fe
  -- ζ has no zeros on Ω
  have hζnz : ∀ ρ ∈ RH.RS.Ω, riemannZeta ρ ≠ 0 :=
    RH.RS.no_offcritical_zeros_from_schur Θ hSchur assign
  -- Nonvanishing of Ξ_ext on Ω via local factorization on Ω
  have hΞnz : ∀ ρ ∈ RH.RS.Ω, riemannXi_ext ρ ≠ 0 := by
    intro ρ hΩ
    have hEq : riemannXi_ext ρ = G_ext ρ * riemannZeta ρ :=
      RH.AcademicFramework.CompletedXi.xi_ext_factorization_on_Ω ρ hΩ
    have hG := hGnz ρ hΩ
    have hZ := hζnz ρ hΩ
    have : G_ext ρ * riemannZeta ρ ≠ 0 := mul_ne_zero hG hZ
    intro hXi0; rw [hEq] at hXi0; exact this hXi0
  -- Conclude RH for Ξ_ext by symmetry wrapper
  exact RH_riemannXi riemannXi_ext hΞnz symXi

end RH.Proof.Final

namespace RH.Proof.Final

open RH.AcademicFramework.CompletedXi

/-- One-shot wrapper: from CR-outer choose, FE for `riemannXi_ext`, and nonvanishing of `G_ext`
 on `Ω`, conclude mathlib's `RiemannZeta.RiemannHypothesis`. -/
theorem RiemannHypothesis_mathlib_from_CR_outer_ext
    (choose : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      RH.RS.OffZeros.LocalData (riemannZeta := riemannZeta)
        (Θ := RH.RS.Θ_of RH.RS.CRGreenOuterData) (ρ := ρ))
    (hGnz : ∀ ρ ∈ RH.RS.Ω, G_ext ρ ≠ 0)
    : RiemannHypothesis := by
  -- FE for Ξ_ext via dedicated lemma to avoid aliasing
  have fe : ∀ s, riemannXi_ext s = riemannXi_ext (1 - s) :=
    fun s => RH.AcademicFramework.CompletedXi.xi_ext_functional_equation s
  -- Get Hxi_ext from the CR-outer route
  have Hxi : ∀ ρ, riemannXi_ext ρ = 0 → ρ.re = (1 / 2 : ℝ) :=
    RiemannHypothesis_from_CR_outer_ext fe choose hGnz
  -- Export to mathlib
  exact RH_mathlib_from_xi_ext Hxi

-- (legacy wrapper removed)
end RH.Proof.Final

/- End-to-end certificate route (integration check): from
1) outer existence on Ω with boundary modulus `|det₂/ξ_ext|`,
2) a half–plane Poisson transport predicate for `F := 2·J_pinch det2 O`,
3) a Kξ certificate `KxiBound α c`, and
4) pinned u‑trick data at each `ξ_ext` zero,
conclude `RiemannHypothesis` by invoking the certificate pipeline.

This theorem wires the existing RS/Cert lemmas without introducing new
assumptions beyond the route inputs. -/
-- moved below wrappers to avoid forward reference

namespace RH.Proof.Final

open RH.AcademicFramework.CompletedXi

/-- One-shot wrapper (removable-extension form): assuming for each ζ-zero `ρ ∈ Ω` there exists
an open, preconnected `U ⊆ Ω` isolating `ρ` and an analytic extension `g` of
`Θ := Θ_of CRGreenOuterData` across `ρ` with `g ρ = 1` and not identically `1`,
conclude mathlib's `RiemannHypothesis` via the ext route. -/
theorem RiemannHypothesis_mathlib_from_CR_outer_ext_removable
    (hRem : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧
          AnalyticOn ℂ (RH.RS.Θ_of RH.RS.CRGreenOuterData) (U \ {ρ}) ∧
          Set.EqOn (RH.RS.Θ_of RH.RS.CRGreenOuterData) g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1) :
    RiemannHypothesis := by
  -- Package a `LocalData` chooser from the removable-extension assignment
  let chooseOff := RH.RS.OffZeros.choose_CR
      (Θ := RH.RS.Θ_of RH.RS.CRGreenOuterData)
      (assign :=
        (fun ρ (hΩ : ρ ∈ RH.RS.OffZeros.Ω) (hζ : riemannZeta ρ = 0) =>
          hRem ρ (by simpa [RH.RS.OffZeros.Ω, RH.RS.Ω, Set.mem_setOf_eq] using hΩ) hζ))
  let choose : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      RH.RS.OffZeros.LocalData (riemannZeta := riemannZeta)
        (Θ := RH.RS.Θ_of RH.RS.CRGreenOuterData) (ρ := ρ) :=
    fun ρ hΩ hζ =>
      chooseOff ρ (by simpa [RH.RS.OffZeros.Ω, RH.RS.Ω, Set.mem_setOf_eq] using hΩ) hζ
  -- Nonvanishing of the ext Archimedean factor on Ω
  have hGnz : ∀ ρ ∈ RH.RS.Ω, G_ext ρ ≠ 0 := G_ext_nonzero_on_Ω
  -- Invoke the ext route
  exact RiemannHypothesis_mathlib_from_CR_outer_ext choose hGnz

-- (assign-based pinch wrappers removed; we keep the CR-outer removable route and pinch skeleton)

-- (assign-based entry wrapper removed; use CR-outer removable route or pinch skeleton)

end RH.Proof.Final

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

/-- No-right-zeros from an RS-style removable assignment. If `Θ` is Schur on
`Ω \\ {Ξ=0}` and for each putative zero `ρ` there is a local removable extension
`g` with `g ρ = 1` that agrees with `Θ` on `U \\ {ρ}` and is not identically `1`,
then `Ξ` has no zeros on `Ω`. -/
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
      intro h; exact hx.2 (by simpa [h])
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

/-- RH from the assign-based pinch. -/
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

/-- Specialization of the assign-based pinch to `riemannXi_ext`. -/
theorem RiemannHypothesis_from_pinch_ext_assign
    (Θ : ℂ → ℂ)
    (hSchur : RH.RS.IsSchurOn Θ (RH.RS.Ω \ {z | riemannXi_ext z = 0}))
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
  exact RH.Proof.poissonIntegralinch.RH_from_pinch_assign riemannXi_ext Θ symXi hSchur assign

/-- Export to mathlib from the assign-based pinch route. -/
theorem RiemannHypothesis_mathlib_from_pinch_ext_assign
    (Θ : ℂ → ℂ)
    (hSchur : RH.RS.IsSchurOn Θ (RH.RS.Ω \ {z | riemannXi_ext z = 0}))
    (assign : ∀ ρ, ρ ∈ RH.RS.Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          Set.EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
    : RiemannHypothesis := by
  have Hxi : ∀ ρ, riemannXi_ext ρ = 0 → ρ.re = (1 / 2 : ℝ) :=
    RiemannHypothesis_from_pinch_ext_assign Θ hSchur assign
  exact RH_mathlib_from_xi_ext Hxi

end RH.Proof.Final

/--- Assign-based entry wrapper: given a removable-extension assignment at `Ξ_ext`-zeros
in `Ω` for a candidate `Θ`, conclude `RiemannHypothesis` via the assign-based pinch. -/
theorem RH_from_assign
    (assign : ∀ ρ, ρ ∈ RH.RS.Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ (RH.RS.Θ_of RH.RS.CRGreenOuterData) (U \ {ρ}) ∧
          Set.EqOn (RH.RS.Θ_of RH.RS.CRGreenOuterData) g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
    : RiemannHypothesis := by
  refine RH.Proof.Final.RiemannHypothesis_mathlib_from_pinch_ext_assign
    (Θ := RH.RS.Θ_of RH.RS.CRGreenOuterData)
    (by
      intro z hz
      have hSchur : RH.RS.IsSchurOn (RH.RS.Θ_of RH.RS.CRGreenOuterData)
                      (RH.RS.Ω \ {w | riemannZeta w = 0}) :=
        RH.RS.Θ_Schur_of RH.RS.CRGreenOuterData
      have hzΩ : z ∈ RH.RS.Ω := hz.1
      have hzXi_ne : riemannXi_ext z ≠ 0 := by
        simpa [Set.mem_setOf_eq] using hz.2
      have hzZeta_ne : riemannZeta z ≠ 0 := by
        intro hζ
        have hXi : riemannXi_ext z = 0 :=
          (RH.AcademicFramework.CompletedXi.xi_ext_zeros_eq_zeta_zeros_on_Ω z hzΩ).mpr hζ
        exact hzXi_ne hXi
      have hzMem : z ∈ RH.RS.Ω \ {w | riemannZeta w = 0} := by
        refine ⟨hzΩ, ?_⟩
        intro hzSet
        have hζ : riemannZeta z = 0 := by
          simpa [Set.mem_setOf_eq] using hzSet
        exact hzZeta_ne hζ
      exact hSchur z hzMem
      )
    assign

/-- Final theorem using a concrete pinch certificate: build the Ξ-assign from
the certificate and conclude RH. -/
theorem RH_from_pinch_certificate (C : RH.RS.PinchCertificateExt) : RiemannHypothesis := by
  -- Θ from certificate and its Schur bound off Z(Ξ_ext)
  have hSchur : RH.RS.IsSchurOn (RH.RS.Θ_cert C)
      (RH.RS.Ω \ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0}) :=
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

/-- Final Riemann Hypothesis theorem consuming a pinch certificate.
This will be instantiated with a concrete certificate witness. -/
theorem RiemannHypothesis_final (C : RH.RS.PinchCertificateExt) : RiemannHypothesis :=
  RH_from_pinch_certificate C

-- (legacy convenience alias removed to avoid name shadowing)

/-- Top-level RH theorem (certificate-driven alias).
Given a pinch certificate `C`, conclude `RiemannHypothesis`. -/
theorem RH (C : RH.RS.PinchCertificateExt) : RiemannHypothesis :=
  RiemannHypothesis_final C

/-- Clean pinch-ingredients route: given
1) outer existence for `|det₂/ξ_ext|` on Ω,
2) interior positivity `0 ≤ Re(2·J_pinch)` on `Ω \ Z(ξ_ext)`, and
3) a pinned removable extension of `Θ := Cayley(2·J_pinch)` across each `ξ_ext` zero,
conclude mathlib's `RiemannHypothesis` via `RH.RS.RH_from_pinch_ingredients`. -/
theorem RiemannHypothesis_from_pinch_ingredients
    (hOuter : ∃ O : ℂ → ℂ, _root_.RH.RS.OuterHalfPlane O ∧
        _root_.RH.RS.BoundaryModulusEq O (fun s => _root_.RH.RS.det2 s / riemannXi_ext s))
    (hRe_offXi : ∀ z ∈ (_root_.RH.RS.Ω \ {z | riemannXi_ext z = 0}),
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

/-- Convenience: derive the two pinch ingredients from
1) a Poisson interior-positivity statement on Ω for `F := 2·J_pinch`, and
2) pinned u-trick data at each `ξ_ext`-zero,
then conclude `RiemannHypothesis`. -/
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
  -- Ingredient 1: restrict Poisson positivity to the off-zeros set
  let hRe_offXi : ∀ z ∈ (RH.RS.Ω \ {z | riemannXi_ext z = 0}),
        0 ≤ ((2 : ℂ) * (_root_.RH.RS.J_pinch _root_.RH.RS.det2 (Classical.choose hOuter) z)).re :=
    fun z hz => hPoisson z hz.1
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
