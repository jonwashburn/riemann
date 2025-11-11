import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import rh.RS.SchurGlobalization
import rh.RS.OffZerosBridge
import rh.RS.XiExtBridge
import rh.academic_framework.CompletedXi
-- keep this self-contained without importing Proof.Main to avoid cycles

/-!
# Active Proof Assembly

This file collects the minimal RH wrapper lemmas needed on the "active" proof
track. It re-implements the essential nonvanishing-to-critical-line arguments
without importing the heavier `CRGreenOuter`, `PoissonCayley`, or
`WhitneyGeometryDefs` modules so that downstream users can depend on a thin
interface.

## Main results

* `RH_core` — abstract symmetry lemma converting right-half nonvanishing into
  critical-line support.
* `Assembly.RH_riemannXi_from_RS_offZeros` — shows RH for a custom `riemannXi`
  given the RS Schur assign data.
* `Final.RiemannHypothesis_from_pinch_ext_assign` — specialization to the
  completed zeta together with an export version for mathlib.

## Design notes

All analytic and Schur hypotheses are passed in as parameters. This keeps the
file declarative: callers provide the invariants (factorizations, Schur
assignments, removable singularity data) and the lemmas merely orchestrate the
deduction.
-/

namespace RH
namespace Proof

set_option maxRecDepth 4096
set_option diagnostics true

open Complex Set Filter

/-- RH symmetry wrapper (statement-level, generic function Ξ):
If `Ξ` has no zeros in the open right half‑plane `Ω = {Re > 1/2}` and its zeros
are symmetric under `s ↦ 1 - s`, then every zero of `Ξ` lies on the critical
line `Re = 1/2`. -/
theorem RH_core
    {Ξ : ℂ → ℂ}
    (noRightZeros : ∀ ρ ∈ RH.RS.Ω, Ξ ρ ≠ 0)
    (sym : ∀ ρ, Ξ ρ = 0 → Ξ (1 - ρ) = 0) :
    ∀ ρ, Ξ ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  intro ρ h0
  rcases lt_trichotomy ρ.re (1 / 2 : ℝ) with hlt | heq | hgt
  · have hgt' : (1 / 2 : ℝ) < 1 - ρ.re := by linarith
    have hΩσ : (1 - ρ) ∈ RH.RS.Ω := by
      have : (1 / 2 : ℝ) < (1 - ρ).re := by
        simpa [Complex.sub_re, Complex.one_re] using hgt'
      simpa [RH.RS.Ω, Set.mem_setOf_eq] using this
    have h0σ : Ξ (1 - ρ) = 0 := sym ρ h0
    exact ((noRightZeros (1 - ρ) hΩσ) h0σ).elim
  · exact heq
  · have hΩ : ρ ∈ RH.RS.Ω := by simpa [RH.RS.Ω, Set.mem_setOf_eq] using hgt
    exact ((noRightZeros ρ hΩ) h0).elim

namespace Assembly

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
  have hζnz : ∀ ρ ∈ RH.RS.Ω, riemannZeta ρ ≠ 0 :=
    RH.RS.no_offcritical_zeros_from_schur Θ hSchur assign
  have hΞnz : ∀ ρ ∈ RH.RS.Ω, riemannXi ρ ≠ 0 :=
    nonvanishing_of_factor (Ω := RH.RS.Ω)
      (Ξ := riemannXi) (Z := riemannZeta) (G := G) hXiEq hGnz hζnz
  exact RH_core (Ξ := riemannXi) hΞnz symXi

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
  have hζnz : ∀ ρ ∈ RH.RS.Ω, riemannZeta ρ ≠ 0 :=
    RH.RS.no_offcritical_zeros_from_schur Θ hSchur assign
  have hΞnz : ∀ ρ ∈ RH.RS.Ω, riemannXi ρ ≠ 0 := by
    intro ρ hΩ
    have hEq : riemannXi ρ = G ρ * riemannZeta ρ := hXiEqΩ ρ hΩ
    have hG := hGnz ρ hΩ
    have hZ := hζnz ρ hΩ
    have : G ρ * riemannZeta ρ ≠ 0 := mul_ne_zero hG hZ
    intro hXi0; rw [hEq] at hXi0; exact this hXi0
  exact RH_core (Ξ := riemannXi) hΞnz symXi

end Assembly

namespace Final

open RH.AcademicFramework.CompletedXi

-- (Use the conversion provided in rh/Proof/Main.lean)

/-- Assign-based pinch route specialized to `riemannXi_ext`. -/
theorem RiemannHypothesis_from_pinch_ext_assign
    (Θ : ℂ → ℂ)
    (hSchur : RH.RS.IsSchurOn Θ (RH.RS.Ω \ {z | riemannXi_ext z = 0}))
    (assign : ∀ ρ, ρ ∈ RH.RS.Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          Set.EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
    : ∀ ρ, riemannXi_ext ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  -- FE for Ξ_ext and symmetry, derived from completed zeta FE
  have fe : ∀ s, riemannXi_ext s = riemannXi_ext (1 - s) :=
    fun s => by
      change completedRiemannZeta s = completedRiemannZeta (1 - s)
      exact RH.AcademicFramework.zeta_functional_equation s
  have symXi : ∀ ρ, riemannXi_ext ρ = 0 → riemannXi_ext (1 - ρ) = 0 :=
    fun ρ hρ => by
      have h := fe ρ
      have : riemannXi_ext (1 - ρ) = riemannXi_ext ρ := h.symm
      exact this.trans hρ
  -- FE for Ξ_ext and symmetry
  have fe : ∀ s, riemannXi_ext s = riemannXi_ext (1 - s) :=
    fun s => by
      change completedRiemannZeta s = completedRiemannZeta (1 - s)
      exact RH.AcademicFramework.zeta_functional_equation s
  have symXi : ∀ ρ, riemannXi_ext ρ = 0 → riemannXi_ext (1 - ρ) = 0 :=
    fun ρ hρ => by
      have h := fe ρ
      have : riemannXi_ext (1 - ρ) = riemannXi_ext ρ := h.symm
      exact this.trans hρ
  -- No-right-zeros via the assign-based pinch route
  have noRightZeros : ∀ ρ ∈ RH.RS.Ω, riemannXi_ext ρ ≠ 0 := by
    -- Prove via removable-globalization and Schur bound
    intro ρ hΩ hΞρ
    rcases assign ρ hΩ hΞρ with
      ⟨U, hUopen, hUconn, hUsub, hρU, hUZeq, g, hg, hΘU, hExt, hval, z0, hz0U, hneq⟩
    have hρZ : ρ ∈ ({z | riemannXi_ext z = 0} : Set ℂ) := by
      change riemannXi_ext ρ = 0
      exact hΞρ
    have hUminusSub : (U \ {ρ}) ⊆ (RH.RS.Ω \ ({z | riemannXi_ext z = 0})) := by
      intro x hx
      have hxU : x ∈ U := hx.1
      have hxNe : x ≠ ρ := by intro h; exact hx.2 (by simpa [h])
      have hxNotZ : x ∉ ({z | riemannXi_ext z = 0} : Set ℂ) := by
        intro hxZ
        have hxInCap : x ∈ (U ∩ {z | riemannXi_ext z = 0}) := ⟨hxU, hxZ⟩
        have hxSingleton : x ∈ ({ρ} : Set ℂ) := by
          -- rewrite cap equality without using simp
          have : (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) := hUZeq
          exact Eq.mp (congrArg (fun t => x ∈ t) this) hxInCap
        have : x = ρ := by
          exact Set.mem_singleton_iff.mp hxSingleton
        exact hxNe this
      exact ⟨hUsub hxU, hxNotZ⟩
    have hg_one : ∀ w ∈ U, g w = 1 :=
      RH.RS.GlobalizeAcrossRemovable ({z | riemannXi_ext z = 0}) Θ hSchur
        U hUopen hUconn hUsub ρ hΩ hρU hρZ g hg hΘU hUminusSub hExt hval
    have : g z0 = 1 := hg_one z0 hz0U
    exact (hneq this).elim
  exact RH_core (Ξ := riemannXi_ext) noRightZeros symXi

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
  -- Export wrapper: redo minimal conversion locally to avoid depending on Main
  have Hxi : ∀ ρ, riemannXi_ext ρ = 0 → ρ.re = (1 / 2 : ℝ) :=
    RiemannHypothesis_from_pinch_ext_assign Θ hSchur assign
  -- Convert to mathlib's statement for ζ via Λ relation
  intro s hζ _hneTriv _
  have hne0 : s ≠ 0 := by
    intro h0; simpa [h0, riemannZeta_zero] using hζ
  have hζdef : riemannZeta s = completedRiemannZeta s / s.Gammaℝ :=
    riemannZeta_def_of_ne_zero hne0
  -- Use trivial-zero guard to forbid Γ(s/2) poles
  have hNoPole : ∀ n : ℕ, s / 2 ≠ - (n : ℂ) := by
    intro n hn
    have two_ne_zero : (2 : ℂ) ≠ 0 := by norm_num
    -- Multiply equality by 2 and rewrite to obtain s = - (n) * 2
    have hmul2 := congrArg (fun z : ℂ => z * 2) hn
    have hs : s = - (n : ℂ) * 2 := by
      simpa [div_mul_cancel₀ s two_ne_zero] using hmul2
    cases n with
    | zero =>
      -- then s = 0, contradict nonzero
      have : s = 0 := by simpa using hs
      exact (hne0 this).elim
    | succ m =>
      -- from hn: s/2 = -(m+1), conclude s = -2 * (↑m + 1)
      have two_ne_zero : (2 : ℂ) ≠ 0 := by norm_num
      have hs0 : s = -2 * ((Nat.succ m : ℕ) : ℂ) := by
        have : s = (s / 2) * 2 := by rw [div_mul_cancel₀ _ two_ne_zero]
        calc
          s = (s / 2) * 2 := this
          _ = (-((m + 1 : ℕ) : ℂ)) * 2 := by simpa [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using congrArg (fun z : ℂ => z * 2) hn
          _ = -2 * ((Nat.succ m : ℕ) : ℂ) := by
            -- -(a) * 2 = -2 * a in a commutative ring
            ring
      have hsWanted : s = -2 * ((m : ℂ) + 1) := by
        simpa [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using hs0
      exact _hneTriv ⟨m, hsWanted⟩
  -- Γℝ(s) ≠ 0 from no-pole
  have hΓR_ne : s.Gammaℝ ≠ 0 := by
    -- use standard nonvanishing factoring: Γℝ(s) = π^{-s/2} Γ(s/2)
    have hπ0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hpow : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
      exact Or.inl hπ0
    have hΓ : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero (by intro n; exact hNoPole n)
    -- unfold Gammaℝ and apply nonvanishing of factors
    change (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) ≠ 0
    exact mul_ne_zero hpow hΓ
  have hΛeq' : riemannZeta s * s.Gammaℝ = completedRiemannZeta s := by
    calc
      riemannZeta s * s.Gammaℝ = (completedRiemannZeta s / s.Gammaℝ) * s.Gammaℝ := by rw [hζdef]
      _ = completedRiemannZeta s := div_mul_cancel₀ _ hΓR_ne
  have hΛ0 : completedRiemannZeta s = 0 := by rw [<- hΛeq', hζ, zero_mul]
  have hXi0 : riemannXi_ext s = 0 := by
    change completedRiemannZeta s = 0
    exact hΛ0
  exact Hxi s hXi0

end Final

end Proof
end RH
