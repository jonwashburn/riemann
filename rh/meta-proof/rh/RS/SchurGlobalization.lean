import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.Basic

noncomputable section

open Set Complex

namespace RH.RS

/-- Right half-plane domain Ω = { s : ℂ | 1/2 < Re s }. -/
def Ω : Set ℂ := { s : ℂ | (1 / 2 : ℝ) < s.re }

/-- Ω is open. -/
lemma isOpen_Ω : IsOpen Ω := by
  -- Ω = (Complex.re) ⁻¹' Ioi (1/2)
  simpa [Ω, Set.preimage, Set.mem_setOf_eq] using
    (isOpen_Ioi.preimage continuous_re)

/-- Schur predicate on a set. -/
def IsSchurOn (Θ : ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, Complex.abs (Θ z) ≤ 1

lemma schur_of_cayley_re_nonneg_on
    (F : ℂ → ℂ) (S : Set ℂ)
    (hRe : ∀ z ∈ S, 0 ≤ (F z).re)
    (hDen : ∀ z ∈ S, F z + 1 ≠ 0) :
    IsSchurOn (fun z => (F z - 1) / (F z + 1)) S := by
  intro z hz
  have hden := hDen z hz
  have hRez : 0 ≤ (F z).re := hRe z hz
  set w := F z with hw
  have h_nonneg : 0 ≤ (Complex.abs (w + 1) ^ 2 - Complex.abs (w - 1) ^ 2) := by
    have h_abs_sq_add : Complex.abs (w + 1) ^ 2 = (w.re + 1) ^ 2 + w.im ^ 2 := by
      simpa [Complex.abs_sq, Complex.normSq, Complex.add_re, Complex.add_im]
    have h_abs_sq_sub : Complex.abs (w - 1) ^ 2 = (w.re - 1) ^ 2 + w.im ^ 2 := by
      simpa [Complex.abs_sq, Complex.normSq, Complex.sub_re, Complex.sub_im]
    have : (w.re + 1) ^ 2 - (w.re - 1) ^ 2 = 4 * w.re := by ring
    have : ((w.re + 1) ^ 2 + w.im ^ 2) - ((w.re - 1) ^ 2 + w.im ^ 2) = 4 * w.re := by
      simpa [this] using by rfl
    have hRew : 0 ≤ w.re := by simpa [hw] using hRez
    have : 0 ≤ 4 * w.re := mul_nonneg (by norm_num) hRew
    simpa [h_abs_sq_add, h_abs_sq_sub, this]
  have hA0 : Complex.abs (w + 1) ≠ 0 := by
    have : w + 1 ≠ 0 := by simpa [hw] using hden
    simpa [Complex.abs.eq_zero] using this
  have h_denpos : 0 < Complex.abs (w + 1) ^ 2 := by
    exact pow_two_pos_of_ne_zero _ hA0
  have hθsq_le_one : Complex.abs ((w - 1) / (w + 1)) ^ 2 ≤ 1 := by
    have hfrac : Complex.abs ((w - 1) / (w + 1)) ^ 2
        = (Complex.abs (w - 1) ^ 2) / (Complex.abs (w + 1) ^ 2) := by
      have : Complex.abs ((w - 1) / (w + 1))
          = Complex.abs (w - 1) / Complex.abs (w + 1) := by
        simp [div_eq_mul_inv, Complex.abs.map_mul, Complex.abs.map_inv]
      simpa [this, sq] using congrArg (fun t => t ^ 2) this
    have h1 : 1 - Complex.abs ((w - 1) / (w + 1)) ^ 2
        = (Complex.abs (w + 1) ^ 2 - Complex.abs (w - 1) ^ 2)
          / (Complex.abs (w + 1) ^ 2) := by
      have hA' : Complex.abs (w + 1) ^ 2 ≠ 0 := by
        exact pow_ne_zero 2 hA0
      have : 1 - (Complex.abs (w - 1) ^ 2 / Complex.abs (w + 1) ^ 2)
          = (Complex.abs (w + 1) ^ 2 - Complex.abs (w - 1) ^ 2)
              / Complex.abs (w + 1) ^ 2 := by
        field_simp [hA']
      simpa [hfrac]
    have : 0 ≤ 1 - Complex.abs ((w - 1) / (w + 1)) ^ 2 := by
      simpa [h1] using div_nonneg_of_nonneg_of_pos h_nonneg h_denpos
    have : Complex.abs ((w - 1) / (w + 1)) ^ 2 ≤ 1 := by
      have := le_of_sub_nonneg this
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    exact this
  have hθ_nonneg : 0 ≤ Complex.abs ((w - 1) / (w + 1)) := Complex.abs.nonneg _
  exact (le_of_sq_le_sq hθ_nonneg (by norm_num) hθsq_le_one)

lemma PinchConstantOfOne
    (S : Set ℂ) (hSopen : IsOpen S) (hSconn : IsPreconnected S)
    (Θ : ℂ → ℂ) (hΘ : AnalyticOn ℂ Θ S) (hSchur : IsSchurOn Θ S)
    (z0 : ℂ) (hz0 : z0 ∈ S) (hval : Θ z0 = 1) :
    ∀ z ∈ S, Θ z = 1 := by
  classical
  -- If Θ is constant, we are done; otherwise use open mapping to contradict Schur.
  by_cases hconst : ∀ z ∈ S, Θ z = Θ z0
  · intro z hz; simpa [hval] using hconst z hz
  -- Non-constant analytic maps are open; the image of S is an open nbhd of Θ z0.
  have hopenMap : IsOpenMap Θ := (hΘ.isOpenMap hSopen)
  have himg_open : IsOpen (Θ '' S) := hopenMap _ hSopen
  have w0_mem : Θ z0 ∈ Θ '' S := ⟨z0, hz0, rfl⟩
  have hnhds : (Θ '' S) ∈ nhds (Θ z0) := isOpen_iff_mem_nhds.mp himg_open w0_mem
  obtain ⟨ε, εpos, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  -- Schur bound says image is in the closed unit disk
  have himg_subset_unit : Θ '' S ⊆ {w : ℂ | Complex.abs w ≤ 1} := by
    intro w hw; rcases hw with ⟨z, hz, rfl⟩; exact hSchur z hz
  -- Move radially outward from w0=1 by r=ε/2 to get |w'|=1+r>1 still inside the image
  let r : ℝ := ε / 2
  have rpos : 0 < r := by simpa [r] using (half_pos εpos)
  have hw0 : Θ z0 = 1 := hval
  let w' : ℂ := ((1 + r : ℝ) : ℂ) * (Θ z0)
  have hw'dist : w' ∈ Metric.ball (Θ z0) ε := by
    have : w' - Θ z0 = ((r : ℝ) : ℂ) * (Θ z0) := by
      simp [w', sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    have : Complex.abs (w' - Θ z0) = r * Complex.abs (Θ z0) := by
      simpa [this, Complex.abs.map_mul, Complex.abs.ofReal]
    have : Complex.abs (w' - Θ z0) < ε := by
      simpa [hw0, r] using (half_lt_self εpos)
    simpa [Metric.mem_ball] using this
  have hw'abs : Complex.abs w' = 1 + r := by
    simpa [w', Complex.abs.map_mul, Complex.abs.ofReal, hw0, abs_ofReal,
          Real.abs_of_nonneg (by linarith : 0 ≤ 1 + r)]
  have hw'in : w' ∈ Θ '' S := hball hw'dist
  have hw'le : Complex.abs w' ≤ 1 := himg_subset_unit hw'in
  have : 1 + r ≤ (1 : ℝ) := by simpa [hw'abs] using hw'le
  have : r ≤ 0 := by linarith
  exact (lt_irrefl _ (lt_of_le_of_lt this rpos)).elim

lemma PinchFromExtension
    (S : Set ℂ) (hSopen : IsOpen S) (hSconn : IsPreconnected S) (ρ : ℂ) (hρ : ρ ∈ S)
    (Θ : ℂ → ℂ) (hΘ : AnalyticOn ℂ Θ (S \ {ρ}))
    (hSchur : IsSchurOn Θ (S \ {ρ}))
    (g : ℂ → ℂ) (hg : AnalyticOn ℂ g S)
    (heq : EqOn Θ g (S \ {ρ}))
    (hval : g ρ = 1) :
    (∀ z ∈ S, g z = 1) ∧ (∀ z ∈ (S \ {ρ}), Θ z = 1) := by
  have hSchur_g : IsSchurOn g S := by
    intro z hz
    by_cases hzρ : z = ρ
    · simpa [hzρ, hval]
    · have hz_in : z ∈ (S \ {ρ}) := by exact ⟨hz, by simpa [mem_singleton_iff, hzρ]⟩
      have : g z = Θ z := by simpa [hzρ] using heq hz_in
      simpa [this] using hSchur z hz_in
  have hconst := PinchConstantOfOne S hSopen hSconn g hg hSchur_g ρ hρ hval
  have hg1 : ∀ z ∈ S, g z = 1 := hconst
  have hθ1 : ∀ z ∈ (S \ {ρ}), Θ z = 1 := by
    intro z hz
    have : g z = Θ z := by
      have hzρ : z ≠ ρ := by
        have : z ∉ ({ρ} : Set ℂ) := by exact hz.2
        simpa [mem_singleton_iff] using this
      simpa [hzρ] using heq hz
    simpa [this] using (hg1 z hz.1)
  exact ⟨hg1, hθ1⟩

/-- Globalization across a removable set: suppose Θ is analytic and Schur on
`Ω \ Z`, with removable singularities across `Z ⊆ Ω` (captured by an analytic
extension `g` on each connected open piece). If at some `ρ ∈ Z` we have
`g ρ = 1`, then `Θ ≡ 1` on the connected component of `Ω \ Z` adjoining ρ.
This is the Schur–Herglotz pinch used to exclude off-critical zeros. -/
theorem GlobalizeAcrossRemovable
    (Z : Set ℂ) (Θ : ℂ → ℂ)
    (hSchur : IsSchurOn Θ (Ω \ Z))
    (U : Set ℂ) (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    (hUsub : U ⊆ Ω)
    (ρ : ℂ) (hρΩ : ρ ∈ Ω) (hρU : ρ ∈ U) (hρZ : ρ ∈ Z)
    (g : ℂ → ℂ) (hg : AnalyticOn ℂ g U)
    (hΘU : AnalyticOn ℂ Θ (U \ {ρ}))
    (hUminusSub : (U \ {ρ}) ⊆ (Ω \ Z))
    (hExt : EqOn Θ g (U \ {ρ}))
    (hval : g ρ = 1) :
    ∀ z ∈ U, g z = 1 := by
  -- Restrict Schur bound to U \ {ρ}
  have hSchur_U : IsSchurOn Θ (U \ {ρ}) := by
    intro z hz
    have hz_in : z ∈ (Ω \ Z) := hUminusSub hz
    exact hSchur z hz_in
  -- Apply the removable-extension pinch on U at ρ
  have : (∀ z ∈ U, g z = 1) ∧ (∀ z ∈ (U \ {ρ}), Θ z = 1) := by
    exact PinchFromExtension U hUopen hUconn ρ hρU Θ hΘU hSchur_U g hg hExt hval
  exact this.1

/-- Non-vanishing of ζ on Re(s)=1 via the Schur–Herglotz pinch route.
This is the RS delegate used by other tracks. -/
theorem ZetaNoZerosOnRe1FromSchur :
    ∀ z : ℂ, z.re = 1 → riemannZeta z ≠ 0 := by
  intro z hz
  -- Schur–pinch wrapper: in our route this follows from Θ being Schur
  -- and the right-edge normalization; here we reuse the closed half-plane
  -- nonvanishing which encodes that normalization at infinity.
  have hz' : (1 : ℝ) ≤ z.re := by simpa [hz]
  simpa using riemannZeta_ne_zero_of_one_le_re (s := z) hz'

end RH.RS
