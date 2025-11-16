import rh.RS.Det2Outer
import rh.RS.Cayley
import rh.RS.WhitneyAeCore
import rh.academic_framework.HalfPlaneOuterV2
import rh.academic_framework.CompletedXi
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.MetricSpace.Basic

/-!
# Route B: Pinned/removable auxiliary lemmas (factored out)

This module hosts the pinned/removable helpers used by the Route B wiring.
It exposes isolating neighbourhoods at `ξ_ext` zeros, the u‑trick construction on
punctured neighbourhoods, and the packaged pinned data for
`Θ := Θ_pinch_of det2 O`.
-/

noncomputable section

namespace RH.RS.RouteB

open Complex Set Filter Topology
open RH.AcademicFramework.CompletedXi
open RH.AcademicFramework.HalfPlaneOuterV2
open scoped Topology unitInterval
open unitInterval

local notation "Ω" => RH.RS.Ω
local notation "O" => RH.RS.WhitneyAeCore.O

attribute [-simp] RH.RS.det2_eq_AF

def XiDomain : Set ℂ := Ω \ ({1} : Set ℂ)

lemma mem_Ω_iff_re {z : ℂ} : z ∈ Ω ↔ (1 / 2 : ℝ) < z.re :=
  Iff.rfl

lemma isOpen_XiDomain : IsOpen XiDomain := by
  simpa [XiDomain] using (isOpen_Ω.sdiff isClosed_singleton)

lemma two_mem_XiDomain : (2 : ℂ) ∈ XiDomain := by
  refine ⟨(mem_Ω_iff_re).2 (by norm_num), ?_⟩
  simpa [Set.mem_singleton_iff] using (show (2 : ℂ) ≠ (1 : ℂ) by norm_num)

lemma isPreconnected_ball_complex (z : ℂ) (r : ℝ) :
    IsPreconnected (Metric.ball z r) :=
  (convex_ball z r).isPreconnected

lemma re_gt_half_of_mem_Ω {z : ℂ} (hz : z ∈ Ω) : (1 / 2 : ℝ) < z.re :=
  (mem_Ω_iff_re).1 hz

lemma convex_re_gt_half {a b : ℝ} (ha : (1 / 2 : ℝ) < a) (hb : (1 / 2 : ℝ) < b)
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (1 / 2 : ℝ) < (1 - θ) * a + θ * b := by
  have hrewrite :
      (1 - θ) * a + θ * b =
        ((1 - θ) * (a - (1 / 2 : ℝ)) + θ * (b - (1 / 2 : ℝ))) + (1 / 2 : ℝ) := by
    ring
  by_cases hθ_zero : θ = 0
  · subst hθ_zero
    simpa [hrewrite] using ha
  by_cases hθ_one : θ = 1
  · subst hθ_one
    simpa [hrewrite] using hb
  have hθ_pos : 0 < θ := lt_of_le_of_ne hθ₀ (by simpa [eq_comm] using hθ_zero)
  have hθ_lt_one : θ < 1 := lt_of_le_of_ne hθ₁ (by simpa [eq_comm] using hθ_one)
  have hθ_pos' : 0 < 1 - θ := sub_pos.2 hθ_lt_one
  have hA : 0 < a - (1 / 2 : ℝ) := sub_pos.2 ha
  have hB : 0 < b - (1 / 2 : ℝ) := sub_pos.2 hb
  have hmain :
      0 < (1 - θ) * (a - (1 / 2 : ℝ)) + θ * (b - (1 / 2 : ℝ)) :=
    add_pos (mul_pos hθ_pos' hA) (mul_pos hθ_pos hB)
  have := add_lt_add_of_lt_of_le hmain (le_of_eq (rfl : (1 / 2 : ℝ) = (1 / 2 : ℝ)))
  simpa [hrewrite] using this

@[simp] lemma abs_div_two (ε : ℝ) : |ε| / 2 = |ε / 2| := by
  have h := abs_div ε (2 : ℝ)
  have hpos : (0 : ℝ) < 2 := by norm_num
  have habs : |(2 : ℝ)| = (2 : ℝ) := by simpa using abs_of_pos hpos
  have : |ε / 2| = |ε| / |(2 : ℝ)| := by simpa using h
  simpa [habs] using this.symm

lemma one_sub_inv_div_one_add_inv_eq {w : ℂ} (hw : w ≠ 0) :
    (1 - (1 : ℂ) / w) / (1 + (1 : ℂ) / w) = (w - 1) / (w + 1) := by
  field_simp [hw, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

lemma one_div_two_mul_div (a b : ℂ) (ha : a ≠ 0) :
    (1 : ℂ) / ((2 : ℂ) * (b / a)) = a / ((2 : ℂ) * b) := by
  have : (2 : ℂ) * (b / a) = ((2 : ℂ) * b) / a := by
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  simp [this, div_eq_mul_inv, ha, mul_comm, mul_left_comm, mul_assoc]

def linePath (z w : ℂ) : Path z w :=
{ toFun := fun t : I =>
    ((1 - (t : ℝ)) : ℂ) * z + ((t : ℝ) : ℂ) * w,
  continuous_toFun := by
    have h :
        Continuous fun r : ℝ =>
          ((1 - (r : ℝ)) : ℂ) * z + ((r : ℝ) : ℂ) * w := by
      simpa using
        (by
            continuity :
            Continuous fun r : ℝ =>
              ((1 - (r : ℝ)) : ℂ) * z + ((r : ℝ) : ℂ) * w)
    simpa using h.comp continuous_subtype_val,
  source' := by
    change ((1 - (0 : ℝ)) : ℂ) * z + ((0 : ℝ) : ℂ) * w = z
    simp
  target' := by
    change ((1 - (1 : ℝ)) : ℂ) * z + ((1 : ℝ) : ℂ) * w = w
    simp }

lemma linePath_apply (z w : ℂ) (t : I) :
    linePath z w t =
      ((1 - (t : ℝ)) : ℂ) * z + ((t : ℝ) : ℂ) * w := rfl

lemma linePath_re (z w : ℂ) (t : I) :
    (linePath z w t).re = (1 - (t : ℝ)) * z.re + (t : ℝ) * w.re := by
  simp [linePath_apply, Complex.add_re, Complex.mul_re, Complex.mul_im]

lemma linePath_im (z w : ℂ) (t : I) :
    (linePath z w t).im = (1 - (t : ℝ)) * z.im + (t : ℝ) * w.im := by
  simp [linePath_apply, Complex.add_im, Complex.mul_re, Complex.mul_im]

lemma linePath_mem_Ω {z w : ℂ} (hz : z ∈ Ω) (hw : w ∈ Ω) :
    ∀ t : I, linePath z w t ∈ Ω := by
  intro t
  have h0 : 0 ≤ (t : ℝ) := t.property.1
  have h1 : (t : ℝ) ≤ 1 := t.property.2
  have hzRe := re_gt_half_of_mem_Ω hz
  have hwRe := re_gt_half_of_mem_Ω hw
  refine (mem_Ω_iff_re).2 ?_
  simpa [linePath_re z w t] using convex_re_gt_half hzRe hwRe h0 h1

lemma linePath_mem_XiDomain {z w : ℂ} (hz : z ∈ Ω) (hw : w ∈ Ω)
    (hAvoid : ∀ t : I, linePath z w t ≠ (1 : ℂ)) :
    ∀ t : I, linePath z w t ∈ XiDomain := by
  intro t
  refine ⟨linePath_mem_Ω hz hw t, ?_⟩
  have : linePath z w t ≠ (1 : ℂ) := hAvoid t
  simpa [Set.mem_singleton_iff] using this

lemma linePath_to_two_avoids_one {z : ℂ} (hzΩ : z ∈ Ω) (hz_ne : z ≠ 1)
    (hz_im : z.im ≠ 0) :
    ∀ t : I, linePath z (2 : ℂ) t ≠ (1 : ℂ) := by
  intro t
  intro h
  have hIm := congrArg Complex.im h
  have hRe := congrArg Complex.re h
  have : (1 - (t : ℝ)) * z.im = 0 := by
    simpa [linePath_im] using hIm
  have ht : (t : ℝ) = 1 := by
    have hcoeff : 1 - (t : ℝ) = 0 := by
      have hz_im' : z.im ≠ 0 := hz_im
      exact mul_eq_zero.mp this |>.resolve_right hz_im'
    exact (sub_eq_zero.mp hcoeff).symm
  have hVal : linePath z (2 : ℂ) t = (2 : ℂ) := by
    simp [linePath_apply, ht]
  have : (2 : ℂ) = (1 : ℂ) := by simpa [hVal] using h
  exact (by norm_num : (2 : ℂ) ≠ (1 : ℂ)) this

lemma vertical_path_avoids_one {z : ℂ} (hz_im : z.im = 0) (hz_ne : z ≠ 1) :
    ∀ t : I, linePath z (z + Complex.I) t ≠ (1 : ℂ) := by
  intro t h
  have hIm := congrArg Complex.im h
  have hImVal : (linePath z (z + Complex.I) t).im = (t : ℝ) := by
    simp [linePath_im, hz_im]
  have htzero : (t : ℝ) = 0 := by simpa [hImVal] using hIm
  have hRe := congrArg Complex.re h
  have hReVal : (linePath z (z + Complex.I) t).re = z.re := by
    simp [linePath_re, htzero]
  have hz_re : z.re = 1 := by
    simpa [hReVal, htzero, Complex.one_re] using hRe
  have hz_im' : z.im = 0 := hz_im
  have hz_eq : z = (1 : ℂ) := by
    apply Complex.ext
    · simpa [hz_re]
    · simpa [hz_im']
  exact hz_ne hz_eq

lemma add_I_mem_Ω {z : ℂ} (hz : z ∈ Ω) : z + Complex.I ∈ Ω := by
  refine (mem_Ω_iff_re).2 ?_
  have hzRe := re_gt_half_of_mem_Ω hz
  simpa [Complex.add_re] using hzRe

lemma add_I_ne_one_of_im_eq_zero {z : ℂ} (hz_im : z.im = 0) : z + Complex.I ≠ (1 : ℂ) := by
  intro h
  have : (z + Complex.I).im = 0 := by simpa [h] using Complex.one_im
  have : (0 : ℝ) + 1 = 0 := by simpa [Complex.add_im, hz_im] using this
  have : (1 : ℝ) = 0 := by simpa using this
  exact one_ne_zero this

lemma vertical_path_mem_Ω {z : ℂ} (hz : z ∈ Ω) :
    ∀ t : I, linePath z (z + Complex.I) t ∈ Ω := by
  intro t
  have hzRe := re_gt_half_of_mem_Ω hz
  have hRe :
      (linePath z (z + Complex.I) t).re = z.re := by
    have : (z + Complex.I).re = z.re := by simp [Complex.add_re]
    have hcomb :
        (1 - (t : ℝ)) * z.re + (t : ℝ) * (z + Complex.I).re = z.re := by
      simp [this, sub_eq_add_neg, mul_add, add_mul]
    simpa [linePath_re] using hcomb
  refine (mem_Ω_iff_re).2 ?_
  simpa [hRe] using hzRe

lemma vertical_path_mem_XiDomain {z : ℂ} (hz : z ∈ XiDomain) (hz_im : z.im = 0) :
    ∀ t : I, linePath z (z + Complex.I) t ∈ XiDomain := by
  have hz_ne : z ≠ (1 : ℂ) := by
    intro h
    have : z ∈ ({1} : Set ℂ) := by simpa [Set.mem_singleton_iff] using h
    exact hz.2 this
  have hzΩ : z ∈ Ω := hz.1
  have hAvoid := vertical_path_avoids_one hz_im hz_ne
  have hΩ' : z + Complex.I ∈ Ω := add_I_mem_Ω hzΩ
  exact linePath_mem_XiDomain hzΩ hΩ' hAvoid

lemma joinedIn_linePath {z w : ℂ} (hz : z ∈ Ω) (hw : w ∈ Ω)
    (hAvoid : ∀ t : I, linePath z w t ≠ (1 : ℂ)) :
    JoinedIn XiDomain z w :=
  ⟨linePath z w, fun t => linePath_mem_XiDomain hz hw hAvoid t⟩

lemma joinedIn_to_two_of_im_ne {z : ℂ} (hz : z ∈ XiDomain) (hz_im : z.im ≠ 0) :
    JoinedIn XiDomain z (2 : ℂ) := by
  have hzΩ : z ∈ Ω := hz.1
  have hz_ne : z ≠ (1 : ℂ) := by
    intro h
    exact hz.2 (by simpa [Set.mem_singleton_iff, h])
  have hAvoid := linePath_to_two_avoids_one hzΩ hz_ne hz_im
  have hΩ2 : (2 : ℂ) ∈ Ω := (two_mem_XiDomain).1
  exact joinedIn_linePath hzΩ hΩ2 hAvoid

lemma joinedIn_vertical {z : ℂ} (hz : z ∈ XiDomain) (hz_im : z.im = 0) :
    JoinedIn XiDomain z (z + Complex.I) :=
  joinedIn_linePath hz.1 (add_I_mem_Ω hz.1)
    (vertical_path_avoids_one hz_im
      (by
        intro h
        exact hz.2 (by simpa [Set.mem_singleton_iff, h])))

lemma joinedIn_addI_to_two {z : ℂ} (hz : z ∈ XiDomain) (hz_im : z.im = 0) :
    JoinedIn XiDomain (z + Complex.I) (2 : ℂ) := by
  have hΩ : z + Complex.I ∈ Ω := add_I_mem_Ω hz.1
  have hIm_ne : (z + Complex.I).im ≠ 0 := by
    simp [Complex.add_im, hz_im]
  have hne : z + Complex.I ≠ (1 : ℂ) := add_I_ne_one_of_im_eq_zero hz_im
  have hAvoid := linePath_to_two_avoids_one hΩ hne hIm_ne
  exact joinedIn_linePath hΩ (two_mem_XiDomain).1 hAvoid

lemma joinedIn_to_two (z : ℂ) (hz : z ∈ XiDomain) :
    JoinedIn XiDomain z (2 : ℂ) := by
  classical
  by_cases hIm : z.im = 0
  · exact (joinedIn_vertical hz hIm).trans (joinedIn_addI_to_two hz hIm)
  · exact joinedIn_to_two_of_im_ne hz hIm

lemma XiDomain_isPathConnected : IsPathConnected XiDomain := by
  refine ⟨(2 : ℂ), two_mem_XiDomain, ?_⟩
  intro z hz
  exact (joinedIn_to_two z hz).symm

noncomputable def pathToTwo (z : ℂ) (hz : z ∈ XiDomain) : Path z (2 : ℂ) :=
  (joinedIn_to_two z hz).somePath

lemma pathToTwo_mem (z : ℂ) (hz : z ∈ XiDomain) :
    ∀ t : I, pathToTwo z hz t ∈ XiDomain :=
  (joinedIn_to_two z hz).somePath_mem

lemma Whitney_O_spec :
    RH.RS.OuterHalfPlane O ∧
    RH.RS.BoundaryModulusEq O (fun s => RH.RS.det2 s / riemannXi_ext s) := by
  refine ⟨?hOuter, ?hBoundary⟩
  ·
    change RH.RS.OuterHalfPlane RH.RS.WhitneyAeCore.O
    simpa [RH.RS.WhitneyAeCore.O] using RH.RS.O_witness_outer
  ·
    change RH.RS.BoundaryModulusEq RH.RS.WhitneyAeCore.O
        (fun s => RH.RS.det2 s / riemannXi_ext s)
    simpa [RH.RS.WhitneyAeCore.O] using RH.RS.O_witness_boundary_modulus

/-- Produce an isolating, preconnected open neighbourhood for a zero of `riemannXi_ext`
inside Ω. The neighbourhood is chosen small enough to avoid `{1}` as well. -/
lemma exists_isolating_preconnected_open
    (ρ : ℂ) (hΩ : ρ ∈ Ω) (hξ : riemannXi_ext ρ = 0) :
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
      (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧ (1 : ℂ) ∉ U := by
  classical
  -- First, show that a zero of `ξ_ext` in Ω cannot lie at `1`
  have hρ_ne_one : ρ ≠ (1 : ℂ) := by
    intro hρ
    have hζ : riemannZeta ρ = 0 :=
      (xi_ext_zeros_eq_zeta_zeros_on_Ω ρ hΩ).1 hξ
    have : riemannZeta (1 : ℂ) = 0 := by simpa [hρ] using hζ
    exact riemannZeta_one_ne_zero this
  -- Convenience: view ρ as a point of `XiDomain = Ω \ {1}`
  have hXi : ρ ∈ XiDomain := by
    refine ⟨hΩ, ?_⟩
    intro hmem
    exact hρ_ne_one (by simpa [Set.mem_singleton_iff] using hmem)
  -- Analyticity of `ξ_ext` on `XiDomain` and at ρ
  have hAnalyticOnXi :
      AnalyticOn ℂ riemannXi_ext XiDomain := by
    simpa [XiDomain] using riemannXi_ext_analytic_on_RSΩ_minus_one
  have hAnalyticOnNhdXi :
      AnalyticOnNhd ℂ riemannXi_ext XiDomain :=
    ((isOpen_XiDomain).analyticOn_iff_analyticOnNhd).1 hAnalyticOnXi
  have hAnalyticAt : AnalyticAt ℂ riemannXi_ext ρ :=
    hAnalyticOnNhdXi ρ hXi
  -- Path-connectedness ⇒ connectedness ⇒ preconnectedness
  have hXi_conn : IsConnected XiDomain :=
    (isOpen_XiDomain.isConnected_iff_isPathConnected).2 XiDomain_isPathConnected
  have hXi_preconn : IsPreconnected XiDomain := hXi_conn.isPreconnected
  have hXi_subset_Ω : XiDomain ⊆ Ω := by
    intro z hz; exact hz.1
  -- Use the isolated-zeros alternative:
  -- either ξ_ext vanishes identically near ρ, or it is non-zero on a punctured neighbourhood.
  rcases hAnalyticAt.eventually_eq_zero_or_eventually_ne_zero with hZero | hNonzero
  · -- If ξ_ext is eventually zero, the identity principle forces it to vanish on all of XiDomain,
    -- contradicting ξ_ext(2) ≠ 0.
    have hfreq :
        ∃ᶠ z in 𝓝[≠] ρ, riemannXi_ext z = 0 :=
      (AnalyticAt.frequently_zero_iff_eventually_zero
        (f := riemannXi_ext) (w := ρ) hAnalyticAt).2 hZero
    have hEqOn :
        Set.EqOn riemannXi_ext 0 XiDomain :=
      AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
        (f := riemannXi_ext) (U := XiDomain) (𝕜 := ℂ)
        hAnalyticOnNhdXi hXi_preconn hXi hfreq
    have : riemannXi_ext (2 : ℂ) = 0 := by
      have hTwo : (2 : ℂ) ∈ XiDomain := two_mem_XiDomain
      simpa using hEqOn hTwo
    exact (riemannXi_ext_two_ne_zero this).elim
  -- Otherwise, ξ_ext is eventually nonzero on a punctured neighbourhood of ρ.
  obtain ⟨ε, hεpos, hεsubset⟩ :=
    Metric.mem_nhdsWithin_iff.mp
      (show {z : ℂ | riemannXi_ext z ≠ 0} ∈ 𝓝[≠] ρ by
        simpa using hNonzero)
  -- Also take a ball contained in `XiDomain` around ρ.
  obtain ⟨δ, hδpos, hδsubset⟩ :=
    Metric.mem_nhds_iff.mp ((isOpen_XiDomain.mem_nhds) hXi)
  -- Work inside the minimum radius so we stay in XiDomain and avoid new zeros.
  set r := min ε δ with hr_def
  have hrpos : 0 < r := lt_min hεpos hδpos
  have hBall_subset_Xi :
      Metric.ball ρ r ⊆ XiDomain := by
    intro z hz
    have hz' : dist z ρ < δ := lt_of_lt_of_le hz (min_le_right _ _)
    exact hδsubset hz'
  have hBall_nonzero :
      Metric.ball ρ r ∩ {z : ℂ | z ≠ ρ} ⊆ {z : ℂ | riemannXi_ext z ≠ 0} := by
    intro z hz
    have hz_dist : dist z ρ < ε := lt_of_lt_of_le hz.1 (min_le_left _ _)
    exact hεsubset ⟨hz_dist, hz.2⟩
  -- Now package the chosen ball as our isolating neighbourhood.
  let U := Metric.ball ρ r
  have hUopen : IsOpen U := by
    simpa [U] using (Metric.isOpen_ball (x := ρ) (ε := r))
  have hUconn : IsPreconnected U := isPreconnected_ball_complex ρ r
  have hUsubsetΩ : U ⊆ Ω :=
    fun z hz => hXi_subset_Ω (hBall_subset_Xi hz)
  have hρU : ρ ∈ U := by
    have : dist ρ ρ < r := by simpa [hr_def] using hrpos
    simpa [U, Metric.mem_ball, dist_self] using this
  have hIso :
      (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) := by
    apply Set.Subset.antisymm
    · intro z hz
      rcases hz with ⟨hzU, hzero⟩
      by_cases hzρ : z = ρ
      · simpa [Set.mem_singleton_iff, hzρ]
      · have : z ∈ Metric.ball ρ r ∩ {z : ℂ | z ≠ ρ} :=
          ⟨hzU, hzρ⟩
        have : riemannXi_ext z ≠ 0 := hBall_nonzero this
        exact (this hzero).elim
    · intro z hz
      obtain rfl : z = ρ := by simpa [Set.mem_singleton_iff] using hz
      refine ⟨hρU, ?_⟩
      simpa [hξ]
  -- Finally ensure the neighbourhood avoids the pole at 1.
  have hOne_not_mem : (1 : ℂ) ∉ U := by
    intro h1
    have : (1 : ℂ) ∈ XiDomain := hBall_subset_Xi h1
    -- But 1 ∉ XiDomain by definition.
    have : (1 : ℂ) ∈ Ω ∧ (1 : ℂ) ∉ ({1} : Set ℂ) := this
    exact this.2 (by simp)
  refine ⟨U, hUopen, hUconn, hUsubsetΩ, hρU, hIso, hOne_not_mem⟩

/-- Restrict analyticity of `Θ_pinch` from the off-zeros set to an
isolating punctured neighbourhood. -/
lemma Theta_pinch_analytic_on_Uminus
    {ρ : ℂ} {U : Set ℂ}
    (hOff : AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 O)
      RH.AcademicFramework.HalfPlaneOuterV2.offXi)
    (hUsub : U ⊆ Ω)
    (hIso : (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ))
    (hOne : (1 : ℂ) ∉ U) :
    AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 O) (U \ {ρ}) := by
  have hsubset :
      (U \ {ρ}) ⊆ RH.AcademicFramework.HalfPlaneOuterV2.offXi := by
    intro z hz
    have hzU : z ∈ U := hz.1
    have hzNe : z ≠ ρ := hz.2
    have hzΩ : z ∈ Ω := hUsub hzU
    have hzXi_ne : riemannXi_ext z ≠ 0 := by
      intro h0
      have : z ∈ (U ∩ {w | riemannXi_ext w = 0}) :=
        ⟨hzU, by simpa [Set.mem_setOf_eq] using h0⟩
      have : z ∈ ({ρ} : Set ℂ) := by simpa [hIso] using this
      exact hzNe (by simpa using this)
    have hz_ne_one : z ≠ (1 : ℂ) := by
      intro h
      exact hOne (by simpa [h] using hzU)
    exact ⟨hzΩ, hz_ne_one, hzXi_ne⟩
  exact hOff.mono hsubset

/-- u‑trick on a punctured isolating neighbourhood: build `u` with
`Θ = (1-u)/(1+u)` and `u → 0`. -/
lemma exists_u_trick_on_punctured
    {ρ : ℂ} {U : Set ℂ}
    (hUopen : IsOpen U) (hρU : ρ ∈ U) (hUsub : U ⊆ Ω)
    (hIso : (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ))
    (hOuter : RH.RS.OuterHalfPlane O)
    (hDet2_nz : RH.RS.det2 ρ ≠ 0) :
    ∃ u : ℂ → ℂ,
      Set.EqOn (RH.RS.Θ_pinch_of RH.RS.det2 O)
        (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
      Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) ∧
      ∀ ⦃z : ℂ⦄, z ∈ U \ {ρ} →
        u z = (O z * riemannXi_ext z) / ((2 : ℂ) * RH.RS.det2 z) := by
  classical
  have hρ_zero : riemannXi_ext ρ = 0 := by
    have : ρ ∈ (U ∩ {z | riemannXi_ext z = 0}) := by
      have : ρ ∈ ({ρ} : Set ℂ) := by simp
      simpa [hIso] using this
    simpa [Set.mem_setOf_eq] using this.2
  have hρ_ne_one : ρ ≠ (1 : ℂ) := by
    intro hρ
    have hζ : riemannZeta ρ = 0 :=
      (xi_ext_zeros_eq_zeta_zeros_on_Ω ρ (hUsub hρU)).1 hρ_zero
    have : riemannZeta (1 : ℂ) = 0 := by simpa [hρ] using hζ
    exact riemannZeta_one_ne_zero this
  let u : ℂ → ℂ :=
    fun z => (O z * riemannXi_ext z) / ((2 : ℂ) * RH.RS.det2 z)
  have hEqOn :
      Set.EqOn (RH.RS.Θ_pinch_of RH.RS.det2 O)
        (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) := by
    intro z hz
    have hzU : z ∈ U := hz.1
    have hzΩ : z ∈ Ω := hUsub hzU
    have hXi_ne : riemannXi_ext z ≠ 0 := by
      intro h0
      have : z ∈ (U ∩ {w | riemannXi_ext w = 0}) :=
        ⟨hzU, by simpa [Set.mem_setOf_eq] using h0⟩
      have : z ∈ ({ρ} : Set ℂ) := by simpa [hIso] using this
      exact hz.2 (by simpa using this)
    have hO_ne : O z ≠ 0 := hOuter.nonzero hzΩ
    have hdet_ne : RH.RS.det2 z ≠ 0 :=
      RH.RS.det2_nonzero_on_RSΩ (s := z) hzΩ
    set Jz : ℂ := RH.RS.J_pinch RH.RS.det2 O z
    have hJz : Jz = RH.RS.det2 z / (O z * riemannXi_ext z) := rfl
    have hu_def :
        u z = (1 : ℂ) / ((2 : ℂ) * Jz) := by
      have hden : (O z * riemannXi_ext z) ≠ 0 := mul_ne_zero hO_ne hXi_ne
      have hfrac :
          (1 : ℂ) / ((2 : ℂ) * Jz) =
            (O z * riemannXi_ext z) / ((2 : ℂ) * RH.RS.det2 z) := by
        simpa [hJz] using
          one_div_two_mul_div (a := O z * riemannXi_ext z)
            (b := RH.RS.det2 z) hden
      have : u z =
          (O z * riemannXi_ext z) / ((2 : ℂ) * RH.RS.det2 z) := rfl
      simpa [this] using hfrac.symm
    have hTheta :
        (RH.RS.Θ_pinch_of RH.RS.det2 O) z =
          ((2 : ℂ) * Jz - 1) / ((2 : ℂ) * Jz + 1) := by
      simp [RH.RS.Θ_pinch_of, RH.RS.Theta_of_J, RH.RS.J_pinch, hJz,
        Theta_of_J]
    have hJ_ne : Jz ≠ 0 := by
      have hden : O z * riemannXi_ext z ≠ 0 := mul_ne_zero hO_ne hXi_ne
      have hnum : RH.RS.det2 z ≠ 0 := hdet_ne
      simpa [hJz] using div_ne_zero hnum hden
    have hratio :
        (1 - u z) / (1 + u z) =
          ((2 : ℂ) * Jz - 1) / ((2 : ℂ) * Jz + 1) := by
      have h2J : (2 : ℂ) * Jz ≠ 0 := mul_ne_zero (by norm_num) hJ_ne
      have := one_sub_inv_div_one_add_inv_eq (w := (2 : ℂ) * Jz) h2J
      simpa [hu_def, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
    simpa [hratio] using hTheta
  have hρΩ : ρ ∈ Ω := hUsub hρU
  have hO_cont : ContinuousAt O ρ :=
    (hOuter.analytic.continuousOn.continuousAt
      (isOpen_Ω.mem_nhds hρΩ))
  have hXi_diff :
      DifferentiableOn ℂ riemannXi_ext (Ω \ ({1} : Set ℂ)) :=
    riemannXi_ext_differentiable_on_RSΩ_minus_one
  have hΩminus_open : IsOpen (Ω \ ({1} : Set ℂ)) := by
    simpa using (isOpen_Ω.sdiff isClosed_singleton)
  have hρ_in : ρ ∈ (Ω \ ({1} : Set ℂ)) := by
    refine ⟨hρΩ, ?_⟩
    intro h1
    have hIso1 : (1 : ℂ) ∈ (U ∩ {z | riemannXi_ext z = 0}) := by
      have hρzero : riemannXi_ext ρ = 0 := by
        have : ρ ∈ (U ∩ {z | riemannXi_ext z = 0}) := by
          have : ρ ∈ ({ρ} : Set ℂ) := by simp
          simpa [hIso] using this
        simpa [Set.mem_setOf_eq] using this.2
      have : 1 = ρ := h1.symm
      refine ⟨by simpa [this] using hρU, ?_⟩
      simpa [this, Set.mem_setOf_eq, hρzero]
    have : (1 : ℂ) = ρ := by
      simpa [hIso, Set.mem_singleton_iff] using hIso1
    exact hρ_ne_one this.symm
  have hXi_cont : ContinuousAt riemannXi_ext ρ :=
    (hXi_diff.differentiableAt
      (IsOpen.mem_nhds hΩminus_open hρ_in)).continuousAt
  have hdet_cont : ContinuousAt RH.RS.det2 ρ :=
    (RH.RS.det2_analytic_on_RSΩ.continuousOn.continuousAt
      (isOpen_Ω.mem_nhds hρΩ))
  have hden_ne :
      ((2 : ℂ) * RH.RS.det2 ρ) ≠ 0 :=
    mul_ne_zero (by norm_num) (by simpa using hDet2_nz)
  have hu_cont : ContinuousAt u ρ := by
    have hnum_cont :
        ContinuousAt (fun z => O z * riemannXi_ext z) ρ :=
      hO_cont.mul hXi_cont
    have hden_cont :
        ContinuousAt (fun z => (2 : ℂ) * RH.RS.det2 z) ρ :=
      (continuousAt_const : ContinuousAt (fun _ : ℂ => (2 : ℂ)) ρ).mul hdet_cont
    have hInv :=
        (continuousAt_inv₀_and_eventually_ne
          (g := fun z => (2 : ℂ) * RH.RS.det2 z)
          (hg := hden_cont) (hρ := hden_ne)).1
    simpa [u, div_eq_mul_inv] using hnum_cont.mul hInv
  have hXiρ : riemannXi_ext ρ = 0 := by
    have : ρ ∈ (U ∩ {z | riemannXi_ext z = 0}) := by
      have : ρ ∈ ({ρ} : Set ℂ) := by simp
      simpa [hIso] using this
    simpa [Set.mem_setOf_eq] using this.2
  have hu_cont_within : ContinuousWithinAt u U ρ :=
    hu_cont.continuousWithinAt
  have hu0 :
      Tendsto u (nhdsWithin ρ U) (nhds (0 : ℂ)) := by
    have : u ρ = 0 := by simp [u, hXiρ]
    simpa [this] using hu_cont_within.tendsto
  have hu0' :
      Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) :=
    hu0.mono_left <|
      nhdsWithin_mono _ fun z hz => hz.1
  refine ⟨u, hEqOn, hu0', ?_⟩
  intro z hz
  simpa [u]

/-- Main export: pinned removable data for
`Θ := Θ_pinch_of det2 O` at each `ξ_ext` zero, assuming the needed
nonnegativity on the AF off-Ξ domain. -/
theorem pinned_removable_data
    (hRe :
      ∀ z ∈ RH.AcademicFramework.HalfPlaneOuterV2.offXi,
        0 ≤ ((2 : ℂ) * RH.RS.J_pinch RH.RS.det2 O z).re)
    (ρ : ℂ) (hΩ : ρ ∈ Ω) (hξ : riemannXi_ext ρ = 0) :
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
      (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
      AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 O) (U \ {ρ}) ∧
      ∃ u : ℂ → ℂ,
        Set.EqOn (RH.RS.Θ_pinch_of RH.RS.det2 O)
          (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
        Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) ∧
        ∃ z, z ∈ U ∧ z ≠ ρ ∧
          (RH.RS.Θ_pinch_of RH.RS.det2 O) z ≠ 1 := by
  classical
  obtain ⟨U, hUopen, hUconn, hUsub, hρU, hIso, hOne⟩ :=
    exists_isolating_preconnected_open ρ hΩ hξ
  have hDet2 : RH.RS.Det2OnOmega :=
    RH.RS.det2_on_Ω_assumed det2_analytic_on_RSΩ
      (by intro s hs; exact det2_nonzero_on_RSΩ (s := s) hs)
  have hOuter : RH.RS.OuterHalfPlane O := (Whitney_O_spec).1
  have hXi :
      AnalyticOn ℂ riemannXi_ext (Ω \ ({1} : Set ℂ)) :=
    riemannXi_ext_analytic_on_RSΩ_minus_one
  have hOff :
      AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 O)
        RH.AcademicFramework.HalfPlaneOuterV2.offXi := by
    exact RH.RS.Theta_pinch_analytic_on_offXi
      (hDet2 := hDet2) (hO := hOuter) (hXi := hXi)
      (hRe := by
        intro z hz
        exact hRe z hz)
  have hΘU :
      AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 O) (U \ {ρ}) :=
    Theta_pinch_analytic_on_Uminus hOff hUsub hIso hOne
  have hdetρ : RH.RS.det2 ρ ≠ 0 :=
    RH.RS.det2_nonzero_on_RSΩ (s := ρ) hΩ
  obtain ⟨u, hEq, hu0, huForm⟩ :=
    exists_u_trick_on_punctured hUopen hρU hUsub hIso hOuter hdetρ
  -- Nontriviality witness
  have : ∃ z, z ∈ U ∧ z ≠ ρ ∧
      (RH.RS.Θ_pinch_of RH.RS.det2 O) z ≠ 1 := by
    obtain ⟨ε, hεpos, hεsubset⟩ :=
      Metric.mem_nhds_iff.mp (hUopen.mem_nhds hρU)
    have hhalf_pos : 0 < ε / 2 := half_pos hεpos
    have hAbs_eps : |ε| = ε := _root_.abs_of_nonneg hεpos.le
    have hAbs_halves : |ε| / 2 = |ε / 2| := abs_div_two ε
    have hAbs_eps_div : |ε / 2| = ε / 2 := by
      have : 0 ≤ ε / 2 := le_of_lt hhalf_pos
      simpa using _root_.abs_of_nonneg this
    let z : ℂ := ρ + (ε / 2 : ℝ)
    have hz_diff : z - ρ = (ε / 2 : ℂ) := by
      simp [z]
    have hhalf_ne : (ε / 2 : ℂ) ≠ 0 :=
      by exact_mod_cast (ne_of_gt hhalf_pos)
    have hz_ne : z ≠ ρ := by
      intro h
      have hz_zero : z - ρ = 0 := by simpa [h]
      have : (ε / 2 : ℂ) = 0 := by
        simpa [hz_diff] using hz_zero
      exact hhalf_ne this
    have hz_ball : z ∈ Metric.ball ρ ε := by
      have hz_dist : dist z ρ = |ε / 2| := by
        simp [dist_eq, hz_diff, Complex.norm_eq_abs, Complex.abs_ofReal]
      have hlt_base : ε / 2 < ε := half_lt_self hεpos
      have hlt : |ε / 2| < ε := by simpa [hAbs_eps_div] using hlt_base
      exact Metric.mem_ball.mpr (by simpa [hz_dist] using hlt)
    have hzU : z ∈ U := hεsubset hz_ball
    have hzUdiff : z ∈ U ∧ z ≠ ρ := ⟨hzU, hz_ne⟩
    have hzUminus : z ∈ U \ {ρ} := by
      refine ⟨hzU, ?_⟩
      simpa [Set.mem_singleton_iff] using hz_ne
    have hzΩ : z ∈ Ω := hUsub hzU
    have hXi_ne : riemannXi_ext z ≠ 0 := by
      intro h0
      have : z ∈ (U ∩ {w | riemannXi_ext w = 0}) :=
        ⟨hzU, by simpa [Set.mem_setOf_eq] using h0⟩
      have : z ∈ ({ρ} : Set ℂ) := by
        simpa [hIso] using this
      exact hz_ne (by simpa using this)
    have hO_ne : O z ≠ 0 := (Whitney_O_spec).1.nonzero hzΩ
    have hdet_ne :
        RH.RS.det2 z ≠ 0 :=
      RH.RS.det2_nonzero_on_RSΩ (s := z) hzΩ
    have hΘz_ne :
        (RH.RS.Θ_pinch_of RH.RS.det2 O) z ≠ 1 := by
      intro h1
      have hEqz := hEq hzUminus
      have hnum := mul_ne_zero hO_ne hXi_ne
      have hden :
          ((2 : ℂ) * RH.RS.det2 z) ≠ 0 := by
        simpa using mul_ne_zero (two_ne_zero : (2 : ℂ) ≠ 0) hdet_ne
      have huz_expr :
          u z = (O z * riemannXi_ext z) / ((2 : ℂ) * RH.RS.det2 z) :=
        huForm hzUminus
      have huz_ne : u z ≠ 0 := by
        simpa [huz_expr] using (div_ne_zero hnum hden)
      have hratio :
          (1 - u z) / (1 + u z) = 1 := by
        simpa [hEqz] using h1
      have hdenom : 1 + u z ≠ 0 := by
        intro hzero
        have : (1 - u z) / (1 + u z) = 0 := by simp [hzero]
        have : (0 : ℂ) = 1 := by simpa [this] using hratio
        exact zero_ne_one this
      have hmul :=
        congrArg (fun t => t * (1 + u z)) hratio
      have hones :
          1 - u z = 1 + u z := by
        simpa [hdenom] using hmul
      have hneg :
          ((-2 : ℂ) * u z) = 0 := by
        have := sub_eq_zero.mpr hones
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
          two_mul] using this
      have htwo : (-2 : ℂ) ≠ 0 := by norm_num
      have huz0 :
          u z = 0 :=
        (mul_eq_zero.mp hneg).resolve_left htwo
      exact huz_ne huz0
    exact ⟨z, hzU, hz_ne, hΘz_ne⟩
  rcases this with ⟨z, hzU, hzNe, hΘz⟩
  refine ⟨U, hUopen, hUconn, hUsub, hρU, hIso, hΘU, u, hEq, hu0, z, hzU, hzNe, hΘz⟩

end RH.RS.RouteB

attribute [simp] RH.RS.det2_eq_AF
