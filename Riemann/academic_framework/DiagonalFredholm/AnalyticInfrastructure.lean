import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit

variable {F : Type*} [NormedAddCommGroup F]
open Set Finset Filter Topology Real Metric

namespace AnalyticOn

/-- **Weierstrass Convergence Theorem** - Now proven using Mathlib4 infrastructure! -/
theorem of_tendstoUniformlyOn
    [CompleteSpace F] [NormedSpace ℂ F]
    {U : Set ℂ} (hU : IsOpen U)
    {Fₙ : ℕ → ℂ → F} (f : ℂ → F)
    (hFₙ : ∀ n, AnalyticOn ℂ (Fₙ n) U)
    (hunif : ∀ z ∈ U, ∃ K, IsCompact K ∧ z ∈ interior K ∧ K ⊆ U ∧
      TendstoUniformlyOn Fₙ f atTop K) :
    AnalyticOn ℂ f U := by
  -- Step 1: Convert AnalyticOn to DifferentiableOn for each Fₙ
  have hFₙ_diff : ∀ n, DifferentiableOn ℂ (Fₙ n) U := fun n =>
    (hFₙ n).differentiableOn

  -- Step 2: Show locally uniform convergence
  have hloc : TendstoLocallyUniformlyOn Fₙ f atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
    intro K hKU hK
    -- For any compact K ⊆ U, show uniform convergence on K
    by_cases h : K.Nonempty
    · -- K is nonempty
      -- For each z ∈ K, get a compact set K'_z with uniform convergence
      have : ∀ z ∈ K, ∃ K', IsCompact K' ∧ z ∈ interior K' ∧ K' ⊆ U ∧
          TendstoUniformlyOn Fₙ f atTop K' := fun z hz => hunif z (hKU hz)
      choose K' hK'_compact hz_int hK'_sub hK'_unif using this
      -- The interiors {interior (K' z hz) : z ∈ K} form an open cover of K
      have hcover : K ⊆ ⋃ z : K, interior (K' z.1 z.2) := by
        intro z hz
        simp only [mem_iUnion]
        use ⟨z, hz⟩
        exact hz_int z hz
      -- By compactness, extract a finite subcover
      obtain ⟨t, ht_cover⟩ :=
        hK.elim_finite_subcover
          (fun z : K => interior (K' z.1 z.2))
          (fun _ => isOpen_interior)
          hcover
      -- Now prove uniform convergence on K using the finite subcover
      rw [tendstoUniformlyOn_iff]
      intro ε hε
      -- For each z in the finite set t, get N_z for ε-uniform convergence
      have : ∀ z ∈ t, ∃ N, ∀ n ≥ N, ∀ x ∈ K' z.1 z.2, dist (Fₙ n x) (f x) < ε := by
        intro z hz_t
        have := tendstoUniformlyOn_iff.mp (hK'_unif z.1 z.2) ε hε
        rw [Filter.eventually_atTop] at this
        obtain ⟨N, hN⟩ := this
        exact ⟨N, fun n hn x hx => (dist_comm _ _).le.trans_lt (hN n hn x hx)⟩
      choose N_fun hN_fun using this
      classical
      let N' : K → ℕ := fun z => if hz : z ∈ t then N_fun z hz else 0
      refine Filter.eventually_atTop.mpr ⟨t.sup N', ?_⟩
      intro n hn x hx
      obtain ⟨⟨z, hzK⟩, hz_t, hz_x⟩ := mem_iUnion₂.mp (ht_cover hx)
      have hxK' : x ∈ K' z hzK := interior_subset hz_x
      have hle : N' ⟨z, hzK⟩ ≤ t.sup N' := Finset.le_sup (by simpa using hz_t)
      have hn' : n ≥ N_fun ⟨z, hzK⟩ hz_t := by
        have : n ≥ N' ⟨z, hzK⟩ := le_trans hle hn
        simpa [N', hz_t] using this
      have hlt := hN_fun ⟨z, hzK⟩ hz_t n hn' x hxK'
      -- If your goal expects dist (f x) (Fₙ n x) < ε, flip with dist_comm:
      simpa [dist_comm] using hlt
    · -- K is empty, uniform convergence is trivial
      rw [Set.not_nonempty_iff_eq_empty] at h
      simp [h, tendstoUniformlyOn_empty]

  -- Step 3: Apply the Mathlib theorem
  have hdiff : DifferentiableOn ℂ f U :=
    hloc.differentiableOn (Eventually.of_forall hFₙ_diff) hU

  -- Step 4: Convert back to AnalyticOn
  exact hdiff.analyticOn hU

/-- **Derivative convergence** - Also in Mathlib! -/
theorem deriv_tendstoUniformlyOn
    [CompleteSpace F] [NormedSpace ℂ F]
    {U : Set ℂ} (hU : IsOpen U)
    {Fₙ : ℕ → ℂ → F} (f : ℂ → F)
    (hFₙ : ∀ n, AnalyticOn ℂ (Fₙ n) U)
    (hunif : ∀ z ∈ U, ∃ K, IsCompact K ∧ z ∈ interior K ∧ K ⊆ U ∧
      TendstoUniformlyOn Fₙ f atTop K) :
    ∀ z ∈ U, ∃ K, IsCompact K ∧ z ∈ interior K ∧ K ⊆ U ∧
      TendstoUniformlyOn (fun n w => deriv (Fₙ n) w) (deriv f) atTop K := by
  intro z hz
  -- Get the compact set from hypothesis
  obtain ⟨K, hK_compact, hz_int, hK_sub, hK_unif⟩ := hunif z hz
  use K, hK_compact, hz_int, hK_sub

  -- Build locally uniform convergence using the theorem we just proved
  have hf_analytic : AnalyticOn ℂ f U :=
    of_tendstoUniformlyOn hU f hFₙ hunif

  have hloc : TendstoLocallyUniformlyOn Fₙ f atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
    intro K' hK'U hK'
    by_cases h : K'.Nonempty
    · have : ∀ z ∈ K', ∃ K'', IsCompact K'' ∧ z ∈ interior K'' ∧ K'' ⊆ U ∧
          TendstoUniformlyOn Fₙ f atTop K'' := fun z hz => hunif z (hK'U hz)
      choose K'' hK''_compact hz_int' hK''_sub hK''_unif using this
      have hcover : K' ⊆ ⋃ z : K', interior (K'' z.1 z.2) := by
        intro z hz
        simp only [mem_iUnion]
        use ⟨z, hz⟩
        exact hz_int' z hz
      obtain ⟨t, ht_cover⟩ :=
        hK'.elim_finite_subcover
          (fun z : K' => interior (K'' z.1 z.2))
          (fun _ => isOpen_interior)
          hcover
      rw [tendstoUniformlyOn_iff]
      intro ε hε
      have : ∀ z ∈ t, ∃ N, ∀ n ≥ N, ∀ x ∈ K'' z.1 z.2, dist (Fₙ n x) (f x) < ε := by
        intro z hz_t
        have := tendstoUniformlyOn_iff.mp (hK''_unif z.1 z.2) ε hε
        rw [Filter.eventually_atTop] at this
        obtain ⟨N, hN⟩ := this
        exact ⟨N, fun n hn x hx => (dist_comm _ _).le.trans_lt (hN n hn x hx)⟩
      choose N_fun hN_fun using this
      classical
      let N' : K' → ℕ := fun z => if hz : z ∈ t then N_fun z hz else 0
      refine Filter.eventually_atTop.mpr ⟨t.sup N', ?_⟩
      intro n hn x hx
      obtain ⟨⟨z, hzK'⟩, hz_t, hz_x⟩ := mem_iUnion₂.mp (ht_cover hx)
      have hxK'' : x ∈ K'' z hzK' := interior_subset hz_x
      have hle : N' ⟨z, hzK'⟩ ≤ t.sup N' := Finset.le_sup (by simpa using hz_t)
      have hn' : n ≥ N_fun ⟨z, hzK'⟩ hz_t := by
        have : n ≥ N' ⟨z, hzK'⟩ := le_trans hle hn
        simpa [N', hz_t] using this
      have hlt := hN_fun ⟨z, hzK'⟩ hz_t n hn' x hxK''
      simpa [dist_comm] using hlt
    · rw [Set.not_nonempty_iff_eq_empty] at h
      simp [h, tendstoUniformlyOn_empty]

  -- Apply derivative convergence from Mathlib
  have hderiv := hloc.deriv (Eventually.of_forall fun n => (hFₙ n).differentiableOn) hU

  -- Extract uniform convergence on K
  exact (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hderiv K hK_sub hK_compact

end AnalyticOn
