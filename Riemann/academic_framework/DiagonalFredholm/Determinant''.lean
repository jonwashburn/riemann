import Riemann.academic_framework.Compat
import Riemann.academic_framework.EulerProduct.PrimeSeries
import Riemann.academic_framework.DiagonalFredholm.WeierstrassProduct
import Riemann.academic_framework.DiagonalFredholm.AnalyticInfrastructure
import Mathlib
--mport Riemann

namespace Real

lemma csSup_empty_ge : 0 ≤ sSup (∅ : Set ℝ) := by
  simp [sSup_empty]

end Real

open scoped BigOperators

namespace Real

/-- For `σ > 1`, the (shifted) p-series `∑ (n : ℕ), (n+1)^{-σ}` converges. -/
lemma summable_rpow {σ : ℝ} (hσ : 1 < σ) :
  Summable (fun n : ℕ => (n + 1 : ℝ) ^ (-σ)) := by
  -- Standard result in mathlib (as an iff). Use the → direction explicitly, via a named function.
  let f : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ) ^ σ
  -- Standard p-series: ∑ 1/n^σ converges for σ>1
  have hg : Summable (fun n : ℕ => 1 / (n : ℝ) ^ σ) :=
    (Real.summable_one_div_nat_rpow).2 hσ
  -- Shift by 1: summability is invariant under finite shifts
  have hshift : Summable (fun n : ℕ => 1 / (n + 1 : ℝ) ^ σ) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ σ) 1).2 hg)
  -- Rewrite 1/(n+1)^σ as (n+1)^(-σ)
  have h_eq :
      (fun n : ℕ => (n + 1 : ℝ) ^ (-σ)) =
      (fun n : ℕ => 1 / (n + 1 : ℝ) ^ σ) := by
    funext n
    have hpos : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
    simpa [one_div] using Real.rpow_neg (le_of_lt hpos) σ
  simpa [h_eq] using hshift

open scoped BigOperators

/-- If `f : ℕ → ℝ` is summable, and `g : {n // p n} → ℝ` is pointwise nonnegative
and pointwise bounded by `f ∘ Subtype.val`, then `g` is summable. -/
lemma Summable.subtype_of_nonneg_of_le
  {p : ℕ → Prop} {f : ℕ → ℝ} {g : {n // p n} → ℝ}
  (hf : Summable f)
  (hg0 : ∀ n : {n // p n}, 0 ≤ g n)
  (hbound : ∀ n : {n // p n}, g n ≤ f n.1) :
  Summable g := by
  -- `f ∘ Subtype.val` is summable by injectivity of `Subtype.val`
  have hf_sub : Summable (fun n : {n // p n} => f n.1) :=
    hf.comp_injective Subtype.val_injective
  exact Summable.of_nonneg_of_le hg0 (fun n => hbound n) hf_sub

/-- Prime p-series: for `σ > 1`, `∑ p : ℙ, p^{-σ}` converges. -/
lemma summable_prime_rpow {σ : ℝ} (hσ : 1 < σ) :
  Summable (fun p : Nat.Primes => (p.1 : ℝ) ^ (-σ)) := by
  -- Step 1: get ∑ (n+1)^(-σ) summable
  have hzeta1 : Summable (fun n : ℕ => (n + 1 : ℝ) ^ (-σ)) :=
    Real.summable_rpow hσ
  -- Step 2: compare (n+2)^(-σ) ≤ (n+1)^(-σ) (since -σ ≤ 0 and n+1 ≤ n+2)
  have hzeta2 : Summable (fun n : ℕ => (n + 2 : ℝ) ^ (-σ)) := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) hzeta1
    have hx : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
    have hxy : (n + 1 : ℝ) ≤ (n + 2 : ℝ) := by linarith
    have hnonpos : -σ ≤ 0 := by linarith
    exact Real.rpow_le_rpow_of_nonpos hx hxy hnonpos
  -- Step 3: reindex to `{n | 2 ≤ n}` via n ↦ n+2 (explicit, light equivalence)
  classical
  let e : ℕ ≃ {n : ℕ // 2 ≤ n} :=
  { toFun := fun n => ⟨n + 2, by simp⟩
    invFun := fun n => n.1 - 2
    left_inv := by intro n; simp
    right_inv := by
      intro n
      have : (n.1 - 2) + 2 = n.1 := by
        exact Nat.sub_add_cancel (by exact n.2)
      simp [this] }
  classical
  let h : {n : ℕ // 2 ≤ n} → ℕ := fun n => n.1 - 2
  have hinj : Function.Injective h := by
    intro a b hab
    dsimp [h] at hab
    have h_add : a.1 - 2 + 2 = b.1 - 2 + 2 := by rw [hab]
    have ha : a.1 - 2 + 2 = a.1 := Nat.sub_add_cancel a.2
    have hb : b.1 - 2 + 2 = b.1 := Nat.sub_add_cancel b.2
    rw [ha, hb] at h_add
    exact Subtype.ext h_add
  have hzeta_subset :
      Summable (fun n : {n : ℕ // 2 ≤ n} => (n.1 : ℝ) ^ (-σ)) := by
    -- reindex `hzeta2 : Summable (fun k : ℕ => (k+2) ^ (-σ))` along the injective map `h`
    have hsum := hzeta2.comp_injective hinj
    -- convert: (↑(h n) + 2) = ↑(h n + 2) = n.1
    convert hsum using 1
    funext n
    simp [h]
    aesop
  -- Step 4: restrict to primes via injective embedding into {n | 2 ≤ n}
  let i : Nat.Primes → {n : ℕ // 2 ≤ n} := fun p => ⟨p.1, p.property.two_le⟩
  have hi : Function.Injective i := by
    intro p q h
    have : p.1 = q.1 := by
      simpa [i] using congrArg (fun x : {n : ℕ // 2 ≤ n} => x.1) h
    exact Subtype.ext this
  have hsum_primes :
      Summable (fun p : Nat.Primes => ((i p).1 : ℝ) ^ (-σ)) :=
    hzeta_subset.comp_injective hi
  simpa [i] using hsum_primes

end Real

noncomputable section

namespace ContinuousLinearMap

open scoped BigOperators ENNReal
open Real

variable {𝕜 ι : Type*} [RCLike 𝕜]

/-- If `‖f i‖ ≤ C * ‖g i‖` for all `i` and `g ∈ ℓᵖ`, then `f ∈ ℓᵖ`. -/
lemma Memℓp.of_bound {α E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    (hp : 0 < p) (f g : α → E) (C : ℝ) (hC : 0 ≤ C)
    (hg : Memℓp g p)
    (hbound : ∀ i, ‖f i‖ ≤ C * ‖g i‖) :
    Memℓp f p := by
  by_cases hp_top : p = ∞
  · -- Case p = ∞
    subst hp_top
    rw [memℓp_infty_iff] at hg ⊢
    obtain ⟨M, hM⟩ := hg
    use C * M
    intro x hx
    rcases hx with ⟨i, rfl⟩
    calc
      ‖f i‖ ≤ C * ‖g i‖ := hbound i
      _ ≤ C * M := by
        have : ‖g i‖ ≤ M := hM ⟨i, rfl⟩
        exact mul_le_mul_of_nonneg_left this hC
  · -- Case 0 < p < ∞
    have hp_ne_top : p ≠ ∞ := hp_top
    have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp.ne' hp_ne_top
    -- get summability from Memℓp
    have hg' : Summable (fun i => ‖g i‖ ^ p.toReal) := by
      simpa using hg.summable hp_pos
    have hC_pow_nonneg : 0 ≤ C ^ p.toReal := by
      exact Real.rpow_nonneg hC _
    refine (memℓp_gen_iff hp_pos).2 ?_
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) (hg'.mul_left (C ^ p.toReal))
    calc ‖f i‖ ^ p.toReal
        ≤ (C * ‖g i‖) ^ p.toReal := by
          gcongr
          exact hbound i
      _ = C ^ p.toReal * ‖g i‖ ^ p.toReal := by
          rw [mul_rpow hC (norm_nonneg _)]

set_option maxHeartbeats 400000 in
/-- Diagonal operator on `ℓ²(ι, 𝕜)` from a uniformly bounded coefficient family `a : ι → 𝕜`.
If `‖a i‖ ≤ C` for all `i`, then the operator norm is ≤ `C`. -/
noncomputable def diagOfBound (a : ι → 𝕜) (C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ i, ‖a i‖ ≤ C) :
    ℓ²(ι, 𝕜) →L[𝕜] ℓ²(ι, 𝕜) :=
by
  classical
  -- Underlying linear map: coordinatewise multiplication
  let Llin : (ℓ²(ι, 𝕜)) →ₗ[𝕜] (ℓ²(ι, 𝕜)) :=
  { toFun := fun x =>
      ⟨(fun i => a i * x i),
        by
          -- Show: (a · x) ∈ ℓ² using ‖a i * x i‖ ≤ C ‖x i‖
          -- hence ‖a i * x i‖^2 ≤ (C^2) ‖x i‖^2 and compare sums
          have h₁ : ∀ i, ‖a i * x i‖ ≤ C * ‖x i‖ := by
            intro i
            have := hbound i
            simpa [norm_mul, mul_comm, mul_left_comm, mul_assoc]
              using mul_le_mul_of_nonneg_right this (norm_nonneg _)
          have h₂ : ∀ i, ‖a i * x i‖ ^ 2 ≤ (C * ‖x i‖) ^ 2 := fun i => by
            gcongr
            exact h₁ i
            -- Now use domination by the summable sequence (C*‖x i‖)^2 = C^2 * ‖x i‖^2

            -- NEW:
          have hx : Summable (fun i => ‖x i‖ ^ (2 : ℝ)) := by
          -- x : ℓ²(ι, 𝕜) means Summable (fun i => ‖x i‖^2)
          -- Extract this from the lp membership condition
            have : Memℓp (fun i => x i) 2 := x.2
            have h_pos : 0 < ENNReal.toReal 2 := by norm_num
            have h_summable := this.summable h_pos
            simp only [ENNReal.toReal_ofNat] at h_summable
            exact h_summable
          have hC2 : 0 ≤ C^2 := sq_nonneg C
          have hdom :
            ∀ i, ‖a i * x i‖ ^ 2 ≤ C^2 * ‖x i‖ ^ (2 : ℝ) := by
            intro i
            calc ‖a i * x i‖ ^ 2
                ≤ (C * ‖x i‖) ^ 2 := h₂ i
              _ = C ^ 2 * ‖x i‖ ^ 2 := by rw [mul_pow]
            aesop
          -- Show: (a · x) ∈ ℓ² using ‖a i * x i‖ ≤ C ‖x i‖
          -- hence ‖a i * x i‖^2 ≤ (C^2) ‖x i‖^2 and compare sums
          have h₁ : ∀ i, ‖a i * x i‖ ≤ C * ‖x i‖ := by
            intro i
            have := hbound i
            simpa [norm_mul, mul_comm, mul_left_comm, mul_assoc]
              using mul_le_mul_of_nonneg_right this (norm_nonneg _)
          have h₂ : ∀ i, ‖a i * x i‖ ^ 2 ≤ (C * ‖x i‖) ^ 2 := fun i => by
            gcongr
            exact h₁ i
          -- Now use domination by the summable sequence (C*‖x i‖)^2 = C^2 * ‖x i‖^2
          have hx : Memℓp (fun i => x i) 2 := x.2
          have hdom : ∀ i, ‖a i * x i‖ ^ 2 ≤ C^2 * ‖x i‖ ^ 2 := by
            intro i
            calc ‖a i * x i‖ ^ 2
                ≤ (C * ‖x i‖) ^ 2 := h₂ i
              _ = C ^ 2 * ‖x i‖ ^ 2 := by rw [mul_pow]
          -- Use Memℓp.of_bound to show membership
          have hp2 : 0 < (2 : ℝ≥0∞) := by norm_num
          exact Memℓp.of_bound hp2 (fun i => a i * x i) (fun i => x i) C hC x.2 h₁
      ⟩,
    map_add' := by
      intro x y; ext i; simp [mul_add]
    map_smul' := by
      intro c x; ext i; simp [mul_left_comm] }
  -- Continuity bound: ‖Llin x‖ ≤ C · ‖x‖
  refine LinearMap.mkContinuous Llin C ?_
  intro x
  -- Use pointwise bound to compare ℓ² norms: ∥(a·x)∥ ≤ C ∥x∥
  -- Turn the previous square domination into a norm inequality
  have h₁ : ∀ i, ‖a i * x i‖ ≤ C * ‖x i‖ := by
    intro i
    have := hbound i
    simpa [norm_mul, mul_comm, mul_left_comm, mul_assoc]
      using mul_le_mul_of_nonneg_right this (norm_nonneg _)
  -- (∑ ‖a i * x i‖^2)^(1/2) ≤ (∑ (C‖x i‖)^2)^(1/2) = C (∑ ‖x i‖^2)^(1/2)
  -- so ∥(a·x)∥ ≤ C ∥x∥
  -- This step is packaged as:
  have h₂ :
      ‖(⟨(fun i => a i * x i), by
        -- (a · x) ∈ ℓ² using the pointwise bound h₁ and x ∈ ℓ²
        have hp2 : 0 < (2 : ℝ≥0∞) := by norm_num
        exact Memℓp.of_bound hp2 (fun i => a i * x i) (fun i => x i) C hC x.2 h₁
      ⟩ : ℓ²(ι, 𝕜))‖ ≤ C * ‖x‖ := by
    have hC' : 0 ≤ C * ‖x‖ := mul_nonneg hC (norm_nonneg _)
    have hp2tr : 0 < (2 : ℝ≥0∞).toReal := by norm_num
    refine lp.norm_le_of_forall_sum_le hp2tr (hC := hC') ?_
    intro s
    classical
    have hterm : ∀ i, ‖a i * x i‖ ^ (2 : ℝ) ≤ (C * ‖x i‖) ^ (2 : ℝ) := fun i => by
      gcongr
      exact h₁ i
    have hsum_le :
        ∑ i ∈ s, ‖a i * x i‖ ^ (2 : ℝ) ≤ ∑ i ∈ s, (C * ‖x i‖) ^ (2 : ℝ) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    calc
      ∑ i ∈ s, ‖a i * x i‖ ^ (2 : ℝ)
          ≤ ∑ i ∈ s, (C * ‖x i‖) ^ (2 : ℝ) := hsum_le
      _ = C ^ 2 * ∑ i ∈ s, ‖x i‖ ^ (2 : ℝ) := by
            simp [mul_pow, Finset.mul_sum]
      _ ≤ C ^ 2 * ‖x‖ ^ (2 : ℝ) := by
            gcongr
            exact lp.sum_rpow_le_norm_rpow (by norm_num) x s
      _ = (C * ‖x‖) ^ (2 : ℝ) := by
            simp [mul_pow]
  -- conclude the mkContinuous bound
  simpa [norm_smul, mul_comm, mul_left_comm, mul_assoc] using h₂

@[simp] lemma diagOfBound_apply {a : ι → 𝕜} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ i, ‖a i‖ ≤ C)
    (x : ℓ²(ι, 𝕜)) (i : ι) :
    (diagOfBound a C hC h x) i = a i * x i := rfl

lemma opNorm_diagOfBound_le {a : ι → 𝕜} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ i, ‖a i‖ ≤ C) :
    ‖diagOfBound a C hC h‖ ≤ C := by
  refine (diagOfBound a C hC h).opNorm_le_bound hC (by
    intro x
    -- pointwise bound: ‖a i * x i‖ ≤ C ‖x i‖
    have h₁ : ∀ i, ‖a i * x i‖ ≤ C * ‖x i‖ := by
      intro i
      have := h i
      simpa [norm_mul, mul_comm, mul_left_comm, mul_assoc]
        using mul_le_mul_of_nonneg_right this (norm_nonneg _)
    -- convert to ℓ² norm bound via finite sums
    have hC' : 0 ≤ C * ‖x‖ := mul_nonneg hC (norm_nonneg _)
    have hp2tr : 0 < (2 : ℝ≥0∞).toReal := by norm_num
    refine lp.norm_le_of_forall_sum_le hp2tr (hC := hC') ?_
    intro s
    classical
    have hterm : ∀ i, ‖a i * x i‖ ^ (2 : ℝ) ≤ (C * ‖x i‖) ^ (2 : ℝ) := fun i => by
      gcongr
      exact h₁ i
    have hsum_le :
        ∑ i ∈ s, ‖a i * x i‖ ^ (2 : ℝ) ≤ ∑ i ∈ s, (C * ‖x i‖) ^ (2 : ℝ) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    calc
      ∑ i ∈ s, ‖(diagOfBound a C hC h x) i‖ ^ (2 : ℝ)
          = ∑ i ∈ s, ‖a i * x i‖ ^ (2 : ℝ) := by
              simp [diagOfBound_apply, norm_mul]
      _ ≤ ∑ i ∈ s, (C * ‖x i‖) ^ (2 : ℝ) := hsum_le
      _ = C ^ 2 * ∑ i ∈ s, ‖x i‖ ^ (2 : ℝ) := by
              simp [mul_pow, Finset.mul_sum]
      _ ≤ C ^ 2 * ‖x‖ ^ (2 : ℝ) := by
              gcongr
              exact lp.sum_rpow_le_norm_rpow (by norm_num) x s
      _ = (C * ‖x‖) ^ (2 : ℝ) := by
              simp [mul_pow]
  )

end ContinuousLinearMap

open Complex Set MeasureTheory
open scoped Topology BigOperators

namespace RH

/-- Index set and Hilbert space. -/
abbrev P := Nat.Primes
abbrev H := ℓ²(P, ℂ)

/-- Domain where A(s) is Hilbert–Schmidt (and bounded). -/
def U : Set ℂ := { s | 1/2 < s.re }

/-- Diagonal coefficients for A(s): p ↦ p^{-s}. -/
@[simp] noncomputable def coeff (s : ℂ) (p : P) : ℂ := (p.1 : ℂ) ^ (-s)

/-- Uniform operator-norm bound on U: for re(s) ≥ 0 we have
    ‖coeff s p‖ ≤ 2^{-re s}. We will use the margin σ to get uniformity on compacts. -/
lemma coeff_norm_le_of_re_nonneg {s : ℂ} (hs : 0 ≤ s.re) (p : P) :
    ‖coeff s p‖ ≤ (2 : ℝ) ^ (-s.re) := by
  have hp_pos : 0 < (p.1 : ℝ) := by exact_mod_cast p.property.pos
  have h2_le_p : (2 : ℝ) ≤ p.1 := by exact_mod_cast p.property.two_le
  -- ‖(p : ℂ) ^ (-s)‖ = p^{-re s} and monotonicity at nonpositive exponents
  have := Complex.norm_natCast_cpow_of_pos p.property.pos (-s)
  -- rewrite the norm of the cpow to a real rpow
  -- this `simp` step is robust across mathlib versions:
  have : ‖(p.1 : ℂ) ^ (-s)‖ = (p.1 : ℝ) ^ (-s.re) := this
  -- compare bases at nonpositive exponent
  have hexp_nonpos : -s.re ≤ 0 := by simpa using (neg_nonpos.mpr hs)
  have hmon := Real.rpow_le_rpow_of_nonpos (by norm_num : 0 < (2 : ℝ)) h2_le_p hexp_nonpos
  simpa [coeff, this]

/-! ### Summability and ideal membership -/

open scoped BigOperators


/-- For `s ∈ U` we have `∑_p ‖p^{-s}‖^2 < ∞` (Hilbert–Schmidt). -/
lemma coeff_sq_summable_of_re_gt_half {s : ℂ} (hs : 1/2 < s.re) :
    Summable (fun p : P => ‖coeff s p‖ ^ (2 : ℝ)) := by
  -- ‖(p : ℂ)^(-s)‖ = p^{-re s}
  have hp : ∀ p : P, ‖coeff s p‖ = (p.1 : ℝ) ^ (-s.re) := by
    intro p; simpa [coeff] using Complex.norm_natCast_cpow_of_pos p.property.pos (-s)
  -- reduce to ∑ p p^{-2 re(s)} which converges if 2 re(s) > 1
  have : Summable (fun p : P => (p.1 : ℝ) ^ (-(2 * s.re))) := by
    exact Real.summable_prime_rpow (by linarith [hs])
  -- convert exponents/form
  -- convert exponents/form without expanding into a product
  convert this using 1
  ext p
  rw [hp]
  rw [← Real.rpow_mul (by exact_mod_cast p.property.pos.le)]
  ring_nf

/-- For `re(s) > 1` we have `∑_p ‖p^{-s}‖ < ∞` (trace-class on diagonal). -/
lemma coeff_summable_of_re_gt_one {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : P => ‖coeff s p‖) := by
  have hp : ∀ p : P, ‖coeff s p‖ = (p.1 : ℝ) ^ (-s.re) := by
    intro p; simpa [coeff] using Complex.norm_natCast_cpow_of_pos p.property.pos (-s)
  have : Summable (fun p : P => (p.1 : ℝ) ^ (-(s.re))) := Real.summable_prime_rpow hs
  aesop

/-- Uniform HS bound on compacts: if `K ⊆ {s | σ ≤ re s}` with `σ > 1/2`, then
    `sup_{s∈K} ∑ ‖coeff s p‖^2 ≤ ∑ (p^{-2σ})`. This is the standard compact-uniform domination. -/
lemma coeff_sq_uniformly_summable_on
    {K : Set ℂ} {σ : ℝ} (hσ : 1/2 < σ)
    (hσK : ∀ s ∈ K, σ ≤ s.re) :
    (∀ᶠ _ in Filter.cocompact ℂ, True) ∧
    (∀ s ∈ K, Summable (fun p : P => ‖coeff s p‖ ^ (2 : ℝ))) ∧
    Summable (fun p : P => (p.1 : ℝ) ^ (-(2 * σ))) := by
  -- pointwise summability on K
  have hpt : ∀ s ∈ K, Summable (fun p : P => ‖coeff s p‖ ^ (2 : ℝ)) := by
    intro s hsK
    have hsσ : 1/2 < s.re := (Std.lt_of_lt_of_le hσ (hσK s hsK))
    exact coeff_sq_summable_of_re_gt_half hsσ
  -- a single dominating series independent of s∈K
  have hdom : ∀ s ∈ K, ∀ p : P, ‖coeff s p‖ ^ (2 : ℝ) ≤ (p.1 : ℝ) ^ (-(2 * σ)) := by
    intro s hsK p
    have hp : ‖coeff s p‖ = (p.1 : ℝ) ^ (-s.re) := by
      simpa [coeff] using Complex.norm_natCast_cpow_of_pos p.property.pos (-s)
    have : (p.1 : ℝ) ^ (-s.re * 2) ≤ (p.1 : ℝ) ^ (-σ * 2) := by
      -- base ≥ 1 (since p ≥ 2)
      have hx1 : 1 ≤ (p.1 : ℝ) := by exact_mod_cast (le_of_lt p.property.one_lt)
      -- exponents: σ ≤ s.re ⇒ -s.re * 2 ≤ -σ * 2
      have hσle : σ ≤ s.re := hσK s hsK
      have hyz : (-s.re * 2) ≤ (-σ * 2) := by linarith
      exact Real.rpow_le_rpow_of_exponent_le hx1 hyz
    -- rewrite both sides using rpow_mul to match exponents
    rw [hp]
    have hx0 : 0 ≤ (p.1 : ℝ) := by exact_mod_cast (Nat.zero_le p.1)
    have lhs :
        ((p.1 : ℝ) ^ (-s.re)) ^ (2 : ℝ) = (p.1 : ℝ) ^ ((-s.re) * 2) := by
      simpa [Real.rpow_mul hx0] using
        (Real.rpow_mul hx0 (-s.re) (2 : ℝ)).symm
    have rhs :
        (p.1 : ℝ) ^ (-(2 * σ)) = (p.1 : ℝ) ^ ((-σ) * 2) := by
      have : -(2 * σ) = (-σ) * 2 := by ring
      simp [this]
    aesop
  have h2σ : 1 < (2 : ℝ) * σ := by
    have := mul_lt_mul_of_pos_left hσ (by norm_num : 0 < (2 : ℝ))
    simpa using this
  have hsum : Summable (fun p : P => (p.1 : ℝ) ^ (-(2 * σ))) :=
    Real.summable_prime_rpow h2σ
  exact ⟨Filter.Eventually.of_forall (by intro; trivial), by
    refine ⟨?_, hsum⟩
    intro s hsK
    exact Summable.of_nonneg_of_le (fun _ => by positivity) (hdom s hsK) hsum⟩

/-! ### A(s) as a bounded diagonal operator with holomorphic dependence -/

/-- A uniform operator-norm bound on U (no piecewise/max): for `s ∈ U` we also have `0 ≤ re s`,
    so `‖coeff s p‖ ≤ 2^{-re s}` yields `‖A(s)‖ ≤ 2^{-re s}`. Outside `Re(s) ≥ 0`, set `A(s) = 0`. -/
def A (s : ℂ) : H →L[ℂ] H :=
  if hs : 0 ≤ s.re then
    let C : ℝ := (2 : ℝ) ^ (-s.re)
    have hC : 0 ≤ C := by exact Real.rpow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) _
    have hb : ∀ p : P, ‖coeff s p‖ ≤ C := fun p => coeff_norm_le_of_re_nonneg hs p
    ContinuousLinearMap.diagOfBound (coeff s) C hC hb
  else
    0

@[simp] lemma A_apply (s : ℂ) (x : H) (p : P) :
  (A s x) p = if 0 ≤ s.re then coeff s p * x p else 0 := by
  by_cases hs : 0 ≤ s.re
  · simp [A, hs, ContinuousLinearMap.diagOfBound_apply]
  · simp [A, hs]

/-- Hilbert–Schmidt on U: `∑ ‖coeff s p‖^2 < ∞`. This is the content of
    `coeff_sq_summable_of_re_gt_half`. In a later step, identify this with
    the HS ideal norm for diagonal operators. -/
lemma A_isHS (s : ℂ) (hs : s ∈ U) :
    Summable (fun p : P => ‖coeff s p‖ ^ (2 : ℝ)) :=
  coeff_sq_summable_of_re_gt_half (by simpa [U] using hs)

/-- Trace-class on `{s | 1 < re s}`: `∑ ‖coeff s p‖ < ∞`. -/
lemma A_isTraceClass (s : ℂ) (hs : 1 < s.re) :
    Summable (fun p : P => ‖coeff s p‖) :=
  coeff_summable_of_re_gt_one hs

lemma coeff_analyticOn (p : P) :
  AnalyticOn ℂ (fun s : ℂ => coeff s p) Set.univ := by
  -- base (p.1 : ℝ) > 0, so s ↦ (p.1 : ℂ)^(-s) is entire
  have hp : 0 < (p.1 : ℝ) := by exact_mod_cast p.property.pos
  -- z ↦ (p.1 : ℂ) ^ z is entire; compose with z = -s
  have hbase : (p.1 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hp)
  have h1 :
      AnalyticOn ℂ (fun z : ℂ => (p.1 : ℂ) ^ z) Set.univ := by
    have hrepr :
        (fun z : ℂ => (p.1 : ℂ) ^ z)
          = (fun z : ℂ => Complex.exp (z * Complex.log (p.1 : ℂ))) := by
      funext z
      simp [Complex.cpow_def_of_ne_zero hbase, mul_comm]
    simpa [hrepr] using
      ((analyticOn_id.mul analyticOn_const).cexp :
        AnalyticOn ℂ (fun z => Complex.exp (z * Complex.log (p.1 : ℂ))) Set.univ)
  have hneg : AnalyticOn ℂ (fun s : ℂ => -s) Set.univ := analyticOn_id.neg
  -- compose with -s
  simpa [coeff] using (h1.comp hneg (mapsTo_univ _ _))

lemma coeff_sq_uniform_bound_on_compact
  {K : Set ℂ} (_ : IsCompact K) {σ : ℝ} (_ : 1/2 < σ)
  (hσK : ∀ s ∈ K, σ ≤ s.re) :
  ∀ s ∈ K, ∀ p : P, ‖coeff s p‖ ^ (2 : ℝ) ≤ (p.1 : ℝ) ^ (-(2 * σ)) := by
  intro s hsK p
  have hp : ‖coeff s p‖ = (p.1 : ℝ) ^ (-s.re) := by
    simpa [coeff] using Complex.norm_natCast_cpow_of_pos p.property.pos (-s)
  have hx1 : 1 ≤ (p.1 : ℝ) := by exact_mod_cast (le_of_lt p.property.one_lt)
  have hσle : σ ≤ s.re := hσK s hsK
  have hyz : (-s.re * 2) ≤ (-σ * 2) := by linarith
  -- use exponent monotonicity for bases ≥ 1
  have : (p.1 : ℝ) ^ (-s.re * 2) ≤ (p.1 : ℝ) ^ (-σ * 2) :=
    Real.rpow_le_rpow_of_exponent_le hx1 hyz
  -- rewrite LHS as (‖coeff‖)^2 using rpow_mul
  have hx0 : 0 ≤ (p.1 : ℝ) := by exact_mod_cast (Nat.zero_le p.1)
  have lhs :
      ((p.1 : ℝ) ^ (-s.re)) ^ (2 : ℝ) = (p.1 : ℝ) ^ ((-s.re) * 2) := by
    simpa [Real.rpow_mul hx0] using
      (Real.rpow_mul hx0 (-s.re) (2 : ℝ)).symm
  have rhs :
      (p.1 : ℝ) ^ (-(2 * σ)) = (p.1 : ℝ) ^ ((-σ) * 2) := by
    have : -(2 * σ) = (-σ) * 2 := by ring
    simp [this]
  aesop
open scoped ENNReal
/-- Rank-one operator on ℓ²: projects onto coordinate p, multiplies by c, embeds back. -/
noncomputable def rankOne (p : P) (c : ℂ) : H →L[ℂ] H :=
  -- Extract coordinate p: x ↦ x p
  let proj : H →L[ℂ] ℂ :=
    { toFun := fun x => x p
      map_add' := fun x y => rfl
      map_smul' := fun r x => rfl
      cont :=
        (continuous_apply p).comp
          ((lp.uniformContinuous_coe (E := fun _ => ℂ) (p := (2 : ℝ≥0∞))).continuous) }
  -- Embed scalar at coordinate p: a ↦ lp.single 2 p a
  let embed : ℂ →L[ℂ] H :=
    { toFun := fun a => lp.single 2 p a
      map_add' := fun a b => by ext i; simp [Pi.single_apply]
      map_smul' := fun r a => by ext i; simp [Pi.single_apply]
      cont := (lp.isometry_single (E := fun _ => ℂ) (p := (2 : ℝ≥0∞)) p).continuous }
  -- Compose: x ↦ c * (x p) at coordinate p, 0 elsewhere
  c • (embed.comp proj)

@[simp] lemma rankOne_apply (p q : P) (c : ℂ) (x : H) :
  (rankOne p c x) q = if p = q then c * x p else 0 := by
  simp [rankOne]
  by_cases h : p = q
  · simp [h, Pi.single_apply]
  · simp [h]

/-- For a finite set F, the partial diagonal operator equals a finite sum of rank-one operators. -/
lemma partial_eq_finset_sum (F : Finset P) (s : ℂ) (hs : 0 ≤ s.re) :
  let C : ℝ := (2 : ℝ) ^ (-s.re)
  let hC : 0 ≤ C := Real.rpow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) _
  let hb : ∀ p : P, ‖(if p ∈ F then coeff s p else 0)‖ ≤ C := by
    intro p; by_cases hpF : p ∈ F
    · simpa [hpF] using coeff_norm_le_of_re_nonneg hs p
    · simpa [hpF] using hC
  ContinuousLinearMap.diagOfBound (fun p => if p ∈ F then coeff s p else 0) C hC hb
    = ∑ p ∈ F, rankOne p (coeff s p) := by
  ext x q
  simp [ContinuousLinearMap.diagOfBound_apply]

/-- Each rank-one operator s ↦ rankOne p (coeff s p) is analytic in s. -/
lemma rankOne_coeff_analyticOn (p : P) :
  AnalyticOn ℂ (fun s => rankOne p (coeff s p)) Set.univ := by
  -- rankOne p c is continuous-linear in c, and s ↦ coeff s p is entire
  have h_coeff : AnalyticOn ℂ (fun s => coeff s p) Set.univ := coeff_analyticOn p
  -- The map c ↦ rankOne p c is continuous-linear (scalar multiplication)
  have h_linear : ∀ s, rankOne p (coeff s p) = (coeff s p) • rankOne p 1 := by
    intro s
    ext x q
    simp [rankOne_apply]
  -- Rewrite as scalar multiplication: (coeff s p) • (constant operator)
  have : (fun s => rankOne p (coeff s p)) = (fun s => (coeff s p) • rankOne p 1) := by
    ext s; aesop
  rw [this]
  -- Apply: analytic function times constant operator is analytic
  exact h_coeff.smul analyticOn_const

/-- Finite sums of analytic functions are analytic. -/
lemma analyticOn_finset_sum {ι : Type*} {f : ι → ℂ → H →L[ℂ] H} {s : Set ℂ} {F : Finset ι}
  (h : ∀ i ∈ F, AnalyticOn ℂ (f i) s) :
  AnalyticOn ℂ (fun z => ∑ i ∈ F, f i z) s := by
  classical
  induction F using Finset.induction with
  | empty =>
    simp
    exact analyticOn_const
  | @insert a B ha ih =>
    have hsum :
        AnalyticOn ℂ (fun z => f a z + ∑ i ∈ B, f i z) s :=
      (h _ (Finset.mem_insert_self _ _)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
    simpa [Finset.sum_insert ha] using hsum

/-- Finite partial diagonal (as a top-level def so it can be unfolded in `simp`). -/
private noncomputable def partial' (F : Finset P) (s : ℂ) : H →L[ℂ] H :=
  if hs : 0 ≤ s.re then
    let C : ℝ := (2 : ℝ) ^ (-s.re)
    have hC : 0 ≤ C := by exact Real.rpow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) _
    have hb : ∀ p : P, ‖(if p ∈ F then coeff s p else 0)‖ ≤ C := by
      intro p; by_cases hpF : p ∈ F
      · simpa [hpF] using coeff_norm_le_of_re_nonneg hs p
      · simpa [hpF] using hC
    ContinuousLinearMap.diagOfBound (fun p => if p ∈ F then coeff s p else 0) C hC hb
  else
    0

open Set Finset ContinuousLinearMap

/-- Monotonicity of natural powers on ℝ for nonnegative bases. -/
lemma pow_le_pow_of_le_left {a b : ℝ} {n : ℕ} (ha : 0 ≤ a) (hab : a ≤ b) :
  a ^ n ≤ b ^ n := by
  induction' n with n ih
  · simp
  · have hb : 0 ≤ b := le_trans ha hab
    calc
      a ^ (n + 1) = a ^ n * a := by simp [pow_succ]
      _ ≤ b ^ n * a := by
        exact mul_le_mul_of_nonneg_right ih ha
      _ ≤ b ^ n * b := by
        exact mul_le_mul_of_nonneg_left hab (pow_nonneg hb _)
      _ = b ^ (n + 1) := by simp [pow_succ]

/-- The operator norm of the difference of two diagonal operators is bounded by the
supremum of the coefficient differences. -/
lemma diagOfBound_sub_norm_le {ι : Type*} (a b : ι → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C) (hb : ∀ i, ‖b i‖ ≤ C) :
    ‖diagOfBound a C hC ha - diagOfBound b C hC hb‖
      ≤ sSup (Set.range fun i => ‖a i - b i‖) := by
  by_cases h_range_empty : Set.range (fun i => ‖a i - b i‖) = ∅
  · have h_is_empty : IsEmpty ι := by rwa [Set.range_eq_empty_iff] at h_range_empty
    have heq : diagOfBound a C hC ha = diagOfBound b C hC hb := by
      ext x i
      exact h_is_empty.elim i
    -- The norm is 0, and sSup ∅ = 0
    simp [heq, h_range_empty]
  have h_bdd : BddAbove (Set.range fun i => ‖a i - b i‖) := by
    use 2 * C
    intro y hy
    obtain ⟨i, rfl⟩ := hy
    calc ‖a i - b i‖
        ≤ ‖a i‖ + ‖b i‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (ha i) (hb i)
      _ = 2 * C := by ring
  have h_nonneg : ∀ x ∈ Set.range (fun i => ‖a i - b i‖), 0 ≤ x := by
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    exact norm_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound _ (by
    exact le_csSup_of_le h_bdd (Set.nonempty_iff_ne_empty.mpr h_range_empty).some_mem
      (h_nonneg _ (Set.nonempty_iff_ne_empty.mpr h_range_empty).some_mem)) ?_
  intro x
  have h_sub : (diagOfBound a C hC ha - diagOfBound b C hC hb) x =
      ⟨fun i => (a i - b i) * x i, by
        have hp2 : 0 < (2 : ℝ≥0∞) := by norm_num
        apply Memℓp.of_bound hp2 (fun i => (a i - b i) * x i) (fun i => x i) (2 * C)
        · linarith
        · exact x.2
        · intro i
          calc ‖(a i - b i) * x i‖
              = ‖a i - b i‖ * ‖x i‖ := norm_mul _ _
            _ ≤ (‖a i‖ + ‖b i‖) * ‖x i‖ := by gcongr; exact norm_sub_le _ _
            _ ≤ (C + C) * ‖x i‖ := by gcongr; exact ha i; exact hb i
            _ = 2 * C * ‖x i‖ := by ring⟩ := by
    ext i
    simp [sub_mul]
  rw [h_sub]
  have hC' : 0 ≤ sSup (Set.range fun i => ‖a i - b i‖) * ‖x‖ := by
    apply mul_nonneg
    · exact le_csSup_of_le h_bdd (Set.nonempty_iff_ne_empty.mpr h_range_empty).some_mem
        (h_nonneg _ (Set.nonempty_iff_ne_empty.mpr h_range_empty).some_mem)
    · exact norm_nonneg _
  have hp2tr : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  refine lp.norm_le_of_forall_sum_le hp2tr (hC := hC') ?_
  intro s
  classical
  have hterm : ∀ i, ‖(a i - b i) * x i‖ ^ (2 : ℝ)
      ≤ (sSup (Set.range fun j => ‖a j - b j‖) * ‖x i‖) ^ (2 : ℝ) := by
    intro i
    have hbase :
        ‖(a i - b i) * x i‖ ≤ sSup (Set.range fun j => ‖a j - b j‖) * ‖x i‖ := by
      simpa [norm_mul] using
        (mul_le_mul_of_nonneg_right
          (le_csSup h_bdd (Set.mem_range_self i))
          (norm_nonneg _))
    gcongr
  have hsum_le : ∑ i ∈ s, ‖(a i - b i) * x i‖ ^ (2 : ℝ)
      ≤ ∑ i ∈ s, (sSup (Set.range fun j => ‖a j - b j‖) * ‖x i‖) ^ (2 : ℝ) :=
    Finset.sum_le_sum (fun i _ => hterm i)
  calc
    ∑ i ∈ s, ‖(a i - b i) * x i‖ ^ (2 : ℝ)
        ≤ ∑ i ∈ s, (sSup (Set.range fun j => ‖a j - b j‖) * ‖x i‖) ^ (2 : ℝ) := hsum_le
    _ = (sSup (Set.range fun j => ‖a j - b j‖)) ^ 2 * ∑ i ∈ s, ‖x i‖ ^ (2 : ℝ) := by
          simp [mul_pow, Finset.mul_sum]
    _ ≤ (sSup (Set.range fun j => ‖a j - b j‖)) ^ 2 * ‖x‖ ^ (2 : ℝ) := by
          gcongr
          exact lp.sum_rpow_le_norm_rpow (by norm_num) x s
    _ = (sSup (Set.range fun j => ‖a j - b j‖) * ‖x‖) ^ (2 : ℝ) := by
          simp [mul_pow]

-- Uniform convergence of the partial diagonal operators to the full diagonal, on a compact K,
-- under the uniform bound ‖coeff s p‖ ≤ (p.1)^{-σ} with σ > 1/2. We use the simple op-norm bound
-- ‖diag(b)‖ ≤ sup_p ‖b p‖ and the fact that sup_{p ∉ F} (p.1 : ℝ) ^ (-σ) → 0 as F ↑ atTop.
lemma ContinuousLinearMap.tendstoUniformlyOn_diagOfBound_of_HS
  (K : Set ℂ) (_ : IsCompact K)
  {σ : ℝ} (hσ : 1/2 < σ)
  (hσK : ∀ s ∈ K, σ ≤ s.re)
  (coeff : ℂ → Nat.Primes → ℂ)
  -- pointwise bound for all s by a fixed p-series with exponent σ
  (hcoeff : ∀ s : ℂ, ∀ p : Nat.Primes, ‖coeff s p‖ ≤ (p.1 : ℝ) ^ (-σ)) :
  TendstoUniformlyOn
    (fun (F : Finset Nat.Primes) (s : ℂ) =>
      let C : ℝ := max ((2 : ℝ) ^ (-σ)) ((2 : ℝ) ^ (-s.re))
      have hC : 0 ≤ C := by positivity
      ContinuousLinearMap.diagOfBound (fun p => if p ∈ F then coeff s p else 0) C hC
        (by
          intro p
          by_cases hp : p ∈ F
          · simp [hp]
            -- bound via hcoeff: ‖coeff s p‖ ≤ (p.1)^{-σ} ≤ 2^{-σ} ≤ C
            have hzσ : -σ ≤ 0 := by linarith [hσ]
            have hmono_base :
                (p.1 : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
              Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast p.property.two_le) hzσ
            have hbound : ‖coeff s p‖ ≤ C := by
              have : ‖coeff s p‖ ≤ (p.1 : ℝ) ^ (-σ) := hcoeff s p
              have : ‖coeff s p‖ ≤ (2 : ℝ) ^ (-σ) := this.trans hmono_base
              exact this.trans (le_max_left _ _)
            exact hbound
          · simp [hp]
            exact hC
        ))
    (fun s =>
      let C : ℝ := max ((2 : ℝ) ^ (-σ)) ((2 : ℝ) ^ (-s.re))
      have hC : 0 ≤ C := by positivity
      ContinuousLinearMap.diagOfBound (fun p => coeff s p) C hC
        (by
          intro p
          by_cases s ∈ K
          · -- bound via hcoeff: ‖coeff s p‖ ≤ (p.1)^{-σ} ≤ 2^{-σ} ≤ C
            have hzσ : -σ ≤ 0 := by linarith [hσ]
            have hmono_base :
                (p.1 : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
              Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast p.property.two_le) hzσ
            have : ‖coeff s p‖ ≤ (p.1 : ℝ) ^ (-σ) := hcoeff s p
            have : ‖coeff s p‖ ≤ (2 : ℝ) ^ (-σ) := this.trans hmono_base
            exact this.trans (le_max_left _ _)
          · -- outside K: irrelevant; just use the global bound and C ≥ 2^{-σ}
            have hzσ : -σ ≤ 0 := by linarith [hσ]
            have hmono_base :
                (p.1 : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
              Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast p.property.two_le) hzσ
            have : ‖coeff s p‖ ≤ (2 : ℝ) ^ (-σ) :=
              (hcoeff s p).trans hmono_base
            exact this.trans (le_max_left _ _)
    ))
    Filter.atTop K := by
  classical
  refine Metric.tendstoUniformlyOn_iff.mpr ?_
  intro ε hε
  -- Use ε/2 to get strict inequality at the end
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, (n : ℝ) ^ (-σ) ≤ ε / 2 := by
    -- standard archimedean estimate: n^{-σ} → 0
    have hσpos : 0 < σ := (lt_trans (by norm_num) hσ)
    -- choose N with (N : ℝ) ≥ ((ε/2)⁻¹) ^ (1 / σ)
    obtain ⟨N, hNlarge⟩ :=
      Archimedean.arch (M := ℝ) (x := ((ε/2)⁻¹) ^ (1 / σ)) (y := 1) (by norm_num : 0 < (1 : ℝ))
    refine ⟨N, ?_⟩
    intro n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hpow : (n : ℝ) ^ σ ≥ (N : ℝ) ^ σ := by
      exact Real.rpow_le_rpow (by exact_mod_cast (Nat.cast_nonneg N)) hn' hσpos.le
    have htarget : (N : ℝ) ^ σ ≥ (ε/2)⁻¹ := by
      have hNreal : ((ε/2)⁻¹) ^ (1 / σ) ≤ (N : ℝ) := by simpa [nsmul_one] using hNlarge
      have hεpos : 0 ≤ (ε/2)⁻¹ := by positivity
      have hx_nonneg : 0 ≤ ((ε/2)⁻¹) ^ (1 / σ) := by
        exact Real.rpow_nonneg hεpos _
      have hx := Real.rpow_le_rpow hx_nonneg hNreal hσpos.le
      -- (((ε/2)⁻¹)^(1/σ))^σ ≤ (N : ℝ)^σ ⇒ (ε/2)⁻¹ ≤ (N : ℝ)^σ
      have : (ε/2)⁻¹ ≤ (N : ℝ) ^ σ := by
        -- Use the fact that (1/σ) * σ = 1, so x^((1/σ)*σ) = x^1 = x
        have h_cancel : (1 / σ) * σ = 1 := by field_simp
        -- Rewrite hx using rpow_mul: (x^a)^b = x^(a*b)
        rw [← Real.rpow_mul hεpos, h_cancel, Real.rpow_one] at hx
        exact hx
      simpa [ge_iff_le] using this
    have : (n : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-σ) := by
      have hNpos : 0 < (N : ℝ) := by
        have hNreal : ((ε/2)⁻¹) ^ (1 / σ) ≤ (N : ℝ) := by simpa [nsmul_one] using hNlarge
        have hεpos : 0 < (ε/2)⁻¹ := by positivity
        have hpow_pos : 0 < ((ε/2)⁻¹) ^ (1 / σ) := Real.rpow_pos_of_pos hεpos (1 / σ)
        exact lt_of_lt_of_le hpow_pos hNreal
      exact Real.rpow_le_rpow_of_nonpos hNpos hn' (by linarith : -σ ≤ 0)
    have hNσ_bound : (N : ℝ) ^ (-σ) ≤ ε / 2 := by
      have : (N : ℝ) ^ σ ≥ (ε/2)⁻¹ := htarget
      have hNpos : 0 < (N : ℝ) := by
        have hNreal : ((ε/2)⁻¹) ^ (1 / σ) ≤ (N : ℝ) := by simpa [nsmul_one] using hNlarge
        have hεpos : 0 < (ε/2)⁻¹ := by positivity
        have hpow_pos : 0 < ((ε/2)⁻¹) ^ (1 / σ) := Real.rpow_pos_of_pos hεpos (1 / σ)
        exact lt_of_lt_of_le hpow_pos hNreal
      have hpos : 0 < (N : ℝ) ^ σ := Real.rpow_pos_of_pos hNpos σ
      have hεinv_pos : 0 < (ε/2)⁻¹ := inv_pos.mpr hε2
      -- (N : ℝ) ^ σ ≥ (ε/2)⁻¹, so by one_div_le_one_div_of_le: ((N : ℝ) ^ σ)⁻¹ ≤ ((ε/2)⁻¹)⁻¹ = ε/2
      have : ((N : ℝ) ^ σ)⁻¹ ≤ ε / 2 := by
        have h1 : ((N : ℝ) ^ σ)⁻¹ ≤ ((ε/2)⁻¹)⁻¹ := inv_inequality hεinv_pos htarget
        simpa [inv_inv] using h1
      -- rewrite ((N : ℝ) ^ σ)⁻¹ = (N : ℝ) ^ (-σ)
      simpa [Real.rpow_neg (le_of_lt hNpos)] using this
    exact this.trans hNσ_bound
  -- take F large enough so that it contains all primes < N
  classical
  -- primes < N as a finset of `Nat.Primes`
  let F0 : Finset Nat.Primes :=
    (((Finset.range N).filter Nat.Prime).attach).image
      (fun n => ⟨n.1, (Finset.mem_filter.mp n.2).2⟩)
  refine Filter.eventually_atTop.2 ⟨F0, ?_⟩
  intro F hFsup s hsK
  -- tail bound is ≤ sup_{p ∉ F} (p.1)^{-σ} ≤ ε by construction
  have hσle : σ ≤ s.re := hσK s hsK
  -- Show that F contains all primes < N
  have hFF : ∀ p : Nat.Primes, p.1 < N → p ∈ F := by
    intro p hp
    have : p ∈ F0 := by
      simp only [F0, Finset.mem_image, Finset.mem_attach]
      use ⟨p.1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp, p.property⟩⟩
      simp only [true_and]
      exact Subtype.ext rfl
    exact hFsup this
  -- Each coefficient difference is bounded
  have hbound_each : ∀ p : Nat.Primes, ‖(if p ∈ F then coeff s p else 0) - coeff s p‖ ≤ ε / 2 := by
    intro p
    by_cases hpF : p ∈ F
    · simp [hpF]
      exact le_of_lt hε2
    · have hp_ge_N : N ≤ p.1 := by
        by_contra h
        push_neg at h
        exact hpF (hFF p h)
      have : ‖coeff s p‖ ≤ (p.1 : ℝ) ^ (-σ) := hcoeff s p
      have : (p.1 : ℝ) ^ (-σ) ≤ ε / 2 := hN p.1 hp_ge_N
      simpa [hpF, norm_neg] using (hcoeff s p).trans this
  -- The operator norm difference is bounded by the supremum, which is ≤ ε/2 < ε
  -- The distance between the two operators (both diagOfBound with different coefficient sets)
  -- is at most the supremum of the coefficient differences
  calc dist (ContinuousLinearMap.diagOfBound _ _ _ _) (ContinuousLinearMap.diagOfBound _ _ _ _)
      = ‖ContinuousLinearMap.diagOfBound _ _ _ _ - ContinuousLinearMap.diagOfBound _ _ _ _‖ := by
        rw [dist_eq_norm]
      _ ≤ sSup (Set.range fun p => ‖coeff s p - (if p ∈ F then coeff s p else 0)‖) := by
        -- Apply the operator norm bound for diagonal operators
        refine diagOfBound_sub_norm_le
          (a := fun p => coeff s p)
          (b := fun p => if p ∈ F then coeff s p else 0)
          (C := max ((2 : ℝ) ^ (-σ)) ((2 : ℝ) ^ (-s.re)))
          ?hC ?ha ?hb
      _ ≤ ε / 2 := by
          refine csSup_le ?_ (fun y hy => ?_)
          · exact range_nonempty (fun p => ‖coeff s p - (if p ∈ F then coeff s p else 0)‖)
          · obtain ⟨p, rfl⟩ := hy
            simpa [norm_sub_rev] using hbound_each p
      _ < ε := by linarith



theorem analyticOn_A : AnalyticOn ℂ (fun s : ℂ => A s) U := by
  refine fun s0 hs0 => ?_
  -- choose σ with 1/2 < σ < s0.re and a small ball included in {s | σ < re s} ⊆ U
  obtain ⟨σ, hσhalf, hσ⟩ : ∃ σ, (1/2 : ℝ) < σ ∧ σ < s0.re := by
    -- s0 ∈ U = {s | 1/2 < s.re}, so s0.re > 1/2
    have hs0_gt_half : (1/2 : ℝ) < s0.re := by simpa [U, Set.mem_setOf_eq] using hs0
    refine ⟨(s0.re + 1/2)/2, ?_, ?_⟩
    · -- (1/2 : ℝ) < (s0.re + 1/2)/2
      linarith [hs0_gt_half]
    · -- (s0.re + 1/2)/2 < s0.re
      linarith
  have hopen : IsOpen {s : ℂ | σ < s.re} := by
    simpa using (isOpen_lt continuous_const Complex.continuous_re)
  obtain ⟨r, hrpos, hball⟩ :
      ∃ r > 0, Metric.ball s0 r ⊆ {s : ℂ | σ < s.re} :=
    Metric.isOpen_iff.mp hopen s0 hσ
  -- Define the finite-partial-sum operators and show they are analytic and converge locally uniformly
  classical
  -- finite partial diagonals for A, written as a definitional `have` to avoid `let` parsing issues
  let partial' :
      ∀ F : Finset P, ℂ → H →L[ℂ] H :=
    fun F s =>
      if hs : 0 ≤ s.re then
        let C : ℝ := (2 : ℝ) ^ (-s.re)
        have hC : 0 ≤ C := by exact Real.rpow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) _
        have hb : ∀ p : P, ‖(if p ∈ F then coeff s p else 0)‖ ≤ C := by
          intro p; by_cases hpF : p ∈ F
          · simpa [hpF] using coeff_norm_le_of_re_nonneg hs p
          · simpa [hpF] using hC
        ContinuousLinearMap.diagOfBound (fun p => if p ∈ F then coeff s p else 0) C hC hb
      else
        0
  -- Each finite partial sum is analytic on the ball (hence on U in a neighborhood)
  have h_partial_analytic :
      ∀ F : Finset P, AnalyticOn ℂ (fun s => partial' F s) (Metric.ball s0 r) := by
    intro F
    -- On the ball we have 0 ≤ re s
    have h_ball_nonneg : ∀ s ∈ Metric.ball s0 r, 0 ≤ s.re := by
      intro s hs
      have hlt : σ < s.re := by
        have : s ∈ {s : ℂ | σ < s.re} := hball hs
        simpa [Set.mem_setOf_eq] using this
      have hσ0 : 0 ≤ σ := (lt_trans (by norm_num : (0 : ℝ) < 1/2) hσhalf).le
      exact le_trans hσ0 (le_of_lt hlt)
    -- Finite sum of analytic rank-one maps
    let g : ℂ → H →L[ℂ] H := fun s => ∑ p ∈ F, rankOne p (coeff s p)
    have hg : AnalyticOn ℂ g (Metric.ball s0 r) :=
      analyticOn_finset_sum (F := F) (s := Metric.ball s0 r)
        (fun p hp => (rankOne_coeff_analyticOn p).mono (by simp))
    -- Equality on the ball with the true finite diagonal
    have heq : Set.EqOn (fun s => partial' F s) g (Metric.ball s0 r) := by
      intro s hs
      have hs_re : 0 ≤ s.re := h_ball_nonneg s hs
      simpa [g, partial', hs_re] using
        (partial_eq_finset_sum F s hs_re)
    -- Transfer analyticity by congruence on the set (note argument order)
    exact hg.congr heq
  -- Locally uniform convergence in operator norm on a compact `Metric.closedBall s0 (r/2)`
  -- Use the HS tail estimate from `coeff_sq_uniformly_summable_on`
  have h_unif :
      TendstoUniformlyOn
        (fun (F : Finset P) s => partial' F s)
        (fun s => A s) Filter.atTop (Metric.closedBall s0 (r/2)) := by
    -- For s in the closed ball of radius r/2, we have σ ≤ re s (since it's contained in the open ball r)
    have hσK : ∀ s ∈ Metric.closedBall s0 (r/2), σ ≤ s.re := by
      intro s hs
      have hsubset : Metric.closedBall s0 (r/2) ⊆ Metric.ball s0 r := by
        have : r / 2 < r := by linarith [hrpos]
        exact Metric.closedBall_subset_ball this
      have hs' : s ∈ Metric.ball s0 r := hsubset hs
      have : s ∈ {s : ℂ | σ < s.re} := hball hs'
      exact le_of_lt (by simpa [Set.mem_setOf_eq] using this)
    -- Prove uniform convergence directly using the tail bound
    refine Metric.tendstoUniformlyOn_iff.mpr ?_
    intro ε hε
    -- Use ε/2 to get strict inequality at the end
    have hε2 : 0 < ε / 2 := by linarith
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, (n : ℝ) ^ (-σ) ≤ ε / 2 := by
      have hσpos : 0 < σ := (lt_trans (by norm_num) hσhalf)
      obtain ⟨N, hNlarge⟩ :=
        Archimedean.arch (M := ℝ) (x := ((ε/2)⁻¹) ^ (1 / σ)) (y := 1) (by norm_num : 0 < (1 : ℝ))
      refine ⟨N, ?_⟩
      intro n hn
      have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hpow : (n : ℝ) ^ σ ≥ (N : ℝ) ^ σ := by
        exact Real.rpow_le_rpow (by exact_mod_cast (Nat.cast_nonneg N)) hn' hσpos.le
      have htarget : (N : ℝ) ^ σ ≥ (ε/2)⁻¹ := by
        have hNreal : ((ε/2)⁻¹) ^ (1 / σ) ≤ (N : ℝ) := by simpa [nsmul_one] using hNlarge
        have hεpos : 0 ≤ (ε/2)⁻¹ := by positivity
        have hx_nonneg : 0 ≤ ((ε/2)⁻¹) ^ (1 / σ) := Real.rpow_nonneg hεpos _
        have hx := Real.rpow_le_rpow hx_nonneg hNreal hσpos.le
        have : (ε/2)⁻¹ ≤ (N : ℝ) ^ σ := by
          have h_cancel : (1 / σ) * σ = 1 := by field_simp
          rw [← Real.rpow_mul hεpos, h_cancel, Real.rpow_one] at hx
          exact hx
        simpa [ge_iff_le] using this
      have : (n : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-σ) := by
        have hNpos : 0 < (N : ℝ) := by
          have hNreal : ((ε/2)⁻¹) ^ (1 / σ) ≤ (N : ℝ) := by simpa [nsmul_one] using hNlarge
          have hεpos : 0 < (ε/2)⁻¹ := by positivity
          have hpow_pos : 0 < ((ε/2)⁻¹) ^ (1 / σ) := Real.rpow_pos_of_pos hεpos (1 / σ)
          exact lt_of_lt_of_le hpow_pos hNreal
        exact Real.rpow_le_rpow_of_nonpos hNpos hn' (by linarith : -σ ≤ 0)
      have hNσ_bound : (N : ℝ) ^ (-σ) ≤ ε / 2 := by
        have : (N : ℝ) ^ σ ≥ (ε/2)⁻¹ := htarget
        have hNpos : 0 < (N : ℝ) := by
          have hNreal : ((ε/2)⁻¹) ^ (1 / σ) ≤ (N : ℝ) := by simpa [nsmul_one] using hNlarge
          have hεpos : 0 < (ε/2)⁻¹ := by positivity
          have hpow_pos : 0 < ((ε/2)⁻¹) ^ (1 / σ) := Real.rpow_pos_of_pos hεpos (1 / σ)
          exact lt_of_lt_of_le hpow_pos hNreal
        have hpos : 0 < (N : ℝ) ^ σ := Real.rpow_pos_of_pos hNpos σ
        have hεinv_pos : 0 < (ε/2)⁻¹ := inv_pos.mpr hε2
        have : ((N : ℝ) ^ σ)⁻¹ ≤ ε / 2 := by
          have h1 : ((N : ℝ) ^ σ)⁻¹ ≤ ((ε/2)⁻¹)⁻¹ := inv_inequality hεinv_pos htarget
          simpa [inv_inv] using h1
        simpa [Real.rpow_neg (le_of_lt hNpos)] using this
      exact this.trans hNσ_bound
    -- Define F0 containing all primes < N
    let F0 : Finset Nat.Primes :=
      (((Finset.range N).filter Nat.Prime).attach).image
        (fun n => ⟨n.1, (Finset.mem_filter.mp n.2).2⟩)
    refine Filter.eventually_atTop.mpr ⟨F0, ?_⟩
    intro F hFsup s hsK
    -- Show distance between operators is < ε
    have hσle : σ ≤ s.re := hσK s hsK
    have hs_nonneg : 0 ≤ s.re := by linarith [hσhalf, hσle]
    -- Both operators are defined with the same coefficients on the ball
    simp only [partial', A, hs_nonneg, dite_true]
    -- F contains all primes < N
    have hFF : ∀ p : Nat.Primes, p.1 < N → p ∈ F := by
      intro p hp
      have : p ∈ F0 := by
        simp only [F0, Finset.mem_image, Finset.mem_attach]
        use ⟨p.1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp, p.property⟩⟩
        simp only [true_and]
        exact Subtype.ext rfl
      exact hFsup this
    -- The difference is a diagonal with coefficients (if p ∈ F then coeff s p else 0) - coeff s p
    -- The distance equals the operator norm of this difference
    -- For p ∈ F, the coefficient is 0; for p ∉ F, it's -coeff s p
    -- So we need to bound ‖coeff s p‖ for p ∉ F
    have hbound_tail : ∀ p : Nat.Primes, p ∉ F → ‖coeff s p‖ ≤ ε / 2 := by
      intro p hpF
      have hp_ge_N : N ≤ p.1 := by
        by_contra h; push_neg at h
        exact hpF (hFF p h)
      have hp1 : ‖coeff s p‖ = (p.1 : ℝ) ^ (-s.re) := by
        simpa [coeff] using Complex.norm_natCast_cpow_of_pos p.property.pos (-s)
      rw [hp1]
      have h1 : (p.1 : ℝ) ^ (-s.re) ≤ (p.1 : ℝ) ^ (-σ) := by
        have hx1 : 1 ≤ (p.1 : ℝ) := by exact_mod_cast (le_of_lt p.property.one_lt)
        have : (-s.re) ≤ (-σ) := by linarith
        exact Real.rpow_le_rpow_of_exponent_le hx1 this
      have h2 : (p.1 : ℝ) ^ (-σ) ≤ ε / 2 := hN p.1 hp_ge_N
      exact h1.trans h2
    -- Use opNorm bound for diagonal operators
    calc dist (diagOfBound (coeff s) (2 ^ (-s.re)) _ _)
              (diagOfBound (fun p => if p ∈ F then coeff s p else 0) (2 ^ (-s.re)) _ _)
        = ‖diagOfBound (coeff s) (2 ^ (-s.re)) _ _ -
            diagOfBound (fun p => if p ∈ F then coeff s p else 0) (2 ^ (-s.re)) _ _‖ := by
          rw [dist_eq_norm]
      _ ≤ sSup (Set.range fun p => ‖coeff s p - (if p ∈ F then coeff s p else 0)‖) := by
          apply diagOfBound_sub_norm_le
      _ ≤ ε / 2 := by
          refine csSup_le ?_ (fun y hy => ?_)
          · exact range_nonempty fun p ↦ ‖coeff s p - (if p ∈ F then coeff s p else 0)‖
          · obtain ⟨p, rfl⟩ := hy
            by_cases hpF : p ∈ F
            · simp [hpF]; linarith
            · simp [hpF]; exact hbound_tail p hpF
      _ < ε := by linarith
  -- Apply the Weierstrass Convergence Theorem to conclude analyticity
  -- The theorem is stated in AnalyticInfrastructure.lean with full mathematical documentation
  have hlim : AnalyticOn ℂ (fun s => A s) (Metric.ball s0 r) := by
    -- Reindex finsets by ℕ: for each n, take F_n = {p : primes | p.1 < n}
    let Fseq : ℕ → Finset P := fun n =>
      (((Finset.range n).filter Nat.Prime).attach).image
        (fun m => ⟨m.1, (Finset.mem_filter.mp m.2).2⟩)
    -- Define the sequence of partial sums
    let Fₙ : ℕ → ℂ → H →L[ℂ] H := fun n s => partial' (Fseq n) s
    -- Each Fₙ is analytic on the ball
    have hFn_analytic : ∀ n, AnalyticOn ℂ (Fₙ n) (Metric.ball s0 r) := by
      intro n
      exact h_partial_analytic (Fseq n)
    -- Show that Fₙ converges locally uniformly to A
    have hFn_unif : ∀ z ∈ Metric.ball s0 r, ∃ K,
        IsCompact K ∧ z ∈ interior K ∧ K ⊆ Metric.ball s0 r ∧
        TendstoUniformlyOn Fₙ (fun s => A s) Filter.atTop K := by
      intro z hz
      -- Use the closed ball of radius (r + dist z s0) / 2 around s0
      let ρ := (r + dist z s0) / 2
      have hρ : dist z s0 < ρ := by
        simp [ρ]
        have : dist z s0 < r := by simpa [Metric.mem_ball] using hz
        linarith
      have hρr : ρ < r := by
        simp [ρ]
        have : dist z s0 < r := by simpa [Metric.mem_ball] using hz
        linarith
      let ρ' := min (r/2) ((r/2 + dist z s0) / 2)
      use Metric.closedBall s0 ρ'
      constructor
      · exact closedBall_compact_complex s0 ρ'
      constructor
      · rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
        use ρ' - dist z s0
        constructor
        · have hz_dist : dist z s0 < r := Metric.mem_ball.mp hz
          simp only [ρ']
          have : dist z s0 < (r + dist z s0) / 2 := by linarith
          have : (r + dist z s0) / 2 ≤ r := by linarith
          linarith [min_le_right (r/2) ((r + dist z s0) / 2)]
        · intro w hw
          simp [Metric.mem_closedBall] at hw ⊢
          calc dist w s0 ≤ dist w z + dist z s0 := dist_triangle _ _ _
            _ < (ρ' - dist z s0) + dist z s0 := by linarith [hw]
            _ = ρ' := by ring
      constructor
      · intro w hw
        simp [Metric.mem_closedBall] at hw
        simp [Metric.mem_ball]
        have : ρ' ≤ r/2 := min_le_left _ _
        calc dist w s0 ≤ ρ' := hw
          _ ≤ r/2 := this
          _ < r := by linarith [hrpos]
      · -- Fseq n is cofinal in Finset P under ⊆
        have hcofinal : ∀ F : Finset P, ∃ n, F ⊆ Fseq n := by
          intro F
          obtain ⟨N, hN⟩ := F.exists_nat_subset_range
          refine ⟨N, ?_⟩
          intro p hp
          -- from hN we get p.1 ∈ range N
          have hp1 : p.1 ∈ Finset.range N := by
            have : p.1 ∈ (do let a ← F; pure (a.1)) := by
              -- image membership for Subtype.val
              simpa [Finset.mem_image] using ⟨p, hp, rfl⟩
            exact hN this
          -- now expand Fseq N and build the witness in the image
          simp only [Fseq, Finset.mem_image, Finset.mem_attach]
          refine ⟨⟨p.1, Finset.mem_filter.mpr ⟨hp1, p.property⟩⟩, ?_, ?_⟩
          · simp
          · exact Subtype.ext rfl
        -- Convert uniform convergence from Finset to ℕ via the metric criterion
        refine Metric.tendstoUniformlyOn_iff.mpr ?_
        intro ε hε
        obtain ⟨F0, hF0⟩ := Filter.eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.mp h_unif) ε hε)
        obtain ⟨N, hN⟩ := hcofinal F0
        refine Filter.eventually_atTop.2 ?_
        refine ⟨N, ?_⟩
        intro n hn
        intro s hs
        simp [Fₙ]
        have hFn_ge : F0 ⊆ Fseq n := by
          intro p hp
          have hpN : p ∈ Fseq N := hN hp
          classical
          -- deduce p.1 < N from hpN
          have hp_lt_N : p.1 < N := by
            obtain ⟨m, hm, hm_eq⟩ :
                ∃ m ∈ (((Finset.range N).filter Nat.Prime).attach),
                  (fun m => ⟨m.1, (Finset.mem_filter.mp m.2).2⟩) m = p := by
              simpa [Fseq] using hpN
            have hm' : m.1 ∈ (Finset.range N).filter Nat.Prime := by aesop
            have hm_range : m.1 ∈ Finset.range N := (Finset.mem_filter.mp hm').1
            have : p.1 = m.1 := by
              simpa using (congrArg Subtype.val hm_eq).symm
            exact by simpa [this] using (Finset.mem_range.mp hm_range)
          have hp_range_n : p.1 ∈ Finset.range n := Finset.mem_range.mpr (lt_of_lt_of_le hp_lt_N hn)
          simp only [Fseq, Finset.mem_image, Finset.mem_attach]
          refine ⟨⟨p.1, Finset.mem_filter.mpr ⟨hp_range_n, p.property⟩⟩, ?_, ?_⟩
          · simp
          · exact Subtype.ext rfl
        exact hF0 _ hFn_ge _ hs
    -- Apply the Weierstrass Convergence Theorem (from AnalyticInfrastructure.lean)
    exact AnalyticOn.of_tendstoUniformlyOn Metric.isOpen_ball (fun s => A s) hFn_analytic hFn_unif
  -- Conclude analyticity at s0 within U
  -- hlim gives analyticity within the ball; lift to U via monotonicity
  have : Metric.ball s0 r ⊆ U := by
    intro s hs
    simp only [U, Set.mem_setOf_eq]
    have : σ < s.re := hball hs
    linarith [hσhalf]
  exact (hlim.mono this) s0 (Metric.mem_ball_self hrpos)

end RH
