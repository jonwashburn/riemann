import Riemann.academic_framework.HadamardFactorization.GrowthBound

noncomputable section

namespace ComplexAnalysis
namespace Hadamard

open Complex Real BigOperators Finset Set Filter Topology Metric ValueDistribution
open scoped Topology


--set_option maxHeartbeats 0 in
/--
**Hadamard Factorization Theorem**

Every entire function `f` of finite order `ρ` can be written as:
`f(z) = z^m * e^P(z) * ∏ E_p(z/a_n)`
where `p := ⌊ρ⌋` and `P` is a polynomial of degree `≤ p`.

Reference: https://terrytao.wordpress.com/2020/12/23/246b-notes-1-zeroes-poles-and-factorisation-of-meromorphic-functions/#more-12187

Theorem 22 (Hadamard factorisation theorem)
Let {\rho \geq 0}, let {d := \lfloor \rho \rfloor}, and let {f} be an entire function of order at
most {\rho} (not identically zero), with a zero of order {m \geq 0} at the origin and the remaining
zeroes indexed (with multiplicity) as a finite or infinite sequence {z_1, z_2, \dots}. Then

 f(z) = e^{g(z)} z^m \prod_n E_d(z/z_n) \ \ \ \ \ (19)

for some polynomial {g} of degree at most {d}. The convergence in the infinite product is locally uniform.
-/
theorem hadamard_factorization
    {ρ : ℝ} {f : ℂ → ℂ}
    (hρ : 0 ≤ ρ)
    (hf : EntireOfFiniteOrder ρ f)
    (hz : ZeroData f) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ (Nat.floor ρ) ∧
      ∀ z : ℂ,
        f z = Complex.exp (Polynomial.eval z P) *
          z ^ hz.ord0 *
          ∏' n : ℕ, (ComplexAnalysis.Hadamard.weierstrassFactor (Nat.floor ρ) (z / hz.zeros n)) := by
  classical
  -- 1. Choose genus m = floor(ρ)
  set m : ℕ := Nat.floor ρ
  have hmρ : (m : ℝ) ≤ ρ := by
    -- `floor ρ ≤ ρ`
    simpa [m] using (Nat.floor_le hρ)
  have hσ : ρ < (m + 1 : ℝ) := Nat.lt_floor_add_one ρ

  -- 2. Construct Canonical Product F
  have hsum : Summable (fun n => ‖hz.zeros n‖⁻¹ ^ (m + 1)) := by
    have hσ_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hsum_real := lindelof_zero_data hf hz hσ hσ_pos
    -- convert `Real.rpow` with nat exponent to `pow`
    simpa [Nat.cast_add_one] using (hsum_real.congr fun n => by
      simpa using (Real.rpow_natCast (x := ‖hz.zeros n‖⁻¹) (n := m + 1)))
  let G := fun z => ∏' n, weierstrassFactor m (z / hz.zeros n)
  let F := fun z => z ^ hz.ord0 * G z

  -- 3. Construct Quotient H = f/F
  -- F has the same zeros as f, so H is entire.
  have hG_entire : Differentiable ℂ G := by
    simpa [G] using (differentiable_canonical_product_zeroData (hz := hz) (m := m) hsum)
  have hF_entire : Differentiable ℂ F := by
    simpa [F] using ( (differentiable_id.pow hz.ord0).mul hG_entire )

  -- `f` is not identically zero (otherwise `ZeroData` would force `ℂ` to be countable).
  have hf_not_all_zero : ¬ (∀ z : ℂ, f z = 0) := zeroData_not_all_zero hz
  have hf_nontrivial : ∃ z : ℂ, f z ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf_not_all_zero h

  -- `analyticOrderAt f z` is never `⊤` (since `f` is analytic on `univ` and not locally zero anywhere).
  have hf_not_top : ∀ z : ℂ, analyticOrderAt f z ≠ ⊤ := by
    rcases hf_nontrivial with ⟨z1, hz1⟩
    have hf_an : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
      (analyticOnNhd_univ_iff_differentiable).2 hf.entire
    have hz1_not_top : analyticOrderAt f z1 ≠ ⊤ := by
      have : analyticOrderAt f z1 = 0 :=
        (hf.entire.analyticAt z1).analyticOrderAt_eq_zero.2 hz1
      simp [this]
    intro z
    exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (hf := hf_an)
      (U := (Set.univ : Set ℂ)) (x := z1) (y := z) (by simpa using isPreconnected_univ)
      (by simp) (by simp) hz1_not_top

  -- Convert `ZeroData`'s `analyticOrderNatAt` specifications into `analyticOrderAt` equalities.
  have horder_f0 : analyticOrderAt f (0 : ℂ) = (hz.ord0 : ℕ∞) := by
    have hcast :
        (analyticOrderNatAt f (0 : ℂ) : ℕ∞) = analyticOrderAt f (0 : ℂ) :=
      Nat.cast_analyticOrderNatAt (f := f) (z₀ := (0 : ℂ)) (hf_not_top 0)
    simpa [hz.ord0_spec] using hcast.symm

  have horder_f_nonzero :
      ∀ {z : ℂ}, z ≠ 0 → analyticOrderAt f z = (Nat.card {n : ℕ // hz.zeros n = z} : ℕ∞) := by
    intro z hz0
    have hcast :
        (analyticOrderNatAt f z : ℕ∞) = analyticOrderAt f z :=
      Nat.cast_analyticOrderNatAt (f := f) (z₀ := z) (hf_not_top z)
    -- `zeros_mult_spec` is stated for `analyticOrderNatAt`; convert via `Nat.cast_analyticOrderNatAt`
    -- without `simp` (to avoid `simp`-looping on casts).
    have hmult :
        (analyticOrderNatAt f z : ℕ∞) = (Nat.card {n : ℕ // hz.zeros n = z} : ℕ∞) :=
      congrArg (fun n : ℕ => (n : ℕ∞)) (hz.zeros_mult_spec z hz0)
    calc
      analyticOrderAt f z = (analyticOrderNatAt f z : ℕ∞) := by simp [hcast]
      _ = (Nat.card {n : ℕ // hz.zeros n = z} : ℕ∞) := hmult

  -- Analytic order of the canonical product at a nonzero zero.
  have horder_G_nonzero :
      ∀ {z : ℂ}, z ≠ 0 → analyticOrderAt G z = (Nat.card {n : ℕ // hz.zeros n = z} : ℕ∞) := by
    intro z hz0
    -- Finite fiber of indices with `hz.zeros n = z`.
    let sSet : Set ℕ := {n : ℕ | hz.zeros n = z}
    have hsSet_fin : sSet.Finite := by
      -- `ZeroData.finite_fiber` from `Basic.lean`
      simpa [sSet, Set.mem_setOf_eq] using (hz.finite_fiber (z := z) hz0)
    let s : Finset ℕ := hsSet_fin.toFinset
    have hs_mem : ∀ n : ℕ, n ∈ s ↔ hz.zeros n = z := by
      intro n
      -- membership in `toFinset` ↔ membership in the underlying set
      simp [s, sSet, Set.mem_setOf_eq]

    -- Remove the (finitely many) indices in the fiber by turning them into padding zeros.
    let zeros' : ℕ → ℂ := fun n => if n ∈ s then (0 : ℂ) else hz.zeros n
    let G' : ℂ → ℂ := fun w => ∏' n : ℕ, weierstrassFactor m (w / zeros' n)

    -- `zeros'` still satisfies the same local finiteness condition for nonzero values.
    have finite_in_ball' :
        ∀ R : ℝ, ({n : ℕ | zeros' n ≠ 0 ∧ ‖zeros' n‖ ≤ R} : Set ℕ).Finite := by
      intro R
      refine (hz.finite_in_ball R).subset ?_
      intro n hn
      have hnmem : n ∉ s := by
        intro hnmem
        -- then `zeros' n = 0`, contradicting `zeros' n ≠ 0`
        simp [zeros', hnmem] at hn
      have hEq : zeros' n = hz.zeros n := by simp [zeros', hnmem]
      refine ⟨?_, ?_⟩
      · -- nonzero
        simpa [hEq] using hn.1
      · -- norm bound
        simpa [hEq] using hn.2

    -- Summability for the modified sequence follows by comparison with `hsum`.
    have hsum' : Summable (fun n : ℕ => ‖zeros' n‖⁻¹ ^ (m + 1)) := by
      refine Summable.of_nonneg_of_le (f := fun n => ‖hz.zeros n‖⁻¹ ^ (m + 1))
        (g := fun n => ‖zeros' n‖⁻¹ ^ (m + 1)) ?_ ?_ hsum
      · intro n; positivity
      · intro n
        by_cases hn : n ∈ s
        · -- `zeros' n = 0`, so the term is `0 ≤ _`
          simp [zeros', hn]
        · simp [zeros', hn]

    have hG'_entire : Differentiable ℂ G' := by
      simpa [G'] using
        (differentiable_canonical_product_of_finiteInBall zeros' finite_in_ball' m hsum')

    -- `G' z ≠ 0` because all remaining factors are nonzero at `z`.
    have hG'_ne : G' z ≠ 0 := by
      have hfac : ∀ n : ℕ, weierstrassFactor m (z / zeros' n) ≠ 0 := by
        intro n
        by_cases hn : n ∈ s
        · -- `zeros' n = 0` ⇒ factor = 1
          simp [zeros', hn, weierstrassFactor_zero]
        · -- otherwise `zeros' n = hz.zeros n` and `hz.zeros n ≠ z`
          have hnz : hz.zeros n ≠ z := by
            intro hnz
            have : n ∈ s := (hs_mem n).2 hnz
            exact hn this
          -- if `hz.zeros n = 0` it's also fine
          by_cases h0 : hz.zeros n = 0
          · simp [zeros', hn, h0, weierstrassFactor_zero]
          · -- nonzero and not equal ⇒ factor nonzero
            intro h0fac
            have h0fac' : weierstrassFactor m (z / hz.zeros n) = 0 := by
              simpa [zeros', hn] using h0fac
            have hw1 : z / hz.zeros n = (1 : ℂ) :=
              (weierstrassFactor_eq_zero_iff (m := m) (z := z / hz.zeros n)).1 h0fac'
            have hz_eq : z = hz.zeros n := by
              have h' := congrArg (fun w : ℂ => w * hz.zeros n) hw1
              -- (z / a) * a = 1 * a, so z = a (since a ≠ 0)
              simpa [div_eq_mul_inv, mul_assoc, h0] using h'
            exact hnz hz_eq.symm
      exact
        (tprod_weierstrassFactor_ne_zero_of_forall_of_finiteInBall zeros' finite_in_ball' m hsum' z hfac)

    -- Decompose the full product into a finite product over the fiber times `G'`.
    have h_decomp : ∀ w : ℂ,
        G w = (∏ n ∈ s, weierstrassFactor m (w / hz.zeros n)) * G' w := by
      intro w
      classical
      -- Write the full product as a product of two functions: a finite part supported on `s`,
      -- and the “complementary” part where indices in `s` are replaced by `1`.
      let fW : ℕ → ℂ := fun n => weierstrassFactor m (w / hz.zeros n)
      let aW : ℕ → ℂ := fun n => if n ∈ s then fW n else 1
      let bW : ℕ → ℂ := fun n => weierstrassFactor m (w / zeros' n)

      have hab : ∀ n : ℕ, aW n * bW n = fW n := by
        intro n
        by_cases hn : n ∈ s
        · -- on `s`, `zeros' n = 0`, hence `bW n = 1`
          have : zeros' n = (0 : ℂ) := by simp [zeros', hn]
          simp [aW, bW, fW, hn, this, weierstrassFactor_zero]
        · -- off `s`, `zeros' n = hz.zeros n`
          have : zeros' n = hz.zeros n := by simp [zeros', hn]
          simp [aW, bW, fW, hn, this]

      -- `aW` is multipliable since it differs from `1` only on the finite set `s`.
      have ha_mulSupport : Function.mulSupport aW ⊆ (s : Set ℕ) := by
        refine (Function.mulSupport_subset_iff'.2 ?_)
        intro n hn
        have hn' : n ∉ s := by simpa using hn
        simp [aW, hn']
      have ha_mul : Multipliable aW :=
        multipliable_of_finite_mulSupport ((s.finite_toSet).subset ha_mulSupport)

      -- `bW` is multipliable by the same Weierstrass-tail summability argument used to define `G'`.
      have htail_bW : Summable (fun n : ℕ => bW n - 1) := by
        -- this is exactly the `finite_in_ball'` majorant argument for `zeros'`
        simpa [bW, G', zeros'] using
          (summable_weierstrassFactor_sub_one_of_finiteInBall zeros' finite_in_ball' m hsum' w)
      have hb_mul : Multipliable bW := by
        simpa [bW, add_sub_cancel] using
          (Complex.multipliable_one_add_of_summable (f := fun n : ℕ => bW n - 1) htail_bW)

      have hmul :
          (∏' n : ℕ, fW n) = (∏' n : ℕ, aW n) * (∏' n : ℕ, bW n) := by
        -- Use `tprod_mul` on `aW * bW`, then rewrite pointwise to `fW`.
        have ht := (Multipliable.tprod_mul (f := aW) (g := bW) ha_mul hb_mul)
        -- rewrite the LHS `∏'(aW*bW)` into `∏' fW`
        have hcongr : (∏' n : ℕ, aW n * bW n) = ∏' n : ℕ, fW n := by
          refine tprod_congr (fun n => ?_)
          simp [hab n]
        -- assemble
        simpa [hcongr] using ht

      have hA :
          (∏' n : ℕ, aW n) = ∏ n ∈ s, fW n := by
        -- `aW = 1` off `s`.
        have ht : (∏' n : ℕ, aW n) = ∏ n ∈ s, aW n := by
          refine tprod_eq_prod (f := aW) (s := s) ?_
          intro n hn
          have hn' : n ∉ s := by simpa using hn
          simp [aW, hn']
        -- simplify on `s`.
        have ht' : (∏ n ∈ s, aW n) = ∏ n ∈ s, fW n := by
          classical
          refine Finset.prod_congr rfl ?_
          intro n hn
          simp [aW, hn]
        exact ht.trans ht'

      have hB : (∏' n : ℕ, bW n) = G' w := by
        rfl

      -- Put everything together.
      have : G w = (∏ n ∈ s, fW n) * (∏' n : ℕ, bW n) := by
        -- `G w = ∏' fW`
        have : G w = ∏' n : ℕ, fW n := by rfl
        -- rewrite using `hmul` and `hA`
        simp [this, hmul, hA]
      -- Finally, unfold `fW`.
      simpa [fW, G', hB, mul_assoc, G] using this

    -- Compute `analyticOrderAt G z` using the decomposition.
    have hA_an : AnalyticAt ℂ (fun w : ℂ => ∏ n ∈ s, weierstrassFactor m (w / hz.zeros n)) z := by
      -- finite product of entire functions
      have : Differentiable ℂ (fun w : ℂ => ∏ n ∈ s, weierstrassFactor m (w / hz.zeros n)) := by
        -- differentiable finite product
        have hdf : ∀ n ∈ s, Differentiable ℂ (fun w : ℂ => weierstrassFactor m (w / hz.zeros n)) := by
          intro n _hn
          exact (differentiable_weierstrassFactor m).comp (differentiable_id.div_const (hz.zeros n))
        -- `Finset.prod_fn` rewrites the finset product of functions into a pointwise finset product.
        simpa [Finset.prod_fn] using
          (Differentiable.finset_prod (f := fun n w => weierstrassFactor m (w / hz.zeros n)) hdf)
      exact this.analyticAt z
    have hG'_an : AnalyticAt ℂ G' z := hG'_entire.analyticAt z

    have horder_A :
        analyticOrderAt (fun w : ℂ => ∏ n ∈ s, weierstrassFactor m (w / hz.zeros n)) z
          = (s.card : ℕ∞) := by
      -- rewrite the finite product as a power of the single factor `(w ↦ weierstrassFactor m (w / z))`
      have hEq :
          (fun w : ℂ => ∏ n ∈ s, weierstrassFactor m (w / hz.zeros n))
            = fun w : ℂ => (weierstrassFactor m (w / z)) ^ s.card := by
        funext w
        classical
        -- on the fiber, `hz.zeros n = z`
        have : ∏ n ∈ s, weierstrassFactor m (w / hz.zeros n) = ∏ _n ∈ s, weierstrassFactor m (w / z) := by
          refine Finset.prod_congr rfl ?_
          intro n hn
          have hn' : hz.zeros n = z := (hs_mem n).1 hn
          simp [hn']
        -- constant finset product
        simp [this, Finset.prod_const]
      -- compute analytic order of the power at `z`
      have hfac_order :
          analyticOrderAt (fun w : ℂ => weierstrassFactor m (w / z)) z = (1 : ℕ∞) := by
        simpa using (analyticOrderAt_weierstrassFactor_div_self (m := m) (a := z) hz0)
      have hfac_an : AnalyticAt ℂ (fun w : ℂ => weierstrassFactor m (w / z)) z := by
        exact ((differentiable_weierstrassFactor m).comp (differentiable_id.div_const z)).analyticAt z
      -- `analyticOrderAt (f^n) = n • analyticOrderAt f`
      have hpow :
          analyticOrderAt (fun w : ℂ => (weierstrassFactor m (w / z)) ^ s.card) z
            = s.card • analyticOrderAt (fun w : ℂ => weierstrassFactor m (w / z)) z :=
        analyticOrderAt_pow (𝕜 := ℂ) (f := fun w : ℂ => weierstrassFactor m (w / z)) (z₀ := z) hfac_an s.card
      -- finish
      simp [hEq, hpow, hfac_order]

    have horder_G' : analyticOrderAt G' z = 0 := by
      exact (hG'_an.analyticOrderAt_eq_zero).2 hG'_ne

    -- Now `G = A * G'`, hence order is sum.
    have hG_eq : G = fun w : ℂ => (∏ n ∈ s, weierstrassFactor m (w / hz.zeros n)) * G' w := by
      funext w
      simp [h_decomp w]
    have hG_order_finset : analyticOrderAt G z = (s.card : ℕ∞) := by
      calc
      analyticOrderAt G z
          = analyticOrderAt (fun w : ℂ => (∏ n ∈ s, weierstrassFactor m (w / hz.zeros n)) * G' w) z := by
              simp [hG_eq]
      _ = analyticOrderAt (fun w : ℂ => ∏ n ∈ s, weierstrassFactor m (w / hz.zeros n)) z
            + analyticOrderAt G' z := by
              simpa [Pi.mul_apply] using (analyticOrderAt_mul (𝕜 := ℂ) (f := fun w : ℂ => ∏ n ∈ s, weierstrassFactor m (w / hz.zeros n))
                (g := G') (z₀ := z) hA_an hG'_an)
      _ = (s.card : ℕ∞) := by simp [horder_A, horder_G']

    -- `s` is the finset of the fiber `{n | hz.zeros n = z}`, so `s.card` matches `Nat.card {n // hz.zeros n = z}`.
    have hs_card : s.card = Nat.card {n : ℕ // hz.zeros n = z} := by
      classical
      -- Give the fiber a `Fintype` structure (it is finite because `z ≠ 0`).
      haveI : Finite {n : ℕ // hz.zeros n = z} := hz.finite_fiber_type (z := z) hz0
      letI : Fintype {n : ℕ // hz.zeros n = z} := Fintype.ofFinite _
      -- Build an explicit equivalence `s ≃ {n // hz.zeros n = z}` using `hs_mem`.
      let e : (↥s) ≃ {n : ℕ // hz.zeros n = z} :=
        { toFun := fun x => ⟨x.1, (hs_mem x.1).1 x.2⟩
          invFun := fun x => ⟨x.1, (hs_mem x.1).2 x.2⟩
          left_inv := by
            intro x
            ext
            rfl
          right_inv := by
            intro x
            ext
            rfl }
      -- Convert cards.
      have hs_fin : s.card = Fintype.card {n : ℕ // hz.zeros n = z} := by
        -- `Fintype.card ↥s = s.card`
        have hs0 : Fintype.card (↥s) = s.card := Fintype.card_coe s
        -- and `card ↥s = card fiber` by `e`.
        have hs1 : Fintype.card (↥s) = Fintype.card {n : ℕ // hz.zeros n = z} := Fintype.card_congr e
        exact hs0.symm.trans hs1
      exact hs_fin.trans (by
        simp)

    -- Final form.
    simpa [hs_card] using hG_order_finset

  -- Compute the analytic order of `F` and show it matches `f` everywhere.
  have horder_F : ∀ z : ℂ, analyticOrderAt F z = analyticOrderAt f z := by
    intro z
    by_cases hz0 : z = 0
    · subst hz0
      -- `G 0 = 1`, hence `analyticOrderAt G 0 = 0`.
      have hG0 : G (0 : ℂ) = 1 := by
        simp [G, weierstrassFactor_zero, tprod_one]
      have hG0_ne : G (0 : ℂ) ≠ 0 := by simp [hG0]
      have hG0_order : analyticOrderAt G (0 : ℂ) = 0 :=
        (hG_entire.analyticAt 0).analyticOrderAt_eq_zero.2 hG0_ne
      have hpow_order : analyticOrderAt (fun w : ℂ => w ^ hz.ord0) (0 : ℂ) = (hz.ord0 : ℕ∞) := by
        -- centered monomial at 0
        simpa [sub_zero] using
          (analyticOrderAt_centeredMonomial (𝕜 := ℂ) (z₀ := (0 : ℂ)) (n := hz.ord0))
      have hF_order :
          analyticOrderAt F (0 : ℂ) = analyticOrderAt (fun w : ℂ => w ^ hz.ord0) (0 : ℂ)
            + analyticOrderAt G (0 : ℂ) := by
        have hpow_an : AnalyticAt ℂ (fun w : ℂ => w ^ hz.ord0) (0 : ℂ) :=
          (differentiable_id.pow hz.ord0).analyticAt 0
        have hG_an : AnalyticAt ℂ G (0 : ℂ) := hG_entire.analyticAt 0
        simpa [F, G, Pi.mul_apply] using
          (analyticOrderAt_mul (𝕜 := ℂ) (f := fun w : ℂ => w ^ hz.ord0) (g := G) (z₀ := (0 : ℂ))
            hpow_an hG_an)
      -- compare to `f`
      simpa [horder_f0, hpow_order, hG0_order] using hF_order
    · -- `z ≠ 0`: the power factor has order `0`.
      have hpow_ne : (z ^ hz.ord0) ≠ 0 := by
        simpa using pow_ne_zero hz.ord0 hz0
      have hpow_an : AnalyticAt ℂ (fun w : ℂ => w ^ hz.ord0) z :=
        (differentiable_id.pow hz.ord0).analyticAt z
      have hpow_order : analyticOrderAt (fun w : ℂ => w ^ hz.ord0) z = 0 :=
        (hpow_an.analyticOrderAt_eq_zero).2 hpow_ne
      have hG_an : AnalyticAt ℂ G z := hG_entire.analyticAt z
      have hF_order :
          analyticOrderAt F z =
            analyticOrderAt (fun w : ℂ => w ^ hz.ord0) z + analyticOrderAt G z := by
        simpa [F, Pi.mul_apply] using
          (analyticOrderAt_mul (𝕜 := ℂ) (f := fun w : ℂ => w ^ hz.ord0) (g := G) (z₀ := z) hpow_an hG_an)
      have hfz : analyticOrderAt f z = (Nat.card {n : ℕ // hz.zeros n = z} : ℕ∞) :=
        horder_f_nonzero (z := z) hz0
      have hGz : analyticOrderAt G z = (Nat.card {n : ℕ // hz.zeros n = z} : ℕ∞) :=
        horder_G_nonzero (z := z) hz0
      -- conclude
      simp [hF_order, hpow_order, hfz, hGz]

  have h_ord : ∀ z : ℂ, analyticOrderAt F z ≤ analyticOrderAt f z := by
    intro z
    simp [horder_F z]

  -- Entire quotient `H = f / F`.
  have hF_nontrivial : ∃ z : ℂ, F z ≠ 0 := by
    rcases hf_nontrivial with ⟨z1, hz1⟩
    refine ⟨z1, ?_⟩
    intro hF0
    have hFpos : 0 < analyticOrderAt F z1 :=
      (analyticOrderAt_pos_iff_zero (hF_entire.analyticAt z1)).2 hF0
    have hfpos : 0 < analyticOrderAt f z1 := lt_of_lt_of_le hFpos (h_ord z1)
    exact hz1 ((analyticOrderAt_pos_iff_zero (hf.entire.analyticAt z1)).1 hfpos)

  obtain ⟨H, hH_ent, hH_eq⟩ :=
    quotient_entire (f := f) (G := F) hf.entire hF_entire hF_nontrivial h_ord

  -- `H` is zero-free, because `F` captures all zeros of `f` with multiplicity.
  have h_prod_eq : ∀ z : ℂ, f z = H z * F z := by
    intro z
    by_cases hFz : F z = 0
    · -- then `f z = 0` by comparing analytic orders
      have hFpos : 0 < analyticOrderAt F z :=
        (analyticOrderAt_pos_iff_zero (hF_entire.analyticAt z)).2 hFz
      have hfpos : 0 < analyticOrderAt f z := lt_of_lt_of_le hFpos (h_ord z)
      have hfz : f z = 0 := (analyticOrderAt_pos_iff_zero (hf.entire.analyticAt z)).1 hfpos
      simp [hfz, hFz]
    · -- on `F z ≠ 0` we have `H z = f z / F z`
      have hHz : H z = f z / F z := hH_eq z hFz
      calc
        f z = (f z / F z) * F z := by
              simpa using (div_mul_cancel₀ (f z) hFz).symm
        _ = H z * F z := by simp [hHz]

  have hH_nz : ∀ z : ℂ, H z ≠ 0 := by
    intro z
    have hH_an : AnalyticAt ℂ H z := hH_ent.analyticAt z
    have hF_an : AnalyticAt ℂ F z := hF_entire.analyticAt z
    have hmul :
        analyticOrderAt f z = analyticOrderAt H z + analyticOrderAt F z := by
      -- rewrite `f` as `H*F`
      have hEq : f = fun w : ℂ => H w * F w := by
        funext w
        simp [h_prod_eq w]
      -- `analyticOrderAt (H*F) = ...`
      have := analyticOrderAt_mul (𝕜 := ℂ) (f := H) (g := F) (z₀ := z) hH_an hF_an
      simpa [hEq] using this
    -- since `analyticOrderAt f z = analyticOrderAt F z`, the order of `H` is zero
    have hH0 : analyticOrderAt H z = 0 := by
      have hf_eq : analyticOrderAt f z = analyticOrderAt F z := by simp [horder_F z]
      -- rearrange
      have : analyticOrderAt H z + analyticOrderAt F z = analyticOrderAt F z := by
        simpa [hmul] using hf_eq
      -- cancel `+ analyticOrderAt F z` using injectivity (valid when the right summand is not `⊤`).
      have hF_not_top : analyticOrderAt F z ≠ ⊤ := by
        -- `analyticOrderAt F z = analyticOrderAt f z` and `f` is not locally zero anywhere.
        simpa [horder_F z] using (hf_not_top z)
      have : analyticOrderAt H z + analyticOrderAt F z = (0 : ℕ∞) + analyticOrderAt F z := by
        simpa using this
      exact (ENat.add_left_injective_of_ne_top hF_not_top) this
    exact (hH_an.analyticOrderAt_eq_zero).1 hH0

  -- 4. H has finite order at most ρ (Tao's Theorem 22 sharp step)
  -- 4a. Coarse bound: H has finite order `m+1` (needed to identify H as exp of a polynomial).
  have hH_bound := hadamard_quotient_growth_bound hf hz m hσ F H hH_ent hH_nz hH_eq rfl

  -- 4b. Sharp bound: H has finite order at most any `τ` with `ρ < τ < m+1`
  -- (Cartan/minimum-modulus step; this matches Tao's use of an arbitrary ε > 0).
  set τ : ℝ := (ρ + (m + 1 : ℝ)) / 2
  have hρτ : ρ < τ := by
    dsimp [τ]
    linarith [hσ]
  have hτ_lt : τ < (m + 1 : ℝ) := by
    dsimp [τ]
    linarith [hσ]
  have hτ_nonneg : 0 ≤ τ := by
    dsimp [τ]
    linarith [hρ]
  have hH_order : EntireOfFiniteOrder τ H :=
    hadamard_quotient_entireOfFiniteOrder_lt
      (m := m) (hρ := hρ) (hmρ := hmρ) (hτ := hρτ) (hτ_lt := hτ_lt)
      (hf := hf) (hz := hz)
      (F := F) (H := H) (hH_entire := hH_ent) (hH_nonzero := hH_nz)
      (hH_eq := hH_eq) (hF_def := rfl)

  -- 5. H = exp(P) with polynomial degree control from order
  obtain ⟨P, hP_deg, hP_eq⟩ := zero_free_polynomial_growth_is_exp_poly hH_ent hH_nz
      (by
        obtain ⟨C, _, h⟩ := hH_bound
        refine ⟨C, (by positivity), h⟩)

  -- 6. Degree bound: `deg P ≤ ⌊ρ⌋` (integer-order obstruction for exp-polynomials).
  have hP_nat : P.natDegree ≤ Nat.floor ρ := by
    -- Rewrite the `EntireOfFiniteOrder` hypothesis along `H = exp(P.eval)`,
    -- and apply the integer-order obstruction at exponent `τ < m+1`.
    have hfun : H = (fun z : ℂ => Complex.exp (Polynomial.eval z P)) := by
      funext z
      simp [hP_eq z]
    have hExp : EntireOfFiniteOrder τ (fun z : ℂ => Complex.exp (Polynomial.eval z P)) := by
      simpa [hfun] using hH_order
    have hPτ : P.natDegree ≤ Nat.floor τ :=
      natDegree_le_floor_of_entireOfFiniteOrder_exp_eval (hρ := hτ_nonneg) P hExp
    -- Use `τ < m+1` to show `Nat.floor τ ≤ m`, then conclude.
    have hfloorτ_le_m : Nat.floor τ ≤ m := by
      have hlt : Nat.floor τ < m + 1 := by
        -- `Nat.floor τ < m+1 ↔ τ < (m+1 : ℝ)`
        have : Nat.floor τ < m + 1 ↔ τ < (m + 1 : ℝ) := by
          simpa using (Nat.floor_lt (n := m + 1) hτ_nonneg)
        exact this.2 (by simpa using hτ_lt)
      exact Nat.le_of_lt_succ hlt
    exact le_trans hPτ hfloorτ_le_m
  have hP_final : P.degree ≤ (Nat.floor ρ) :=
    Polynomial.degree_le_of_natDegree_le hP_nat

  refine ⟨P, hP_final, ?_⟩
  intro z
  -- Use `f = H * F`, unfold `F`, and rewrite `H` as `exp(P)`.
  calc
    f z = H z * F z := (h_prod_eq z)
    _ = Complex.exp (Polynomial.eval z P) * (z ^ hz.ord0 * G z) := by
          simp [hP_eq z, F, mul_left_comm]
    _ = Complex.exp (Polynomial.eval z P) * z ^ hz.ord0 * G z := by
          simp [mul_assoc]
    _ = Complex.exp (Polynomial.eval z P) * z ^ hz.ord0 *
          ∏' n : ℕ, weierstrassFactor m (z / hz.zeros n) := by
          rfl

end Hadamard
end ComplexAnalysis



/-! ## Part 8: Exports and Compatibility -/

/-- Re-export the main theorem for convenient access. -/
theorem Complex.hadamard_factorization_main
    {ρ : ℝ} {f : ℂ → ℂ}
    (hρ : 0 ≤ ρ)
    (hf : ComplexAnalysis.Hadamard.EntireOfFiniteOrder ρ f)
    (hz : ComplexAnalysis.Hadamard.ZeroData f) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ (Nat.floor ρ) ∧
      ∀ z : ℂ,
        f z = Complex.exp (Polynomial.eval z P) *
          z ^ hz.ord0 *
          ∏' n : ℕ, (ComplexAnalysis.Hadamard.weierstrassFactor (Nat.floor ρ) (z / hz.zeros n)) :=
  ComplexAnalysis.Hadamard.hadamard_factorization (hρ := hρ) hf hz

end
