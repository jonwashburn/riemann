import Notes.Papers.CW.Lindenberg
import Notes.Papers.CW.LindebergStep
import Mathlib.Probability.Independence.Kernel.IndepFun

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
open scoped BigOperators

namespace Probability.Lindeberg

/-!
## Blockwise Lindeberg replacement (scalar case)

This file plugs the *one-step scalar replacement bound* (`LindebergStep.lean`) into the
telescoping skeleton in `Lindenberg.lean`, yielding a full blockwise replacement estimate for
real-valued independent blocks.

Design notes (IDS / Autoformalizer):
- we avoid new “heap” structures; the only new definitions are small abbreviations/predicates;
- cross-independence is expressed via a single `iIndepFun` hypothesis on a combined family;
- the final theorem is stated at the level of expectations of a test function `phi : ℝ → ℝ`,
  matching the CW/Arguin use in Berry–Esseen style arguments.
-/

section ScalarBlocks

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

variable {n : ℕ}

/-- Joint family containing both block sequences, used to state cross-independence. -/
def jointFamily (A B : BlockSequence (E := ℝ) P n) : (Sum (Fin n) (Fin n)) → Ω → ℝ
  | Sum.inl i => A.X i
  | Sum.inr i => B.X i

omit [IsProbabilityMeasure P] in
lemma measurable_jointFamily (A B : BlockSequence (E := ℝ) P n) :
    ∀ s, Measurable (jointFamily (P := P) A B s) := by
  intro s
  cases s with
  | inl i => simpa [jointFamily] using A.meas i
  | inr i => simpa [jointFamily] using B.meas i

/-- Second moment matching for scalar blocks (the hypothesis needed for the scalar one-step lemma). -/
def secondMomentsMatch (A B : BlockSequence (E := ℝ) P n) : Prop :=
  ∀ k, (∫ ω, (A.X k ω) ^ 2 ∂P) = (∫ ω, (B.X k ω) ^ 2 ∂P)


/-!
### One increment bound (hybrid `i` to `i+1`)

We rewrite the hybrid sums as `U + X` and `U + Y`, where `U` does not depend on either
`X = A.X i` or `Y = B.X i`, and then apply `lindeberg_step_scalar`.
-/
omit [IsProbabilityMeasure P] in
lemma hybrid_sum_eq_U_add
    (A B : BlockSequence (E := ℝ) P n) (i : ℕ) (hi : i < n) :
    (∀ ω,
        (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else A.X j ω)
          =
        (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else if (j : ℕ) = i then 0 else A.X j ω)
          + A.X ⟨i, hi⟩ ω)
    ∧
    (∀ ω,
        (∑ j : Fin n, if (j : ℕ) < (i + 1) then B.X j ω else A.X j ω)
          =
        (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else if (j : ℕ) = i then 0 else A.X j ω)
          + B.X ⟨i, hi⟩ ω) := by
  classical
  -- Let `k : Fin n` be the index corresponding to `i`.
  let k : Fin n := ⟨i, hi⟩
  refine ⟨?_, ?_⟩
  · intro ω
    -- Use a pointwise decomposition of the summand that isolates the `k`-term.
    have hterm :
        (fun j : Fin n => if (j : ℕ) < i then B.X j ω else A.X j ω)
          =
        fun j : Fin n =>
          (if (j : ℕ) < i then B.X j ω else if j = k then 0 else A.X j ω)
            + (if j = k then A.X k ω else 0) := by
      funext j
      by_cases hjlt : (j : ℕ) < i
      · -- then `j ≠ k`
        have hjne : j ≠ k := by
          intro h
          have : (j : ℕ) = i := by simpa [k] using congrArg (fun t : Fin n => (t : ℕ)) h
          exact (ne_of_lt hjlt) this
        simp [hjlt, hjne]
      · have hjge : i ≤ (j : ℕ) := le_of_not_gt hjlt
        by_cases hjeq : j = k
        · subst hjeq
          simp [k]
        · -- `j ≠ k`, so the `else` part is `A.X j ω`
          simp [hjlt, hjeq]
    calc
      (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else A.X j ω)
          = ∑ j : Fin n,
              ((if (j : ℕ) < i then B.X j ω else if j = k then 0 else A.X j ω)
                + (if j = k then A.X k ω else 0)) := by
              simp [hterm]
      _ = (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else if j = k then 0 else A.X j ω)
            + (∑ j : Fin n, if j = k then A.X k ω else 0) := by
              simp [Finset.sum_add_distrib]
      _ = (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else if j = k then 0 else A.X j ω)
            + A.X k ω := by
              -- `∑ j, if j = k then c else 0 = c`
              simp
      _ = (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else if (j : ℕ) = i then 0 else A.X j ω)
            + A.X k ω := by
              -- rewrite `j = k` as `(j:ℕ)=i`
              refine congrArg (fun t => t + A.X k ω) ?_
              refine Finset.sum_congr rfl ?_
              intro j hj
              by_cases hji : (j : ℕ) = i
              · have : j = k := by
                  ext
                  simp [k, hji]
                -- At `j = k`, both conditionals evaluate to `0`.
                have hk_val : (k : ℕ) = i := by simp [k]
                have hk_not_lt : ¬ (k : ℕ) < i := by simp [hk_val]
                simp [this, hk_val]
              · have : j ≠ k := by
                  intro h
                  have : (j : ℕ) = i := by simpa [k] using congrArg (fun t : Fin n => (t : ℕ)) h
                  exact hji this
                simp [this, hji]
  · intro ω
    -- Same decomposition, but the isolated term is `B.X k ω`.
    have hterm :
        (fun j : Fin n => if (j : ℕ) < (i + 1) then B.X j ω else A.X j ω)
          =
        fun j : Fin n =>
          (if (j : ℕ) < i then B.X j ω else if j = k then 0 else A.X j ω)
            + (if j = k then B.X k ω else 0) := by
      funext j
      by_cases hjlt : (j : ℕ) < i
      · have : (j : ℕ) < i + 1 := lt_trans hjlt (Nat.lt_succ_self i)
        have hjne : j ≠ k := by
          intro h
          have : (j : ℕ) = i := by simpa [k] using congrArg (fun t : Fin n => (t : ℕ)) h
          exact (ne_of_lt hjlt) this
        simp [hjlt, this, hjne]
      · have hjge : i ≤ (j : ℕ) := le_of_not_gt hjlt
        by_cases hjeq : j = k
        · subst hjeq
          have : (i : ℕ) < i + 1 := Nat.lt_succ_self i
          simp [k, this]
        · have hij : i < (j : ℕ) := lt_of_le_of_ne hjge (by
              intro hji
              have : j = k := by
                ext
                simp [k, hji]
              exact hjeq this)
          have : ¬ (j : ℕ) < i + 1 := not_lt_of_ge (Nat.succ_le_of_lt hij)
          simp [hjlt, hjeq, this]
    calc
      (∑ j : Fin n, if (j : ℕ) < (i + 1) then B.X j ω else A.X j ω)
          = ∑ j : Fin n,
              ((if (j : ℕ) < i then B.X j ω else if j = k then 0 else A.X j ω)
                + (if j = k then B.X k ω else 0)) := by
              simp [hterm]
      _ = (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else if j = k then 0 else A.X j ω)
            + (∑ j : Fin n, if j = k then B.X k ω else 0) := by
              simp [Finset.sum_add_distrib]
      _ = (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else if j = k then 0 else A.X j ω)
            + B.X k ω := by
              simp
      _ = (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else if (j : ℕ) = i then 0 else A.X j ω)
            + B.X k ω := by
              refine congrArg (fun t => t + B.X k ω) ?_
              refine Finset.sum_congr rfl ?_
              intro j hj
              by_cases hji : (j : ℕ) = i
              · have : j = k := by
                  ext
                  simp [k, hji]
                have hk_val : (k : ℕ) = i := by simp [k]
                have hk_not_lt : ¬ (k : ℕ) < i := by simp [hk_val]
                simp [this, hk_val]
              · have : j ≠ k := by
                  intro h
                  have : (j : ℕ) = i := by simpa [k] using congrArg (fun t : Fin n => (t : ℕ)) h
                  exact hji this
                simp [this, hji]

/-!
### Full scalar blockwise replacement bound
-/

theorem lindeberg_replacement_scalar
    (A B : BlockSequence (E := ℝ) P n)
    (hAB : iIndepFun (β := fun _ : Sum (Fin n) (Fin n) => ℝ) (jointFamily (P := P) A B) P)
    (h2 : secondMomentsMatch (P := P) A B)
    {phi : ℝ → ℝ} {A0 A1 A2 M : ℝ}
    (hphi : ContDiff ℝ 3 phi)
    (hA0 : ∀ x, |phi x| ≤ A0)
    (hA1 : ∀ x, |deriv phi x| ≤ A1)
    (hA2 : ∀ x, |iteratedDeriv 2 phi x| ≤ A2)
    (hM : ∀ x, |iteratedDeriv 3 phi x| ≤ M)
    (hA3 : ∀ k, Integrable (fun ω => |A.X k ω| ^ 3) P)
    (hB3 : ∀ k, Integrable (fun ω => |B.X k ω| ^ 3) P) :
    dist
        (∫ ω, phi (total_field (E := ℝ) P A ω) ∂P)
        (∫ ω, phi (total_field (E := ℝ) P B ω) ∂P)
      ≤ ∑ i ∈ Finset.range n,
          (M / 6) * ((if h : i < n then ∫ ω, |A.X ⟨i, h⟩ ω| ^ 3 ∂P else 0)
                    + (if h : i < n then ∫ ω, |B.X ⟨i, h⟩ ω| ^ 3 ∂P else 0)) := by
  classical
  -- Use the deterministic telescoping wrapper from `Lindenberg.lean`.
  let ε : ℕ → ℝ :=
    fun i =>
      (M / 6) * ((if h : i < n then ∫ ω, |A.X ⟨i, h⟩ ω| ^ 3 ∂P else 0)
                + (if h : i < n then ∫ ω, |B.X ⟨i, h⟩ ω| ^ 3 ∂P else 0))
  refine lindeberg_replacement_of_step_bounds (E := ℝ) (P := P) A B phi (ε := ε) ?_
  intro i hi
  -- Build the index `⟨i, hi'⟩ : Fin n`.
  have hi' : i < n := Finset.mem_range.mp hi
  set k : Fin n := ⟨i, hi'⟩

  -- Define the “rest” sum `U` with the `i`-th term removed.
  let U : Ω → ℝ :=
    fun ω => ∑ j : Fin n,
      if (j : ℕ) < i then B.X j ω else if (j : ℕ) = i then 0 else A.X j ω

  -- Identify the two hybrid sums as `U + A_i` and `U + B_i`.
  have hUadd := (hybrid_sum_eq_U_add (P := P) A B i hi').1
  have hUadd' := (hybrid_sum_eq_U_add (P := P) A B i hi').2

  -- Independence of `U` from `A_i` and `B_i` comes from joint independence of all blocks.
  -- We express `U` as a sum over a finset of indices excluding `k`.
  -- (This is the only nontrivial probabilistic combinatorics; everything else is analytic.)
  have hmeasJoint := measurable_jointFamily (P := P) A B

  -- Build the index sets used in `U` (all blocks except `k` and except `inr k`).
  let sU : Finset (Sum (Fin n) (Fin n)) :=
    ((Finset.univ.filter fun j : Fin n => (j : ℕ) < i).image (fun j => (Sum.inr j : Sum (Fin n) (Fin n))))
      ∪ ((Finset.univ.filter fun j : Fin n => i < (j : ℕ)).image (fun j => (Sum.inl j : Sum (Fin n) (Fin n))))

  have hk_notin : Sum.inl k ∉ sU := by
    intro hmem
    rcases Finset.mem_union.mp hmem with hmemL | hmemR
    · -- impossible: `Sum.inl k` cannot be in an `inr`-image
      rcases Finset.mem_image.mp hmemL with ⟨j, _, h⟩
      cases h
    · -- in the `inl`-image we get `i < k`, contradicting `k.val = i`
      rcases Finset.mem_image.mp hmemR with ⟨j, hj, h⟩
      have hk_eq : (k : ℕ) = i := by simp [k]
      have hjlt : i < (j : ℕ) := (Finset.mem_filter.mp hj).2
      -- `h : Sum.inl j = Sum.inl k` implies `j = k`
      have : j = k := by
        injection h
      subst this
      -- contradiction `i < k.val = i`
      simp [hk_eq] at hjlt

  have hk_notin' : Sum.inr k ∉ sU := by
    intro hmem
    rcases Finset.mem_union.mp hmem with hmemL | hmemR
    · -- in the `inr`-image we get `k.val < i`, contradicting `k.val = i`
      rcases Finset.mem_image.mp hmemL with ⟨j, hj, h⟩
      have hk_eq : (k : ℕ) = i := by simp [k]
      have hjlt : (j : ℕ) < i := (Finset.mem_filter.mp hj).2
      have : j = k := by
        injection h
      subst this
      simp [hk_eq] at hjlt
    · -- impossible: `Sum.inr k` cannot be in an `inl`-image
      rcases Finset.mem_image.mp hmemR with ⟨j, _, h⟩
      cases h

  -- Express `U` as a finset sum over `sU`.
  have hU_as_sum : U = fun ω => ∑ s ∈ sU, jointFamily (P := P) A B s ω := by
    funext ω
    classical
    -- Abbreviate the left/right index sets on `Fin n`.
    let sL : Finset (Fin n) := Finset.univ.filter fun j : Fin n => (j : ℕ) < i
    let sR : Finset (Fin n) := Finset.univ.filter fun j : Fin n => i < (j : ℕ)
    have hdisj : Disjoint (sL.image (fun j => (Sum.inr j : Sum (Fin n) (Fin n))))
        (sR.image (fun j => (Sum.inl j : Sum (Fin n) (Fin n)))) := by
      classical
      refine Finset.disjoint_left.2 ?_
      intro x hxL hxR
      rcases Finset.mem_image.mp hxL with ⟨jL, _, rfl⟩
      rcases Finset.mem_image.mp hxR with ⟨jR, _, h⟩
      cases h
    -- Compute the RHS sum by splitting the union.
    have hsU : sU =
        (sL.image (fun j => (Sum.inr j : Sum (Fin n) (Fin n))))
          ∪ (sR.image (fun j => (Sum.inl j : Sum (Fin n) (Fin n)))) := by
      simp [sU, sL, sR]
    -- Rewrite `U` as the sum of two filtered sums.
    have hU' :
        (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else if (j : ℕ) = i then 0 else A.X j ω)
          = (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else 0)
              + (∑ j : Fin n, if i < (j : ℕ) then A.X j ω else 0) := by
      -- pointwise split into the three cases `j<i`, `j=i`, `i<j`
      have hterm :
          (fun j : Fin n =>
              if (j : ℕ) < i then B.X j ω else if (j : ℕ) = i then 0 else A.X j ω)
            = fun j : Fin n =>
              (if (j : ℕ) < i then B.X j ω else 0) + (if i < (j : ℕ) then A.X j ω else 0) := by
        funext j
        by_cases hjlt : (j : ℕ) < i
        · have : ¬ i < (j : ℕ) := not_lt_of_ge (le_of_lt hjlt)
          simp [hjlt, this]
        · have hjge : i ≤ (j : ℕ) := le_of_not_gt hjlt
          by_cases hji : (j : ℕ) = i
          · subst hji
            simp
          · have hij : i < (j : ℕ) := lt_of_le_of_ne hjge (Ne.symm hji)
            have : ¬ (j : ℕ) < i := hjlt
            simp [this, hji, hij]
      -- sum and use `Finset.sum_add_distrib`
      calc
        (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else if (j : ℕ) = i then 0 else A.X j ω)
            = ∑ j : Fin n,
                ((if (j : ℕ) < i then B.X j ω else 0) + (if i < (j : ℕ) then A.X j ω else 0)) := by
                  simp [hterm]
        _ = (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else 0)
              + (∑ j : Fin n, if i < (j : ℕ) then A.X j ω else 0) := by
                  simp [Finset.sum_add_distrib]
    -- Now compute the sum over `sU` using `sum_union` and `sum_image` (injective constructors).
    have hsumU :
        (∑ s ∈ sU, jointFamily (P := P) A B s ω)
          = (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else 0)
              + (∑ j : Fin n, if i < (j : ℕ) then A.X j ω else 0) := by
      -- rewrite as sum over the union
      have : (∑ s ∈ sU, jointFamily (P := P) A B s ω)
            = (∑ s ∈ (sL.image (fun j => (Sum.inr j : Sum (Fin n) (Fin n)))), jointFamily (P := P) A B s ω)
              + (∑ s ∈ (sR.image (fun j => (Sum.inl j : Sum (Fin n) (Fin n)))), jointFamily (P := P) A B s ω) := by
        -- `∑ s ∈ sU` is `Finset.sum` over `sU`
        simp [hsU, Finset.sum_union, hdisj, add_comm]
      -- Evaluate each image sum back on `Fin n`.
      have hL :
          (∑ s ∈ (sL.image (fun j => (Sum.inr j : Sum (Fin n) (Fin n)))),
              jointFamily (P := P) A B s ω)
            = ∑ j : Fin n, if (j : ℕ) < i then B.X j ω else 0 := by
        -- `sum_image` over an injective map (`Sum.inr`).
        have hinj : Function.Injective (fun j : Fin n => (Sum.inr j : Sum (Fin n) (Fin n))) :=
          fun x y h => by cases h; rfl
        -- rewrite as sum over `sL` and then `sum_filter`.
        have : (∑ s ∈ (sL.image (fun j => (Sum.inr j : Sum (Fin n) (Fin n)))),
                  jointFamily (P := P) A B s ω)
              = ∑ j ∈ sL, jointFamily (P := P) A B (Sum.inr j) ω := by
            simp
        -- convert `sL` into an `ite` sum over `Fin n`
        simp [sL, jointFamily, Finset.sum_filter]
      have hR :
          (∑ s ∈ (sR.image (fun j => (Sum.inl j : Sum (Fin n) (Fin n)))),
              jointFamily (P := P) A B s ω)
            = ∑ j : Fin n, if i < (j : ℕ) then A.X j ω else 0 := by
        have hinj : Function.Injective (fun j : Fin n => (Sum.inl j : Sum (Fin n) (Fin n))) :=
          fun x y h => by cases h; rfl
        have : (∑ s ∈ (sR.image (fun j => (Sum.inl j : Sum (Fin n) (Fin n)))),
                  jointFamily (P := P) A B s ω)
              = ∑ j ∈ sR, jointFamily (P := P) A B (Sum.inl j) ω := by
            simp
        simp [sR, jointFamily, Finset.sum_filter]
      -- put pieces together
      nlinarith [this, hL, hR]
    -- Finally, `U ω` is the LHS, and the RHS sum equals it by `hU'`.
    -- So `U ω = ∑ s ∈ sU, jointFamily s ω`.
    have : U ω = (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else if (j : ℕ) = i then 0 else A.X j ω) := rfl
    -- combine the two rewrites
    simp [this, hU', hsumU, U]

  have hUX : U ⟂ᵢ[P] (fun ω => A.X k ω) := by
    -- independence between sum over `sU` and `A.X k` (which is `jointFamily (inl k)`).
    have hI :
        IndepFun (fun ω => ∑ s ∈ sU, jointFamily (P := P) A B s ω)
          (jointFamily (P := P) A B (Sum.inl k)) P := by
      -- `iIndepFun` + measurability + `k ∉ sU`
      have hI' :
          (∑ s ∈ sU, jointFamily (P := P) A B s) ⟂ᵢ[P]
            jointFamily (P := P) A B (Sum.inl k) :=
        iIndepFun.indepFun_finset_sum_of_notMem (μ := P) (f := jointFamily (P := P) A B)
          hAB hmeasJoint (s := sU) (i := Sum.inl k) hk_notin
      -- rewrite the sum of functions pointwise
      refine IndepFun.congr hI' ?_ (by rfl)
      -- `∀ ω`, the pointwise value of the sum of functions is the sum of pointwise values
      refine ae_of_all _ (fun ω => ?_)
      simp [Finset.sum_apply]
    -- rewrite via `hU_as_sum`
    simpa [hU_as_sum, jointFamily] using hI

  have hUY : U ⟂ᵢ[P] (fun ω => B.X k ω) := by
    have hI :
        IndepFun (fun ω => ∑ s ∈ sU, jointFamily (P := P) A B s ω)
          (jointFamily (P := P) A B (Sum.inr k)) P := by
      have hI' :
          (∑ s ∈ sU, jointFamily (P := P) A B s) ⟂ᵢ[P]
            jointFamily (P := P) A B (Sum.inr k) :=
        iIndepFun.indepFun_finset_sum_of_notMem (μ := P) (f := jointFamily (P := P) A B)
          hAB hmeasJoint (s := sU) (i := Sum.inr k) hk_notin'
      refine IndepFun.congr hI' ?_ (by rfl)
      refine ae_of_all _ (fun ω => ?_)
      simp [Finset.sum_apply]
    simpa [hU_as_sum, jointFamily] using hI

  -- Apply the one-step scalar lemma with moment matching.
  have hEX : (∫ ω, A.X k ω ∂P) = (∫ ω, B.X k ω ∂P) := by
    -- both are 0 by centering
    simpa [mean] using (by
      simpa [k] using (A.centered k).trans (B.centered k).symm)
  have hEX2 : (∫ ω, (A.X k ω) ^ 2 ∂P) = (∫ ω, (B.X k ω) ^ 2 ∂P) := h2 k

  -- Convert the increment distance to the absolute value and bound it.
  -- Use the identities `hUadd` and `hUadd'` to match the shape expected by `lindeberg_step_scalar`.
  have hstep :=
    Probability.Lindeberg.lindeberg_step_scalar (P := P)
      (U := U) (X := fun ω => A.X k ω) (Y := fun ω => B.X k ω)
      hUX hUY
      (hU := by
        -- measurability of `U`: finite sum of measurable functions
        classical
        -- rewrite the `Fintype` sum as a `Finset` sum and apply `Finset.measurable_sum`.
        let f : Fin n → Ω → ℝ := fun j ω =>
          if (j : ℕ) < i then B.X j ω else if (j : ℕ) = i then 0 else A.X j ω
        have hf : ∀ j ∈ (Finset.univ : Finset (Fin n)), Measurable (f j) := by
          intro j hj
          by_cases hji : (j : ℕ) < i
          · simpa [f, hji] using B.meas j
          · by_cases hjeq : (j : ℕ) = i
            · simp [f, hjeq]
            · simpa [f, hji, hjeq] using A.meas j
        -- `U` is definitionally the corresponding sum.
        simpa [U, f] using (Finset.measurable_sum (s := (Finset.univ : Finset (Fin n))) hf))
      (hX := A.meas k) (hY := B.meas k)
      (phi := phi) (A0 := A0) (A1 := A1) (A2 := A2) (M := M)
      hphi hA0 hA1 hA2 hM
      (hX3 := hA3 k) (hY3 := hB3 k)
      hEX hEX2

  -- Finish by rewriting the two hybrid integrals to `phi (U + A_i)` and `phi (U + B_i)`.
  -- The `dist` on `ℝ` is `|x-y|`.
  have hεi :
      ε i = (M / 6) * ((∫ ω, |A.X k ω| ^ 3 ∂P) + (∫ ω, |B.X k ω| ^ 3 ∂P)) := by
    -- on `i < n`, the `if` branches in `ε` simplify.
    simp [ε, hi', k]
  -- rewrite the target bound using `hUadd`, `hUadd'`, and then discharge it by `hstep`.
  simpa [Real.dist_eq, hUadd, hUadd', U, k, hεi] using hstep

end ScalarBlocks

end Probability.Lindeberg

namespace Probability.Lindeberg

/-!
## Blockwise Lindeberg replacement (scalar) with moment-mismatch terms

The CW/Arguin method is normally used in a regime where the blocks do **not** match second moments
exactly (e.g. when dropping lower-order terms in the covariance).  The one-step estimate
`lindeberg_step_scalar_bound` already supports this; this theorem lifts it to the full blockwise
telescoping bound.

This is the “most general” form of the scalar blockwise replacement bound; the exact-matching
theorem `lindeberg_replacement_scalar` is recovered by specializing the mismatch terms to `0`.
-/

section ScalarBlocksMismatch

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]
variable {n : ℕ}

open scoped BigOperators

theorem lindeberg_replacement_scalar_mismatch
    (A B : BlockSequence (E := ℝ) P n)
    (hAB : iIndepFun (β := fun _ : Sum (Fin n) (Fin n) => ℝ) (jointFamily (P := P) A B) P)
    {phi : ℝ → ℝ} {A0 A1 A2 M : ℝ}
    (hphi : ContDiff ℝ 3 phi)
    (hA0 : ∀ x, |phi x| ≤ A0)
    (hA1 : ∀ x, |deriv phi x| ≤ A1)
    (hA2 : ∀ x, |iteratedDeriv 2 phi x| ≤ A2)
    (hM : ∀ x, |iteratedDeriv 3 phi x| ≤ M)
    (hA3 : ∀ k, Integrable (fun ω => |A.X k ω| ^ 3) P)
    (hB3 : ∀ k, Integrable (fun ω => |B.X k ω| ^ 3) P) :
    dist
        (∫ ω, phi (total_field (E := ℝ) P A ω) ∂P)
        (∫ ω, phi (total_field (E := ℝ) P B ω) ∂P)
      ≤ ∑ i ∈ Finset.range n,
          (A1 * |(if h : i < n then (∫ ω, A.X ⟨i, h⟩ ω ∂P) else 0)
                    - (if h : i < n then (∫ ω, B.X ⟨i, h⟩ ω ∂P) else 0)|
            + ((1 + 1 : ℝ)⁻¹) * A2 *
                |(if h : i < n then (∫ ω, (A.X ⟨i, h⟩ ω) ^ 2 ∂P) else 0)
                    - (if h : i < n then (∫ ω, (B.X ⟨i, h⟩ ω) ^ 2 ∂P) else 0)|
            + (M / 6) *
                ((if h : i < n then ∫ ω, |A.X ⟨i, h⟩ ω| ^ 3 ∂P else 0)
                  + (if h : i < n then ∫ ω, |B.X ⟨i, h⟩ ω| ^ 3 ∂P else 0))) := by
  classical
  -- Use the deterministic telescoping wrapper from `Lindenberg.lean`.
  let ε : ℕ → ℝ :=
    fun i =>
      (A1 * |(if h : i < n then (∫ ω, A.X ⟨i, h⟩ ω ∂P) else 0)
                - (if h : i < n then (∫ ω, B.X ⟨i, h⟩ ω ∂P) else 0)|)
        + ((1 + 1 : ℝ)⁻¹) * A2 *
            |(if h : i < n then (∫ ω, (A.X ⟨i, h⟩ ω) ^ 2 ∂P) else 0)
                - (if h : i < n then (∫ ω, (B.X ⟨i, h⟩ ω) ^ 2 ∂P) else 0)|
        + (M / 6) *
            ((if h : i < n then ∫ ω, |A.X ⟨i, h⟩ ω| ^ 3 ∂P else 0)
              + (if h : i < n then ∫ ω, |B.X ⟨i, h⟩ ω| ^ 3 ∂P else 0))

  refine lindeberg_replacement_of_step_bounds (E := ℝ) (P := P) A B phi (ε := ε) ?_
  intro i hi
  have hi' : i < n := Finset.mem_range.mp hi
  set k : Fin n := ⟨i, hi'⟩

  -- Define the “rest” sum `U` with the `i`-th term removed.
  let U : Ω → ℝ :=
    fun ω => ∑ j : Fin n,
      if (j : ℕ) < i then B.X j ω else if (j : ℕ) = i then 0 else A.X j ω

  -- Identify the two hybrid sums as `U + A_i` and `U + B_i`.
  have hUadd := (hybrid_sum_eq_U_add (P := P) A B i hi').1
  have hUadd' := (hybrid_sum_eq_U_add (P := P) A B i hi').2

  have hmeasJoint := measurable_jointFamily (P := P) A B

  -- Build the index sets used in `U` (all blocks except `k` and except `inr k`).
  let sU : Finset (Sum (Fin n) (Fin n)) :=
    ((Finset.univ.filter fun j : Fin n => (j : ℕ) < i).image (fun j => (Sum.inr j : Sum (Fin n) (Fin n))))
      ∪ ((Finset.univ.filter fun j : Fin n => i < (j : ℕ)).image (fun j => (Sum.inl j : Sum (Fin n) (Fin n))))

  have hk_notin : Sum.inl k ∉ sU := by
    intro hmem
    rcases Finset.mem_union.mp hmem with hmemL | hmemR
    · rcases Finset.mem_image.mp hmemL with ⟨j, _, h⟩
      cases h
    · rcases Finset.mem_image.mp hmemR with ⟨j, hj, h⟩
      have hk_eq : (k : ℕ) = i := by simp [k]
      have hjlt : i < (j : ℕ) := (Finset.mem_filter.mp hj).2
      have : j = k := by
        injection h
      subst this
      simp [hk_eq] at hjlt

  have hk_notin' : Sum.inr k ∉ sU := by
    intro hmem
    rcases Finset.mem_union.mp hmem with hmemL | hmemR
    · rcases Finset.mem_image.mp hmemL with ⟨j, hj, h⟩
      have hk_eq : (k : ℕ) = i := by simp [k]
      have hjlt : (j : ℕ) < i := (Finset.mem_filter.mp hj).2
      have : j = k := by
        injection h
      subst this
      simp [hk_eq] at hjlt
    · rcases Finset.mem_image.mp hmemR with ⟨j, _, h⟩
      cases h

  -- Express `U` as a finset sum over `sU`.
  have hU_as_sum : U = fun ω => ∑ s ∈ sU, jointFamily (P := P) A B s ω := by
    funext ω
    classical
    -- Abbreviate the left/right index sets on `Fin n`.
    let sL : Finset (Fin n) := Finset.univ.filter fun j : Fin n => (j : ℕ) < i
    let sR : Finset (Fin n) := Finset.univ.filter fun j : Fin n => i < (j : ℕ)
    have hdisj : Disjoint (sL.image (fun j => (Sum.inr j : Sum (Fin n) (Fin n))))
        (sR.image (fun j => (Sum.inl j : Sum (Fin n) (Fin n)))) := by
      classical
      refine Finset.disjoint_left.2 ?_
      intro x hxL hxR
      rcases Finset.mem_image.mp hxL with ⟨jL, _, rfl⟩
      rcases Finset.mem_image.mp hxR with ⟨jR, _, h⟩
      cases h
    -- Compute the RHS sum by splitting the union.
    have hsU : sU =
        (sL.image (fun j => (Sum.inr j : Sum (Fin n) (Fin n))))
          ∪ (sR.image (fun j => (Sum.inl j : Sum (Fin n) (Fin n)))) := by
      simp [sU, sL, sR]
    -- Rewrite `U` as the sum of two filtered sums.
    have hU' :
        (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else if (j : ℕ) = i then 0 else A.X j ω)
          = (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else 0)
              + (∑ j : Fin n, if i < (j : ℕ) then A.X j ω else 0) := by
      -- pointwise split into the three cases `j<i`, `j=i`, `i<j`
      have hterm :
          (fun j : Fin n =>
              if (j : ℕ) < i then B.X j ω else if (j : ℕ) = i then 0 else A.X j ω)
            = fun j : Fin n =>
              (if (j : ℕ) < i then B.X j ω else 0) + (if i < (j : ℕ) then A.X j ω else 0) := by
        funext j
        by_cases hjlt : (j : ℕ) < i
        · have : ¬ i < (j : ℕ) := not_lt_of_ge (le_of_lt hjlt)
          simp [hjlt, this]
        · have hjge : i ≤ (j : ℕ) := le_of_not_gt hjlt
          by_cases hji : (j : ℕ) = i
          · subst hji
            simp
          · have hij : i < (j : ℕ) := lt_of_le_of_ne hjge (Ne.symm hji)
            have : ¬ (j : ℕ) < i := hjlt
            simp [this, hji, hij]
      -- sum and use `Finset.sum_add_distrib`
      calc
        (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else if (j : ℕ) = i then 0 else A.X j ω)
            = ∑ j : Fin n,
                ((if (j : ℕ) < i then B.X j ω else 0) + (if i < (j : ℕ) then A.X j ω else 0)) := by
                  simp [hterm]
        _ = (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else 0)
              + (∑ j : Fin n, if i < (j : ℕ) then A.X j ω else 0) := by
                  simp [Finset.sum_add_distrib]
    -- Now compute the sum over `sU` using `sum_union` and `sum_image` (injective constructors).
    have hsumU :
        (∑ s ∈ sU, jointFamily (P := P) A B s ω)
          = (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else 0)
              + (∑ j : Fin n, if i < (j : ℕ) then A.X j ω else 0) := by
      -- rewrite as sum over the union
      have : (∑ s ∈ sU, jointFamily (P := P) A B s ω)
            = (∑ s ∈ (sL.image (fun j => (Sum.inr j : Sum (Fin n) (Fin n)))), jointFamily (P := P) A B s ω)
              + (∑ s ∈ (sR.image (fun j => (Sum.inl j : Sum (Fin n) (Fin n)))), jointFamily (P := P) A B s ω) := by
        simp [hsU, Finset.sum_union, hdisj, add_comm]
      -- Evaluate each image sum back on `Fin n`.
      have hL :
          (∑ s ∈ (sL.image (fun j => (Sum.inr j : Sum (Fin n) (Fin n)))),
              jointFamily (P := P) A B s ω)
            = ∑ j : Fin n, if (j : ℕ) < i then B.X j ω else 0 := by
        have hinj : Function.Injective (fun j : Fin n => (Sum.inr j : Sum (Fin n) (Fin n))) :=
          fun x y h => by cases h; rfl
        have : (∑ s ∈ (sL.image (fun j => (Sum.inr j : Sum (Fin n) (Fin n)))),
                  jointFamily (P := P) A B s ω)
              = ∑ j ∈ sL, jointFamily (P := P) A B (Sum.inr j) ω := by
            simp
        simp [sL, jointFamily, Finset.sum_filter]
      have hR :
          (∑ s ∈ (sR.image (fun j => (Sum.inl j : Sum (Fin n) (Fin n)))),
              jointFamily (P := P) A B s ω)
            = ∑ j : Fin n, if i < (j : ℕ) then A.X j ω else 0 := by
        have hinj : Function.Injective (fun j : Fin n => (Sum.inl j : Sum (Fin n) (Fin n))) :=
          fun x y h => by cases h; rfl
        have : (∑ s ∈ (sR.image (fun j => (Sum.inl j : Sum (Fin n) (Fin n)))),
                  jointFamily (P := P) A B s ω)
              = ∑ j ∈ sR, jointFamily (P := P) A B (Sum.inl j) ω := by
            simp
        simp [sR, jointFamily, Finset.sum_filter]
      nlinarith [this, hL, hR]
    -- Finally, `U ω` is the LHS, and the RHS sum equals it by `hU'`.
    have : U ω = (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else if (j : ℕ) = i then 0 else A.X j ω) := rfl
    simp [this, hU', hsumU, U]

  -- independence of `U` from `A_i` and `B_i`
  have hUX : U ⟂ᵢ[P] (fun ω => A.X k ω) := by
    have hI' :
        (∑ s ∈ sU, jointFamily (P := P) A B s) ⟂ᵢ[P] jointFamily (P := P) A B (Sum.inl k) :=
      iIndepFun.indepFun_finset_sum_of_notMem (μ := P) (f := jointFamily (P := P) A B)
        hAB hmeasJoint (s := sU) (i := Sum.inl k) hk_notin
    have hI :
        IndepFun (fun ω => ∑ s ∈ sU, jointFamily (P := P) A B s ω)
          (jointFamily (P := P) A B (Sum.inl k)) P := by
      refine IndepFun.congr hI' ?_ (by rfl)
      refine ae_of_all _ (fun ω => ?_)
      simp [Finset.sum_apply]
    simpa [hU_as_sum, jointFamily] using hI

  have hUY : U ⟂ᵢ[P] (fun ω => B.X k ω) := by
    have hI' :
        (∑ s ∈ sU, jointFamily (P := P) A B s) ⟂ᵢ[P] jointFamily (P := P) A B (Sum.inr k) :=
      iIndepFun.indepFun_finset_sum_of_notMem (μ := P) (f := jointFamily (P := P) A B)
        hAB hmeasJoint (s := sU) (i := Sum.inr k) hk_notin'
    have hI :
        IndepFun (fun ω => ∑ s ∈ sU, jointFamily (P := P) A B s ω)
          (jointFamily (P := P) A B (Sum.inr k)) P := by
      refine IndepFun.congr hI' ?_ (by rfl)
      refine ae_of_all _ (fun ω => ?_)
      simp [Finset.sum_apply]
    simpa [hU_as_sum, jointFamily] using hI

  -- Apply the one-step mismatch bound
  have hstep :=
    Probability.Lindeberg.lindeberg_step_scalar_bound (P := P)
      (U := U) (X := fun ω => A.X k ω) (Y := fun ω => B.X k ω)
      hUX hUY
      (hU := by
        classical
        let f : Fin n → Ω → ℝ := fun j ω =>
          if (j : ℕ) < i then B.X j ω else if (j : ℕ) = i then 0 else A.X j ω
        have hf : ∀ j ∈ (Finset.univ : Finset (Fin n)), Measurable (f j) := by
          intro j hj
          by_cases hji : (j : ℕ) < i
          · simpa [f, hji] using B.meas j
          · by_cases hjeq : (j : ℕ) = i
            · simp [f, hjeq]
            · simpa [f, hji, hjeq] using A.meas j
        simpa [U, f] using (Finset.measurable_sum (s := (Finset.univ : Finset (Fin n))) hf))
      (hX := A.meas k) (hY := B.meas k)
      (phi := phi) (A0 := A0) (A1 := A1) (A2 := A2) (M := M)
      hphi hA0 hA1 hA2 hM
      (hX3 := hA3 k) (hY3 := hB3 k)

  -- identify `ε i` on `i < n` and conclude
  have hεi : ε i =
      A1 * |(∫ ω, A.X k ω ∂P) - (∫ ω, B.X k ω ∂P)|
        + ((1 + 1 : ℝ)⁻¹) * A2 * |(∫ ω, (A.X k ω) ^ 2 ∂P) - (∫ ω, (B.X k ω) ^ 2 ∂P)|
        + (M / 6) * ((∫ ω, |A.X k ω| ^ 3 ∂P) + (∫ ω, |B.X k ω| ^ 3 ∂P)) := by
    simp [ε, hi', k]

  -- `dist` on `ℝ` is `|·|`
  -- rewrite the two hybrid integrals to `phi (U + A_i)` and `phi (U + B_i)`
  have hI0 :
      (∫ ω, phi (∑ j : Fin n, if (j : ℕ) < i then B.X j ω else A.X j ω) ∂P)
        = ∫ ω, phi (U ω + A.X k ω) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards with ω
    simp [hUadd ω, k, U]

  have hI1 :
      (∫ ω, phi (∑ j : Fin n, if (j : ℕ) < (i + 1) then B.X j ω else A.X j ω) ∂P)
        = ∫ ω, phi (U ω + B.X k ω) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards with ω
    simp [hUadd' ω, k, U]

  -- finish
  -- `lindeberg_step_scalar_bound` controls the absolute difference
  have := hstep
  -- rewrite LHS in terms of the hybrid sums
  -- and use the definition of `ε`.
  simpa [Real.dist_eq, hI0, hI1, hεi, ε, hi', k] using this

end ScalarBlocksMismatch

end Probability.Lindeberg
