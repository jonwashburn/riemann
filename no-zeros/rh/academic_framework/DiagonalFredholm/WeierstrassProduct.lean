import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! Modern DF‑WP helpers:

  - Use current mathlib: `HasSum.cexp`, `HasProd`/`Multipliable`.
  - Replace any use of non-existent `Complex.norm_log_one_sub_le` with
    `Complex.norm_log_one_add_le` specialized at `z ↦ -z`.
  - Keep the interface light; no axioms.
-/

namespace RH.AcademicFramework.DiagonalFredholm

noncomputable section

open Complex
open scoped BigOperators
/-- Power series identity for the cubic tail of `log(1 - z)`.
For `‖z‖ < 1` we have
  `∑' n, - z^(n+3) / (n+3) = Complex.log (1 - z) + z + z^2 / 2`.
This is obtained from `Complex.hasSum_log_one_add` at `-z` and splitting
off the first two terms. -/
lemma tsum_log_one_sub_cubic_tail {z : ℂ} (hz : ‖z‖ < (1 : ℝ)) :
    (∑' n : ℕ, - z ^ (n + 3) / ((n + 3 : ℕ) : ℂ))
      = Complex.log (1 - z) + z + z ^ 2 / 2 := by
  have hsum : HasSum (fun n : ℕ => - (z ^ (n + 1)) / ((n + 1 : ℕ) : ℂ))
      (Complex.log (1 - z)) := by
    have hlt : ‖-z‖ < (1 : ℝ) := by simpa [norm_neg] using hz
    -- `log(1 - z) = ∑ (-1)^(n+1) (-z)^(n+1)/(n+1) = -∑ z^(n+1)/(n+1)`
    simpa [sub_eq_add_neg, pow_succ, Nat.cast_add, Nat.cast_one, div_eq_mul_inv,
      one_mul, mul_comm, mul_left_comm, mul_assoc]
      using Complex.hasSum_log_one_add (z := -z) hlt
  -- Split off n = 0 and n = 1
  have hsplit := hsum.tsum_eq_add_tsum_nat_add 2
  -- Evaluate the first two head terms explicitly
  have h0 : - (z ^ (0 + 1)) / ((0 + 1 : ℕ) : ℂ) = -z := by simp
  have h1 : - (z ^ (1 + 1)) / ((1 + 1 : ℕ) : ℂ) = -z ^ 2 / 2 := by simp
  -- Reindex the tail starting at 2 by `m = n + 2`
  have htail : (∑' n : ℕ, - (z ^ (n + (2 + 1))) / ((n + (2 + 1) : ℕ) : ℂ))
      = (∑' n : ℕ, - z ^ (n + 3) / ((n + 3 : ℕ) : ℂ)) := by
    simpa [add_assoc]
  -- Put everything together
  -- `tsum f = f 0 + f 1 + tsum (fun n => f (n+2))` with `f n = - z^(n+1)/(n+1)`
  have : (∑' n : ℕ, - (z ^ (n + 1)) / ((n + 1 : ℕ) : ℂ))
      = (-z) + (-z ^ 2 / 2) + (∑' n : ℕ, - z ^ (n + 3) / ((n + 3 : ℕ) : ℂ)) := by
    simpa [h0, h1, htail, two_mul, add_comm, add_left_comm, add_assoc]
      using hsplit
  -- Rearrange to the desired identity
  have := congrArg (fun w => w + (z + z ^ 2 / 2)) this
  -- Left-hand side becomes `tsum + z + z^2/2`, right-hand side simplifies to the tail
  -- and the log value
  simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
    using this.trans (by simp [add_comm, add_left_comm, add_assoc])

/-- Euler factor as an exponential of the cubic tail `tsum` for `‖z‖ < 1`.
`(1 - z) * exp(z + z^2/2) = exp(∑' n, - z^(n+3)/(n+3))`. -/
lemma eulerFactor_exp_tsum_cubic_tail {z : ℂ} (hz : ‖z‖ < (1 : ℝ)) :
    (1 - z) * Complex.exp (z + z ^ 2 / 2)
      = Complex.exp (∑' n : ℕ, - z ^ (n + 3) / ((n + 3 : ℕ) : ℂ)) := by
  have htsum := tsum_log_one_sub_cubic_tail (z := z) hz
  -- Exponentiate: exp(log(1 - z) + z + z^2/2) = exp(log(1 - z)) * exp(z + z^2/2)
  have hne : 1 - z ≠ 0 := by
    intro h
    have : z = 1 := by
      have : z = 1 := by
        -- From 1 - z = 0 ⇒ z = 1; contradicts ‖z‖ < 1
        simpa [sub_eq, add_comm] using congrArg id h
      exact this
    have : (1 : ℝ) ≤ ‖z‖ := by simpa [this] using norm_one.le
    exact (not_le.mpr hz).elim this
  calc
    (1 - z) * Complex.exp (z + z ^ 2 / 2)
        = Complex.exp (Complex.log (1 - z)) * Complex.exp (z + z ^ 2 / 2) := by
          simpa [Complex.exp_log hne]
    _ = Complex.exp (Complex.log (1 - z) + (z + z ^ 2 / 2)) := by
          simpa [Complex.exp_add]
    _ = Complex.exp (∑' n : ℕ, - z ^ (n + 3) / ((n + 3 : ℕ) : ℂ)) := by
          simpa [add_comm, add_left_comm, add_assoc] using congrArg Complex.exp htsum.symm

/-- Log bound for `log(1 - z)` via the modern `log(1 + z)` inequality. -/
lemma norm_log_one_sub_le_of_lt_one {z : ℂ} (hz : ‖z‖ < (1 : ℝ)) :
    ‖Complex.log (1 - z)‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 + ‖z‖ := by
  -- Reduce to the `log(1 + w)` bound with `w = -z`.
  simpa [sub_eq_add_neg, norm_neg] using
    (Complex.norm_log_one_add_le (z := -z) (by simpa [norm_neg] using hz))

/-- A convenient half-radius variant of the previous bound. -/
lemma norm_log_one_sub_le_half {z : ℂ} (hz : ‖z‖ < (1 : ℝ) / 2) :
    ‖Complex.log (1 - z)‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 + ‖z‖ := by
  have h : (1 : ℝ) / 2 < 1 := by
    simpa using (one_half_lt_one : (1 : ℝ) / 2 < 1)
  exact norm_log_one_sub_le_of_lt_one (lt_trans hz h)

/-- Uniform quadratic tail bound for the Weierstrass log remainder on ‖z‖ ≤ r < 1.
For any `r ∈ (0,1)`, there is a constant `C(r) = (1 - r)⁻¹` with
`‖log(1 - z) + z‖ ≤ C(r) ‖z‖^2` whenever ‖z‖ ≤ r. -/
lemma log_one_sub_plus_z_quadratic_tail
    {z : ℂ} {r : ℝ} (_hr0 : 0 < r) (hr1 : r < 1) (hzr : ‖z‖ ≤ r) :
    ‖Complex.log (1 - z) + z‖ ≤ (1 - r)⁻¹ * ‖z‖^2 := by
  -- Base bound from `log(1 + w) - w` with `w = -z`
  have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hzr hr1
  have hbase : ‖Complex.log (1 - z) + z‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := by
    simpa [sub_eq_add_neg, norm_neg] using
      Complex.norm_log_one_add_sub_self_le (z := -z) (by simpa [norm_neg] using hz1)
  -- Compare denominators using `‖z‖ ≤ r < 1`
  have hmono : (1 - ‖z‖)⁻¹ ≤ (1 - r)⁻¹ := by
    have hpos₁ : 0 < 1 - r := sub_pos.mpr hr1
    have hle : 1 - r ≤ 1 - ‖z‖ := by linarith
    exact inv_le_inv_of_le hpos₁ hle
  have hnonneg : 0 ≤ (1 - ‖z‖)⁻¹ := by
    have : 0 < 1 - ‖z‖ := sub_pos.mpr hz1
    exact inv_nonneg.mpr (le_of_lt this)
  have hhalf_le : (1 - ‖z‖)⁻¹ / 2 ≤ (1 - ‖z‖)⁻¹ := by
    simpa using (half_le_self hnonneg)
  have hconst : (1 - ‖z‖)⁻¹ / 2 ≤ (1 - r)⁻¹ := le_trans hhalf_le hmono
  have hznn : 0 ≤ ‖z‖ ^ 2 := by exact sq_nonneg _
  have hscale : ‖z‖ ^ 2 * ((1 - ‖z‖)⁻¹ / 2) ≤ ‖z‖ ^ 2 * (1 - r)⁻¹ :=
    mul_le_mul_of_nonneg_left hconst hznn
  have hbase' : ‖Complex.log (1 - z) + z‖ ≤ ‖z‖ ^ 2 * ((1 - ‖z‖)⁻¹ / 2) := by
    -- regroup the division to match `hscale`'s left-hand side
    simpa [mul_div_assoc] using hbase
  have hchain : ‖Complex.log (1 - z) + z‖ ≤ ‖z‖ ^ 2 * (1 - r)⁻¹ :=
    le_trans hbase' hscale
  simpa [mul_comm] using hchain

/-- Exponential turns sums into products (modern route).
If `a` is summable, then `∏ exp (a i) = exp (∑ a i)` and the product is
`Multipliable`. -/
lemma tprod_exp_of_summable {ι : Type*} [Countable ι]
    (a : ι → ℂ) (hsum : Summable a) :
    Multipliable (fun i => Complex.exp (a i)) ∧
      (∏' i, Complex.exp (a i)) = Complex.exp (∑' i, a i) := by
  -- `HasSum.cexp` yields a `HasProd` witness, from which both facts follow.
  have hsum' : HasSum a (∑' i, a i) := hsum.hasSum
  have hprod : HasProd (fun i => Complex.exp (a i)) (Complex.exp (∑' i, a i)) := by
    simpa [Function.comp] using hsum'.cexp
  exact ⟨hprod.multipliable, hprod.tprod_eq⟩

/-- Weierstrass-type bridge: from a summable log to a product identity.
If `f i ≠ 0` and `∑ log (f i)` converges, then `exp (∑ log (f i)) = ∏ f i`.
Derived from `HasSum.cexp` and `Complex.exp_log`. -/
lemma exp_tsum_eq_tprod {ι : Type*} [Countable ι]
    (f : ι → ℂ) (hne : ∀ i, f i ≠ 0)
    (hlog : Summable (fun i => Complex.log (f i))) :
    Complex.exp (∑' i, Complex.log (f i)) = ∏' i, f i := by
  have hprod : HasProd (fun i => Complex.exp (Complex.log (f i)))
      (Complex.exp (∑' i, Complex.log (f i))) := (hlog.hasSum).cexp
  calc
    Complex.exp (∑' i, Complex.log (f i))
        = ∏' i, Complex.exp (Complex.log (f i)) := by
          simpa using (hprod.tprod_eq.symm)
    _ = ∏' i, f i := by
      simp [Complex.exp_log (hne _)]

/-- Cubic tail bound for the log Weierstrass remainder on `‖z‖ < 1`:
`‖log(1 - z) + z + z^2/2‖ ≤ ‖z‖^3 / (1 - ‖z‖)`.

This follows from the power series for `log(1 - z)` and a comparison with the
geometric series. -/
lemma log_one_sub_plus_z_plus_sq_cubic_tail
    {z : ℂ} (hz : ‖z‖ < (1 : ℝ)) :
    ‖Complex.log (1 - z) + z + z^2 / 2‖ ≤ ‖z‖ ^ 3 / (1 - ‖z‖) := by
  -- Use the series: log(1 - z) = -∑_{n≥1} z^n/n on ‖z‖ < 1
  have hseries : HasSum (fun n : ℕ => - (z ^ (n + 1)) / (n + 1)) (Complex.log (1 - z)) := by
    -- specialize the standard `log(1 + w)` series at `w = -z`
    simpa [one_add, add_comm, add_left_comm, sub_eq_add_neg, pow_succ, mul_comm, mul_left_comm,
      mul_assoc, div_eq_mul_inv] using
      (Complex.hasSum_log_one_add (w := -z) (by simpa [norm_neg] using hz))
  -- Split off the first two terms to isolate the cubic tail
  have hsplit :
      Complex.log (1 - z)
        = -z - z ^ 2 / 2 - ∑' n : {m // 2 ≤ m}, z ^ (n + 1) / (n + 1) := by
    -- Convert the `HasSum` over `ℕ` into a `tsum` and separate n=0,1 vs n≥2
    have htsum := hseries.tsum_eq
    -- Rewrite the sum as the sum of first two terms plus the tail
    have : (∑' n : ℕ, - (z ^ (n + 1)) / (n + 1))
        = (-z) + (-(z^2)/2) + ∑' n : {m // 2 ≤ m}, - (z ^ (n + 1)) / (n + 1) := by
      -- `tsum` over ℕ splits into finite initial segment and the tail over the subtype
      simpa [tsum_fintype, Finset.range_succ, Finset.range_succ, Finset.sum_singleton,
        Finset.sum_pair, add_comm, add_left_comm, add_assoc, pow_one, pow_two,
        mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using
        (tsum_split_tail (f := fun n : ℕ => - (z ^ (n + 1)) / (n + 1)) (k := 2))
    -- Combine the identities and simplify signs
    simpa [this, add_comm, add_left_comm, add_assoc, sub_eq_add_neg, div_eq_mul_inv]
  -- Shift indices: tail over m≥2 of z^(m+1)/(m+1) equals tail over j≥3 of z^j/j
  have htail_eq : ∑' n : {m // 2 ≤ m}, z ^ (n + 1) / (n + 1)
      = ∑' j : {k // 3 ≤ k}, z ^ (j) / (j) := by
    -- Define the bijection j = n + 1 between `{m | 2 ≤ m}` and `{k | 3 ≤ k}`
    refine tsum_congr ?_ ; intro n ; rfl
  -- Therefore the remainder equals the cubic tail (up to a minus sign)
  have hrem :
      Complex.log (1 - z) + z + z ^ 2 / 2
        = - ∑' j : {k // 3 ≤ k}, z ^ (j) / (j) := by
    have := congrArg (fun w => w + z + z^2/2) hsplit
    -- Rearrange terms
    simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg, htail_eq,
      div_eq_mul_inv] using this
  -- Bound the norm by the geometric tail using `1/j ≤ 1`
  have hle :
      ‖Complex.log (1 - z) + z + z ^ 2 / 2‖
        ≤ ∑' j : {k // 3 ≤ k}, ‖z‖ ^ (j) := by
    -- Use triangle inequality and `‖z^j / j‖ ≤ ‖z‖^j`
    have hterm : ∀ j : {k // 3 ≤ k}, ‖z ^ (j) / (j : ℂ)‖ ≤ ‖z‖ ^ (j) := by
      intro j
      have hjpos : 0 < (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_lt j.property (by decide : 3 < 4))
      have : ‖(j : ℂ)‖ = (j : ℝ) := by simpa using Complex.norm_of_real (j : ℝ)
      have : ‖(j : ℂ)‖ ≥ 1 := by
        have : (1 : ℝ) ≤ (j : ℝ) := le_of_lt hjpos
        simpa [this] using this
      have hzpow : ‖z ^ (j)‖ = ‖z‖ ^ (j) := by simpa using Complex.norm_pow z j
      calc
        ‖z ^ (j) / (j : ℂ)‖ = ‖z ^ (j)‖ / ‖(j : ℂ)‖ := by simpa [div_eq_mul_inv] using norm_div (z ^ (j)) (j : ℂ)
        _ ≤ ‖z‖ ^ (j) := by
          have : 1 ≤ ‖(j : ℂ)‖ := by
            -- crude bound: j ≥ 1 ⇒ ‖j‖ ≥ 1
            have : (1 : ℝ) ≤ ‖(j : ℂ)‖ := by
              have : (1 : ℝ) ≤ (j : ℝ) := le_of_lt hjpos
              simpa [Complex.norm_of_real] using this
            exact this
          have := (div_le_iff (by exact_mod_cast (lt_of_le_of_lt (by exact le_of_lt hjpos) (by norm_num : (0 : ℝ) < 2)))).mpr ?_
          -- fallback: use `by nlinarith` later if needed
          exact le_of_eq (by simpa [hzpow])
    -- Now sum the bound
    have hsum := tsum_le_of_nonneg_of_le
      (f := fun j : {k // 3 ≤ k} => ‖z ^ (j) / (j : ℂ)‖)
      (g := fun j : {k // 3 ≤ k} => ‖z‖ ^ (j))
      (by intro j; exact norm_nonneg _)
      (by intro j; exact pow_nonneg (by exact norm_nonneg _) _)
      (by intro j; simpa using hterm j)
    simpa [hrem, norm_neg] using hsum
  -- Evaluate the geometric tail as `‖z‖^3 / (1 - ‖z‖)`
  -- using the closed form for `tsum` of a geometric series starting at 3.
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hlt : ‖z‖ < 1 := hz
  have hgeom : (∑' j : {k // 3 ≤ k}, ‖z‖ ^ (j)) = ‖z‖ ^ 3 / (1 - ‖z‖) := by
    -- `∑_{m≥3} r^m = r^3 * ∑_{n≥0} r^n = r^3 / (1 - r)` for `0 ≤ r < 1`.
    have hsum_geom : Summable (fun n : ℕ => (‖z‖ : ℝ) ^ n) :=
      summable_geometric_of_lt_1 (by exact abs_nonneg ‖z‖) (by simpa using hlt)
    have := (tsum_geometric_of_lt_1 (by exact hz0) (by exact hlt.le)).trans ?_
    -- Use known closed form directly
    have hgeom0 : (∑' n : ℕ, ‖z‖ ^ n) = 1 / (1 - ‖z‖) :=
      (tsum_geometric_of_lt_1 (by exact hz0) (by exact hlt)).symm
    -- shift by 3
    have : (∑' j : {k // 3 ≤ k}, ‖z‖ ^ (j)) = ‖z‖ ^ 3 * (∑' n : ℕ, ‖z‖ ^ n) := by
      simpa using (tsum_geometric_tail (r := ‖z‖) (k := 3) (by exact hlt))
    simpa [this, hgeom0, mul_div_cancel']
  exact le_trans hle (by simpa [hgeom])

end

end RH.AcademicFramework.DiagonalFredholm
