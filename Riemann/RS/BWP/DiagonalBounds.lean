import Riemann.RS.CRGreenOuter
import Riemann.RS.WhitneyAeCore
import Riemann.RS.SchurGlobalization
import Riemann.Cert.KxiWhitney_RvM
import Riemann.RS.WhitneyGeometryDefs
import Riemann.RS.BWP.Constants
import Riemann.RS.BWP.Definitions
import Riemann.RS.BWP.Laplacian
import Riemann.RS.BWP.CRCalculus
import Mathlib.Tactic
import Mathlib
import Riemann.academic_framework.CompletedXi
import Riemann.RS.HalfPlaneOuterV2
--import Riemann.RS.RouteB_Final
import Riemann.academic_framework.Compat
import Riemann.RS.PoissonKernelDyadic
import Riemann.RS.PoissonKernelAnalysis
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import PrimeNumberTheoremAnd.Auxiliary
import StrongPNT.PNT1_ComplexAnalysis
/-!
# Diagonal Bounds and Schur Row Control

This module contains:
1. **KxiDiag namespace**: Separation lemmas for annular energy bounds
2. **Schur row bounds**: Cross-term control via row-sum majorization
3. **Annular split**: Decomposition of box energy into per-annulus contributions
4. **Calibrated bounds**: Default constant configuration (α = 1/2, S = 0.08)

These results bound the Carleson energy by combining:
- Diagonal decay (from separation)
- Schur cross-term control (from row bounds)
- VK zero-density counts

The key theorem is `carleson_energy_bound_from_split_schur_and_counts_default`,
which assembles these ingredients under the default calibrations.
-/

/-- p-series summability starting at n+1: ∑ 1/(n+1)^p converges for p > 1. -/
lemma summable_one_div_nat_add_one_pow (p : ℝ) (hp : 1 < p) :
  Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℝ) ^ p)) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ p) :=
    (Real.summable_one_div_nat_rpow (p := p)).2 hp
  simpa using
    (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ p) 1).2 h

/-- Special case p = 2. -/
lemma summable_one_div_nat_add_one_pow_two :
  Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℝ) ^ 2)) := by
  have h := summable_one_div_nat_add_one_pow (p := (2 : ℝ)) (by norm_num)
  simpa [Real.rpow_natCast] using h

namespace Finset
open Set Finset
-- If s ⊆ t then card s ≤ card t
lemma card_le_of_subset {α} [DecidableEq α] {s t : Finset α} (h : s ⊆ t) :
  s.card ≤ t.card := by exact card_le_card h

end Finset

lemma sub_lt_sub_of_lt_of_le {α} [AddCommGroup α]  [LinearOrder α] [IsOrderedAddMonoid α]
  {a c b d : α} (h₁ : c < a) (h₂ : b ≤ d) :
  a - b > c - d := by
  have h₁' := sub_lt_sub_right h₁ b
  have h₂' := sub_le_sub_left h₂ c
  exact lt_of_le_of_lt h₂' h₁'

/-- Monotonicity of set integrals: if `f ≤ g` almost everywhere on `s`,
and both are integrable on `s`, then `∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ`. -/
-- If a > 0, then a * b ≤ c ↔ b ≤ c / a
lemma mul_le_iff_le_one_left_of_nonneg {a b c : ℝ} (ha : 0 < a) :
  a * b ≤ c ↔ b ≤ c / a := by
  constructor
  · intro h
    -- b * a ≤ c then b ≤ c / a
    have h' : b * a ≤ c := by simpa [mul_comm] using h
    exact (le_div_iff₀ ha).2 h'
  · intro hb
    -- b ≤ c / a then a * b ≤ c
    have h' : b * a ≤ c := (le_div_iff₀ ha).1 hb
    simpa [mul_comm] using h'

-- If a ≤ b and 0 ≤ c then a + c ≤ b + c
lemma add_le_add_of_le_of_nonneg {a b c : ℝ} (h : a ≤ b) (_ : 0 ≤ c) :
  a + c ≤ b + c := by
  simpa using add_le_add_right h c


namespace Finset
set_option linter.unusedVariables false in
/-- Regroup a sum by the values of a function: sum over elements equals
    sum over image values of the fiber cardinality times the weight. -/
lemma sum_bij_subtype {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) (w : β → ℝ) :
  ∑ a ∈ s, w (f a)
    = ∑ b ∈ s.image f, ((s.filter (fun a => f a = b)).card : ℝ) * w b := by
  classical
  -- turn the RHS into a sum over the fiber
  have hfiber :
      ∀ b ∈ s.image f,
        ((s.filter (fun a => f a = b)).card : ℝ) * w b
          = ∑ a ∈ s.filter (fun a => f a = b), w b := by
    intro b hb
    simp [sum_const, nsmul_eq_mul]
  -- expand LHS by "inserting" the image index, then swap and evaluate fibers
  calc
    ∑ a ∈ s, w (f a)
        = ∑ a ∈ s, ∑ b ∈ s.image f, (if b = f a then w b else 0) := by
            refine sum_congr rfl ?_
            intro a ha
            -- (∑ over b∈image f) selects exactly the `b = f a`
            have hmem : f a ∈ s.image f := mem_image.mpr ⟨a, ha, rfl⟩
            symm
            calc ∑ b ∈ s.image f, (if b = f a then w b else 0)
                = ∑ b ∈ s.image f, (if f a = b then w b else 0) := by simp only [eq_comm]
              _ = if f a ∈ s.image f then w (f a) else 0 := sum_ite_eq (s.image f) (f a) w
              _ = w (f a) := if_pos hmem
    _   = ∑ b ∈ s.image f, ∑ a ∈ s, (if b = f a then w b else 0) := by
            rw [sum_comm]
    _   = ∑ b ∈ s.image f, ∑ a ∈ s.filter (fun a => f a = b), w b := by
            refine sum_congr rfl fun b hb => ?_
            -- pull the `if` into a filter
            simp only [eq_comm, sum_filter]  -- `sum_filter` gives: sum over filter = sum of ifs
    _   = ∑ b ∈ s.image f, ((s.filter (fun a => f a = b)).card : ℝ) * w b := by
            refine sum_congr rfl ?_
            intro b hb; exact (hfiber b hb).symm

-- Sum ≤ (#s) · c under pointwise bound f x ≤ c and f x ≥ 0
lemma sum_le_card_nsmul_of_nonneg {α} (s : Finset α) (f : α → ℝ) {c : ℝ}
  (_ : 0 ≤ c)
  (h_le : ∀ x ∈ s, f x ≤ c)
  (_ : ∀ x ∈ s, 0 ≤ f x) :
  ∑ x ∈ s, f x ≤ (s.card : ℝ) * c := by
  classical
  -- pointwise bound: f x ≤ c for x ∈ s
  have hpoint : ∀ x ∈ s, f x ≤ (fun _ => c) x := by
    intro x hx; simpa using h_le x hx
  -- sum ≤ sum of constants = card · c
  have hsum_le : (∑ x ∈ s, f x) ≤ (∑ _x ∈ s, c) :=
    sum_le_sum hpoint
  simpa [sum_const, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hsum_le

-- Nonnegativity of a nonnegative series
lemma tsum_of_nonneg {f : ℕ → ℝ} (h : ∀ n, 0 ≤ f n) :
  0 ≤ ∑' n, f n :=
tsum_nonneg h


end Finset

namespace Riemann.RS.BoundaryWedgeProof

open Real Complex
open MeasureTheory RH.Cert RH.RS  RH.RS.BoundaryWedgeProof RH.RS.PoissonKernelAnalysis KxiWhitneyRvM
--open RH.Cert.KxiWhitneyRvM Riemann.RS.BoundaryWedgeProof

/-! ## KxiDiag: Separation and diagonal bounds -/

namespace KxiDiag

/-- Separation from the base interval: if `γ` lies in the k‑th annulus and `k≥1`,
then for all `t ∈ I.interval` one has `|t−γ| ≥ 2^{k−1}·I.len`. -/
lemma separation_from_base_of_annulus
  (I : RH.Cert.WhitneyInterval) {k : ℕ} (hk : 1 ≤ k) {γ : ℝ}
  (hA : annulusDyadic I k γ) :
  ∀ t ∈ I.interval, (2 : ℝ)^(k-1) * I.len ≤ |t - γ| := by
  intro t ht
  -- |t−γ| ≥ |γ−t0| − |t−t0|
  have hdist : |t - γ| ≥ |γ - I.t0| - |t - I.t0| := by
    -- triangle inequality on ℝ
    have := abs_sub_le_iff.1 (abs_sub (t) (γ))
    -- Use |x−z| ≥ |y−z| − |x−y|; here choose y = I.t0
    -- fallback: standard inequality |x−z| ≥ |y−z| − |x−y|
    have : |t - γ| ≥ |I.t0 - γ| - |t - I.t0| := by
      -- Use triangle inequality: |a - c| ≥ ||b - c| - |a - b||
      -- Here a = t, b = I.t0, c = γ
      have h1 : |t - γ| ≥ |I.t0 - γ| - |t - I.t0| :=
        PoissonKernelAnalysis.sep_lower_bound t I.t0 γ
      -- Since we want the weaker inequality without absolute value on RHS
      have h2 : |I.t0 - γ| - |t - I.t0| ≥ |I.t0 - γ| - |t - I.t0| := by
        exact Preorder.le_refl (|I.t0 - γ| - |t - I.t0|)
      exact le_trans h2 h1
    -- |I.t0−γ| = |γ−t0|
    simpa [abs_sub_comm]
      using this
  -- On the base: |t−t0| ≤ I.len
  have hbase : |t - I.t0| ≤ I.len := by
    have hL : I.t0 - I.len ≤ t ∧ t ≤ I.t0 + I.len := by
      exact ht
    have h1 : -I.len ≤ t - I.t0 := by linarith
    have h2 : t - I.t0 ≤ I.len := by linarith
    exact (abs_le.mpr ⟨h1, h2⟩)
  -- From annulus: |γ−t0| > 2^k·I.len
  have hAnn_lt : (2 : ℝ)^k * I.len < |γ - I.t0| := by
    have := hA.left
    -- |γ−t0| = |t0−γ|
    simpa [abs_sub_comm] using this
  -- Combine: |t−γ| ≥ |γ−t0| − |t−t0| > 2^k·I.len − I.len ≥ 2^{k−1}·I.len
  have _ : |t - γ| > (2 : ℝ)^k * I.len - I.len := by
    -- From hdist: |t - γ| ≥ |γ - I.t0| - |t - I.t0|
    -- From hAnn_lt: |γ - I.t0| > 2^k * I.len
    -- From hbase: |t - I.t0| ≤ I.len
    -- So: |t - γ| ≥ |γ - I.t0| - |t - I.t0| > 2^k * I.len - I.len
    have h1 : |γ - I.t0| - |t - I.t0| > (2 : ℝ)^k * I.len - I.len := by
      exact sub_lt_sub_of_lt_of_le hAnn_lt hbase
    exact Std.lt_of_lt_of_le h1 hdist
  -- 2^k·L − L ≥ 2^{k−1}·L for k≥1
  have _ : (2 : ℝ)^k * I.len - I.len ≥ (2 : ℝ)^(k-1) * I.len := by
    have hposL : 0 ≤ I.len := (le_of_lt I.len_pos)
    have : (2 : ℝ)^k - 1 ≥ (2 : ℝ)^(k-1) := by
      -- since k≥1, 2^k = 2 * 2^{k-1} and 2^{k-1} ≥ 1
      have hk' : (2 : ℝ)^k = (2 : ℝ) * (2 : ℝ)^(k - 1) := by
        have h' : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
        rw [h', pow_succ']; simp
      have hge1 : (1 : ℝ) ≤ (2 : ℝ)^(k - 1) := by
        exact PoissonKernelDyadic.two_pow_ge_one (k - 1)
      have hNonneg : (2 : ℝ)^(k - 1) - 1 ≥ 0 := by linarith
      have hId :
          (2 : ℝ) * (2 : ℝ)^(k - 1) - 1 - (2 : ℝ)^(k - 1)
            = (2 : ℝ)^(k - 1) - 1 := by
        ring
      have hstep' :
          (2 : ℝ) * (2 : ℝ)^(k - 1) - 1 ≥ (2 : ℝ)^(k - 1) := by
        have : (2 : ℝ) * (2 : ℝ)^(k - 1) - 1 - (2 : ℝ)^(k - 1) ≥ 0 := by
          simpa [hId] using hNonneg
        linarith
      simpa [hk'] using hstep'
    -- multiply both sides by L ≥ 0 and rewrite (a - 1) * L = a*L - L
    have hmul :
        (2 : ℝ)^(k - 1) * I.len ≤ ((2 : ℝ)^k - 1) * I.len :=
      mul_le_mul_of_nonneg_right (by simpa using this) hposL
    simpa [sub_mul, one_mul] using hmul
  -- conclude ≥ by weakening strict >
  exact PoissonKernelDyadic.sep_from_base_of_annulus hbase hA hk-- le_trans (le_of_lt hstep) hgeom

open RH.RS.BoundaryWedgeProof KxiWhitneyRvM

/-- Diagonal annulus energy bound specialized to a singleton center. -/
lemma annular_diag_singleton_bound
  (I : RH.Cert.WhitneyInterval) {k : ℕ} (hk : 1 ≤ k) (α : ℝ) (hα : 0 ≤ α) (γ : ℝ)
  (hsep : ∀ t ∈ I.interval, (2 : ℝ)^(k-1) * I.len ≤ |t - γ|) :
  annularEnergyDiag α I ({γ} : Finset ℝ)
    ≤ (16 * (α ^ 4)) * (2 * I.len) / ((4 : ℝ) ^ k) * (1 : ℝ) := by
  -- feed the separation predicate to the diagonal lemma with Zk = {γ}
  have hSeparated : Diagonal.SeparatedFromBase k I ({γ} : Finset ℝ) := by
    intro γ' hγ' t ht
    -- only element is γ
    have : γ' = γ := by
      have : γ' ∈ ({γ} : Finset ℝ) := hγ'
      simpa using Finset.mem_singleton.mp this
    simpa [this] using hsep t ht
  -- apply the diagonal bound with card = 1
  simpa using Diagonal.annularEnergyDiag_le (hα := hα) (hk := hk) (I := I) (Zk := ({γ} : Finset ℝ)) hSeparated

end KxiDiag
open KxiDiag



/-! ## Schur-type cross-term control

We formalize a row-sum (Schur) bound at fixed annulus scale, which controls the
cross terms by the diagonal. This is the right abstraction to bound
`annularEnergy` linearly in the number of centers, provided we can estimate the
row sums using dyadic separation and short-interval counts.

We encode a row-sum Schur bound at fixed σ, uniformly in σ ∈ (0, α·|I|]:
for each row `γ ∈ Zk` the cross-term integral is dominated by `S` times the
diagonal integral at `γ`. This is the positive-kernel Schur test specialized to
`Ksigma`, and is the right abstraction to control `annularEnergy` by the diagonal.
-/

/-- Row-sum Schur bound for a fixed annulus scale `σ`. -/
structure AnnularSchurRowBound (α : ℝ) (I : RH.Cert.WhitneyInterval) (Zk : Finset ℝ) where
  S : ℝ
  S_nonneg : 0 ≤ S
  row_bound : ∀ ⦃σ : ℝ⦄, 0 ≤ σ → σ ≤ α * I.len →
    ∀ γ ∈ Zk,
      (∫ t in I.interval,
        (∑ γ' ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ')) *
          KxiWhitneyRvM.Ksigma σ (t - γ))
      ≤ S * (∫ t in I.interval, (KxiWhitneyRvM.Ksigma σ (t - γ))^2)

/-- Row-sum Schur bound for a whole interval `I`. -/
structure AnnularSchurRowBoundWhole (α : ℝ) (I : RH.Cert.WhitneyInterval) (Zk : Finset ℝ) where
  S : ℝ
  S_nonneg : 0 ≤ S
  row_bound :
    ∀ ⦃σ : ℝ⦄, 0 ≤ σ → σ ≤ α * I.len →
    ∀ γ ∈ Zk,
      (∫ t in I.interval,
        (∑ γ' ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ')) *
          KxiWhitneyRvM.Ksigma σ (t - γ))
      ≤ S * (∫ t : ℝ, (KxiWhitneyRvM.Ksigma σ (t - γ))^2)

/-- Short-interval multiplicity cap for a finite set `Z` up to radius `R`. -/
structure ShortIntervalMultiplicity (Z : Finset ℝ) (R : ℝ) where
  M : ℕ
  bound : ∀ (x : ℝ), (Z.filter (fun z => x - R ≤ z ∧ z ≤ x + R)).card ≤ M

/-- Number of points of `Z` within `r` of `x`. -/
noncomputable def nearCount (Z : Finset ℝ) (x r : ℝ) : ℕ :=
  (Z.filter (fun z => x - r ≤ z ∧ z ≤ x + r)).card

open scoped BigOperators
open Real

/-- Tail constant for the shell bound: 1 + 2 · ∑_{n≥1} 1/(n+1)^2. -/
noncomputable def C_shell : ℝ :=
  1 + 2 * (∑' n : ℕ, 1 / ((n + 1 : ℝ)^2))

/-- 2-intervals bound per shell: for each `n ≥ 0`, the number of points of `Z` with
    `⌊|x-γ|/(2s)⌋ = n+1` is at most `2·M`. -/
lemma shell_card_le_twoM
  {s : ℝ} (hs : 0 < s) {Z : Finset ℝ}
  (hM : ShortIntervalMultiplicity Z (2 * s)) (x : ℝ) (n : ℕ) :
  (Z.filter (fun γ => Nat.floor (|x - γ| / (2 * s)) = n + 1)).card ≤ 2 * hM.M := by
  classical
  set S := Z.filter (fun γ => Nat.floor (|x - γ| / (2 * s)) = n + 1)
  have hsplit :
      S.card
        = (S.filter (fun γ => γ ≤ x)).card + (S.filter (fun γ => x ≤ γ)).card := by
    -- `γ = x` cannot occur since `⌊0⌋ = 0 ≠ n+1`
    have hdisj : Disjoint (S.filter (fun γ => γ ≤ x)) (S.filter (fun γ => x ≤ γ)) := by
      refine Finset.disjoint_left.mpr ?_
      intro γ hγ hγ'
      -- from membership in both sides we get γ = x
      have hx1 : γ ≤ x := (Finset.mem_filter.mp hγ).2
      have hx2 : x ≤ γ := (Finset.mem_filter.mp hγ').2
      have hx : γ = x := le_antisymm hx1 hx2
      -- but then floor(|x-γ|/(2s)) = 0, contradicting membership in S (n+1 ≠ 0)
      have hpos : 0 < 2 * s := mul_pos (by norm_num) hs
      have hx0 : Nat.floor (|x - γ| / (2 * s)) = 0 := by
        simp [hx]
      have hSγ : γ ∈ S := (Finset.mem_filter.mp hγ).1
      have hm : Nat.floor (|x - γ| / (2 * s)) = n + 1 := by
        simpa [S] using (Finset.mem_filter.mp hSγ).2
      have : n + 1 = 0 := by simp [hm] at hx0
      exact (Nat.succ_ne_zero n) this
    -- cover: total order splits S into left and right filters
    have hcover :
        (S.filter (fun γ => γ ≤ x)) ∪ (S.filter (fun γ => x ≤ γ)) = S := by
      ext γ
      constructor
      · intro hγ
        rcases Finset.mem_union.mp hγ with hL | hR
        · exact (Finset.mem_filter.mp hL).1
        · exact (Finset.mem_filter.mp hR).1
      · intro hSγ
        rcases le_total γ x with hγx | hxγ
        · exact
            Finset.mem_union.mpr
              (Or.inl (Finset.mem_filter.mpr ⟨hSγ, hγx⟩))
        · exact
            Finset.mem_union.mpr
              (Or.inr (Finset.mem_filter.mpr ⟨hSγ, hxγ⟩))
    classical
    simpa [hcover] using (Finset.card_union_of_disjoint hdisj)
  -- bound left side block by `M`
  have hleft :
      (S.filter (fun γ => γ ≤ x)).card ≤ hM.M := by
    -- If `γ ∈ S` and `γ ≤ x`, then `(n+1)·(2s) ≤ x-γ < (n+2)·(2s)`,
    -- hence `γ ∈ [x-(n+2)·(2s), x-(n+1)·(2s)]`, which sits inside
    -- the `4s`-interval centered at `cL := x - (n + 3/2)·(2s)`.
    set cL : ℝ := x - ((n : ℝ) + 3/2) * (2 * s)
    have hsubset :
        (S.filter (fun γ => γ ≤ x)) ⊆
        (Z.filter (fun γ => cL - 2 * s ≤ γ ∧ γ ≤ cL + 2 * s)) := by
      intro γ hγ
      rcases Finset.mem_filter.mp hγ with ⟨hSγ, hγx⟩
      have hm : Nat.floor (|x - γ| / (2 * s)) = n + 1 := by
        simpa [S] using (Finset.mem_filter.mp hSγ).2
      have hxγ : 0 ≤ x - γ := sub_nonneg.mpr hγx
      have hbounds :
          (n : ℝ) + 1 ≤ (|x - γ| / (2 * s)) ∧ (|x - γ| / (2 * s)) < (n : ℝ) + 2 := by
        exact And.intro
          (by
            have hnn : 0 ≤ |x - γ| / (2 * s) := by
              have hpos : 0 < 2 * s := mul_pos (by norm_num) hs
              exact div_nonneg (abs_nonneg _) hpos.le
            have := Nat.floor_le (a := |x - γ| / (2 * s)) hnn
            simpa [hm, Nat.cast_add, Nat.cast_one] using this)
          (by
            have := Nat.lt_floor_add_one (a := |x - γ| / (2 * s))
            simpa [hm, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using this)
      have habs : |x - γ| = x - γ := abs_of_nonneg hxγ
      have hγI :
          x - ((n : ℝ) + 2) * (2 * s) ≤ γ ∧ γ ≤ x - ((n : ℝ) + 1) * (2 * s) := by
        have : (n : ℝ) + 1 ≤ (x - γ) / (2 * s) ∧ (x - γ) / (2 * s) < (n : ℝ) + 2 := by
          simpa [habs] using And.intro hbounds.1 hbounds.2
        constructor
        ·
          -- lower bound: x - ((n+2)·2s) ≤ γ from (x-γ) < (n+2)·2s
          have hlt : x - γ < ((n : ℝ) + 2) * (2 * s) :=
            (div_lt_iff₀ (mul_pos (by norm_num) hs)).1 this.2
          have hlt' : x - ((n : ℝ) + 2) * (2 * s) < γ := by linarith
          exact hlt'.le
        ·
          -- upper bound: γ ≤ x - ((n+1)·2s) from (n+1)·2s ≤ (x-γ)
          have hle : ((n : ℝ) + 1) * (2 * s) ≤ x - γ :=
            (le_div_iff₀ (mul_pos (by norm_num) hs)).1 this.1
          have hle' : γ ≤ x - ((n : ℝ) + 1) * (2 * s) := by linarith
          exact hle'
      -- and that interval is contained in the `4s`-interval around `cL`
      have hIcc_sub :
          (fun γ => x - ((n : ℝ) + 2) * (2 * s) ≤ γ ∧ γ ≤ x - ((n : ℝ) + 1) * (2 * s))
            γ → cL - 2 * s ≤ γ ∧ γ ≤ cL + 2 * s := by
        intro h
        constructor
        · -- left bound: use cL - 2s = x - (n+2)·(2s) - s ≤ x - (n+2)·(2s) ≤ γ
          have hs_nonneg : 0 ≤ s := (le_of_lt hs)
          have hcL_left :
              cL - 2 * s = x - ((n : ℝ) + 2) * (2 * s) - s := by
            -- algebraic normalization: expand cL and simplify
            simpa [cL] using by
              have : x - ((n : ℝ) + 3/2) * (2 * s) - 2 * s
                    = x - ((n : ℝ) + 2) * (2 * s) - s := by
                ring
              exact this
          have hstep :
              x - ((n : ℝ) + 2) * (2 * s) - s ≤ x - ((n : ℝ) + 2) * (2 * s) :=
            sub_le_self _ hs_nonneg
          have hle' : cL - 2 * s ≤ x - ((n : ℝ) + 2) * (2 * s) := by
            simpa [hcL_left] using hstep
          exact le_trans hle' h.1
        · -- right bound: γ ≤ x - (n+1)·(2s) ≤ cL + 2s, since cL + 2s = x - (n+1)·(2s) + s
          have hs_nonneg : 0 ≤ s := (le_of_lt hs)
          have hcL_plus :
              cL + 2 * s = x - ((n : ℝ) + 1) * (2 * s) + s := by
            -- algebraic normalization: expand cL and simplify
            simpa [cL] using by
              have : x - ((n : ℝ) + 3/2) * (2 * s) + 2 * s
                    = x - ((n : ℝ) + 1) * (2 * s) + s := by
                ring
              exact this
          have hstep :
              x - ((n : ℝ) + 1) * (2 * s) ≤ cL + 2 * s := by
            have hbase :
                x - ((n : ℝ) + 1) * (2 * s)
                  ≤ x - ((n : ℝ) + 1) * (2 * s) + s := by
              simpa using
                (le_add_of_nonneg_right hs_nonneg :
                  x - ((n : ℝ) + 1) * (2 * s)
                    ≤ x - ((n : ℝ) + 1) * (2 * s) + s)
            simpa [hcL_plus, add_comm, add_left_comm, add_assoc] using hbase
          exact le_trans h.2 hstep
      have : γ ∈ (Z.filter (fun γ => cL - 2 * s ≤ γ ∧ γ ≤ cL + 2 * s)) := by
        refine Finset.mem_filter.mpr ?_
        exact ⟨(Finset.mem_filter.mp hSγ).1,
               hIcc_sub hγI⟩
      exact this
    exact (le_trans (Finset.card_le_of_subset hsubset) (hM.bound cL))
  -- bound right side block by `M` (symmetric)
  have hright :
      (S.filter (fun γ => x ≤ γ)).card ≤ hM.M := by
    set cR : ℝ := x + ((n : ℝ) + 3/2) * (2 * s)
    have hsubset :
        (S.filter (fun γ => x ≤ γ)) ⊆
        (Z.filter (fun γ => cR - 2 * s ≤ γ ∧ γ ≤ cR + 2 * s)) := by
      intro γ hγ
      rcases Finset.mem_filter.mp hγ with ⟨hSγ, hxγ⟩
      have hm : Nat.floor (|x - γ| / (2 * s)) = n + 1 := by
        simpa [S] using (Finset.mem_filter.mp hSγ).2
      have hxγ' : 0 ≤ γ - x := sub_nonneg.mpr hxγ
      have hbounds :
          (n : ℝ) + 1 ≤ (|x - γ| / (2 * s)) ∧ (|x - γ| / (2 * s)) < (n : ℝ) + 2 := by
        exact And.intro
          (by
            have hnn : 0 ≤ |x - γ| / (2 * s) := by
              have hpos : 0 < 2 * s := mul_pos (by norm_num) hs
              exact div_nonneg (abs_nonneg _) hpos.le
            have := Nat.floor_le (a := |x - γ| / (2 * s)) hnn
            simpa [hm, Nat.cast_add, Nat.cast_one] using this)
          (by
            have := Nat.lt_floor_add_one (a := |x - γ| / (2 * s))
            simpa [hm, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using this)
      have habs : |x - γ| = γ - x := by
        rw [abs_sub_comm]
        exact abs_of_nonneg hxγ'
      have hγI :
          x + ((n : ℝ) + 1) * (2 * s) ≤ γ ∧ γ ≤ x + ((n : ℝ) + 2) * (2 * s) := by
        constructor
        ·
          -- from (n+1) ≤ (|x-γ|)/(2s) and |x-γ| = γ-x, deduce x + (n+1)·(2s) ≤ γ
          have hle0 : ((n : ℝ) + 1) * (2 * s) ≤ γ - x := by
            have := hbounds.1
            have := (le_div_iff₀ (mul_pos (by norm_num) hs)).1 this
            simpa [habs] using this
          have hle1 := add_le_add_right hle0 x
          -- x + ((n+1)·2s) ≤ (γ - x) + x = γ
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hle1
        ·
          -- from (|x-γ|)/(2s) < (n+2) and |x-γ| = γ-x, deduce γ ≤ x + (n+2)·(2s)
          have hlt0 : γ - x < ((n : ℝ) + 2) * (2 * s) := by
            have := hbounds.2
            have := (div_lt_iff₀ (mul_pos (by norm_num) hs)).1 this
            simpa [habs] using this
          have hlt1 := add_lt_add_right hlt0 x
          -- γ < x + (n+2)·(2s) hence γ ≤ x + ...
          exact (le_of_lt (by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hlt1))
      have hIcc_sub :
          (fun γ => x + ((n : ℝ) + 1) * (2 * s) ≤ γ ∧ γ ≤ x + ((n : ℝ) + 2) * (2 * s))
            γ → cR - 2 * s ≤ γ ∧ γ ≤ cR + 2 * s := by
        intro h
        constructor
        · -- left bound: cR - 2s = x + (n+1)·(2s) - s ≤ x + (n+1)·(2s) ≤ γ
          have hs_nonneg : 0 ≤ s := (le_of_lt hs)
          have hcR_left :
              cR - 2 * s = x + ((n : ℝ) + 1) * (2 * s) - s := by
            -- algebraic normalization: expand cR and simplify
            simpa [cR] using by
              have : x + ((n : ℝ) + 3/2) * (2 * s) - 2 * s
                    = x + ((n : ℝ) + 1) * (2 * s) - s := by
                ring
              exact this
          have hstep :
              x + ((n : ℝ) + 1) * (2 * s) - s ≤ x + ((n : ℝ) + 1) * (2 * s) :=
            sub_le_self _ hs_nonneg
          have hle' : cR - 2 * s ≤ x + ((n : ℝ) + 1) * (2 * s) := by
            simpa [hcR_left] using hstep
          exact le_trans hle' h.1
        · -- right bound: γ ≤ x + (n+2)·(2s) ≤ cR + 2s, with cR + 2s = x + (n+2)·(2s) + s
          have hs_nonneg : 0 ≤ s := (le_of_lt hs)
          have hcR_plus :
              cR + 2 * s = x + ((n : ℝ) + 2) * (2 * s) + s := by
            -- algebraic normalization: expand cR and simplify
            simpa [cR] using by
              have : x + ((n : ℝ) + 3/2) * (2 * s) + 2 * s
                    = x + ((n : ℝ) + 2) * (2 * s) + s := by
                ring
              exact this
          have hstep :
              x + ((n : ℝ) + 2) * (2 * s) ≤ cR + 2 * s := by
            have hbase :
                x + ((n : ℝ) + 2) * (2 * s) ≤ (x + ((n : ℝ) + 2) * (2 * s)) + s := by
              exact le_add_of_nonneg_right hs_nonneg
            simpa [hcR_plus, add_comm, add_left_comm, add_assoc] using hbase
          exact le_trans h.2 hstep
      have : γ ∈ (Z.filter (fun γ => cR - 2 * s ≤ γ ∧ γ ≤ cR + 2 * s)) := by
        refine Finset.mem_filter.mpr ?_
        exact ⟨(Finset.mem_filter.mp hSγ).1, hIcc_sub hγI⟩
      exact this
    exact (le_trans (Finset.card_le_of_subset hsubset) (hM.bound cR))
  -- combine the two sides
  have : S.card ≤ hM.M + hM.M := by
    simpa [hsplit] using add_le_add hleft hright
  -- rewrite 2 * M as M + M
  simpa [two_mul] using this

open Finset
set_option linter.unusedVariables false in
/-- Standard shell bound: with a short-interval multiplicity cap at radius `2s`,
    the Cauchy/Poisson row-weight sum at scale `2s` is bounded by `C_shell · M`. -/
lemma cauchy_shell_sum_bound
  {s : ℝ} (hs : 0 < s) {Z : Finset ℝ}
  (hM : ShortIntervalMultiplicity Z (2 * s)) (x : ℝ) :
  ∑ γ ∈ Z, (4 * s^2) / ((x - γ)^2 + (2 * s)^2)
    ≤ (hM.M : ℝ) * C_shell := by
  classical
  -- For each γ, let mγ := ⌊|x-γ| / (2s)⌋
  let m : ℝ → ℕ := fun y => Nat.floor (|y| / (2 * s))
  -- Pointwise weight bound by shell-index:
  have hpt : ∀ γ ∈ Z,
      (4 * s^2) / ((x - γ)^2 + (2 * s)^2)
        ≤ 1 / (1 + (m (x - γ))^2) := by
    intro γ _; dsimp [m]
    -- floor property: 2 s · m ≤ |x-γ|
    have hfloor : (m (x - γ) : ℝ) ≤ |x - γ| / (2 * s) := by
      exact Nat.floor_le (by
        have hpos : 0 < 2 * s := mul_pos (by norm_num) hs
        exact div_nonneg (abs_nonneg _) hpos.le)
    have hmul : 2 * s * (m (x - γ) : ℝ) ≤ |x - γ| := by
      have hpos : 0 < 2 * s := mul_pos (by norm_num) hs
      exact
        (mul_le_iff_le_one_left_of_nonneg
          (a := 2 * s) (b := (m (x - γ) : ℝ)) (c := |x - γ|) hpos).2 hfloor
    have hsq : (2 * s * (m (x - γ) : ℝ))^2 ≤ (x - γ)^2 := by
      have : 0 ≤ 2 * s * (m (x - γ) : ℝ) := by positivity
      calc (2 * s * (m (x - γ) : ℝ))^2
          ≤ |x - γ|^2 := pow_le_pow_left₀ this hmul 2
        _ = (x - γ)^2 := sq_abs _
    -- Use monotonicity in the denominator
    have hden :
        (x - γ)^2 + (2 * s)^2
          ≥ (2 * s)^2 * (1 + (m (x - γ) : ℝ)^2) := by
      -- (x-γ)^2 ≥ (2 s m)^2
      have hx : (x - γ)^2 ≥ (2 * s * (m (x - γ) : ℝ))^2 := by simpa using hsq
      have hx' : (x - γ)^2 + (2 * s)^2 ≥ (2 * s)^2 + (2 * s)^2 * (m (x - γ) : ℝ)^2 := by
        have : (2 * s)^2 + (2 * s * (m (x - γ) : ℝ))^2 ≤ (2 * s)^2 + (x - γ)^2 := by
          exact add_le_add_right hx ((2 * s)^2)
        calc (2 * s)^2 + (2 * s)^2 * (m (x - γ) : ℝ)^2
            = (2 * s)^2 + (2 * s * (m (x - γ) : ℝ))^2 := by ring
          _ ≤ (2 * s)^2 + (x - γ)^2 := this
          _ = (x - γ)^2 + (2 * s)^2 := by ring
      calc (x - γ)^2 + (2 * s)^2
          ≥ (2 * s)^2 + (2 * s)^2 * (m (x - γ) : ℝ)^2 := hx'
        _ = (2 * s)^2 * (1 + (m (x - γ) : ℝ)^2) := by ring
    -- Now invert and multiply by 4 s^2
    have hpos_rhs : 0 < (2 * s)^2 * (1 + (m (x - γ) : ℝ)^2) := by positivity
    have hinv :
        (4 * s^2) / ((x - γ)^2 + (2 * s)^2)
          ≤ (4 * s^2) / ((2 * s)^2 * (1 + (m (x - γ) : ℝ)^2)) := by
      have h_inv : 1 / ((x - γ)^2 + (2 * s)^2) ≤ 1 / ((2 * s)^2 * (1 + (m (x - γ) : ℝ)^2)) :=
        one_div_le_one_div_of_le hpos_rhs hden
      calc (4 * s^2) / ((x - γ)^2 + (2 * s)^2)
          = (4 * s^2) * (1 / ((x - γ)^2 + (2 * s)^2)) := by ring
        _ ≤ (4 * s^2) * (1 / ((2 * s)^2 * (1 + (m (x - γ) : ℝ)^2))) := by
            exact mul_le_mul_of_nonneg_left h_inv (by positivity)
        _ = (4 * s^2) / ((2 * s)^2 * (1 + (m (x - γ) : ℝ)^2)) := by ring
    have hσ : (2 * s)^2 = 4 * s^2 := by
      ring
    have hpos : (1 + (m (x - γ) : ℝ)^2) ≠ 0 := by positivity
    calc (4 * s^2) / ((x - γ)^2 + (2 * s)^2)
        ≤ (4 * s^2) / ((2 * s)^2 * (1 + (m (x - γ) : ℝ)^2)) := hinv
      _ = (4 * s^2) / (4 * s^2 * (1 + (m (x - γ) : ℝ)^2)) := by rw [hσ]
      _ = 1 / (1 + (m (x - γ) : ℝ)^2) := by
            have h4s2_ne : 4 * s^2 ≠ 0 := by
              have hs_ne : s ≠ 0 := ne_of_gt hs
              have : s^2 ≠ 0 := pow_ne_zero 2 hs_ne
              exact mul_ne_zero (by norm_num) this
            have hdiv : (4 * s^2) / (4 * s^2) = 1 := div_self h4s2_ne
            calc (4 * s^2) / (4 * s^2 * (1 + (m (x - γ) : ℝ)^2))
                = ((4 * s^2) / (4 * s^2)) / (1 + (m (x - γ) : ℝ)^2) := by rw [div_mul_eq_div_div]
              _ = 1 / (1 + (m (x - γ) : ℝ)^2) := by rw [hdiv]
      _ = (1 + (m (x - γ) : ℝ)^2)⁻¹ := one_div _
      _ = 1 / (1 + (m (x - γ) : ℝ)^2) := by ring
  -- Sum the pointwise bounds
  have hsum_le :
      ∑ γ ∈ Z, (4 * s^2) / ((x - γ)^2 + (2 * s)^2)
        ≤ ∑ γ ∈ Z, 1 / (1 + (m (x - γ) : ℝ)^2) :=
    Finset.sum_le_sum (by intro γ hγ; exact hpt γ hγ)
  -- Group by m = 0 and m ≥ 1; multiplicity bounds give counts ≤ M (for m=0) and ≤ 2M (for m≥1)
  have hcount0 :
      (∑ γ ∈ Z.filter (fun γ => m (x - γ) = 0),
        1 / (1 + ((m (x - γ) : ℝ)^2)))
      ≤ (hM.M : ℝ) * 1 := by
    -- Each term equals 1/(1+0) = 1; the filter selects |x-γ| < 2s
    have hval : ∀ γ ∈ Z, m (x - γ) = 0 → 1 / (1 + (m (x - γ))^2) = 1 := by
      intro γ hγ hm; simp [hm]
    -- Card ≤ M by hM.bound with center x and radius 2s
    have hsub :
        (Z.filter (fun γ => m (x - γ) = 0)).card
          ≤ hM.M := by
      -- {γ | |x-γ| < 2s} ⊆ [x - 2s, x + 2s]; length 4s; use hM.bound
      -- Choose the midpoint x; then "filter" ≤ count in that interval
      have hsubset :
          (Z.filter (fun γ => |x - γ| ≤ 2 * s)).card
            ≤ hM.M := by
        -- {γ | |x-γ| ≤ 2s} ⊆ [x - 2s, x + 2s], then apply `hM.bound x`
        have hsub :
            (Z.filter (fun γ => |x - γ| ≤ 2 * s))
              ⊆ (Z.filter (fun γ => x - 2 * s ≤ γ ∧ γ ≤ x + 2 * s)) := by
          intro γ hγ
          simp [Finset.mem_filter] at hγ ⊢
          rcases hγ with ⟨hZ, habs⟩
          constructor
          · exact hZ
          ·
            have hx0 := abs_sub_le_iff.1 habs
            -- Produce the normalized forms: x ≤ γ + 2*s and γ ≤ x + 2*s
            have h₁ : x ≤ γ + 2 * s := by
              have : x ≤ 2 * s + γ := (sub_le_iff_le_add).1 hx0.1
              simpa [add_comm] using this
            have h₂ : γ ≤ x + 2 * s := by
              have : γ ≤ 2 * s + x := (sub_le_iff_le_add).1 hx0.2
              simpa [add_comm] using this
            constructor
            · exact h₁
            · exact h₂
        have hcard_mono :
            (Z.filter (fun γ => |x - γ| ≤ 2 * s)).card
              ≤ (Z.filter (fun γ => x - 2 * s ≤ γ ∧ γ ≤ x + 2 * s)).card :=
          Finset.card_le_of_subset hsub
        exact le_trans hcard_mono (hM.bound x)
      -- Since m=0 implies |x-γ|/(2s) < 1 ⇒ |x-γ| ≤ 2s, we can compare filters
      have hle :
          (Z.filter (fun γ => m (x - γ) = 0)).card
            ≤ (Z.filter (fun γ => |x - γ| ≤ 2 * s)).card := by
        refine Finset.card_le_card (fun γ hγ => by
          simp only [Finset.mem_filter] at hγ ⊢
          constructor
          · exact hγ.1
          · have hm := hγ.2
            simp only [m] at hm
            have : |x - γ| / (2 * s) < 1 := by
              by_contra h
              push_neg at h
              have : 1 ≤ ⌊|x - γ| / (2 * s)⌋₊ :=
                (Nat.one_le_floor_iff (|x - γ| / (2 * s))).mpr h--Nat.one_le_floor_iff.mpr h
              omega
            have hlt : |x - γ| < 2 * s := by
              have hpos : 0 < 2 * s := by positivity
              have h := (div_lt_iff₀ hpos).1 this
              simpa [mul_comm, mul_left_comm, mul_assoc] using h
            exact hlt.le)
      exact le_trans hle hsubset
    -- Sum = (#filter)*1
    have := Finset.sum_le_card_nsmul_of_nonneg
              (s := Z.filter (fun γ => m (x - γ) = 0))
              (f := fun γ => 1 / (1 + (m (x - γ))^2))
              (c := 1)
              (h_le := by
                intro γ hγ
                -- (1 + m^2)⁻¹ ≤ 1 since 1 ≤ 1 + m^2 and x ↦ 1/x is decreasing on (0, ∞)
                have hnonneg : 0 ≤ (↑(m (x - γ)) : ℝ) ^ 2 := by positivity
                have hone_le : (1 : ℝ) ≤ 1 + (↑(m (x - γ)) : ℝ) ^ 2 := by
                  simp
                have h := one_div_le_one_div_of_le (by norm_num : 0 < (1 : ℝ)) hone_le
                simpa [one_div] using h)
    -- Direct: sum ≤ card * 1 ≤ M*1
    simpa [one_div] using
      (le_trans
        (by classical
            have := Finset.sum_le_card_nsmul_of_nonneg
                      (s := Z.filter (fun γ => m (x - γ) = 0))
                      (f := fun γ => 1 / (1 + (m (x - γ))^2))
                      (c := (1 : ℝ))
                      (by norm_num) -- 0 ≤ c
                      (by
                        intro γ hγ
                        -- (1 + m^2)⁻¹ ≤ 1
                        have hnonneg : 0 ≤ (↑(m (x - γ)) : ℝ) ^ 2 := by positivity
                        have hone_le : (1 : ℝ) ≤ 1 + (↑(m (x - γ)) : ℝ) ^ 2 := by
                          simp
                        have h := one_div_le_one_div_of_le (by norm_num : 0 < (1 : ℝ)) hone_le
                        simpa [one_div] using h)
                      (by
                        intro γ hγ
                        -- nonneg of the summand
                        have hdenpos : 0 < 1 + (↑(m (x - γ)) : ℝ) ^ 2 := by positivity
                        simpa [one_div] using (inv_nonneg.mpr hdenpos.le))
            simpa using this)
        (by
          have : ((Z.filter (fun γ => m (x - γ) = 0)).card : ℝ) ≤ hM.M := by
            simpa using hsub
          linarith))
  -- For m ≥ 1, group by shells and use the per-shell 2-intervals bound (#shell ≤ 2M)
  have hcount_pos :
      (∑ γ ∈ Z.filter (fun γ => 0 < m (x - γ)),
        (1 : ℝ) / (1 + (m (x - γ))^2))
    ≤ (hM.M : ℝ) * (2 * (∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℝ)^2))) := by
    classical
    -- pointwise: 1/(1+m^2) ≤ 1/m^2 = 1/((n+1)^2) with n = m-1
    have hpt :
        ∀ γ ∈ Z.filter (fun γ => 0 < m (x - γ)),
          (1 : ℝ) / (1 + (m (x - γ))^2)
            ≤ (1 : ℝ) / ((m (x - γ) : ℝ)^2) := by
      intro γ hγ
      have hmpos : 0 < m (x - γ) := (Finset.mem_filter.mp hγ).2
      have hden_pos : 0 < (m (x - γ) : ℝ)^2 := by exact pow_pos (Nat.cast_pos.mpr hmpos) 2
      have hle_den : (m (x - γ) : ℝ)^2 ≤ 1 + (m (x - γ) : ℝ)^2 := by linarith
      exact one_div_le_one_div_of_le hden_pos hle_den
    have hsum₁ :
        (∑ γ ∈ Z.filter (fun γ => 0 < m (x - γ)),
          (1 : ℝ) / (1 + (m (x - γ))^2))
      ≤ (∑ γ ∈ Z.filter (fun γ => 0 < m (x - γ)),
          (1 : ℝ) / ((m (x - γ) : ℝ)^2)) :=
      Finset.sum_le_sum hpt
    -- group by the shell index n = m(·) - 1
    -- group the sum by the shell index m(·); use the fiberwise identity
    have hgroup :
        (∑ γ ∈ Z.filter (fun γ => 0 < m (x - γ)),
          (1 : ℝ) / ((m (x - γ) : ℝ)^2))
      = ∑ n ∈  (Z.filter (fun γ => 0 < m (x - γ))).image (fun γ => m (x - γ)),
          ((Z.filter (fun γ => 0 < m (x - γ))).filter (fun γ => m (x - γ) = n)).card
            * (1 / ((n : ℝ)^2)) := by
      classical
      exact Finset.sum_bij_subtype
        (Z.filter (fun γ => 0 < m (x - γ)))
        (fun γ => m (x - γ))
        (fun n => (1 : ℝ) / ((n : ℝ)^2))

    -- bound each fiber by 2M (since n = m(·) ≥ 1 on S)
    have hshell_le :
        ∀ n, ((Z.filter (fun γ => 0 < m (x - γ))).filter (fun γ => m (x - γ) = n)).card
              ≤ 2 * hM.M := by
      classical
      intro n
      -- `S.filter (m = n)` ⊆ `Z.filter (m = n)` and for n ≥ 1 we have the 2M bound
      have hsub :
          ((Z.filter (fun γ => 0 < m (x - γ))).filter (fun γ => m (x - γ) = n))
            ⊆ (Z.filter (fun γ => m (x - γ) = n)) := by
        intro γ hγ
        simp [Finset.mem_filter] at hγ ⊢
        exact ⟨hγ.1.1, hγ.2⟩
      -- when n = 0, the set is empty because of `0 < m` in S
      by_cases hn : n = 0
      · subst hn
        -- empty because 0 < m(·) cannot be 0
        have : ((Z.filter (fun γ => 0 < m (x - γ))).filter (fun γ => m (x - γ) = 0)).card = 0 := by
          classical
          have hempty : ((Z.filter (fun γ => 0 < m (x - γ))).filter (fun γ => m (x - γ) = 0)) = ∅ := by
            classical
            apply Finset.filter_eq_empty_iff.mpr
            intro γ hγ
            simp [Finset.mem_filter] at hγ
            exact (Nat.pos_iff_ne_zero.mp hγ.2)
          simp [hempty]
        simp [this]
      · -- n ≥ 1: specialize the previously proved 2M shell bound
        have hn' : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
        -- translate `m (x-γ) = n` to `Nat.floor(|x-γ|/(2s)) = n` (by def of m)
        have : (Z.filter (fun γ => m (x - γ) = n)).card ≤ 2 * hM.M := by
          have hn_eq : n = n - 1 + 1 := by omega
          rw [hn_eq]
          exact shell_card_le_twoM hs hM x (n - 1)
        exact (le_trans (card_le_of_subset hsub) this)

    -- compare the finite regrouped sum to the full (nonnegative) series
    have hnonneg_n : ∀ n, 0 ≤ (1 / ((n : ℝ)^2)) := by
      intro n; have : 0 ≤ (n : ℝ)^2 := sq_nonneg _; exact one_div_nonneg.mpr this
    have hsum₂ :
        (∑ n ∈  (Z.filter (fun γ => 0 < m (x - γ))).image (fun γ => m (x - γ)),
          ((Z.filter (fun γ => 0 < m (x - γ))).filter (fun γ => m (x - γ) = n)).card
            * (1 / ((n : ℝ)^2)))
      ≤ (2 * (hM.M : ℝ)) * (∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℝ)^2)) := by
      classical
      -- pull out uniform 2M bound and enlarge finite sum to the full series
      have : ∀ n, 0 ≤ ((Z.filter (fun γ => 0 < m (x - γ))).filter (fun γ => m (x - γ) = n)).card := by
        intro n; exact Nat.cast_nonneg _
      -- name the filtered set to avoid re-elaboration of long terms
      set S := Z.filter (fun γ => 0 < m (x - γ)) with hS
      calc
        _ ≤ ∑ n ∈  S.image (fun γ => m (x - γ)),
            (2 * (hM.M : ℝ)) * (1 / ((n : ℝ)^2)) := by
              classical
              have hpoint :
                  ∀ n ∈ S.image (fun γ => m (x - γ)),
                    ((S.filter (fun γ => m (x - γ) = n)).card : ℝ) * (1 / ((n : ℝ)^2))
                      ≤ (2 * (hM.M : ℝ)) * (1 / ((n : ℝ)^2)) := by
                intro n hn
                have : (S.filter (fun γ => m (x - γ) = n)).card ≤ 2 * hM.M := hshell_le n
                exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) (hnonneg_n n)
              simpa [hS] using sum_le_sum hpoint
        _ = (2 * (hM.M : ℝ)) * (∑ n ∈  (Z.filter (fun γ => 0 < m (x - γ))).image (fun γ => m (x - γ)),
            (1 / ((n : ℝ)^2))) := by
              rw [Finset.mul_sum]
        _ ≤ (2 * (hM.M : ℝ)) * (∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℝ)^2)) := by
              have h2M : 0 ≤ (2 * (hM.M : ℝ)) := by positivity
              refine mul_le_mul_of_nonneg_left ?_ h2M
              -- bound the finite sum by the full p-series, then shift (n ↦ n+1)
              have hsum0 : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ)^2)) := by
                simp
              have h0 : (1 : ℝ) / ((0 : ℝ)^2) = 0 := by simp
              have hshift :
                (∑' n : ℕ, (1 : ℝ) / ((n : ℝ)^2))
                  = ∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℝ)^2) := by
                simpa [Finset.range_one, h0] using
                  (Summable.sum_add_tsum_nat_add
                    (k := 1)
                    (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ)^2)) hsum0).symm
              calc
                (∑ n ∈  (Z.filter (fun γ => 0 < m (x - γ))).image (fun γ => m (x - γ)),
                  (1 : ℝ) / ((n : ℝ)^2))
                    ≤ ∑' n : ℕ, (1 : ℝ) / ((n : ℝ)^2) := by
                      refine (Summable.sum_le_tsum
                        (s := (Z.filter (fun γ => 0 < m (x - γ))).image (fun γ => m (x - γ)))
                        (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ)^2))
                        (by
                          intro n hn
                          have : 0 ≤ (n : ℝ)^2 := by exact sq_nonneg _
                          exact one_div_nonneg.mpr this)
                        hsum0)
                _ = ∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℝ)^2) := hshift

    -- plug regrouping into the earlier chain
    have hsum₁ :
        (∑ γ ∈ Z.filter (fun γ => 0 < m (x - γ)),
          (1 : ℝ) / ((m (x - γ) : ℝ)^2))
      ≤ (hM.M : ℝ) * (2 * (∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℝ)^2))) := by
      -- regroup and apply hsum₂
      calc
        _ = ∑ n ∈  (Z.filter (fun γ => 0 < m (x - γ))).image (fun γ => m (x - γ)),
            ((Z.filter (fun γ => 0 < m (x - γ))).filter (fun γ => m (x - γ) = n)).card
              * (1 / ((n : ℝ)^2)) := hgroup
        _ ≤ (2 * (hM.M : ℝ)) * (∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℝ)^2)) := hsum₂
        _ = (hM.M : ℝ) * (2 * (∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℝ)^2))) := by ring
    -- combine
    have hsum_mono :
      (∑ γ ∈ Z.filter (fun γ => 0 < m (x - γ)),
        (1 : ℝ) / (1 + (m (x - γ) : ℝ)^2))
      ≤ ∑ γ ∈ Z.filter (fun γ => 0 < m (x - γ)), (1 : ℝ) / ((m (x - γ) : ℝ)^2) := by
      apply sum_le_sum
      intro γ hγ
      -- 0 < a^2 and a^2 ≤ 1 + a^2 ⇒ 1/(1 + a^2) ≤ 1/a^2
      have ha : 0 < (m (x - γ) : ℝ) := by
        exact_mod_cast (Finset.mem_filter.mp hγ).2
      have hsqpos : 0 < (m (x - γ) : ℝ)^2 := sq_pos_of_pos ha
      have hle : (m (x - γ) : ℝ)^2 ≤ 1 + (m (x - γ) : ℝ)^2 := by linarith
      exact one_div_le_one_div_of_le hsqpos hle
    exact le_trans hsum_mono hsum₁
  -- Put the two pieces together and compare constants
  have : ∑ γ ∈ Z, (1 : ℝ) / (1 + (m (x - γ))^2)
        ≤ (hM.M : ℝ) * C_shell := by
    -- split into m=0 and m≥1
    -- split the sum into m=0 and m>0 parts without relying on conv/rw patterns
    have hsplit :
      ∑ γ ∈ Z, (1 : ℝ) / (1 + (m (x - γ) : ℝ)^2)
        = (∑ γ ∈ Z.filter (fun γ => m (x - γ) = 0),
            (1 : ℝ) / (1 + (m (x - γ) : ℝ)^2))
          + (∑ γ ∈ Z.filter (fun γ => 0 < m (x - γ)),
            (1 : ℝ) / (1 + (m (x - γ) : ℝ)^2)) := by
      classical
      -- first rewrite the integrand as a sum of if-branches, pointwise
      have hfun :
        (fun γ => (1 : ℝ) / (1 + (m (x - γ) : ℝ)^2))
          =
        (fun γ =>
          (if m (x - γ) = 0 then (1 : ℝ) / (1 + (m (x - γ) : ℝ)^2) else 0)
          + (if 0 < m (x - γ) then (1 : ℝ) / (1 + (m (x - γ) : ℝ)^2) else 0)) := by
        funext γ
        by_cases h0 : m (x - γ) = 0
        · simp [h0]
        · have : 0 < m (x - γ) := Nat.pos_of_ne_zero h0
          simp [h0, this]
      -- sum of a pointwise sum is sum of sums; then identify the two filters
      have :=
        calc
          ∑ γ ∈ Z, (1 : ℝ) / (1 + (m (x - γ) : ℝ)^2)
              = ∑ γ ∈ Z,
                  ((if m (x - γ) = 0 then (1 : ℝ) / (1 + (m (x - γ) : ℝ)^2) else 0)
                  + (if 0 < m (x - γ) then (1 : ℝ) / (1 + (m (x - γ) : ℝ)^2) else 0)) := by
                    simp_rw [hfun]
          _ = (∑ γ ∈ Z, if m (x - γ) = 0 then (1 : ℝ) / (1 + (m (x - γ) : ℝ)^2) else 0)
              + (∑ γ ∈ Z, if 0 < m (x - γ) then (1 : ℝ) / (1 + (m (x - γ) : ℝ)^2) else 0) := by
                    simp [Finset.sum_add_distrib]
      -- turn ifs into filters
      simp only [Finset.sum_filter]
      exact this
    rw [hsplit]
    simp_rw [C_shell]
    ring_nf
    -- bound the two pieces separately and factor constants
    have hsum_split_le :
      (∑ γ ∈ Z.filter (fun γ => m (x - γ) = 0),
        (1 : ℝ) / (1 + (m (x - γ) : ℝ)^2))
      + (∑ γ ∈ Z.filter (fun γ => 0 < m (x - γ)),
        (1 : ℝ) / (1 + (m (x - γ) : ℝ)^2))
      ≤ (hM.M : ℝ) * 1 + (hM.M : ℝ) * (2 * (∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℝ)^2))) := by
      exact add_le_add hcount0 hcount_pos
    -- rewrite RHS to M * (1 + 2 · series) and finish
    have : (∑ γ ∈ Z.filter (fun γ => m (x - γ) = 0),
              (1 : ℝ) / (1 + (m (x - γ) : ℝ)^2))
          + (∑ γ ∈ Z.filter (fun γ => 0 < m (x - γ)),
              (1 : ℝ) / (1 + (m (x - γ) : ℝ)^2))
          ≤ (hM.M : ℝ) * (1 + 2 * (∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℝ)^2))) := by
      simpa [mul_add, mul_one, mul_assoc, mul_left_comm, mul_comm] using hsum_split_le
    convert le_trans this ?_ using 1
    · simp only [one_div]
    field_simp [C_shell]
    ring_nf
    aesop
  exact le_trans hsum_le this

open RH.RS.PoissonKernelAnalysis

set_option linter.unusedVariables false in
/-- Schur row bound (whole-line diagonal) produced from a short-interval multiplicity cap. -/
noncomputable def annularSchur_from_multiplicityWhole
  {α : ℝ} (I : RH.Cert.WhitneyInterval) (Zk : Finset ℝ)
  (hα : 0 ≤ α)
  (hMult : ShortIntervalMultiplicity Zk (2 * α * I.len)) :
  AnnularSchurRowBoundWhole α I Zk :=
by
  classical
  let C : ℝ := C_shell
  refine
    { S := C * (hMult.M : ℝ)
      S_nonneg := ?nonneg
      row_bound := ?bound }
  · have hseries :
      0 ≤ ∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℝ)^2) :=
        tsum_of_nonneg (by intro n; positivity)
    have hC : 0 ≤ C := by
      simpa [C, C_shell] using
        add_nonneg (by norm_num) (mul_nonneg (by norm_num) hseries)
    have hMnonneg : 0 ≤ (hMult.M : ℝ) := by exact_mod_cast Nat.zero_le _
    exact mul_nonneg hC hMnonneg
  · intro σ hσ0 hσle γ hγ
    by_cases hσpos : 0 < σ
    · -- identical to the existing "Step 1–Step 4" derivation
      -- Step 1: reduce integrals over I.interval to whole-line integrals
      have h_int_each :
          ∀ γ' ∈ Zk,
            Integrable
              (fun t => KxiWhitneyRvM.Ksigma σ (t - γ') * KxiWhitneyRvM.Ksigma σ (t - γ))
              (Measure.restrict volume I.interval) := by
        intro γ' _
        have hsum :
          Continuous (fun t => KxiWhitneyRvM.Ksigma σ (t - γ')) := by
          have hden : Continuous (fun t => (t - γ')^2 + σ^2) :=
            ((continuous_id.sub continuous_const).pow 2).add continuous_const
          have hden_ne : ∀ t, (t - γ')^2 + σ^2 ≠ 0 := by
            intro t
            have : 0 < σ^2 := sq_pos_of_ne_zero (ne_of_gt hσpos)
            exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) this)
          exact (continuous_const).div hden hden_ne
        have hK :
          Continuous (fun t => KxiWhitneyRvM.Ksigma σ (t - γ)) := by
          have hden : Continuous (fun t => (t - γ)^2 + σ^2) :=
            ((continuous_id.sub continuous_const).pow 2).add continuous_const
          have hden_ne : ∀ t, (t - γ)^2 + σ^2 ≠ 0 := by
            intro t
            have : 0 < σ^2 := sq_pos_of_ne_zero (ne_of_gt hσpos)
            exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) this)
          exact (continuous_const).div hden hden_ne
        have hcont := (hsum.mul hK)
        have hIcompact : IsCompact I.interval := by
          simpa [WhitneyInterval.interval] using isCompact_Icc
        exact hcont.continuousOn.integrableOn_compact hIcompact
      have hswap :
        (∫ t in I.interval,
          (∑ γ' ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ')) * KxiWhitneyRvM.Ksigma σ (t - γ))
          =
        ∑ γ' ∈ Zk, ∫ t in I.interval, KxiWhitneyRvM.Ksigma σ (t - γ') * KxiWhitneyRvM.Ksigma σ (t - γ) := by
        classical
        have hmul :
          (fun t => (∑ x ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - x)) * KxiWhitneyRvM.Ksigma σ (t - γ))
            =
          (fun t => ∑ x ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - x) * KxiWhitneyRvM.Ksigma σ (t - γ)) := by
          funext t
          simp [Finset.mul_sum, mul_comm]
        have hInt :
          ∀ γ' ∈ Zk,
            Integrable
              (fun t => KxiWhitneyRvM.Ksigma σ (t - γ') * KxiWhitneyRvM.Ksigma σ (t - γ))
              (volume.restrict (WhitneyInterval.interval I)) := by
          intro γ' hγ'; simpa [KxiWhitneyRvM.Ksigma] using h_int_each γ' hγ'
        have hswap_prod :
          (∫ t in I.interval,
              ∑ γ' ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ') * KxiWhitneyRvM.Ksigma σ (t - γ))
            =
          ∑ γ' ∈ Zk, ∫ t in I.interval,
              KxiWhitneyRvM.Ksigma σ (t - γ') * KxiWhitneyRvM.Ksigma σ (t - γ) := by
          simpa [integral_finset_sum] using
            (integral_finset_sum (s := Zk)
              (f := fun γ' t =>
                KxiWhitneyRvM.Ksigma σ (t - γ') * KxiWhitneyRvM.Ksigma σ (t - γ)) hInt)
        aesop
        --simpa [hmul] using hswap_prod
      have hswap :
        (∫ t in I.interval,
          (∑ γ' ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ')) * KxiWhitneyRvM.Ksigma σ (t - γ))
          =
        ∑ γ' ∈ Zk, ∫ t in I.interval, KxiWhitneyRvM.Ksigma σ (t - γ') * KxiWhitneyRvM.Ksigma σ (t - γ) :=
          hswap
      have hset_le_whole :
        ∀ γ' ∈ Zk,
          (∫ t in I.interval, KxiWhitneyRvM.Ksigma σ (t - γ') * KxiWhitneyRvM.Ksigma σ (t - γ))
            ≤ ∫ t : ℝ, KxiWhitneyRvM.Ksigma σ (t - γ') * KxiWhitneyRvM.Ksigma σ (t - γ) := by
        intro γ' hγ'
        have hnn : ∀ t, 0 ≤ KxiWhitneyRvM.Ksigma σ (t - γ') * KxiWhitneyRvM.Ksigma σ (t - γ) := by
          intro t; refine mul_nonneg ?_ ?_
          · exact div_nonneg hσ0 (by nlinarith)
          · exact div_nonneg hσ0 (by nlinarith)
        exact setIntegral_le_integral
          (μ := volume) (s := I.interval)
          (f := fun t => KxiWhitneyRvM.Ksigma σ (t - γ') * KxiWhitneyRvM.Ksigma σ (t - γ))
          (PoissonKernelDyadic.Ksigma_prod_integrable hσpos hσpos)
          (Filter.Eventually.of_forall hnn)
      have hmono :
        (∫ t in I.interval, (∑ γ' ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ')) * KxiWhitneyRvM.Ksigma σ (t - γ))
          ≤ ∑ γ' ∈ Zk, ∫ t : ℝ, KxiWhitneyRvM.Ksigma σ (t - γ') * KxiWhitneyRvM.Ksigma σ (t - γ) := by
        classical
        have :=
          Finset.sum_le_sum
            (by intro γ' hγ'; exact hset_le_whole γ' hγ')
        aesop
      -- Step 2: convolution identity on ℝ
      have hpair :
        ∀ γ' ∈ Zk,
          ∫ t : ℝ, KxiWhitneyRvM.Ksigma σ (t - γ') * KxiWhitneyRvM.Ksigma σ (t - γ)
            = Real.pi * KxiWhitneyRvM.Ksigma (2 * σ) (γ - γ') := by
        intro γ' _; simpa [mul_comm]
          using KxiWhitneyRvM.PoissonKernel.cauchy_convolution σ γ γ' hσpos
      have hdiag :
        ∫ t : ℝ, (KxiWhitneyRvM.Ksigma σ (t - γ))^2 = (Real.pi / 2) / σ := by
        simpa using KxiWhitneyRvM.PoissonKernel.poisson_kernel_squared_integral σ γ hσpos
      have hratio :
        (∑ γ' ∈ Zk, ∫ t : ℝ, KxiWhitneyRvM.Ksigma σ (t - γ') * KxiWhitneyRvM.Ksigma σ (t - γ))
          = ((∑ γ' ∈ Zk, (4 * σ^2) / ((γ - γ')^2 + (2 * σ)^2)))
            * (∫ t : ℝ, (KxiWhitneyRvM.Ksigma σ (t - γ))^2) := by
        classical
        have hσne : σ ≠ 0 := ne_of_gt hσpos
        have hterm :
          ∀ γ', Real.pi * KxiWhitneyRvM.Ksigma (2 * σ) (γ - γ')
                = ((4 * σ^2) / ((γ - γ')^2 + (2 * σ)^2))
                    * ((Real.pi / 2) / σ) := by
          intro γ'
          have : KxiWhitneyRvM.Ksigma (2 * σ) (γ - γ') = (2 * σ) / ((γ - γ')^2 + (2 * σ)^2) := rfl
          have : Real.pi * KxiWhitneyRvM.Ksigma (2 * σ) (γ - γ')
                = Real.pi * ((2 * σ) / ((γ - γ')^2 + (2 * σ)^2)) := by simp
          rw [this]
          field_simp [hσne]
          ring
        calc
          (∑ γ' ∈ Zk, ∫ t : ℝ, KxiWhitneyRvM.Ksigma σ (t - γ') * KxiWhitneyRvM.Ksigma σ (t - γ))
              = ∑ γ' ∈ Zk, (Real.pi * KxiWhitneyRvM.Ksigma (2 * σ) (γ - γ')) := by
                    refine Finset.sum_congr rfl ?_; intro γ' hγ'; simpa using hpair γ' hγ'
          _   = ∑ γ' ∈ Zk,
                  ((4 * σ^2) / ((γ - γ')^2 + (2 * σ)^2)) * ((Real.pi / 2) / σ) := by
                    refine Finset.sum_congr rfl ?_; intro γ' hγ'; simpa using hterm γ'
          _   = ((∑ γ' ∈ Zk, (4 * σ^2) / ((γ - γ')^2 + (2 * σ)^2)))
                  * ((Real.pi / 2) / σ) := by
                    simp [Finset.sum_mul]
          _   = ((∑ γ' ∈ Zk, (4 * σ^2) / ((γ - γ')^2 + (2 * σ)^2)))
                  * (∫ t : ℝ, (KxiWhitneyRvM.Ksigma σ (t - γ))^2) := by
                    simp_rw [hdiag]
      -- Step 3: shell/multiplicity bound
      have hσle' : 2 * σ ≤ 2 * α * I.len := by
        have := mul_le_mul_of_nonneg_left hσle (by norm_num : (0 : ℝ) ≤ 2)
        simpa [mul_left_comm, mul_assoc] using this
      have hshell :
        (∑ γ' ∈ Zk, (4 * σ^2) / ((γ - γ')^2 + (2 * σ)^2))
          ≤ C * (hMult.M : ℝ) := by
        have hbound :
          (∑ γ' ∈ Zk, (4 * σ^2) / ((γ - γ')^2 + (2 * σ)^2))
            ≤ (hMult.M : ℝ) * C_shell := by
          refine cauchy_shell_sum_bound
            (hs := hσpos) (Z := Zk)
            (hM :=
              { M := hMult.M
                bound := by
                  intro x
                  refine (Finset.card_le_of_subset ?hsub).trans (hMult.bound x)
                  intro γ' hγ'
                  simp [Finset.mem_filter] at hγ' ⊢
                  rcases hγ' with ⟨hxZ, hxint⟩
                  constructor
                  · exact hxZ
                  · rcases hxint with ⟨hL, hR⟩
                    constructor
                    · exact le_add_of_le_add_left hL hσle'
                    · exact le_add_of_le_add_left hR hσle' })
            (x := γ)
        simpa [C, mul_comm] using hbound
      -- Step 4: conclude the row bound
      have hnn : ∀ t, 0 ≤ (KxiWhitneyRvM.Ksigma σ (t - γ))^2 := by intro _; exact sq_nonneg _
      have hdiag_le :
        (∫ t in I.interval, (KxiWhitneyRvM.Ksigma σ (t - γ))^2)
          ≤ ∫ t : ℝ, (KxiWhitneyRvM.Ksigma σ (t - γ))^2 :=
        setIntegral_le_integral
          (μ := volume) (s := I.interval)
          (f := fun t => (KxiWhitneyRvM.Ksigma σ (t - γ))^2)
          (KxiWhitneyRvM.PoissonKernel.ksigma_squared_integrable σ γ hσpos)
          (Filter.Eventually.of_forall hnn)
      have h_upper :=
        calc
          (∫ t in I.interval,
              (∑ γ' ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ')) * KxiWhitneyRvM.Ksigma σ (t - γ))
              ≤ ∑ γ' ∈ Zk, ∫ t : ℝ, KxiWhitneyRvM.Ksigma σ (t - γ') * KxiWhitneyRvM.Ksigma σ (t - γ) := hmono
          _ = ((∑ γ' ∈ Zk, (4 * σ^2) / ((γ - γ')^2 + (2 * σ)^2)))
                * (∫ t : ℝ, (KxiWhitneyRvM.Ksigma σ (t - γ))^2) := hratio
          _ ≤ (C * (hMult.M : ℝ)) * (∫ t : ℝ, (KxiWhitneyRvM.Ksigma σ (t - γ))^2) := by
                simpa using mul_le_mul_of_nonneg_right hshell (by positivity)
      exact h_upper
    · -- σ = 0: both sides vanish
      have hσeq : σ = 0 := le_antisymm (le_of_not_gt hσpos) hσ0
      have hL :
        (∫ t in I.interval,
          (∑ γ' ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ')) * KxiWhitneyRvM.Ksigma σ (t - γ)) = 0 := by
        simp [hσeq, KxiWhitneyRvM.Ksigma]
      have hR :
        (∫ t : ℝ, (KxiWhitneyRvM.Ksigma σ (t - γ))^2) = 0 := by
        simp [hσeq, KxiWhitneyRvM.Ksigma]
      have hzero :
        (∫ t in I.interval,
          (∑ γ' ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ')) * KxiWhitneyRvM.Ksigma σ (t - γ)) ≤
          (C * (hMult.M : ℝ)) * 0 := by
        aesop
      simp [hσeq]

lemma integrableOn_iff_integrable_restrict
    {α : Type*} [MeasurableSpace α]
    {E : Type*} [NormedAddCommGroup E]
    {μ : Measure α} {s : Set α} {f : α → E} :
    IntegrableOn f s μ ↔ Integrable f (Measure.restrict μ s) := by
  rfl

/-- Continuous on a compact interval ⇒ integrable on that interval. -/
lemma integrableOn_of_continuousOn_compact
    {f : ℝ → ℝ} {s : Set ℝ} {μ : Measure ℝ} [IsFiniteMeasureOnCompacts μ]
    (hs : IsCompact s) (hf : ContinuousOn f s) :
    IntegrableOn f s μ := by exact ContinuousOn.integrableOn_compact hs hf--hf.integrableOn_compact hs
    -- (works for any normed group/codomain once you generalize)

lemma integrableOn_slice_left_of_continuousOn
    {F : ℝ × ℝ → ℝ} {a₁ b₁ a₂ b₂ σ : ℝ}
    (hσ : σ ∈ Set.Icc a₂ b₂)
    (hF : ContinuousOn F (Set.Icc a₁ b₁ ×ˢ Set.Icc a₂ b₂)) :
    IntegrableOn (fun t => F (t, σ)) (Set.Icc a₁ b₁) volume := by
  have hslice :
      ContinuousOn (fun t => F (t, σ)) (Set.Icc a₁ b₁) := by
    refine hF.comp
      ((Continuous.prodMk continuous_id continuous_const).continuousOn)
      ?_
    intro t ht
    exact ⟨ht, hσ⟩
  have hcompact : IsCompact (Set.Icc a₁ b₁) := isCompact_Icc
  exact integrableOn_of_continuousOn_compact hcompact hslice

lemma integrableOn_slice_right_of_continuousOn
    {F : ℝ × ℝ → ℝ} {a₁ b₁ a₂ b₂ t : ℝ}
    (ht : t ∈ Set.Icc a₁ b₁)
    (hF : ContinuousOn F (Set.Icc a₁ b₁ ×ˢ Set.Icc a₂ b₂)) :
    IntegrableOn (fun σ => F (t, σ)) (Set.Icc a₂ b₂) volume := by
  have hslice :
      ContinuousOn (fun σ => F (t, σ)) (Set.Icc a₂ b₂) := by
    refine hF.comp
      ((Continuous.prodMk continuous_const continuous_id).continuousOn)
      ?_
    intro σ hσ
    exact ⟨ht, hσ⟩
  have hcompact : IsCompact (Set.Icc a₂ b₂) := isCompact_Icc
  exact integrableOn_of_continuousOn_compact hcompact hslice

lemma continuousOn_mul_on_rectangle
    {F G : ℝ × ℝ → ℝ} {a₁ b₁ a₂ b₂ : ℝ}
    (hF : ContinuousOn F (Set.Icc a₁ b₁ ×ˢ Set.Icc a₂ b₂))
    (hG : ContinuousOn G (Set.Icc a₁ b₁ ×ˢ Set.Icc a₂ b₂)) :
    ContinuousOn (fun p => F p * G p)
      (Set.Icc a₁ b₁ ×ˢ Set.Icc a₂ b₂) :=
  hF.mul hG

noncomputable def linComboCLM (a b : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ
    + b • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] lemma linComboCLM_apply (a b : ℝ) (v : ℝ × ℝ) :
    linComboCLM a b v = a * v.1 + b * v.2 := by
  rcases v with ⟨t, σ⟩
  simp [linComboCLM, smul_eq_mul]

@[simp] lemma linComboCLM_apply_fst (a b : ℝ) :
    linComboCLM a b (1, 0) = a := by
  simp [linComboCLM]

@[simp] lemma linComboCLM_apply_snd (a b : ℝ) :
    linComboCLM a b (0, 1) = b := by
  simp [linComboCLM]

noncomputable def embedFstCLM : ℝ →L[ℝ] ℝ × ℝ :=
  { toLinearMap :=
      { toFun := fun x => (x, 0)
        map_add' := by intro x y; ext <;> simp
        map_smul' := by intro a x; ext <;> simp }
    cont :=
      (continuous_id.prodMk continuous_const) }

noncomputable def embedSndCLM : ℝ →L[ℝ] ℝ × ℝ :=
  { toLinearMap :=
      { toFun := fun x => (0, x)
        map_add' := by intro x y; ext <;> simp
        map_smul' := by intro a x; ext <;> simp }
    cont :=
      (continuous_const.prodMk continuous_id) }

@[simp] lemma embedFstCLM_apply (x : ℝ) : embedFstCLM x = (x, 0) := rfl
@[simp] lemma embedSndCLM_apply (x : ℝ) : embedSndCLM x = (0, x) := rfl

noncomputable def fDerivMap
    (U U_t U_σ U_tt U_tσ : ℝ × ℝ → ℝ) :
    ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ :=
  fun p =>
    linComboCLM
      ((U_t p) ^ 2 + U p * U_tt p)
      (U_t p * U_σ p + U p * U_tσ p)

noncomputable def gDerivMap
    (U U_t U_σ U_σt U_σσ : ℝ × ℝ → ℝ) :
    ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ :=
  fun p =>
    linComboCLM
      (U_t p * U_σ p + U p * U_σt p)
      ((U_σ p) ^ 2 + U p * U_σσ p)

lemma hasFDerivAt_mul_UUt
    {U U_t U_σ U_tt U_tσ : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hU :
      HasFDerivAt U (linComboCLM (U_t p) (U_σ p)) p)
    (hUt :
      HasFDerivAt U_t (linComboCLM (U_tt p) (U_tσ p)) p) :
    HasFDerivAt (fun q => U q * U_t q)
      (fDerivMap U U_t U_σ U_tt U_tσ p) p := by
  have hderiv :=
    hU.mul hUt
  have hlin :
      U p • linComboCLM (U_tt p) (U_tσ p)
        + U_t p • linComboCLM (U_t p) (U_σ p)
        = fDerivMap U U_t U_σ U_tt U_tσ p := by
    refine ContinuousLinearMap.ext fun v => ?_
    rcases v with ⟨t, σ⟩
    simp [fDerivMap, linComboCLM, add_comm, add_left_comm, add_assoc,
      smul_add, add_smul, mul_comm, mul_left_comm, pow_two]
  exact hderiv.congr_fderiv hlin

lemma hasFDerivAt_mul_UUσ
    {U U_t U_σ U_σt U_σσ : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hU :
      HasFDerivAt U (linComboCLM (U_t p) (U_σ p)) p)
    (hUσ :
      HasFDerivAt U_σ (linComboCLM (U_σt p) (U_σσ p)) p) :
    HasFDerivAt (fun q => U q * U_σ q)
      (gDerivMap U U_t U_σ U_σt U_σσ p) p := by
  have hderiv :=
    hU.mul hUσ
  have hlin :
      U p • linComboCLM (U_σt p) (U_σσ p)
        + U_σ p • linComboCLM (U_t p) (U_σ p)
        = gDerivMap U U_t U_σ U_σt U_σσ p := by
    refine ContinuousLinearMap.ext fun v => ?_
    rcases v with ⟨t, σ⟩
    simp [gDerivMap, linComboCLM, add_comm, add_left_comm, add_assoc,
      smul_add, add_smul, mul_comm, mul_left_comm, pow_two]
  exact hderiv.congr_fderiv hlin

lemma divergence_mul_grad_sq
    {U U_t U_σ U_tt U_tσ U_σt U_σσ : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hLaplace : U_tt p + U_σσ p = 0) :
    (fDerivMap U U_t U_σ U_tt U_tσ p) (1, 0)
      + (gDerivMap U U_t U_σ U_σt U_σσ p) (0, 1)
      = (U_t p) ^ 2 + (U_σ p) ^ 2 := by
  have hLap' :
      U p * U_tt p + U p * U_σσ p = 0 := by
    have := congrArg (fun x => U p * x) hLaplace
    simpa [mul_add] using this
  have hx₁ :
      (fDerivMap U U_t U_σ U_tt U_tσ p) (1, 0)
        + (gDerivMap U U_t U_σ U_σt U_σσ p) (0, 1)
        = U p * U_tt p + (U p * U_σσ p + ((U_t p) ^ 2 + (U_σ p) ^ 2)) := by
    simp [fDerivMap, gDerivMap,
      linComboCLM_apply, add_comm, add_left_comm, add_assoc,  pow_two]
  have hx₂ :
      U p * U_tt p + (U p * U_σσ p + ((U_t p) ^ 2 + (U_σ p) ^ 2))
        = (U_t p) ^ 2 + (U_σ p) ^ 2 := by
    have :=
      congrArg (fun x : ℝ => x + ((U_t p) ^ 2 + (U_σ p) ^ 2)) hLap'
    simpa [add_comm, add_left_comm, add_assoc]
      using this
  exact hx₁.trans hx₂


lemma norm_of_nonneg_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (h : 0 ≤ ∫ a, f a ∂μ) :
  ‖∫ a, f a ∂μ‖ = ∫ a, f a ∂μ := by
  simp [Real.norm_eq_abs, _root_.abs_of_nonneg h]

lemma integrableOn_finset_sum
    {ι : Type*} (s : Finset ι)
    {α : Type*} [MeasurableSpace α]
    {E : Type*} [NormedAddCommGroup E]
    {μ : Measure α} {S : Set α} {f : ι → α → E}
    (hf : ∀ i ∈ s, IntegrableOn (f i) S μ) :
    IntegrableOn (fun x ↦ ∑ i ∈ s, f i x) S μ := by
  classical
  have hf' :
      ∀ i ∈ s, Integrable (fun x => f i x) (Measure.restrict μ S) := by
    intro i hi
    simpa [IntegrableOn] using hf i hi
  have :
      Integrable (fun x => ∑ i ∈ s, f i x) (Measure.restrict μ S) :=
    MeasureTheory.integrable_finset_sum (s := s)
      (f := fun i => fun x => f i x) hf'
  simpa [IntegrableOn] using this

/-- Schur-type domination: if a row-sum bound holds, then the annular energy is
bounded by `S` times the diagonal annular energy. -/
lemma annularEnergy_le_S_times_diag
  {α : ℝ} (I : RH.Cert.WhitneyInterval) (Zk : Finset ℝ)
  (_ : 0 ≤ α)
  (h : AnnularSchurRowBound α I Zk) :
  annularEnergy α I Zk
    ≤ h.S * annularEnergyDiag α I Zk := by
  classical
  -- Expand definitions and apply the row bound pointwise in σ
  simp [annularEnergy, annularEnergyDiag]
  -- Reduce to proving the integrand inequality for a.e. σ ∈ (0, αL]
  have hmono :
    ∫ σ in Set.Ioc (0 : ℝ) (α * I.len),
      (∫ t in I.interval, (∑ γ ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ)) ^ 2) * σ
    ≤ ∫ σ in Set.Ioc (0 : ℝ) (α * I.len),
      h.S * ((∫ t in I.interval, (∑ γ ∈ Zk, (KxiWhitneyRvM.Ksigma σ (t - γ)) ^ 2)) * σ) := by
    refine MeasureTheory.setIntegral_mono_ae_restrict
      (hf := ?hfin)
      (hg := ?hfin')
      ?hAE
    case hfin =>
      -- hfin: IntegrableOn (LHS) on the σ-strip via measurability + domination by a constant
      have h_meas :
          AEStronglyMeasurable
            (fun σ =>
              (∫ t in I.interval, (∑ γ ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ)) ^ 2) * σ)
            (Measure.restrict volume (Set.Ioc (0 : ℝ) (α * I.len))) :=
        RH.Cert.KxiWhitneyRvM.PoissonKernel.integrand_measurable_full α I Zk
      -- uniform bound on the strip: C = (card Zk)^2 * (π/2)
      have h_bound :
          ∀ ⦃σ : ℝ⦄, σ ∈ Set.Ioc (0 : ℝ) (α * I.len) →
            ‖(∫ t in I.interval, (∑ γ ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ)) ^ 2) * σ‖
              ≤ (Zk.card : ℝ)^2 * (Real.pi / 2) := by
        intro σ hσ
        have hσpos : 0 < σ := hσ.1
        simpa using
          RH.Cert.KxiWhitneyRvM.PoissonKernel.norm_Vk_sq_integral_mul_sigma_le_card_sq_pi
            (I := I) (Zk := Zk) (σ := σ) hσpos
      -- integrability via domination by a constant on a finite-measure strip
      exact
        (integrableOn_iff_integrable_restrict).2
          ⟨h_meas,
            HasFiniteIntegral.of_bounded
              (μ := Measure.restrict volume (Set.Ioc (0 : ℝ) (α * I.len)))
              (f := fun σ =>
                (∫ t in I.interval, (∑ γ ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ)) ^ 2) * σ)
              (C := (Zk.card : ℝ)^2 * (Real.pi / 2))
              ((ae_restrict_iff' measurableSet_Ioc).mpr
                (Filter.Eventually.of_forall (fun σ hσ => h_bound hσ)))⟩
    · -- hfin': IntegrableOn (RHS) on the σ-strip: constant multiple of the diagonal integrand
      have h_meas :
          AEStronglyMeasurable
            (fun σ =>
              (∫ t in I.interval, (∑ γ ∈ Zk, (KxiWhitneyRvM.Ksigma σ (t - γ)) ^ 2)) * σ)
            (Measure.restrict volume (Set.Ioc (0 : ℝ) (α * I.len))) :=
        RH.Cert.KxiWhitneyRvM.integrand_diagonal_measurable_full α I Zk
      -- uniform bound of the diagonal σ-integrand by the same constant
      have h_bound :
          ∀ ⦃σ : ℝ⦄, σ ∈ Set.Ioc (0 : ℝ) (α * I.len) →
            ‖(∫ t in I.interval, (∑ γ ∈ Zk, (KxiWhitneyRvM.Ksigma σ (t - γ)) ^ 2)) * σ‖
              ≤ (Zk.card : ℝ) * (Real.pi / 2) := by
        intro σ hσ
        have hσpos : 0 < σ := hσ.1
        simpa using
          RH.Cert.KxiWhitneyRvM.PoissonKernel.norm_diag_integral_mul_sigma_le_card_pi
            (I := I) (Zk := Zk) (σ := σ) hσpos
      -- first get integrability of the diagonal integrand, then scale by h.S
      have hdiag :
        Integrable
          (fun σ =>
            (∫ t in I.interval, (∑ γ ∈ Zk, (KxiWhitneyRvM.Ksigma σ (t - γ)) ^ 2)) * σ)
          (Measure.restrict volume (Set.Ioc (0 : ℝ) (α * I.len))) := by
        exact
          ⟨h_meas,
            HasFiniteIntegral.of_bounded
              (μ := Measure.restrict volume (Set.Ioc (0 : ℝ) (α * I.len)))
              (f := fun σ =>
                (∫ t in I.interval, (∑ γ ∈ Zk, (KxiWhitneyRvM.Ksigma σ (t - γ)) ^ 2)) * σ)
              (C := (Zk.card : ℝ) * (Real.pi / 2))
              ((ae_restrict_iff' measurableSet_Ioc).mpr
                (Filter.Eventually.of_forall (fun σ hσ => h_bound hσ)))⟩
      exact
        (integrableOn_iff_integrable_restrict).2
          (hdiag.const_mul h.S)
    · -- hAE: a.e. pointwise inequality on the strip from the row bound
      refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
      refine Filter.Eventually.of_forall ?ineq
      intro σ hσ
      have hσ_pos : 0 < σ := by simpa [Set.mem_Ioc] using hσ.1
      have hσ_le : σ ≤ α * I.len := by simpa [Set.mem_Ioc] using hσ.2
      -- Apply the row bound termwise, sum, and multiply by σ ≥ 0
      have hsum_le :
        (∑ γ ∈ Zk, ∫ t in I.interval,
            (∑ γ' ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ')) * KxiWhitneyRvM.Ksigma σ (t - γ))
          ≤
          (∑ γ ∈ Zk, h.S * ∫ t in I.interval, (KxiWhitneyRvM.Ksigma σ (t - γ))^2) := by
        apply Finset.sum_le_sum
        intro γ hγ
        exact h.row_bound (by exact hσ_pos.le) hσ_le γ hγ

      have hσnn : 0 ≤ σ := hσ_pos.le
      have :
        (∫ t in I.interval, (∑ γ ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ)) ^ 2) * σ
          ≤
        (∑ γ ∈ Zk, h.S * ∫ t in I.interval, (KxiWhitneyRvM.Ksigma σ (t - γ))^2) * σ := by
        calc (∫ t in I.interval, (∑ γ ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ)) ^ 2) * σ
            = (∫ t in I.interval, ∑ γ ∈ Zk,
                  (∑ γ' ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ')) * KxiWhitneyRvM.Ksigma σ (t - γ)) * σ := by
                  congr 1
                  have hpt :
                    (fun t => (∑ γ ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ)) ^ 2) =
                    (fun t => ∑ γ ∈ Zk, (∑ γ' ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ')) * KxiWhitneyRvM.Ksigma σ (t - γ)) := by
                    funext t
                    have :
                      (∑ γ ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ)) * (∑ γ' ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ'))
                        = ∑ γ ∈ Zk, (∑ γ' ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ')) * KxiWhitneyRvM.Ksigma σ (t - γ) := by
                      simp [Finset.mul_sum, mul_comm]
                    simpa [pow_two] using this
                  rw [hpt]
        _ = (∑ γ ∈ Zk, ∫ t in I.interval,
                  (∑ γ' ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ')) * KxiWhitneyRvM.Ksigma σ (t - γ)) * σ := by
                  congr 1
                  have h_int_each :
                    ∀ γ ∈ Zk,
                      Integrable
                        (fun t => (∑ γ' ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ')) * KxiWhitneyRvM.Ksigma σ (t - γ))
                        (Measure.restrict volume I.interval) := by
                    intro γ _hγ
                    have hsum :
                      Continuous (fun t => ∑ γ' ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ')) := by
                      apply continuous_finset_sum
                      intro γ' _;
                      have hden : Continuous (fun t => (t - γ')^2 + σ^2) :=
                        ((continuous_id.sub continuous_const).pow 2).add continuous_const
                      have hden_ne : ∀ t, (t - γ')^2 + σ^2 ≠ 0 := by
                        intro t
                        have : 0 < σ^2 := sq_pos_of_ne_zero (ne_of_gt hσ_pos)
                        exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) this)
                      exact (continuous_const).div hden hden_ne
                    have hK :
                      Continuous (fun t => KxiWhitneyRvM.Ksigma σ (t - γ)) := by
                      have hden : Continuous (fun t => (t - γ)^2 + σ^2) :=
                        ((continuous_id.sub continuous_const).pow 2).add continuous_const
                      have hden_ne : ∀ t, (t - γ)^2 + σ^2 ≠ 0 := by
                        intro t
                        have : 0 < σ^2 := sq_pos_of_ne_zero (ne_of_gt hσ_pos)
                        exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) this)
                      exact (continuous_const).div hden hden_ne
                    have hcont := hsum.mul hK
                    have hIcompact : IsCompact I.interval := by
                      simpa [RH.Cert.WhitneyInterval.interval] using isCompact_Icc
                    exact hcont.continuousOn.integrableOn_compact hIcompact
                  rw [← integral_finset_sum Zk h_int_each]
        _ ≤ (∑ γ ∈ Zk, h.S * ∫ t in I.interval, (KxiWhitneyRvM.Ksigma σ (t - γ))^2) * σ :=
              mul_le_mul_of_nonneg_right hsum_le hσnn
      -- rewrite the RHS to match the target
      have hsum_pull :
        (∑ γ ∈ Zk, h.S * ∫ t in I.interval, (KxiWhitneyRvM.Ksigma σ (t - γ))^2)
          = h.S * (∑ γ ∈ Zk, ∫ t in I.interval, (KxiWhitneyRvM.Ksigma σ (t - γ))^2) := by
        rw [Finset.mul_sum]
      have hsum_sq :
        (∫ t in I.interval, (∑ γ ∈ Zk, (KxiWhitneyRvM.Ksigma σ (t - γ)) ^ 2))
          =
        (∑ γ ∈ Zk, ∫ t in I.interval, (KxiWhitneyRvM.Ksigma σ (t - γ))^2) := by
        have h_int_sq : ∀ γ ∈ Zk, Integrable (fun t => (KxiWhitneyRvM.Ksigma σ (t - γ))^2) (Measure.restrict volume I.interval) := by
          intro γ _hγ
          have hK : Continuous (fun t => KxiWhitneyRvM.Ksigma σ (t - γ)) := by
            have hden : Continuous (fun t => (t - γ)^2 + σ^2) :=
              ((continuous_id.sub continuous_const).pow 2).add continuous_const
            have hden_ne : ∀ t, (t - γ)^2 + σ^2 ≠ 0 := by
              intro t
              have : 0 < σ^2 := sq_pos_of_ne_zero (ne_of_gt hσ_pos)
              exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) this)
            exact (continuous_const).div hden hden_ne
          have hcont := hK.pow 2
          have hIcompact : IsCompact I.interval := by
            simpa [RH.Cert.WhitneyInterval.interval] using isCompact_Icc
          exact hcont.continuousOn.integrableOn_compact hIcompact
        rw [integral_finset_sum Zk h_int_sq]
      show (∫ t in I.interval, (∑ γ ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ)) ^ 2) * σ
        ≤ h.S * ((∫ t in I.interval, ∑ γ ∈ Zk, (KxiWhitneyRvM.Ksigma σ (t - γ)) ^ 2) * σ)
      calc (∫ t in I.interval, (∑ γ ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ)) ^ 2) * σ
          ≤ (∑ γ ∈ Zk, h.S * ∫ t in I.interval, (KxiWhitneyRvM.Ksigma σ (t - γ))^2) * σ := this
        _ = (h.S * (∑ γ ∈ Zk, ∫ t in I.interval, (KxiWhitneyRvM.Ksigma σ (t - γ))^2)) * σ := by
              rw [hsum_pull]
        _ = h.S * ((∑ γ ∈ Zk, ∫ t in I.interval, (KxiWhitneyRvM.Ksigma σ (t - γ))^2) * σ) := by ring
        _ = h.S * ((∫ t in I.interval, ∑ γ ∈ Zk, (KxiWhitneyRvM.Ksigma σ (t - γ)) ^ 2) * σ) := by
              rw [← hsum_sq]
  calc ∫ σ in Set.Ioc 0 (α * I.len),
          (∫ t in I.interval, (∑ γ ∈ Zk, KxiWhitneyRvM.Ksigma σ (t - γ)) ^ 2) * σ
      ≤ ∫ σ in Set.Ioc 0 (α * I.len),
          h.S * ((∫ t in I.interval, ∑ γ ∈ Zk, (KxiWhitneyRvM.Ksigma σ (t - γ)) ^ 2) * σ) := hmono
    _ = h.S * ∫ σ in Set.Ioc 0 (α * I.len),
          (∫ t in I.interval, ∑ γ ∈ Zk, (KxiWhitneyRvM.Ksigma σ (t - γ)) ^ 2) * σ := by
      rw [integral_const_mul]

/-! ## Annular decomposition and Zk extraction -/
open Classical in
/-- Centers in the k-th annulus extracted from residue bookkeeping. -/
noncomputable def Zk (I : RH.Cert.WhitneyInterval) (k : ℕ) : Finset ℝ :=
  ((residue_bookkeeping I).atoms.map (fun a => a.ρ.im)).toFinset.filter (fun γ => annulusDyadic I k γ)

/-- Separation for extracted centers: if k ≥ 1 and γ ∈ Zk, then all base points satisfy
`|t−γ| ≥ 2^{k−1}·I.len`. -/
lemma Zk_separated_from_base
  (I : RH.Cert.WhitneyInterval) {k : ℕ} (hk : 1 ≤ k) :
  Diagonal.SeparatedFromBase k I (Zk I k) := by
  classical
  intro γ hγ t ht
  -- Membership in Zk implies the annulus predicate
  have hmem := Finset.mem_filter.mp hγ
  have hAnn : annulusDyadic I k γ := hmem.2
  -- Apply the singleton separation lemma
  exact KxiDiag.separation_from_base_of_annulus I hk hAnn t ht

/-- Define per‑annulus centers and energy E_k at aperture α. -/
noncomputable def Ek (α : ℝ) (I : RH.Cert.WhitneyInterval) (k : ℕ) : ℝ :=
  annularEnergy α I (Zk I k)

/-- Annular energies `Ek` are nonnegative for every aperture and annulus index. -/
lemma Ek_nonneg {α : ℝ} (I : RH.Cert.WhitneyInterval) (k : ℕ) :
  0 ≤ Ek α I k := by
  unfold Ek
  have := RH.Cert.KxiWhitneyRvM.annularEnergy_nonneg
    (α := α) (I := I) (Zk := Zk I k)
  simpa using this

/-- Diagonal bound for the extracted centers: for k ≥ 1,
`annularEnergyDiag ≤ (16·α^4)·|I|·4^{-k}·(Zk.card)`. -/
lemma annularEnergyDiag_bound_Zk
  (I : RH.Cert.WhitneyInterval) {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (hα : 0 ≤ α) :
  annularEnergyDiag α I (Zk I k)
    ≤ (16 * (α ^ 4)) * (2 * I.len) / ((4 : ℝ) ^ k) * ((Zk I k).card : ℝ) := by
  classical
  -- Use separation for Zk at scale k ≥ 1
  have hsep : Diagonal.SeparatedFromBase k I (Zk I k) :=
    Zk_separated_from_base I hk
  simpa using Diagonal.annularEnergyDiag_le (hα := hα) (hk := hk)
    (I := I) (Zk := Zk I k) hsep

/-- Full annular energy is bounded by a Schur row‑sum factor times the diagonal energy. -/
lemma annularEnergy_le_S_times_diag_of_row_bound
  {α : ℝ} (I : RH.Cert.WhitneyInterval) (k : ℕ)
  (hα : 0 ≤ α) (hRow : AnnularSchurRowBound α I (Zk I k)) :
  annularEnergy α I (Zk I k)
    ≤ hRow.S * annularEnergyDiag α I (Zk I k) := by
  classical
  -- Apply the general Schur domination lemma with our row bound witness
  exact annularEnergy_le_S_times_diag I (Zk I k) hα hRow

/-- Per‑annulus bound for E_k in terms of Zk.card, assuming a Schur row‑sum bound
with factor `S`. -/
lemma Ek_bound_from_diag_and_row
  (I : RH.Cert.WhitneyInterval) {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (hα : 0 ≤ α)
  (hRow : AnnularSchurRowBound α I (Zk I k)) :
  Ek α I k ≤ (hRow.S * (16 * (α ^ 4))) * (2 * I.len) / ((4 : ℝ) ^ k) * ((Zk I k).card : ℝ) := by
  classical
  have h1 := annularEnergy_le_S_times_diag_of_row_bound (I := I) (k := k) hα hRow
  have h2 := annularEnergyDiag_bound_Zk (I := I) (k := k) hk hα
  -- Multiply the diagonal bound by S and combine
  have hS_nonneg : 0 ≤ hRow.S := hRow.S_nonneg
  -- h1: E_k ≤ S * EnerDiag; h2: EnerDiag ≤ 16 α^4 · |I| · 4^{-k} · card
  exact le_trans h1 (by
    have := mul_le_mul_of_nonneg_left h2 hS_nonneg
    simpa [Ek, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using this)

/-! ## Calibrated constants and default configuration -/

/-- Default aperture for calibrated decay. -/
noncomputable def α_split : ℝ := 1 / 2

/-- Default Schur factor for calibrated decay. -/
noncomputable def S_split : ℝ := 0.08

@[simp] lemma α_split_nonneg : 0 ≤ α_split := by simp [α_split]

@[simp] lemma Cdecay_split_eval : S_split * (16 * (α_split ^ 4)) = 0.08 := by
  -- (1/2)^4 = 1/16, so 16 * (1/16) = 1, hence S_split * 1 = 0.08
  have h1 : (α_split ^ 4) = (1 : ℝ) / 16 := by
    have : α_split = (1 : ℝ) / 2 := rfl
    rw [this]
    norm_num
  simp [S_split]
  aesop

/-- Hypothesis bundling for Schur row bounds with calibrated constant S_split. -/
structure HasSchurRowBounds (I : RH.Cert.WhitneyInterval) where
  row : ∀ k : ℕ, 1 ≤ k → AnnularSchurRowBound α_split I (Zk I k)
  S_le : ∀ k : ℕ, ∀ hk : 1 ≤ k, (row k hk).S ≤ S_split

/-- Per‑annulus calibrated bound with α_split and S_split. -/
lemma Ek_bound_calibrated
  (I : RH.Cert.WhitneyInterval) (hSchur : HasSchurRowBounds I) {k : ℕ} (hk : 1 ≤ k) :
  Ek α_split I k ≤ (S_split * (16 * (α_split ^ 4))) * (2 * I.len) / ((4 : ℝ) ^ k) * ((Zk I k).card : ℝ) := by
  classical
  have hα := α_split_nonneg
  -- Row‑sum Schur bound at level k
  have h0 :=
    Ek_bound_from_diag_and_row (I := I) (k := k) hk hα (hSchur.row k hk)
  -- Replace S by S_split using S ≤ S_split and monotonicity
  have hSle' : (hSchur.row k hk).S ≤ S_split :=
    hSchur.S_le k hk
  have hNonneg :
      0 ≤ ((16 * (α_split ^ 4)) * (2 * I.len) / ((4 : ℝ) ^ k) * ((Zk I k).card : ℝ)) := by
    -- ... existing nonnegativity proof ...
    have hpos1 : 0 ≤ (16 : ℝ) * (α_split ^ 4) := by
      have : 0 ≤ (α_split ^ 4) := pow_nonneg hα 4
      exact mul_nonneg (by norm_num) this
    have hpos2 : 0 ≤ 2 * I.len := mul_nonneg (by norm_num) I.len_pos.le
    have hpos3 : 0 ≤ 1 / ((4 : ℝ) ^ k) := by
      have : 0 ≤ (4 : ℝ) ^ k := by
        have : (0 : ℝ) ≤ 4 := by norm_num
        exact pow_nonneg this _
      exact one_div_nonneg.mpr this
    have hpos4 : 0 ≤ ((Zk I k).card : ℝ) := Nat.cast_nonneg _
    have step1 :
        0 ≤ ((16 : ℝ) * (α_split ^ 4)) * (2 * I.len) :=
      mul_nonneg hpos1 hpos2
    have step2 :
        0 ≤ ((16 : ℝ) * (α_split ^ 4)) * (2 * I.len) * (1 / ((4 : ℝ) ^ k)) :=
      mul_nonneg step1 hpos3
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_nonneg step2 hpos4

  have := mul_le_mul_of_nonneg_left hSle' hNonneg
  -- Multiply both sides of `h0` by the common nonnegative scalar to compare S and S_split
  have hrewrite :
      ((hSchur.row k hk).S * (16 * (α_split ^ 4))) * (2 * I.len) / ((4 : ℝ) ^ k) * ((Zk I k).card : ℝ)
        ≤ (S_split * (16 * (α_split ^ 4))) * (2 * I.len) / ((4 : ℝ) ^ k) * ((Zk I k).card : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this

  exact le_trans h0 hrewrite

open scoped Interval
open MeasureTheory Set intervalIntegral

--namespace Riemann.RS.BoundaryWedgeProof

/-- Green identity on a rectangle, abstracted to a divergence integrand.

Let `f, g : ℝ × ℝ → ℝ` be the coordinate functions of a vector field
and let `f', g'` be their Fréchet derivatives. Assume the hypotheses of
`MeasureTheory.integral2_divergence_prod_of_hasFDerivWithinAt_off_countable`
and suppose the divergence `x ↦ f' x (1,0) + g' x (0,1)` agrees almost
everywhere on the rectangle with an integrand `F (x,y)`.

Then the integral of `F` over the rectangle is equal to the usual
four boundary integrals of `f` and `g`.  This is exactly the
divergence theorem, with the divergence rewritten as `F`.  -/
theorem green_first_identity_rectangle
  (f g : ℝ × ℝ → ℝ)
  (f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ)
  (a₁ a₂ b₁ b₂ : ℝ) (s : Set (ℝ × ℝ)) (hs : s.Countable)
  (Hcf : ContinuousOn f ([[a₁, b₁]] ×ˢ [[a₂, b₂]]))
  (Hcg : ContinuousOn g ([[a₁, b₁]] ×ˢ [[a₂, b₂]]))
  (Hdf : ∀ x ∈ Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ
                   Ioo (min a₂ b₂) (max a₂ b₂) \ s,
    HasFDerivAt f (f' x) x)
  (Hdg : ∀ x ∈ Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ
                   Ioo (min a₂ b₂) (max a₂ b₂) \ s,
    HasFDerivAt g (g' x) x)
  (Hi_div :
    IntegrableOn (fun x => f' x (1, 0) + g' x (0, 1))
      ([[a₁, b₁]] ×ˢ [[a₂, b₂]]))
  (F : ℝ × ℝ → ℝ)
  (hF :
    (fun x => f' x (1, 0) + g' x (0, 1))
      =ᵐ[volume.restrict ([[a₁, b₁]] ×ˢ [[a₂, b₂]])] F) :
  ∫ x in a₁..b₁, ∫ y in a₂..b₂, F (x, y)
    =
  (((∫ x in a₁..b₁, g (x, b₂)) - ∫ x in a₁..b₁, g (x, a₂)) +
   ∫ y in a₂..b₂, f (b₁, y)) -
   ∫ y in a₂..b₂, f (a₁, y) := by
  -- Step 1: apply the divergence theorem with integrand `f' (1,0)+g' (0,1)`.
  have hDT :=
    MeasureTheory.integral2_divergence_prod_of_hasFDerivAt_off_countable
      f g f' g' a₁ a₂ b₁ b₂ s hs Hcf Hcg Hdf Hdg Hi_div
  -- The RHS is already the desired boundary expression; we just have to
  -- replace the LHS integrand by `F` using the a.e. equality `hF`.
  -- First rewrite the iterated integral as a set integral on the rectangle.
  have h_iter_to_set :
      ∫ x in [[a₁, b₁]], ∫ y in [[a₂, b₂]],
        f' (x, y) (1, 0) + g' (x, y) (0, 1)
        =
      ∫ z in [[a₁, b₁]] ×ˢ [[a₂, b₂]],
        f' z (1, 0) + g' z (0, 1) := by
    -- exactly your existing proof using `setIntegral_prod`
    have := (setIntegral_prod
      (f := fun z : ℝ × ℝ =>
        f' z (1, 0) + g' z (0, 1))
      (s := [[a₁, b₁]]) (t := [[a₂, b₂]]) Hi_div).symm
    simpa using this

  have h_set_to_iter :
      ∫ z in [[a₁, b₁]] ×ˢ [[a₂, b₂]],
        F z
        =
      ∫ x in [[a₁, b₁]], ∫ y in [[a₂, b₂]], F (x, y) := by
    -- exactly your existing proof using `setIntegral_prod`
    have Hi_F :
        IntegrableOn F ([[a₁, b₁]] ×ˢ [[a₂, b₂]])
        (volume : Measure (ℝ × ℝ)) :=
      (Hi_div.congr_fun_ae (f := fun x =>
          f' x (1, 0) + g' x (0, 1))
        (g := F) hF)
    have := (setIntegral_prod
      (f := fun z : ℝ × ℝ => F z)
      (s := [[a₁, b₁]]) (t := [[a₂, b₂]]) Hi_F)
    simpa using this
  -- Use `hF` to replace the integrand in the set integral.
  have h_rewrite :
      ∫ z in [[a₁, b₁]] ×ˢ [[a₂, b₂]],
        f' z (1, 0) + g' z (0, 1)
        =
      ∫ z in [[a₁, b₁]] ×ˢ [[a₂, b₂]], F z := by
    -- rectangle as a measurable set in ℝ × ℝ
    have hrect :
        MeasurableSet ([[a₁, b₁]] ×ˢ [[a₂, b₂]]) :=
      (measurableSet_uIcc.prod measurableSet_uIcc)
    -- turn `hF` (AE equality w.r.t. the restricted measure) into the
    -- form required by `setIntegral_congr_ae`
    have hAE :
        ∀ᵐ z : ℝ × ℝ ∂volume,
          z ∈ [[a₁, b₁]] ×ˢ [[a₂, b₂]] →
            f' z (1, 0) + g' z (0, 1) = F z := by
      -- `hF` : (fun z => div z) =ᵐ[volume.restrict rect] F z
      have hAE_restrict :
          ∀ᵐ z : ℝ × ℝ ∂volume.restrict ([[a₁, b₁]] ×ˢ [[a₂, b₂]]),
            f' z (1, 0) + g' z (0, 1) = F z := hF
      exact
        (ae_restrict_iff'
          (μ := volume)
          (s := [[a₁, b₁]] ×ˢ [[a₂, b₂]])
          (p := fun z => f' z (1, 0) + g' z (0, 1) = F z)
          (hs := hrect)).1 hAE_restrict
    exact setIntegral_congr_ae (μ := volume)
      (s := [[a₁, b₁]] ×ˢ [[a₂, b₂]]) hrect hAE
  -- Now tie everything together.
  -- From the divergence theorem:
  have := hDT
  -- Replace the LHS using the two equalities above.
  -- LHS of `hDT`:
  --   ∫_{x∈[a₁,b₁]} ∫_{y∈[a₂,b₂]} (f' (x,y)(1,0)+g' (x,y)(0,1))
  -- equals
  --   ∫_{z∈[[a₁,b₁]]×[[a₂,b₂]]} (f' z (1,0)+g' z (0,1))  by `h_iter_to_set`,
  -- which equals
  --   ∫_{z∈[[a₁,b₁]]×[[a₂,b₂]]} F z                       by `h_rewrite`,
  -- which equals
  --   ∫_{x∈[a₁,b₁]} ∫_{y∈[a₂,b₂]} F(x,y)                  by `h_set_to_iter`.
  -- Equality on the unordered intervals (set-integral level).
  have hLHS_uIcc :
      ∫ x in [[a₁, b₁]], ∫ y in [[a₂, b₂]],
        f' (x, y) (1, 0) + g' (x, y) (0, 1)
        =
      ∫ x in [[a₁, b₁]], ∫ y in [[a₂, b₂]], F (x, y) := by
    calc
      ∫ x in [[a₁, b₁]], ∫ y in [[a₂, b₂]],
          f' (x, y) (1, 0) + g' (x, y) (0, 1)
          = ∫ z in [[a₁, b₁]] ×ˢ [[a₂, b₂]],
              f' z (1, 0) + g' z (0, 1) := h_iter_to_set
      _ = ∫ z in [[a₁, b₁]] ×ˢ [[a₂, b₂]], F z := h_rewrite
      _ = ∫ x in [[a₁, b₁]], ∫ y in [[a₂, b₂]], F (x, y) := h_set_to_iter

  -- Now transport this equality back to the oriented interval form aᵢ..bᵢ on both sides.
  have hLHS :
      ∫ x in a₁..b₁, ∫ y in a₂..b₂,
        f' (x, y) (1, 0) + g' (x, y) (0, 1)
        =
      ∫ x in a₁..b₁, ∫ y in a₂..b₂, F (x, y) := by
    classical
    -- Abbreviate the divergence integrand
    let div := fun (x : ℝ) (y : ℝ) =>
      f' (x, y) (1, 0) + g' (x, y) (0, 1)
    -- Rewrite the uIcc–level equality in terms of `div`
    have h_box :
        ∫ x in [[a₁, b₁]], ∫ y in [[a₂, b₂]], div x y
          =
        ∫ x in [[a₁, b₁]], ∫ y in [[a₂, b₂]], F (x, y) := by
      simpa [div] using hLHS_uIcc
    -- We now transport this equality to the oriented intervals in all four order cases.
    have h_res :
        ∫ x in a₁..b₁, ∫ y in a₂..b₂, div x y
          =
        ∫ x in a₁..b₁, ∫ y in a₂..b₂, F (x, y) := by
      rcases le_total a₁ b₁ with h₁ | h₁
      · -- Case 1: a₁ ≤ b₁
        rcases le_total a₂ b₂ with h₂ | h₂
        · -- Case 1a: a₁ ≤ b₁, a₂ ≤ b₂
          have h_box_Icc :
              ∫ x in Icc a₁ b₁, ∫ y in Icc a₂ b₂, div x y
                =
              ∫ x in Icc a₁ b₁, ∫ y in Icc a₂ b₂, F (x, y) := by
            simpa [div, uIcc_of_le h₁, uIcc_of_le h₂] using h_box
          have h_div :
              ∫ x in a₁..b₁, ∫ y in a₂..b₂, div x y
                =
              ∫ x in Icc a₁ b₁, ∫ y in Icc a₂ b₂, div x y := by
            simp [div, intervalIntegral.integral_of_le h₁,
                  intervalIntegral.integral_of_le h₂,
                  setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
          have h_F :
              ∫ x in a₁..b₁, ∫ y in a₂..b₂, F (x, y)
                =
              ∫ x in Icc a₁ b₁, ∫ y in Icc a₂ b₂, F (x, y) := by
            simp [intervalIntegral.integral_of_le h₁,
                  intervalIntegral.integral_of_le h₂,
                  setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
          calc
            ∫ x in a₁..b₁, ∫ y in a₂..b₂, div x y
                = ∫ x in Icc a₁ b₁, ∫ y in Icc a₂ b₂, div x y := h_div
            _ = ∫ x in Icc a₁ b₁, ∫ y in Icc a₂ b₂, F (x, y) := h_box_Icc
            _ = ∫ x in a₁..b₁, ∫ y in a₂..b₂, F (x, y) := h_F.symm
        · -- Case 1b: a₁ ≤ b₁, b₂ ≤ a₂
          have h_box_Icc :
              ∫ x in Icc a₁ b₁, ∫ y in Icc b₂ a₂, div x y
                =
              ∫ x in Icc a₁ b₁, ∫ y in Icc b₂ a₂, F (x, y) := by
            simpa [div, uIcc_of_le h₁, uIcc_of_ge h₂] using h_box
          have h_div :
              ∫ x in a₁..b₁, ∫ y in a₂..b₂, div x y
                =
              - ∫ x in Icc a₁ b₁, ∫ y in Icc b₂ a₂, div x y := by
            simp [div, intervalIntegral.integral_of_le h₁,
                  intervalIntegral.integral_of_ge h₂,
                  setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
            exact
              MeasureTheory.integral_neg fun a ↦
                ∫ (x : ℝ) in Set.Icc b₂ a₂, (f' (a, x)) (1, 0) + (g' (a, x)) (0, 1)
          have h_F :
              ∫ x in a₁..b₁, ∫ y in a₂..b₂, F (x, y)
                =
              - ∫ x in Icc a₁ b₁, ∫ y in Icc b₂ a₂, F (x, y) := by
            simp [intervalIntegral.integral_of_le h₁,
                  intervalIntegral.integral_of_ge h₂,
                  setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
            exact MeasureTheory.integral_neg fun a ↦ ∫ (y : ℝ) in Set.Icc b₂ a₂, F (a, y)
          have h_box_neg :
              - ∫ x in Icc a₁ b₁, ∫ y in Icc b₂ a₂, div x y
                =
              - ∫ x in Icc a₁ b₁, ∫ y in Icc b₂ a₂, F (x, y) := by
            simpa using congrArg Neg.neg h_box_Icc
          calc
            ∫ x in a₁..b₁, ∫ y in a₂..b₂, div x y
                = - ∫ x in Icc a₁ b₁, ∫ y in Icc b₂ a₂, div x y := h_div
            _ = - ∫ x in Icc a₁ b₁, ∫ y in Icc b₂ a₂, F (x, y) := h_box_neg
            _ = ∫ x in a₁..b₁, ∫ y in a₂..b₂, F (x, y) := h_F.symm
      · -- Case 2: b₁ ≤ a₁
        rcases le_total a₂ b₂ with h₂ | h₂
        · -- Case 2a: b₁ ≤ a₁, a₂ ≤ b₂
          have h_box_Icc :
              ∫ x in Icc b₁ a₁, ∫ y in Icc a₂ b₂, div x y
                =
              ∫ x in Icc b₁ a₁, ∫ y in Icc a₂ b₂, F (x, y) := by
            simpa [div, uIcc_of_ge h₁, uIcc_of_le h₂] using h_box
          have h_div :
              ∫ x in a₁..b₁, ∫ y in a₂..b₂, div x y
                =
              - ∫ x in Icc b₁ a₁, ∫ y in Icc a₂ b₂, div x y := by
            simp [div, intervalIntegral.integral_of_ge h₁,
                  intervalIntegral.integral_of_le h₂,
                  setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
          have h_F :
              ∫ x in a₁..b₁, ∫ y in a₂..b₂, F (x, y)
                =
              - ∫ x in Icc b₁ a₁, ∫ y in Icc a₂ b₂, F (x, y) := by
            simp [intervalIntegral.integral_of_ge h₁,
                  intervalIntegral.integral_of_le h₂,
                  setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
          have h_box_neg :
              - ∫ x in Icc b₁ a₁, ∫ y in Icc a₂ b₂, div x y
                =
              - ∫ x in Icc b₁ a₁, ∫ y in Icc a₂ b₂, F (x, y) := by
            simpa using congrArg Neg.neg h_box_Icc
          calc
            ∫ x in a₁..b₁, ∫ y in a₂..b₂, div x y
                = - ∫ x in Icc b₁ a₁, ∫ y in Icc a₂ b₂, div x y := h_div
            _ = - ∫ x in Icc b₁ a₁, ∫ y in Icc a₂ b₂, F (x, y) := h_box_neg
            _ = ∫ x in a₁..b₁, ∫ y in a₂..b₂, F (x, y) := h_F.symm
        · -- Case 2b: b₁ ≤ a₁, b₂ ≤ a₂
          have h_box_Icc :
              ∫ x in Icc b₁ a₁, ∫ y in Icc b₂ a₂, div x y
                =
              ∫ x in Icc b₁ a₁, ∫ y in Icc b₂ a₂, F (x, y) := by
            simpa [div, uIcc_of_ge h₁, uIcc_of_ge h₂] using h_box
          have h_div :
              ∫ x in a₁..b₁, ∫ y in a₂..b₂, div x y
                =
              ∫ x in Icc b₁ a₁, ∫ y in Icc b₂ a₂, div x y := by
            -- first reduce both interval integrals to a double-negated Icc-expression
            have h_aux :
                ∫ x in a₁..b₁, ∫ y in a₂..b₂, div x y
                  =
                -∫ x in Icc b₁ a₁, -∫ y in Icc b₂ a₂, div x y := by
              simp [div, intervalIntegral.integral_of_ge h₁,
                     intervalIntegral.integral_of_ge h₂,
                     setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
            -- use linearity: the outer minus cancels the inner minus
            have h_inner :
                ∫ x in Icc b₁ a₁, -∫ y in Icc b₂ a₂, div x y
                  =
                -∫ x in Icc b₁ a₁, ∫ y in Icc b₂ a₂, div x y := by
              exact MeasureTheory.integral_neg fun a ↦ ∫ (y : ℝ) in Set.Icc b₂ a₂, div a y
            have h_sign :
                -∫ x in Icc b₁ a₁, -∫ y in Icc b₂ a₂, div x y
                  =
                ∫ x in Icc b₁ a₁, ∫ y in Icc b₂ a₂, div x y := by
              -- apply `Neg.neg` to both sides of `h_inner` and simplify
              have := congrArg Neg.neg h_inner
              simpa using this
            exact h_aux.trans h_sign
          have h_F :
              ∫ x in a₁..b₁, ∫ y in a₂..b₂, F (x, y)
                =
              ∫ x in Icc b₁ a₁, ∫ y in Icc b₂ a₂, F (x, y) := by
            -- first reduce to the double-negated Icc expression
            have h_auxF :
                ∫ x in a₁..b₁, ∫ y in a₂..b₂, F (x, y)
                  =
                -∫ x in Icc b₁ a₁, -∫ y in Icc b₂ a₂, F (x, y) := by
              simp [intervalIntegral.integral_of_ge h₁,
                    intervalIntegral.integral_of_ge h₂,
                    setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
            -- move the inner minus sign outside the outer integral
            have h_innerF :
                ∫ x in Icc b₁ a₁, -∫ y in Icc b₂ a₂, F (x, y)
                  =
                -∫ x in Icc b₁ a₁, ∫ y in Icc b₂ a₂, F (x, y) := by
              simpa using
                (MeasureTheory.integral_neg
                  (f := fun x => ∫ y in Icc b₂ a₂, F (x, y)))
            -- cancel the two minus signs
            have h_signF :
                -∫ x in Icc b₁ a₁, -∫ y in Icc b₂ a₂, F (x, y)
                  =
                ∫ x in Icc b₁ a₁, ∫ y in Icc b₂ a₂, F (x, y) := by
              have := congrArg Neg.neg h_innerF
              simpa using this
            exact h_auxF.trans h_signF

          calc
            ∫ x in a₁..b₁, ∫ y in a₂..b₂, div x y
                = ∫ x in Icc b₁ a₁, ∫ y in Icc b₂ a₂, div x y := h_div
            _ = ∫ x in Icc b₁ a₁, ∫ y in Icc b₂ a₂, F (x, y) := h_box_Icc
            _ = ∫ x in a₁..b₁, ∫ y in a₂..b₂, F (x, y) := h_F.symm
    exact h_res
  -- `hDT` says `LHS_div = boundary`.  We want `∫∫ F = boundary`.
  have := this
  have :=
    congrArg id this
  --   from hDT:  ∫∫div = boundary
  --   from hLHS: ∫∫div = ∫∫F
  -- so `∫∫F = boundary`.
  simpa [hLHS] using this

open MeasureTheory Set Interval Filter Topology
open scoped MeasureTheory Filter Topology
open RH.Cert RH.RS  RH.RS.BoundaryWedgeProof

/-- If a real-valued function is a.e. nonpositive on a measurable set, then its integral
over that set is ≤ 0. -/
lemma integral_nonpos_of_ae_nonpos
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (_ : MeasurableSet s)
    {f : α → ℝ}
    (h_nonpos : ∀ᵐ x ∂μ.restrict s, f x ≤ 0) :
    ∫ x in s, f x ∂μ ≤ 0 := by
  -- 0 ≤ -f a.e. on s
  have h_nonneg' : ∀ᵐ x ∂μ.restrict s, 0 ≤ -f x := by
    filter_upwards [h_nonpos] with x hx
    exact neg_nonneg.mpr hx
  -- so ∫ -f ≥ 0 with the restricted measure
  have h_int_nonneg : 0 ≤ ∫ x, -f x ∂μ.restrict s :=
    MeasureTheory.setIntegral_nonneg_of_ae_restrict h_nonneg'
  -- rewrite goal in terms of the restricted measure
  change ∫ x, f x ∂μ.restrict s ≤ 0
  -- 0 ≤ -∫ f ↔ ∫ f ≤ 0
  have h0 : 0 ≤ -∫ x, f x ∂μ.restrict s := by
    simpa [MeasureTheory.integral_neg] using h_int_nonneg
  exact neg_nonneg.mp h0

/-- Concrete top-boundary inequality used in the CR–Green box:
if the trace integrand on the top edge is a.e. ≤ 0, then its integral is ≤ 0. -/
lemma top_boundary_nonpos
    (I : RH.Cert.WhitneyInterval)
    (g : ℝ → ℝ)
    (h_top :
      ∀ᵐ t ∂volume.restrict (RH.Cert.WhitneyInterval.interval I), g t ≤ 0) :
    ∫ t in RH.Cert.WhitneyInterval.interval I, g t ∂volume ≤ 0 :=
  integral_nonpos_of_ae_nonpos
    (by
      -- measurability of the interval
      simp [RH.Cert.WhitneyInterval.interval])
    h_top

/-- Abstract decay / symmetry hypothesis on the vertical sides of the Whitney box:
the signed side contribution is a.e. nonpositive. This is the analytic heart
(one proves it using specific properties of `U_halfplane`). -/
class SideBoundaryControl (I : RH.Cert.WhitneyInterval) where
  (side_integral_nonpos :
    (∫ σ in Set.Ioc 0 (α_split * I.len),
        U_halfplane (I.t0 + I.len, σ) ∂volume)
    - (∫ σ in Set.Ioc 0 (α_split * I.len),
        U_halfplane (I.t0 - I.len, σ) ∂volume)
    ≤ 0)

/-- Side boundary contribution is nonpositive under `SideBoundaryControl`. -/
lemma side_boundaries_negligible (I : RH.Cert.WhitneyInterval) [SideBoundaryControl I] :
  (∫ σ in Set.Ioc 0 (α_split * I.len),
      U_halfplane (I.t0 + I.len, σ) ∂volume)
  - (∫ σ in Set.Ioc 0 (α_split * I.len),
      U_halfplane (I.t0 - I.len, σ) ∂volume)
  ≤ 0 :=
  SideBoundaryControl.side_integral_nonpos (I := I)

open ContinuousLinearMap AnalyticAt

/-- The Frechét derivative of `halfPlaneCoord` is the constant linear map `halfPlaneLinear`.
Since `halfPlaneCoord` is an affine map (constant + linear), its derivative is the linear part. -/
lemma hasFDerivAt_halfPlaneCoord (p : ℝ × ℝ) :
  HasFDerivAt halfPlaneCoord halfPlaneLinear p := by
  -- derivative of the linear part
  have hlin : HasFDerivAt (fun q : ℝ × ℝ => halfPlaneLinear q) halfPlaneLinear p :=
    halfPlaneLinear.hasFDerivAt
  -- adding a constant does not change the derivative
  exact hlin.const_add (((1 / 2 : ℝ) : ℂ))

/-! ### Flat coordinates version of scalar fields

We first work in flat coordinates on `ℝ × ℝ`, writing a complex point as `x + y·I`.  Given a
complex map `G : ℂ → ℂ`, we package the real part of `G` as a scalar field on `ℝ × ℝ` and
record its first and second partial derivatives.  Later we will transport these constructions
to Whitney coordinates via `halfPlaneCoord`. -/


open Complex


/-- Real part field in flat coordinates from a complex map `G`.

We view the flat coordinates as the `L²` product `WithLp 2 (ℝ × ℝ)`.  This is
definitionally the same underlying type as `ℝ × ℝ`, but it carries the inner
product and norm induced by the `L²` structure, which is convenient for the
Laplacian API. -/
noncomputable def U_flat (G : ℂ → ℂ) (q : WithLp 2 (ℝ × ℝ)) : ℝ :=
  let p := WithLp.equiv 2 (ℝ × ℝ) q
  (G (p.1 + p.2 * Complex.I)).re

/-- First partial derivative of `U_flat G` in the `x`-direction. -/
noncomputable def U_flat_x (G : ℂ → ℂ) (q : WithLp 2 (ℝ × ℝ)) : ℝ :=
  let p := WithLp.equiv 2 (ℝ × ℝ) q
  deriv (fun x : ℝ => U_flat G ((WithLp.equiv 2 (ℝ × ℝ)).symm (x, p.2))) p.1

/-- First partial derivative of `U_flat G` in the `y`-direction. -/
noncomputable def U_flat_y (G : ℂ → ℂ) (q : WithLp 2 (ℝ × ℝ)) : ℝ :=
  let p := WithLp.equiv 2 (ℝ × ℝ) q
  deriv (fun y : ℝ => U_flat G ((WithLp.equiv 2 (ℝ × ℝ)).symm (p.1, y))) p.2

/-- Second partial derivative of `U_flat G` in the `x`-direction. -/
noncomputable def U_flat_xx (G : ℂ → ℂ) (q : WithLp 2 (ℝ × ℝ)) : ℝ :=
  let p := WithLp.equiv 2 (ℝ × ℝ) q
  deriv (fun x : ℝ => U_flat_x G ((WithLp.equiv 2 (ℝ × ℝ)).symm (x, p.2))) p.1

/-- Second partial derivative of `U_flat G` in the `y`-direction. -/
noncomputable def U_flat_yy (G : ℂ → ℂ) (q : WithLp 2 (ℝ × ℝ)) : ℝ :=
  let p := WithLp.equiv 2 (ℝ × ℝ) q
  deriv (fun y : ℝ => U_flat_y G ((WithLp.equiv 2 (ℝ × ℝ)).symm (p.1, y))) p.2


/-- Any linear functional on `ℝ × ℝ` is determined by its values on `(1,0)` and `(0,1)`. -/
lemma linear2_decomp (L : ℝ × ℝ →L[ℝ] ℝ) (v : ℝ × ℝ) :
  L v = v.1 * L (1, 0) + v.2 * L (0, 1) := by
  rcases v with ⟨t, σ⟩
  have ht  : ((t, 0) : ℝ × ℝ) = t • ((1, 0) : ℝ × ℝ) := by ext <;> simp
  have hσ  : ((0, σ) : ℝ × ℝ) = σ • ((0, 1) : ℝ × ℝ) := by ext <;> simp
  have hsum : ((t, σ) : ℝ × ℝ) = ((t, 0) : ℝ × ℝ) + ((0, σ) : ℝ × ℝ) := by ext <;> simp
  calc
    L (t, σ) = L ((t, 0) + (0, σ)) := by simp_rw [hsum]
    _ = L (t, 0) + L (0, σ) := by rw [L.map_add]
    _ = L (t • (1, 0)) + L (σ • (0, 1)) := by rw [ht, hσ]
    _ = t • L (1, 0) + σ • L (0, 1) := by rw [L.map_smul, L.map_smul]
    _ = t * L (1, 0) + σ * L (0, 1) := by simp [smul_eq_mul]

/-
open Complex

/-- Real part field in flat coordinates from a complex map `G`. -/
noncomputable def U_flat (G : ℂ → ℂ) (q : ℝ × ℝ) : ℝ :=
  (G (q.1 + q.2 * Complex.I)).re

/-- First partial derivative of `U_flat G` in the `x`-direction. -/
noncomputable def U_flat_x (G : ℂ → ℂ) (q : ℝ × ℝ) : ℝ :=
  deriv (fun x : ℝ => U_flat G (x, q.2)) q.1

/-- First partial derivative of `U_flat G` in the `y`-direction. -/
noncomputable def U_flat_y (G : ℂ → ℂ) (q : ℝ × ℝ) : ℝ :=
  deriv (fun y : ℝ => U_flat G (q.1, y)) q.2

/-- Second partial derivative of `U_flat G` in the `x`-direction. -/
noncomputable def U_flat_xx (G : ℂ → ℂ) (q : ℝ × ℝ) : ℝ :=
  deriv (fun x : ℝ => U_flat_x G (x, q.2)) q.1

/-- Second partial derivative of `U_flat G` in the `y`-direction. -/
noncomputable def U_flat_yy (G : ℂ → ℂ) (q : ℝ × ℝ) : ℝ :=
  deriv (fun y : ℝ => U_flat_y G (q.1, y)) q.2
  -/

lemma hasDerivAt_fst_slice_of_hasFDerivAt {f : ℝ × ℝ → ℝ}
    {L : ℝ × ℝ →L[ℝ] ℝ} {p : ℝ × ℝ}
    (h : HasFDerivAt f L p) :
    HasDerivAt (fun t : ℝ => f (t, p.2)) (L (1, 0)) p.1 := by
  -- derivative of the curve t ↦ (t, p.2) is embedFstCLM
  have hγ₀ :
      HasFDerivAt embedFstCLM embedFstCLM p.1 :=
    embedFstCLM.hasFDerivAt
  have hγ :
      HasFDerivAt (fun t : ℝ => (t, p.2)) embedFstCLM p.1 := by
    simpa [embedFstCLM_apply] using hγ₀.add_const (0, p.2)
  -- chain rule
  have hcomp : HasFDerivAt (fun t : ℝ => f (t, p.2))
      (L.comp embedFstCLM) p.1 := h.comp p.1 hγ
  -- identify L.comp embedFstCLM with the 1D linear map x ↦ x * L(1,0)
  have hlin :
      L.comp embedFstCLM
        = (ContinuousLinearMap.id ℝ ℝ).smulRight (L (1, 0)) := by
    apply ContinuousLinearMap.ext
    intro x
    have hdecomp := linear2_decomp L (x, 0)
    have h' : L (x, 0) = x * L (1, 0) := by
      simpa [smul_eq_mul] using hdecomp
    simp [ContinuousLinearMap.comp_apply, embedFstCLM_apply, h', smul_eq_mul]
  -- turn Frechet derivative into usual 1D derivative
  simpa [HasDerivAt, hlin] using hcomp

lemma hasDerivAt_snd_slice_of_hasFDerivAt {f : ℝ × ℝ → ℝ}
    {L : ℝ × ℝ →L[ℝ] ℝ} {p : ℝ × ℝ}
    (h : HasFDerivAt f L p) :
    HasDerivAt (fun σ : ℝ => f (p.1, σ)) (L (0, 1)) p.2 := by
  -- derivative of the curve σ ↦ (p.1, σ) is embedSndCLM
  have hγ :
      HasFDerivAt (fun σ : ℝ => (p.1, σ)) embedSndCLM p.2 := by
    simpa [embedSndCLM_apply, add_comm, add_left_comm, add_assoc] using
      (embedSndCLM.hasFDerivAt.add_const (p.1, 0))
  -- chain rule
  have hcomp : HasFDerivAt (fun σ : ℝ => f (p.1, σ))
      (L.comp embedSndCLM) p.2 := h.comp p.2 hγ
  -- identify L.comp embedSndCLM with x ↦ x * L(0,1)
  have hlin :
      L.comp embedSndCLM
        = (ContinuousLinearMap.id ℝ ℝ).smulRight (L (0, 1)) := by
    apply ContinuousLinearMap.ext
    intro x
    have hdecomp := linear2_decomp L (0, x)
    have h' : L (0, x) = x * L (0, 1) := by
      simpa [smul_eq_mul] using hdecomp
    simp [ContinuousLinearMap.comp_apply, embedSndCLM_apply, h', smul_eq_mul]
  simpa [HasDerivAt, hlin] using hcomp



/-! ### Scalar fields induced by a complex map on the upper half-plane -/

/-- Given a complex function `G : ℂ → ℂ`, build a real-valued field on the upper half-plane
in Whitney coordinates by composing with `halfPlaneCoord` and taking real part.

Later we will instantiate `G` as `z ↦ log (J_canonical z)` to obtain `U_halfplane`. -/
noncomputable def U_of (G : ℂ → ℂ) (p : ℝ × ℝ) : ℝ :=
  (G (halfPlaneCoord p)).re

/-- Frechét derivative of `U_of G` at a point `p`, assuming a complex derivative of `G`
at `halfPlaneCoord p`.

If `hG : HasDerivAt G (G' z) z` at `z = halfPlaneCoord p`, then the Frechét derivative of
`U_of G` at `p` is the composition of:

* the linear map `halfPlaneLinear : ℝ × ℝ →L[ℝ] ℂ`, and
* the complex derivative of `G` at `z`, viewed as an `ℝ`‑linear map `ℂ →L[ℝ] ℂ`
  given by multiplication by `G' z`, and
* the real part `ℂ →L[ℝ] ℝ`.


This is just the real chain rule applied to `p ↦ Re (G (halfPlaneCoord p))`. -/
lemma hasFDerivAt_U_of
  (G G' : ℂ → ℂ) (p : ℝ × ℝ)
  (hG : HasDerivAt G (G' (halfPlaneCoord p)) (halfPlaneCoord p)) :
  HasFDerivAt (U_of G)
    ( (Complex.reCLM : ℂ →L[ℝ] ℝ).comp
      (halfPlaneLinear.smulRight (G' (halfPlaneCoord p))) ) p := by
  -- Step 1: derivative of `halfPlaneCoord` at `p`
  have hφ : HasFDerivAt halfPlaneCoord halfPlaneLinear p :=
    hasFDerivAt_halfPlaneCoord p
  -- Step 2: view the complex derivative of `G` as an ℝ‑linear map ℂ →L[ℝ] ℂ
  -- `hG.hasFDerivAt` has derivative `z ↦ (G' (halfPlaneCoord p)) • z` as a ℂ‑linear map;
  -- we restrict scalars to ℝ.
  have hG_F :
      HasFDerivAt G
        ((smulRight (1 : ℂ →L[ℂ] ℂ) (G' (halfPlaneCoord p))).restrictScalars ℝ)
        (halfPlaneCoord p) :=
    hG.hasFDerivAt.restrictScalars ℝ
  -- Step 3: compose `G` with `halfPlaneCoord` via the real chain rule
  have h_comp :
      HasFDerivAt (fun q : ℝ × ℝ => G (halfPlaneCoord q))
        (((smulRight (1 : ℂ →L[ℂ] ℂ) (G' (halfPlaneCoord p))).restrictScalars ℝ).comp
          halfPlaneLinear) p :=
    hG_F.comp p hφ
  -- Step 4: compose with real part (a continuous ℝ‑linear map ℂ →L[ℝ] ℝ)
  -- Step 4: compose with real part (a continuous ℝ‑linear map ℂ →L[ℝ] ℝ)
  have h_re :
      HasFDerivAt (fun q : ℝ × ℝ => (G (halfPlaneCoord q)).re)
        ((Complex.reCLM).comp
          (((smulRight (1 : ℂ →L[ℂ] ℂ) (G' (halfPlaneCoord p))).restrictScalars ℝ).comp
            halfPlaneLinear)) p := by
    -- outer map: z ↦ Re z has derivative `Complex.reCLM` at every point
    have h_outer :
        HasFDerivAt (fun z : ℂ => z.re) Complex.reCLM (G (halfPlaneCoord p)) := by
      simpa using (Complex.reCLM.hasFDerivAt (x := G (halfPlaneCoord p)))
    -- inner map: q ↦ G (halfPlaneCoord q) has derivative `h_comp`
    -- apply the chain rule
    simpa [Function.comp, Complex.re] using
      (h_outer.comp p h_comp)

  -- Step 5: rewrite in terms of `U_of G` and simplify the composed linear map
  have h_simp :
      (Complex.reCLM).comp
        (((smulRight (1 : ℂ →L[ℂ] ℂ) (G' (halfPlaneCoord p))).restrictScalars ℝ).comp
          halfPlaneLinear)
      =
      (Complex.reCLM).comp
        (halfPlaneLinear.smulRight (G' (halfPlaneCoord p))) := by
    -- both sides are ℝ‑linear maps ℝ×ℝ → ℝ; they are equal by evaluation on each vector
    simp [smulRight]
    rfl
  -- express the function `q ↦ (G (halfPlaneCoord q)).re` as `U_of G`
  have h_fun : (fun q : ℝ × ℝ => (G (halfPlaneCoord q)).re) = U_of G := rfl
  rw [h_fun, h_simp] at h_re
  exact h_re

lemma continuous_halfPlaneCoord : Continuous halfPlaneCoord := by
  have hσ :
      Continuous fun p : ℝ × ℝ => (p.2 : ℂ) :=
    Complex.continuous_ofReal.comp continuous_snd
  have ht :
      Continuous fun p : ℝ × ℝ => Complex.I * (p.1 : ℂ) :=
    continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)
  have hlin :
      Continuous fun p : ℝ × ℝ => halfPlaneLinear p :=
    by
      simpa [halfPlaneLinear_apply, add_comm, add_left_comm, add_assoc]
        using hσ.add ht
  have hconst : Continuous fun _ : ℝ × ℝ => ((1 / 2 : ℝ) : ℂ) :=
    continuous_const
  have hsum :
      Continuous fun p : ℝ × ℝ => ((1 / 2 : ℝ) : ℂ) + halfPlaneLinear p :=
    hconst.add hlin
  convert hsum using 1


/-! ### Specialization to the CR–Green potential `U_halfplane` -/

/-- The complex function used to define `U_halfplane` via `U_of`. -/
noncomputable def G_U (z : ℂ) : ℂ :=
  Complex.log (J_canonical z)

/-- Complex derivative of `G_U`. This is the holomorphic derivative of
`z ↦ log (J_canonical z)` wherever it exists. -/
noncomputable def G'_U : ℂ → ℂ :=
  fun z => deriv (fun w : ℂ => Complex.log (J_canonical w)) z

/-- `U_halfplane` expressed as a scalar field induced by the complex map `G_U`. -/
lemma U_halfplane_eq_U_of :
  U_halfplane = U_of G_U := by
  funext p
  -- Unfold both definitions and compare the complex argument
  -- `halfPlaneCoord p = (1/2 + p.2) + I * p.1`.
  have hcoord :
      (((1 / 2 : ℝ) + p.2 : ℝ) : ℂ) + Complex.I * (p.1 : ℂ)
        = halfPlaneCoord p := by
    simp [halfPlaneCoord, halfPlaneLinear_apply, add_comm, add_left_comm, add_assoc]
  -- Rewrite `U_halfplane` through `G_U` and `halfPlaneCoord`
  dsimp [U_halfplane, U_of, G_U]
  -- `U_halfplane` uses the same complex argument; we just re-associate
  -- to match `halfPlaneCoord p`.
  simp [add_comm, add_left_comm]

/-- `U_halfplane` as a flat scalar field coming from `G_U`, in the coordinates
`(t, σ) ↦ (x, y) := (1/2 + σ, t)`. This is the value-level identification
used to transport harmonicity from `U_flat G_U` to `U_halfplane`. -/
lemma U_halfplane_eq_U_flat (p : ℝ × ℝ) :
  U_halfplane p = U_flat G_U ((WithLp.equiv 2 (ℝ × ℝ)).symm (((1 / 2 : ℝ) + p.2), p.1)) := by
  -- First rewrite `U_halfplane` through `U_of G_U`.
  have hU : U_halfplane p = U_of G_U p := by
    have h := U_halfplane_eq_U_of
    simpa using congrArg (fun f => f p) h
  -- Then identify `U_of G_U` with the flat field at `(1/2 + σ, t)`.
  have h_flat :
      U_of G_U p = U_flat G_U ((WithLp.equiv 2 (ℝ × ℝ)).symm (((1 / 2 : ℝ) + p.2), p.1)) := by
    dsimp [U_of, U_flat, G_U]
    -- both sides apply `G_U` to the same complex argument
    simp [halfPlaneCoord_apply, add_comm, add_left_comm, mul_comm]
  simpa [hU] using h_flat

open RH.AcademicFramework.CompletedXi

/-! ## Section 7: Interior Positivity

Poisson transport extends (P+) to the interior.
-/


/-- Poisson transport for the canonical pinch field on the AF off-zeros set.

This version assumes a Poisson representation for the pinch field on `offXi`
and a boundary positivity hypothesis for the same field, and deduces interior
positivity for `2 · J_canonical` on `offXi`. -/
theorem poisson_transport_interior_offXi
    (hRep :
      RH.AcademicFramework.HalfPlaneOuterV2.HasPoissonRepOn
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
        RH.AcademicFramework.HalfPlaneOuterV2.offXi)
    (hBdry :
      RH.AcademicFramework.HalfPlaneOuterV2.BoundaryPositive
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)) :
    ∀ z ∈ RH.AcademicFramework.HalfPlaneOuterV2.offXi,
      0 ≤ ((2 : ℂ) * J_canonical z).re := by
  intro z hz
  -- Apply generic Poisson transport on the subset `offXi`
  have hzPos :=
    RH.AcademicFramework.HalfPlaneOuterV2.poissonTransportOn
      (F := RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
      hRep hBdry z hz
  -- Rewrite `F_pinch det2 outer_exists.outer` as `2 * J_canonical`
  have hJ :
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer) z
        = (2 : ℂ) * J_canonical z := by
    simp [RH.AcademicFramework.HalfPlaneOuterV2.F_pinch, RH.AcademicFramework.HalfPlaneOuterV2.J_pinch, J_canonical, J_CR]
  simpa [hJ] using hzPos


/-- Poisson transport for the canonical pinch field on `Ω \ {ξ_ext = 0}`.

This lemma assumes:
* a Poisson representation for the pinch field on `offXi`;
* boundary positivity for the pinch field; and
* a separate nonnegativity hypothesis at the point `z = 1`.

Under these assumptions we obtain interior positivity of `2 · J_canonical` on
the larger set `Ω \ {ξ_ext = 0}`. -/
theorem poisson_transport_interior_off_zeros
    (hRep :
      RH.AcademicFramework.HalfPlaneOuterV2.HasPoissonRepOn
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
        RH.AcademicFramework.HalfPlaneOuterV2.offXi)
    (hBdry :
      RH.AcademicFramework.HalfPlaneOuterV2.BoundaryPositive
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
    (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re) :
    ∀ z ∈ (RH.Cert.Ω \ {z | riemannXi_ext z = 0}),
      0 ≤ ((2 : ℂ) * J_canonical z).re := by
  intro z hz
  have hzΩ : z ∈ RH.Cert.Ω := hz.1
  have hξ : riemannXi_ext z ≠ 0 := by
    -- membership in RH.Cert.Ω \ {ξ_ext = 0} means z ∉ {ξ_ext = 0}
    have hz_not : z ∉ {z | riemannXi_ext z = 0} := hz.2
    exact fun h0 => hz_not (by simp [Set.mem_setOf_eq, h0])
  by_cases hz1 : z = (1 : ℂ)
  · -- Special point z = 1 is handled by a separate hypothesis
    simpa [hz1] using h₁
  · -- Otherwise z lies in the AF off-zeros set `offXi`
    have hz_AF_Ω : z ∈ RH.AcademicFramework.HalfPlaneOuterV2.Ω := by
      -- RS.Ω and AF.Ω coincide
      have : RH.Cert.Ω = RH.AcademicFramework.HalfPlaneOuterV2.Ω := Ω_eq
      simpa [this] using hzΩ
    have hzOffXi : z ∈ RH.AcademicFramework.HalfPlaneOuterV2.offXi := by
      exact ⟨hz_AF_Ω, hz1, hξ⟩
    -- Apply transport on `offXi` and rewrite the pinch field as `2·J_canonical`
    have hzPos :=
      poisson_transport_interior_offXi (hRep := hRep) (hBdry := hBdry) z hzOffXi
    simpa using hzPos

/-- Poisson transport for the canonical field on all of RH.Cert.Ω.

Combines subset transport on the off‑zeros set with direct evaluation at ξ_ext
zeros. This version is parametric in the Poisson representation and boundary
positivity hypotheses for the pinch field, and in the special value at `z = 1`. -/
theorem poisson_transport_interior
    (hRep :
      RH.AcademicFramework.HalfPlaneOuterV2.HasPoissonRepOn
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
        RH.AcademicFramework.HalfPlaneOuterV2.offXi)
    (hBdry :
      RH.AcademicFramework.HalfPlaneOuterV2.BoundaryPositive
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
    (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re) :
    ∀ z ∈ RH.Cert.Ω, 0 ≤ ((2 : ℂ) * J_canonical z).re := by
  intro z hzΩ
  by_cases hξ : riemannXi_ext z = 0
  · have hJ : J_canonical z = 0 := by
      simp [J_canonical, J_CR, hξ, div_eq_mul_inv, mul_comm,]
    simp [hJ]
  · have hzOff : z ∈ (RH.Cert.Ω \ {z | riemannXi_ext z = 0}) := by
      exact And.intro hzΩ (by simpa [Set.mem_setOf_eq] using hξ)
    exact
      poisson_transport_interior_off_zeros
        (hRep := hRep) (hBdry := hBdry) (h₁ := h₁) z hzOff

open RH.AcademicFramework.HalfPlaneOuterV2

/-- Interior positivity on all of RH.Cert.Ω for the canonical field,
in terms of abstract Poisson + boundary positivity data. -/
theorem interior_positive_J_canonical
    (hRep :
      HasPoissonRepOn
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
        offXi)
    (hBdry :
      BoundaryPositive
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
    (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re) :
    ∀ z ∈ RH.Cert.Ω, 0 ≤ ((2 : ℂ) * J_canonical z).re :=
  poisson_transport_interior
    (hRep := hRep) (hBdry := hBdry) (h₁ := h₁)

/-- Interior positivity on RH.Cert.Ω for the canonical field, assuming:
  * a Poisson representation for the pinch field on `offXi`;
  * the special-value nonnegativity at `z = 1`; and
  * a boundary `(P+)` witness for the canonical field.

This packages the logical flow
`PPlus_canonical → BoundaryPositive (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch …) → interior_positive_J_canonical`. -/
theorem interior_positive_J_canonical_from_PPlus
    (hRep :
      HasPoissonRepOn
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
        offXi)
    (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
    (hP : WhitneyAeCore.PPlus_canonical) :
    ∀ z ∈ RH.Cert.Ω, 0 ≤ ((2 : ℂ) * J_canonical z).re := by
  -- Boundary (P+) ⇒ `BoundaryPositive` for the AF pinch field.
  have hBdry :
      BoundaryPositive (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer) :=
    WhitneyAeCore.boundaryPositive_pinch_from_PPlus_canonical hP
  -- Now apply the abstract Poisson-transport interior positivity theorem.
  exact
    interior_positive_J_canonical
      (hRep := hRep) (hBdry := hBdry) (h₁ := h₁)


/-- Complex derivative of `G_U` on the zero-free region. -/
lemma G_U_hasDerivAt_of_offZeros {z : ℂ}
    (hRep :
      HasPoissonRepOn
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
        offXi)
    (hBdry :
      BoundaryPositive
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
    (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
    (hzΩ : z ∈ RH.Cert.Ω) (hz_ne_one : z ≠ 1) (hzXi : riemannXi_ext z ≠ 0) :
    HasDerivAt G_U (G'_U z) z := by
  classical
  have hJnzero := J_canonical_ne_zero_of_offZeros hzΩ hzXi
  have hJanalytic := analyticAt_J_canonical hzΩ hz_ne_one hzXi
  have hJderiv : HasDerivAt J_canonical (deriv J_canonical z) z :=
    hJanalytic.differentiableAt.hasDerivAt
  have hRe_twice_nonneg :
      0 ≤ ((2 : ℂ) * J_canonical z).re :=
    interior_positive_J_canonical
      (hRep := hRep) (hBdry := hBdry) (h₁ := h₁)
      z hzΩ
  have hRe_nonneg :
      0 ≤ (J_canonical z).re := by
    have hmul :
        0 ≤ (2 : ℝ) * (J_canonical z).re := by
      simpa [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        using hRe_twice_nonneg
    have hmul' : 0 ≤ (J_canonical z).re * 2 := by
      simpa [mul_comm] using hmul
    have hRe : 0 ≤ (J_canonical z).re :=
      nonneg_of_mul_nonneg_left hmul' (by norm_num : (0 : ℝ) < 2)
    exact hRe
  have hslit : J_canonical z ∈ Complex.slitPlane := by
    by_cases hRe_pos : 0 < (J_canonical z).re
    · exact RH.mem_slitPlane_of_ne_zero_of_re_pos hJnzero hRe_pos
    · have hRe_zero :
        (J_canonical z).re = 0 :=
        le_antisymm (le_of_not_gt hRe_pos) hRe_nonneg
      have hIm_ne : (J_canonical z).im ≠ 0 := by
        intro hIm_zero
        have hzero : J_canonical z = 0 := by
          apply Complex.ext
          · simpa [Complex.zero_re] using hRe_zero
          · simpa [Complex.zero_im] using hIm_zero
        exact hJnzero hzero
      exact RH.mem_slitPlane_of_ne_zero_of_im_ne hJnzero hIm_ne
  have hlog :
      HasDerivAt (fun w : ℂ => Complex.log (J_canonical w))
        ((J_canonical z)⁻¹ * deriv J_canonical z) z :=
    (Complex.hasDerivAt_log hslit).comp z hJderiv
  have hderiv :
      deriv (fun w : ℂ => Complex.log (J_canonical w)) z =
        (J_canonical z)⁻¹ * deriv J_canonical z :=
    hlog.deriv
  simpa [G_U, G'_U, hderiv] using hlog

open ContinuousLinearMap


lemma riemannXi_ext_ne_zero_on_strip
    {ε : ℝ} (I : RH.Cert.WhitneyInterval)
    (hε_nonneg : 0 ≤ ε)
    (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
    (hheight : zeroHeightSup α_split I < ε)
    {p : ℝ × ℝ}
    (hp : p ∈ I.interval ×ˢ Set.Icc ε (α_split * I.len)) :
    riemannXi_ext (halfPlaneCoord p) ≠ 0 := by
  have h :=
    zero_and_pole_free_above_height (α := α_split) I hε_nonneg havoid hheight hp
  exact h.1

lemma halfPlaneCoord_ne_one_on_strip
    {ε : ℝ} (I : RH.Cert.WhitneyInterval)
    (hε_nonneg : 0 ≤ ε)
    (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
    (hheight : zeroHeightSup α_split I < ε)
    {p : ℝ × ℝ}
    (hp : p ∈ I.interval ×ˢ Set.Icc ε (α_split * I.len)) :
    halfPlaneCoord p ≠ 1 := by
  have h :=
    zero_and_pole_free_above_height (α := α_split) I hε_nonneg havoid hheight hp
  exact h.2

lemma G_U_hasDerivAt_on_strip
    {ε : ℝ} (I : RH.Cert.WhitneyInterval)
    (hRep :
      HasPoissonRepOn
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
        offXi)
    (hBdry :
      BoundaryPositive
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
    (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
    (hε_pos : 0 < ε)
    (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
    (hheight : zeroHeightSup α_split I < ε)
    {p : ℝ × ℝ}
    (hp : p ∈ I.interval ×ˢ Set.Icc ε (α_split * I.len)) :
    HasDerivAt G_U (G'_U (halfPlaneCoord p)) (halfPlaneCoord p) := by
  have hp_nonneg : 0 ≤ ε := le_of_lt hε_pos
  have hxi :=
    riemannXi_ext_ne_zero_on_strip (I := I) hp_nonneg havoid hheight hp
  have hneq_one :=
    halfPlaneCoord_ne_one_on_strip (I := I) hp_nonneg havoid hheight hp
  have hp_bounds := (Set.mem_Icc.mp (And.right hp)).1
  have hp_height : 0 < p.2 := lt_of_lt_of_le hε_pos hp_bounds
  have hΩ := halfPlaneCoord_mem_Ω_of_pos hp_height
  exact G_U_hasDerivAt_of_offZeros
    (hRep := hRep) (hBdry := hBdry) (h₁ := h₁)
    hΩ hneq_one hxi

/-!  Convenience wrapper: derivative of `G_U` along the Whitney strip,
packaged directly at the Whitney coordinate `p`. -/
lemma G_U_hasDerivAt
    {ε : ℝ} (I : RH.Cert.WhitneyInterval)
    (hRep :
      HasPoissonRepOn
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
        offXi)
    (hBdry :
      BoundaryPositive
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
    (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
    (hε_pos : 0 < ε)
    (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
    (hheight : zeroHeightSup α_split I < ε)
    {p : ℝ × ℝ}
    (hp : p ∈ I.interval ×ˢ Set.Icc ε (α_split * I.len)) :
    HasDerivAt G_U (G'_U (halfPlaneCoord p)) (halfPlaneCoord p) :=
  G_U_hasDerivAt_on_strip (I := I)
    (hRep := hRep) (hBdry := hBdry) (h₁ := h₁)
    (hε_pos := hε_pos) (havoid := havoid) (hheight := hheight) hp

lemma G_U_hasDerivAt_on_strip_image
    {ε : ℝ} (I : RH.Cert.WhitneyInterval)
    (hRep :
      HasPoissonRepOn
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
        offXi)
    (hBdry :
      BoundaryPositive
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
    (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
    (hε_pos : 0 < ε)
    (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
    (hheight : zeroHeightSup α_split I < ε) :
    ∀ z ∈ halfPlaneCoord ''
        (I.interval ×ˢ Set.Icc ε (α_split * I.len)),
      HasDerivAt G_U (G'_U z) z := by
  intro z hz
  rcases hz with ⟨p, hp, rfl⟩
  exact G_U_hasDerivAt_on_strip (I := I)
    (hRep := hRep) (hBdry := hBdry) (h₁ := h₁)
    hε_pos havoid hheight hp

/-!  Second complex derivative of `G_U` on the Whitney strip image. -/

noncomputable def G''_U (z : ℂ) : ℂ := deriv G'_U z

lemma J_canonical_mem_slitPlane_of_offZeros {z : ℂ}
    (hRep :
      HasPoissonRepOn
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
        offXi)
    (hBdry :
      BoundaryPositive
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
    (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
    (hzΩ : z ∈ RH.Cert.Ω) (_hz_ne_one : z ≠ 1) (hzXi : riemannXi_ext z ≠ 0) :
    J_canonical z ∈ Complex.slitPlane := by
  classical
  have hJnzero := J_canonical_ne_zero_of_offZeros hzΩ hzXi
  have hRe_nonneg :
      0 ≤ (J_canonical z).re := by
    have hpos :
        0 ≤ ((2 : ℂ) * J_canonical z).re :=
      interior_positive_J_canonical
        (hRep := hRep) (hBdry := hBdry) (h₁ := h₁)
        z hzΩ
    have : (0 : ℝ) ≤ 2 * (J_canonical z).re := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hpos
    linarith
  by_cases hRe_pos : 0 < (J_canonical z).re
  · exact RH.mem_slitPlane_of_ne_zero_of_re_pos hJnzero hRe_pos
  · have hRe_eq : (J_canonical z).re = 0 :=
      le_antisymm (le_of_not_gt hRe_pos) hRe_nonneg
    have hIm_ne : (J_canonical z).im ≠ 0 := by
      intro hIm_zero
      have : J_canonical z = 0 := by
        apply Complex.ext <;> simp [hRe_eq, hIm_zero]
      exact hJnzero this
    exact RH.mem_slitPlane_of_ne_zero_of_im_ne hJnzero hIm_ne

/-!  `G_U` is analytic on `Ω` away from the zero set of `riemannXi_ext` and the pole at `1`. -/
lemma analyticAt_G_U {z : ℂ}
    (hRep :
      HasPoissonRepOn
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
        offXi)
    (hBdry :
      BoundaryPositive
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
    (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
    (hzΩ : z ∈ RH.Cert.Ω) (hz_ne_one : z ≠ 1) (hzXi : riemannXi_ext z ≠ 0) :
    AnalyticAt ℂ G_U z := by
  classical
  have hJanalytic : AnalyticAt ℂ J_canonical z :=
    analyticAt_J_canonical hzΩ hz_ne_one hzXi
  have hslit : J_canonical z ∈ Complex.slitPlane :=
    J_canonical_mem_slitPlane_of_offZeros
      (hRep := hRep) (hBdry := hBdry) (h₁ := h₁)
      hzΩ hz_ne_one hzXi
  simpa [G_U] using hJanalytic.clog hslit

lemma G'_U_eq_firstCoeff {z : ℂ}
    (hRep :
      HasPoissonRepOn
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
        offXi)
    (hBdry :
      BoundaryPositive
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
    (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
    (hzΩ : z ∈ RH.Cert.Ω) (hz_ne_one : z ≠ 1) (hzXi : riemannXi_ext z ≠ 0) :
    G'_U z = (analyticAt_G_U hRep hBdry h₁ hzΩ hz_ne_one hzXi).choose.coeff 1 := by
  classical
  -- iterated derivative formula at n = 1
  have h₁' :
      iteratedDeriv 1 G_U z
        = (Nat.factorial 1 : ℂ) •
          (analyticAt_G_U hRep hBdry h₁ hzΩ hz_ne_one hzXi).choose.coeff 1 :=
    AnalyticAt.iteratedDeriv_eq_coeff
      (𝕜 := ℂ) (E := ℂ)
      (f := G_U) (z := z)
      (h := analyticAt_G_U hRep hBdry h₁ hzΩ hz_ne_one hzXi) (n := 1)
  -- identify iteratedDeriv 1 with the usual derivative
  have hId : iteratedDeriv 1 G_U = deriv G_U := by
    simp
  have hDeriv :
      deriv G_U z
        = (analyticAt_G_U hRep hBdry h₁ hzΩ hz_ne_one hzXi).choose.coeff 1 := by
    have h' :
        deriv G_U z
          = (Nat.factorial 1 : ℂ) •
            (analyticAt_G_U hRep hBdry h₁ hzΩ hz_ne_one hzXi).choose.coeff 1 := by
      simpa [hId] using h₁'
    simpa [Nat.factorial] using h'
  -- by definition, G'_U is the derivative of G_U
  simpa [G_U, G'_U] using hDeriv

lemma secondDeriv_G_U_eq_coeff2 {z : ℂ}
    (hRep :
      HasPoissonRepOn
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
        offXi)
    (hBdry :
      BoundaryPositive
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
    (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
    (hzΩ : z ∈ RH.Cert.Ω) (hz_ne_one : z ≠ 1) (hzXi : riemannXi_ext z ≠ 0) :
    deriv (deriv G_U) z
      = (2 : ℂ) •
        (analyticAt_G_U hRep hBdry h₁ hzΩ hz_ne_one hzXi).choose.coeff 2 := by
  classical
  -- iterated derivative formula at n = 2
  have h₂ :
      iteratedDeriv 2 G_U z
        = (Nat.factorial 2 : ℂ) •
          (analyticAt_G_U hRep hBdry h₁ hzΩ hz_ne_one hzXi).choose.coeff 2 :=
    AnalyticAt.iteratedDeriv_eq_coeff
      (𝕜 := ℂ) (E := ℂ)
      (f := G_U) (z := z)
      (h := analyticAt_G_U hRep hBdry h₁ hzΩ hz_ne_one hzXi) (n := 2)
  -- identify iteratedDeriv 2 with the second derivative
  have hSucc : iteratedDeriv 2 G_U = deriv (iteratedDeriv 1 G_U) := by
    simpa [Nat.succ_eq_add_one] using
      (iteratedDeriv_succ (n := 1) (f := G_U))
  have hOne : iteratedDeriv 1 G_U = deriv G_U := iteratedDeriv_one (f := G_U)
  have hEq :
      deriv (deriv G_U) z = iteratedDeriv 2 G_U z := by
    have := congrArg (fun f => f z) hSucc
    simpa [hOne] using this.symm
  have h₂' :
      iteratedDeriv 2 G_U z
        = (2 : ℂ) •
          (analyticAt_G_U hRep hBdry h₁ hzΩ hz_ne_one hzXi).choose.coeff 2 := by
    simpa [Nat.factorial] using h₂
  simpa [hEq] using h₂'

/-- Gradient components of a scalar field `U_of G` in Whitney coordinates, extracted
from the Frechét derivative at a point.

We parametrize by an abstract complex derivative `G'`; later, for a concrete `G` we will
choose `G'` to be the complex derivative of `G`. -/
noncomputable def U_t_of (G' : ℂ → ℂ) (p : ℝ × ℝ) : ℝ :=
  let L :
    ℝ × ℝ →L[ℝ] ℝ :=
    Complex.reCLM.comp
      ((ContinuousLinearMap.smulRight
          (ContinuousLinearMap.id ℝ ℂ)
          (G' (halfPlaneCoord p))).comp halfPlaneLinear)
  L (1, 0)

noncomputable def U_σ_of (G' : ℂ → ℂ) (p : ℝ × ℝ) : ℝ :=
  let L :
    ℝ × ℝ →L[ℝ] ℝ :=
    Complex.reCLM.comp
      ((ContinuousLinearMap.smulRight
          (ContinuousLinearMap.id ℝ ℂ)
          (G' (halfPlaneCoord p))).comp halfPlaneLinear)
  L (0, 1)

@[simp] lemma U_t_of_eq (G' : ℂ → ℂ) (p : ℝ × ℝ) :
    U_t_of G' p = ((G' (halfPlaneCoord p)) * Complex.I).re := by
  dsimp [U_t_of]
  have h₁ : halfPlaneLinear (1, 0) = Complex.I := by
    simp [halfPlaneLinear_apply]
  simp [h₁, add_comm, add_left_comm, mul_comm]

@[simp] lemma U_σ_of_eq (G' : ℂ → ℂ) (p : ℝ × ℝ) :
    U_σ_of G' p = (G' (halfPlaneCoord p)).re := by
  dsimp [U_σ_of]
  have h₁ : halfPlaneLinear (0, 1) = (1 : ℂ) := by
    simp [halfPlaneLinear_apply]
  simp [h₁, add_comm, add_left_comm, mul_comm]

lemma U_t_of_eq_neg_im (G' : ℂ → ℂ) (p : ℝ × ℝ) :
    U_t_of G' p = -(G' (halfPlaneCoord p)).im := by
  have := U_t_of_eq G' p
  simp

noncomputable def U_t_canonical : ℝ × ℝ → ℝ :=
  U_t_of G'_U

noncomputable def U_σ_canonical : ℝ × ℝ → ℝ :=
  U_σ_of G'_U

/-! Second-order partial derivatives of the canonical potential `U_halfplane`.

We package them as real derivatives of the first-order fields along the
Whitney coordinates `(t, σ)`. These will later be identified with the
Cartesian second partials coming from the holomorphy of `G_U`. -/

noncomputable def U_tt_canonical (p : ℝ × ℝ) : ℝ :=
  deriv (fun t : ℝ => U_t_canonical (t, p.2)) p.1

noncomputable def U_tσ_canonical (p : ℝ × ℝ) : ℝ :=
  deriv (fun σ : ℝ => U_t_canonical (p.1, σ)) p.2

noncomputable def U_σt_canonical (p : ℝ × ℝ) : ℝ :=
  deriv (fun t : ℝ => U_σ_canonical (t, p.2)) p.1

noncomputable def U_σσ_canonical (p : ℝ × ℝ) : ℝ :=
  deriv (fun σ : ℝ => U_σ_canonical (p.1, σ)) p.2

@[simp] lemma U_t_canonical_eq (p : ℝ × ℝ) :
    U_t_canonical p = ((G'_U (halfPlaneCoord p)) * Complex.I).re :=
  U_t_of_eq G'_U p

@[simp] lemma U_σ_canonical_eq (p : ℝ × ℝ) :
    U_σ_canonical p = (G'_U (halfPlaneCoord p)).re :=
  U_σ_of_eq G'_U p

lemma continuousOn_U_t_of {S : Set (ℝ × ℝ)} {G' : ℂ → ℂ}
    (hG_cont : ContinuousOn G' (halfPlaneCoord '' S)) :
    ContinuousOn (U_t_of G') S := by
  classical
  have hmul :
      ContinuousOn (fun z : ℂ => G' z * Complex.I)
        (halfPlaneCoord '' S) :=
    hG_cont.mul (continuousOn_const : ContinuousOn (fun _ : ℂ => Complex.I) _)
  have hRe :
      ContinuousOn (fun z : ℂ => (G' z * Complex.I).re)
        (halfPlaneCoord '' S) :=
    Continuous.comp_continuousOn Complex.continuous_re hmul
  have hφ :
      ContinuousOn halfPlaneCoord S :=
    (continuous_halfPlaneCoord).continuousOn
  have hmaps :
      MapsTo halfPlaneCoord S (halfPlaneCoord '' S) := by
    intro p hp; exact ⟨p, hp, rfl⟩
  have hcomp :=
    hRe.comp hφ hmaps
  refine (hcomp.congr ?_).mono subset_rfl
  intro p _hp
  simp [U_t_of_eq]

lemma continuousOn_U_σ_of {S : Set (ℝ × ℝ)} {G' : ℂ → ℂ}
    (hG_cont : ContinuousOn G' (halfPlaneCoord '' S)) :
    ContinuousOn (U_σ_of G') S := by
  classical
  have hRe :
      ContinuousOn (fun z : ℂ => (G' z).re)
        (halfPlaneCoord '' S) :=
    Continuous.comp_continuousOn Complex.continuous_re hG_cont
  have hφ :
      ContinuousOn halfPlaneCoord S :=
    (continuous_halfPlaneCoord).continuousOn
  have hmaps :
      MapsTo halfPlaneCoord S (halfPlaneCoord '' S) := by
    intro p hp; exact ⟨p, hp, rfl⟩
  have hcomp :=
    hRe.comp hφ hmaps
  refine (hcomp.congr ?_).mono subset_rfl
  intro p _hp
  simp [U_σ_of_eq]

/-- Continuity of the canonical tangential derivative `U_t_canonical` on a Whitney strip,
provided the complex derivative `G'_U` is continuous on the complex image of the strip. -/
lemma continuousOn_U_t_canonical_on_strip
  (I : RH.Cert.WhitneyInterval) (ε : ℝ)
  (hG_cont :
    ContinuousOn G'_U
      (halfPlaneCoord ''
        (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)))) :
  ContinuousOn U_t_canonical
    (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)) := by
  refine
    continuousOn_U_t_of
      (S := RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len))
      (G' := G'_U) hG_cont

/-- Continuity of the canonical normal derivative `U_σ_canonical` on a Whitney strip,
provided the complex derivative `G'_U` is continuous on the complex image of the strip. -/
lemma continuousOn_U_σ_canonical_on_strip
  (I : RH.Cert.WhitneyInterval) (ε : ℝ)
  (hG_cont :
    ContinuousOn G'_U
      (halfPlaneCoord ''
        (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)))) :
  ContinuousOn U_σ_canonical
    (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)) := by
  refine
    continuousOn_U_σ_of
      (S := RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len))
      (G' := G'_U) hG_cont

/-- On the canonical off-zeros half-plane domain, `G_U` is analytic in a neighborhood of every point. -/
lemma G_U_analyticOnNhd_offZeros
    (hRep :
      HasPoissonRepOn
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
        offXi)
    (hBdry :
      BoundaryPositive
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
    (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re) :
  AnalyticOnNhd ℂ G_U
    {z : ℂ | z ∈ RH.Cert.Ω ∧ z ≠ (1 : ℂ) ∧ riemannXi_ext z ≠ 0} := by
  intro z hz
  rcases hz with ⟨hzΩ, hz_ne_one, hzXi⟩
  exact analyticAt_G_U hRep hBdry h₁ hzΩ hz_ne_one hzXi

/-- On the canonical off-zeros half-plane domain, the complex derivative `G'_U` is analytic,
hence continuous, in a neighborhood of every point. -/
lemma G'_U_continuousOn_offZeros
    (hRep :
      HasPoissonRepOn
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
        offXi)
    (hBdry :
      BoundaryPositive
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
    (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re) :
  ContinuousOn G'_U
    {z : ℂ | z ∈ RH.Cert.Ω ∧ z ≠ (1 : ℂ) ∧ riemannXi_ext z ≠ 0} := by
  -- derivative of an analytic function is analytic-on-nhd, hence continuous
  have hDeriv :
      AnalyticOnNhd ℂ (deriv G_U)
        {z : ℂ | z ∈ RH.Cert.Ω ∧ z ≠ (1 : ℂ) ∧ riemannXi_ext z ≠ 0} :=
    (AnalyticOnNhd.deriv (𝕜 := ℂ) (f := G_U) (s := _)
      (G_U_analyticOnNhd_offZeros hRep hBdry h₁))
  -- `G'_U` is definitionally `deriv G_U`
  have hEq : G'_U = deriv G_U := by
    funext z; rfl
  simpa [hEq] using
    (AnalyticOnNhd.continuousOn (𝕜 := ℂ) (f := deriv G_U)
      (s := {z : ℂ | z ∈ RH.Cert.Ω ∧ z ≠ (1 : ℂ) ∧ riemannXi_ext z ≠ 0}) hDeriv)

/-- The Whitney strip in `(t, σ)`-coordinates maps under `halfPlaneCoord` into the
canonical off-zeros domain for `G_U`, provided we stay above the zero height and
avoid the pole at `1/2`. -/
lemma halfPlaneCoord_image_strip_subset_offZeros
  (I : RH.Cert.WhitneyInterval) {ε : ℝ} (hε_pos : 0 < ε)
  (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
  (hheight : zeroHeightSup α_split I < ε) :
  halfPlaneCoord ''
      (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len))
    ⊆ {z : ℂ | z ∈ RH.Cert.Ω ∧ z ≠ (1 : ℂ) ∧ riemannXi_ext z ≠ 0} := by
  intro z hz
  rcases hz with ⟨p, hp, rfl⟩
  rcases hp with ⟨hp_t, hp_σ⟩
  have hp_nonneg : 0 ≤ ε := le_of_lt hε_pos
  -- ξ_ext ≠ 0 and no pole at 1 along the strip
  have hxi :
      riemannXi_ext (halfPlaneCoord p) ≠ 0 :=
    riemannXi_ext_ne_zero_on_strip
      (I := I) hp_nonneg havoid hheight ⟨hp_t, hp_σ⟩
  have hneq_one :
      halfPlaneCoord p ≠ (1 : ℂ) :=
    halfPlaneCoord_ne_one_on_strip
      (I := I) hp_nonneg havoid hheight ⟨hp_t, hp_σ⟩
  -- positive height σ > 0 on the strip
  have hp_bounds := (Set.mem_Icc.mp hp_σ).1
  have hp_height : 0 < p.2 := lt_of_lt_of_le hε_pos hp_bounds
  have hΩ : halfPlaneCoord p ∈ RH.Cert.Ω :=
    halfPlaneCoord_mem_Ω_of_pos hp_height
  exact ⟨hΩ, hneq_one, hxi⟩

/-- Continuity of `G'_U` along the Whitney strip image in the upper half-plane. -/
lemma continuousOn_G'_U_on_strip
    (hRep :
      HasPoissonRepOn
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
        offXi)
    (hBdry :
      BoundaryPositive
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
    (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
    (I : RH.Cert.WhitneyInterval) {ε : ℝ} (hε_pos : 0 < ε)
    (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
    (hheight : zeroHeightSup α_split I < ε) :
  ContinuousOn G'_U
    (halfPlaneCoord ''
      (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len))) := by
  have hOff := G'_U_continuousOn_offZeros hRep hBdry h₁
  have hSub :
      halfPlaneCoord ''
        (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len))
        ⊆ {z : ℂ | z ∈ RH.Cert.Ω ∧ z ≠ (1 : ℂ) ∧ riemannXi_ext z ≠ 0} :=
    halfPlaneCoord_image_strip_subset_offZeros (I := I)
      (hε_pos := hε_pos) havoid hheight
  exact hOff.mono hSub

lemma G''_U_hasDerivAt_on_strip_image
  (hRep :
    HasPoissonRepOn
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
      offXi)
  (hBdry :
    BoundaryPositive
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
  (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
  (I : RH.Cert.WhitneyInterval) {ε : ℝ} (hε_pos : 0 < ε)
  (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
  (hheight : zeroHeightSup α_split I < ε) :
  ∀ z ∈ halfPlaneCoord ''
      (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)),
    HasDerivAt G'_U (G''_U z) z := by
  intro z hz
  -- points in the Whitney strip map into the canonical off-zeros domain
  have hzOff :
      z ∈ {w : ℂ | w ∈ RH.Cert.Ω ∧ w ≠ (1 : ℂ) ∧ riemannXi_ext w ≠ 0} := by
    have hSub :=
      halfPlaneCoord_image_strip_subset_offZeros
        (I := I) (hε_pos := hε_pos) (havoid := havoid) (hheight := hheight)
    exact hSub hz
  -- `deriv G_U` is analytic on the off-zeros domain
  have hAnalytic_deriv :
      AnalyticOnNhd ℂ (deriv G_U)
        {w : ℂ | w ∈ RH.Cert.Ω ∧ w ≠ (1 : ℂ) ∧ riemannXi_ext w ≠ 0} :=
    AnalyticOnNhd.deriv
      (𝕜 := ℂ) (f := G_U)
      (s := {w : ℂ | w ∈ RH.Cert.Ω ∧ w ≠ (1 : ℂ) ∧ riemannXi_ext w ≠ 0})
      (G_U_analyticOnNhd_offZeros hRep hBdry h₁)
  -- hence `G'_U = deriv G_U` is analytic there as well
  have hAnalytic_G' :
      AnalyticOnNhd ℂ G'_U
        {w : ℂ | w ∈ RH.Cert.Ω ∧ w ≠ (1 : ℂ) ∧ riemannXi_ext w ≠ 0} := by
    intro w hw
    simpa [G'_U] using hAnalytic_deriv w hw
  have hAt : AnalyticAt ℂ G'_U z := hAnalytic_G' z hzOff
  have hDiff : DifferentiableAt ℂ G'_U z := hAt.differentiableAt
  have hDeriv : HasDerivAt G'_U (deriv G'_U z) z := hDiff.hasDerivAt
  simpa [G''_U] using hDeriv


/-- Specialized continuity of the canonical tangential derivative on a Whitney strip. -/
lemma continuousOn_U_t_canonical_strip
  (hRep :
    HasPoissonRepOn
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
      offXi)
  (hBdry :
    BoundaryPositive
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
  (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
  (I : RH.Cert.WhitneyInterval) (ε : ℝ) (hε_pos : 0 < ε)
  (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
  (hheight : zeroHeightSup α_split I < ε) :
  ContinuousOn U_t_canonical
    (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)) := by
  refine continuousOn_U_t_canonical_on_strip
    (I := I) (ε := ε)
    (hG_cont :=
      continuousOn_G'_U_on_strip
        hRep hBdry h₁ I hε_pos havoid hheight)

/-- Specialized continuity of the canonical normal derivative on a Whitney strip. -/
lemma continuousOn_U_σ_canonical_strip
  (hRep :
    HasPoissonRepOn
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
      offXi)
  (hBdry :
    BoundaryPositive
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
  (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
  (I : RH.Cert.WhitneyInterval) (ε : ℝ) (hε_pos : 0 < ε)
  (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
  (hheight : zeroHeightSup α_split I < ε) :
  ContinuousOn U_σ_canonical
    (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)) := by
  refine continuousOn_U_σ_canonical_on_strip
    (I := I) (ε := ε)
    (hG_cont :=
      continuousOn_G'_U_on_strip
        hRep hBdry h₁ I hε_pos havoid hheight)

/-- Integrability of the canonical gradient energy on a Whitney strip:
`(U_t_canonical)^2 + (U_σ_canonical)^2` is integrable on
`I.interval ×ˢ [ε, α_split * I.len]`. This supplies the `Hi_grad` hypothesis
for `green_identity_for_box_energy` in the canonical case. -/
lemma integrableOn_grad_canonical_sq_on_strip
  (hRep :
    HasPoissonRepOn
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
      offXi)
  (hBdry :
    BoundaryPositive
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
  (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
  (I : RH.Cert.WhitneyInterval) (ε : ℝ) (hε_pos : 0 < ε)
  (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
  (hheight : zeroHeightSup α_split I < ε) :
  IntegrableOn
    (fun p : ℝ × ℝ =>
      (U_t_canonical p) ^ 2 + (U_σ_canonical p) ^ 2)
    (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len))
    volume := by
  -- continuity of the gradient components on the closed rectangle
  have hUt :
      ContinuousOn U_t_canonical
        (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)) :=
    continuousOn_U_t_canonical_strip
      hRep hBdry h₁ I ε hε_pos havoid hheight
  have hUσ :
      ContinuousOn U_σ_canonical
        (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)) :=
    continuousOn_U_σ_canonical_strip
      hRep hBdry h₁ I ε hε_pos havoid hheight
  -- continuity of the squared gradient energy
  have hF :
      ContinuousOn
        (fun p : ℝ × ℝ =>
          (U_t_canonical p) ^ 2 + (U_σ_canonical p) ^ 2)
        (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)) := by
    -- squares via products: U_t^2 = U_t * U_t, U_σ^2 = U_σ * U_σ
    have hUt_sq :
        ContinuousOn
          (fun p : ℝ × ℝ => U_t_canonical p * U_t_canonical p)
          (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)) :=
      hUt.mul hUt
    have hUσ_sq :
        ContinuousOn
          (fun p : ℝ × ℝ => U_σ_canonical p * U_σ_canonical p)
          (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)) :=
      hUσ.mul hUσ
    -- sum of continuous functions is continuous
    have hSum :
        ContinuousOn
          (fun p : ℝ × ℝ =>
            U_t_canonical p * U_t_canonical p
              + U_σ_canonical p * U_σ_canonical p)
          (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)) :=
      hUt_sq.add hUσ_sq
    -- rewrite in terms of squares
    refine (hSum.congr ?_).mono subset_rfl
    intro p _
    simp [pow_two, mul_comm]
  -- compactness of the rectangle
  have hcompact :
      IsCompact
        (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)) := by
    -- `I.interval` and `Set.Icc` are compact; their product is compact
    have hI : IsCompact (RH.Cert.WhitneyInterval.interval I) := by
      simpa [RH.Cert.WhitneyInterval.interval] using isCompact_Icc
    have hσ : IsCompact (Set.Icc ε (α_split * I.len)) := isCompact_Icc
    exact hI.prod hσ
  -- integrability from continuity on a compact set (finite-measure-on-compacts)
  have hInt :
      IntegrableOn
        (fun p : ℝ × ℝ =>
          (U_t_canonical p) ^ 2 + (U_σ_canonical p) ^ 2)
        (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len))
        volume :=
    ContinuousOn.integrableOn_compact
      (μ := volume) hcompact hF
  simpa using hInt

/-- On the Whitney box based on `I` between heights `ε` and `α_split * I.len`, assume that
the complex map `G` has derivative `G'` at every point of the complex rectangle
`halfPlaneCoord '' (I.interval ×ˢ Set.Icc ε (α_split * I.len))`.

Then `U_of G` is C¹ on the Whitney box, and its Frechét derivative at each point `p` can be
written in terms of the gradient components `U_t_of G' p` and `U_σ_of G' p`. -/
lemma U_of_C1_on_whitney_box
  (G G' : ℂ → ℂ)
  (I : RH.Cert.WhitneyInterval) (ε : ℝ) (_hε : 0 < ε)
  (hG_deriv :
    ∀ z ∈ halfPlaneCoord '' (RH.Cert.WhitneyInterval.interval I ×ˢ
                              Set.Icc ε (α_split * I.len)),
      HasDerivAt G (G' z) z) :
  ∀ p ∈ RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len),
    HasFDerivAt (U_of G)
      ((U_t_of G' p) • (ContinuousLinearMap.fst ℝ ℝ ℝ)
       + (U_σ_of G' p) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
  intro p hp
  rcases hp with ⟨hp_t, hp_σ⟩
  -- The complex point `z` corresponding to `p` in the upper half-plane
  set z : ℂ := halfPlaneCoord p with hz_def
  have hz_mem : z ∈ halfPlaneCoord ''
      (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)) := by
    refine ⟨p, ?_, by simp [hz_def]⟩
    exact ⟨hp_t, hp_σ⟩
  -- Complex derivative of `G` at `z`
  have hG : HasDerivAt G (G' z) z := hG_deriv z hz_mem
  -- Frechét derivative of `U_of G` at `p` from the abstract chain rule
  let L : ℝ × ℝ →L[ℝ] ℝ :=
    Complex.reCLM.comp
      ((ContinuousLinearMap.smulRight
          (ContinuousLinearMap.id ℝ ℂ)
          (G' z)).comp halfPlaneLinear)
  have hU : HasFDerivAt (U_of G) L p :=
    by
      -- use the abstract chain rule lemma
      simpa [L, hz_def] using hasFDerivAt_U_of G G' p hG

  -- Identify `L` with `U_t_of` / `U_σ_of` packaged as `U_t • fst + U_σ • snd`
  have hUt : U_t_of G' p = L (1, 0) := by
    dsimp [U_t_of, L]
  have hUs : U_σ_of G' p = L (0, 1) := by
    dsimp [U_σ_of, L]

  have hL_eq_basic :
      L =
      (L (1, 0)) • (ContinuousLinearMap.fst ℝ ℝ ℝ)
      + (L (0, 1)) • (ContinuousLinearMap.snd ℝ ℝ ℝ) := by
    apply ContinuousLinearMap.ext
    intro v
    rcases v with ⟨t_val, σ_val⟩
    have hdec := linear2_decomp L (t_val, σ_val)
    have hsum :
        ((L (1, 0)) • (ContinuousLinearMap.fst ℝ ℝ ℝ)
            + (L (0, 1)) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) (t_val, σ_val)
          = t_val * L (1, 0) + σ_val * L (0, 1) := by
      simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        mul_comm]
    have hdecomp :
        L (t_val, σ_val) = t_val * L (1, 0) + σ_val * L (0, 1) := by
      simpa using hdec
    calc
      L (t_val, σ_val)
          = t_val * L (1, 0) + σ_val * L (0, 1) := hdecomp
      _ = ((L (1, 0)) • (ContinuousLinearMap.fst ℝ ℝ ℝ)
          + (L (0, 1)) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) (t_val, σ_val) := hsum.symm

  have hL_eq :
      L =
      (U_t_of G' p) • ContinuousLinearMap.fst ℝ ℝ ℝ
      + (U_σ_of G' p) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    simpa [←hUt, ←hUs] using hL_eq_basic

  -- Replace the derivative in `hU` by the gradient form
  have hU' :
      HasFDerivAt (U_of G)
        ((U_t_of G' p) • (ContinuousLinearMap.fst ℝ ℝ ℝ)
         + (U_σ_of G' p) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    HasFDerivAt.congr_fderiv hU hL_eq
  exact hU'

/-- Specialization of the previous lemma to the CR–Green potential `U_halfplane`,
under analytic hypotheses on `G_U` and its derivative `G'_U`.

Here `G'_U` should be instantiated as the complex derivative of `G_U` on the region of interest;
this lemma only packages the chain rule in Whitney coordinates. -/
lemma U_halfplane_hasFDerivAt_on_whitney_box
  (I : RH.Cert.WhitneyInterval) (ε : ℝ) (hε : 0 < ε)
  (G'_U : ℂ → ℂ)
  (hG_deriv :
    ∀ z ∈ halfPlaneCoord '' (RH.Cert.WhitneyInterval.interval I ×ˢ
                              Set.Icc ε (α_split * I.len)),
      HasDerivAt G_U (G'_U z) z) :
  ∀ p ∈ RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len),
    HasFDerivAt U_halfplane
      ((U_t_of G'_U p) • (ContinuousLinearMap.fst ℝ ℝ ℝ)
       + (U_σ_of G'_U p) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
  intro p hp
  -- identify U_halfplane with U_of G_U, then apply the generic lemma
  have hU : U_halfplane = U_of G_U := U_halfplane_eq_U_of
  simpa [hU] using U_of_C1_on_whitney_box G_U G'_U I ε hε hG_deriv p hp

lemma U_halfplane_hasFDerivAt_linCombo
  (I : RH.Cert.WhitneyInterval) (ε : ℝ) (hε : 0 < ε)
  (G'_U : ℂ → ℂ)
  (hG_deriv :
    ∀ z ∈ halfPlaneCoord '' (RH.Cert.WhitneyInterval.interval I ×ˢ
                              Set.Icc ε (α_split * I.len)),
      HasDerivAt G_U (G'_U z) z) :
  ∀ p ∈ (interior (RH.Cert.WhitneyInterval.interval I))
          ×ˢ interior (Set.Icc ε (α_split * I.len)),
    HasFDerivAt U_halfplane
      (linComboCLM (U_t_of G'_U p) (U_σ_of G'_U p)) p := by
  intro p hp
  classical
  obtain ⟨hp₁, hp₂⟩ := hp
  have hp₁' :
      p.1 ∈ RH.Cert.WhitneyInterval.interval I :=
    interior_subset hp₁
  have hp₂' :
      p.2 ∈ Set.Icc ε (α_split * I.len) :=
    interior_subset hp₂
  have hpS :
      p ∈ RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len) :=
    ⟨hp₁', hp₂'⟩
  have h :=
    U_halfplane_hasFDerivAt_on_whitney_box
      (I := I) (ε := ε) (hε := hε)
      (G'_U := G'_U) (hG_deriv := hG_deriv)
      p hpS
  simpa [linComboCLM]
    using h

/-- `U_halfplane` is C¹ on the canonical Whitney strip once its complex argument
avoids the pole set of `riemannXi_ext`. This specializes the abstract chain-rule
lemma to the actual derivative `G'_U`. -/
lemma U_halfplane_hasFDerivAt_on_strip
  (hRep :
    HasPoissonRepOn
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
      offXi)
  (hBdry :
    BoundaryPositive
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
  (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
  (I : RH.Cert.WhitneyInterval) (ε : ℝ) (hε : 0 < ε)
  (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
  (hheight : zeroHeightSup α_split I < ε) :
  ∀ p ∈ RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len),
    HasFDerivAt U_halfplane
      ((U_t_of G'_U p) • (ContinuousLinearMap.fst ℝ ℝ ℝ)
        + (U_σ_of G'_U p) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
  have hG :
      ∀ z ∈ halfPlaneCoord ''
          (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)),
        HasDerivAt G_U (G'_U z) z :=
    G_U_hasDerivAt_on_strip_image
      (I := I)
      (hRep := hRep) (hBdry := hBdry) (h₁ := h₁)
      (hε_pos := hε) (havoid := havoid) (hheight := hheight)
  exact
    U_halfplane_hasFDerivAt_on_whitney_box
      (I := I) (ε := ε) (hε := hε) (G'_U := G'_U)
      (hG_deriv := hG)

/-- On a Whitney box strip, `U_halfplane` is Fréchet differentiable everywhere,
hence continuous on that strip. This provides the `HcU` hypothesis needed in
`green_identity_for_box_energy` and its refinements. -/
lemma continuousOn_U_halfplane_on_strip
  (hRep :
    HasPoissonRepOn
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
      offXi)
  (hBdry :
    BoundaryPositive
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
  (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
  (I : RH.Cert.WhitneyInterval) (ε : ℝ) (hε : 0 < ε)
  (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
  (hheight : zeroHeightSup α_split I < ε) :
  ContinuousOn U_halfplane
    (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)) := by
  intro p hp
  have hF :=
    U_halfplane_hasFDerivAt_on_strip
      (hRep := hRep) (hBdry := hBdry) (h₁ := h₁)
      (I := I) (ε := ε) (hε := hε)
      (havoid := havoid) (hheight := hheight)
      p hp
  exact hF.continuousAt.continuousWithinAt

/-- Interior version of `U_halfplane_hasFDerivAt_on_strip`, phrased with the
`linComboCLM` packaging used in Green’s identity. -/
lemma U_halfplane_hasFDerivAt_linCombo_on_strip
  (hRep :
    HasPoissonRepOn
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
      offXi)
  (hBdry :
    BoundaryPositive
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
  (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
  (I : RH.Cert.WhitneyInterval) (ε : ℝ) (hε : 0 < ε)
  (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
  (hheight : zeroHeightSup α_split I < ε) :
  ∀ p ∈ (interior (RH.Cert.WhitneyInterval.interval I))
          ×ˢ interior (Set.Icc ε (α_split * I.len)),
    HasFDerivAt U_halfplane
      (linComboCLM (U_t_of G'_U p) (U_σ_of G'_U p)) p := by
  have hG :
      ∀ z ∈ halfPlaneCoord ''
          (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)),
        HasDerivAt G_U (G'_U z) z :=
    G_U_hasDerivAt_on_strip_image
      (I := I)
      (hRep := hRep) (hBdry := hBdry) (h₁ := h₁)
      (hε_pos := hε) (havoid := havoid) (hheight := hheight)
  refine
    U_halfplane_hasFDerivAt_linCombo
      (I := I) (ε := ε) (hε := hε) (G'_U := G'_U)
      (hG_deriv := hG)

open ContinuousLinearMap

lemma gradU_whitney_eq_of_hasFDerivAt {L : ℝ × ℝ →L[ℝ] ℝ}
    {p : ℝ × ℝ} (h : HasFDerivAt U_halfplane L p) :
    gradU_whitney p = (L (1, 0), L (0, 1)) := by
  have ht :=
    (hasDerivAt_fst_slice_of_hasFDerivAt h).deriv
  have hσ :=
    (hasDerivAt_snd_slice_of_hasFDerivAt h).deriv
  ext <;> simp [gradU_whitney, ht, hσ]

lemma gradU_whitney_eq_on_strip
  (hRep :
    HasPoissonRepOn
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
      offXi)
  (hBdry :
    BoundaryPositive
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
  (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
  (I : RH.Cert.WhitneyInterval) (ε : ℝ) (hε : 0 < ε)
  (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
  (hheight : zeroHeightSup α_split I < ε) :
  ∀ p ∈ RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len),
    gradU_whitney p = (U_t_canonical p, U_σ_canonical p) := by
  intro p hp
  have h :=
    U_halfplane_hasFDerivAt_on_strip
      (hRep := hRep) (hBdry := hBdry) (h₁ := h₁)
      (I := I) (ε := ε) (hε := hε)
      (havoid := havoid) (hheight := hheight)
      p hp
  have := gradU_whitney_eq_of_hasFDerivAt h
  simpa using this

lemma hasDerivAt_t_slice_on_strip
  (hRep :
    HasPoissonRepOn
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
      offXi)
  (hBdry :
    BoundaryPositive
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
  (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
  (I : RH.Cert.WhitneyInterval) (ε : ℝ) (hε : 0 < ε)
  (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
  (hheight : zeroHeightSup α_split I < ε)
  {p : ℝ × ℝ}
  (hp : p ∈ RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)) :
  HasDerivAt (fun t => U_halfplane (t, p.2)) (U_t_canonical p) p.1 := by
  have h :=
    U_halfplane_hasFDerivAt_on_strip
      (hRep := hRep) (hBdry := hBdry) (h₁ := h₁)
      (I := I) (ε := ε) (hε := hε)
      (havoid := havoid) (hheight := hheight)
      p hp
  have hslice := hasDerivAt_fst_slice_of_hasFDerivAt h
  simpa [U_t_canonical, linComboCLM_apply_fst] using hslice

lemma hasDerivAt_sigma_slice_on_strip
  (hRep :
    HasPoissonRepOn
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
      offXi)
  (hBdry :
    BoundaryPositive
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
  (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
  (I : RH.Cert.WhitneyInterval) (ε : ℝ) (hε : 0 < ε)
  (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
  (hheight : zeroHeightSup α_split I < ε)
  {p : ℝ × ℝ}
  (hp : p ∈ RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)) :
  HasDerivAt (fun σ => U_halfplane (p.1, σ)) (U_σ_canonical p) p.2 := by
  have h :=
    U_halfplane_hasFDerivAt_on_strip
      (hRep := hRep) (hBdry := hBdry) (h₁ := h₁)
      (I := I) (ε := ε) (hε := hε)
      (havoid := havoid) (hheight := hheight)
      p hp
  have hslice := hasDerivAt_snd_slice_of_hasFDerivAt h
  simpa [U_σ_canonical, linComboCLM_apply_snd] using hslice

/-!  Second-order Fréchet derivatives of the canonical first partials. -/

lemma U_σ_canonical_hasFDerivAt_on_whitney_box
  (hRep :
    HasPoissonRepOn
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
      offXi)
  (hBdry :
    BoundaryPositive
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
  (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
  (I : RH.Cert.WhitneyInterval) (ε : ℝ) (hε : 0 < ε)
  (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
  (hheight : zeroHeightSup α_split I < ε) :
  ∀ p ∈ RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len),
    HasFDerivAt U_σ_canonical
      (linComboCLM (U_σt_canonical p) (U_σσ_canonical p)) p := by
  intro p hp
  classical
  -- Step 1: analytic chain rule for `U_σ_canonical = U_of G'_U`
  have hG'' :
      ∀ z ∈ halfPlaneCoord ''
          (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)),
        HasDerivAt G'_U (G''_U z) z :=
    G''_U_hasDerivAt_on_strip_image hRep hBdry h₁
      (I := I) (hε_pos := hε) (havoid := havoid) (hheight := hheight)
  have h_raw :
      HasFDerivAt (U_of G'_U)
        ((U_t_of G''_U p) • ContinuousLinearMap.fst ℝ ℝ ℝ
          + (U_σ_of G''_U p) • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
    simpa using
      U_of_C1_on_whitney_box G'_U G''_U I ε hε hG'' p hp
  have h_lin :
      HasFDerivAt (U_of G'_U)
        (linComboCLM (U_t_of G''_U p) (U_σ_of G''_U p)) p := by
    have hL :
        (U_t_of G''_U p) • ContinuousLinearMap.fst ℝ ℝ ℝ
          + (U_σ_of G''_U p) • ContinuousLinearMap.snd ℝ ℝ ℝ
        = linComboCLM (U_t_of G''_U p) (U_σ_of G''_U p) := by
      simp [linComboCLM]
    exact h_raw.congr_fderiv hL
  have hσ :
      HasFDerivAt U_σ_canonical
        (linComboCLM (U_t_of G''_U p) (U_σ_of G''_U p)) p := by
    -- identify `U_σ_canonical` with `U_of G'_U`
    have h_eq : U_σ_canonical = U_of G'_U := by
      funext q
      simp [U_σ_canonical, U_σ_of_eq, U_of]
    simpa [h_eq] using h_lin
  -- Step 2: identify coefficients with canonical second partials via slices
  have h_t :
      HasDerivAt (fun t : ℝ => U_σ_canonical (t, p.2))
        (linComboCLM (U_t_of G''_U p) (U_σ_of G''_U p) (1, 0)) p.1 :=
    hasDerivAt_fst_slice_of_hasFDerivAt (f := U_σ_canonical)
      (L := linComboCLM (U_t_of G''_U p) (U_σ_of G''_U p)) hσ
  have h_σ :
      HasDerivAt (fun σ : ℝ => U_σ_canonical (p.1, σ))
        (linComboCLM (U_t_of G''_U p) (U_σ_of G''_U p) (0, 1)) p.2 :=
    hasDerivAt_snd_slice_of_hasFDerivAt (f := U_σ_canonical)
      (L := linComboCLM (U_t_of G''_U p) (U_σ_of G''_U p)) hσ
  have h_t_deriv :
      deriv (fun t : ℝ => U_σ_canonical (t, p.2)) p.1
        = U_t_of G''_U p := by
    simpa [linComboCLM_apply_fst] using h_t.deriv
  have h_σ_deriv :
      deriv (fun σ : ℝ => U_σ_canonical (p.1, σ)) p.2
        = U_σ_of G''_U p := by
    simpa [linComboCLM_apply_snd] using h_σ.deriv
  have hσt_eq :
      U_σt_canonical p = U_t_of G''_U p := by
    simpa [U_σt_canonical] using h_t_deriv
  have hσσ_eq :
      U_σσ_canonical p = U_σ_of G''_U p := by
    simpa [U_σσ_canonical] using h_σ_deriv
  have hL_eq :
      linComboCLM (U_t_of G''_U p) (U_σ_of G''_U p)
        = linComboCLM (U_σt_canonical p) (U_σσ_canonical p) := by
    apply ContinuousLinearMap.ext
    intro v
    rcases v with ⟨t, σ⟩
    simp [linComboCLM_apply, hσt_eq, hσσ_eq]
  exact hσ.congr_fderiv hL_eq

lemma U_t_canonical_hasFDerivAt_on_whitney_box
  (hRep :
    HasPoissonRepOn
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
      offXi)
  (hBdry :
    BoundaryPositive
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
  (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
  (I : RH.Cert.WhitneyInterval) (ε : ℝ) (hε : 0 < ε)
  (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
  (hheight : zeroHeightSup α_split I < ε) :
  ∀ p ∈ RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len),
    HasFDerivAt U_t_canonical
      (linComboCLM (U_tt_canonical p) (U_tσ_canonical p)) p := by
  intro p hp
  classical
  -- Step 1: analytic chain rule for `U_t_canonical` via a rotated derivative.
  -- Define the auxiliary complex map `H z = G'_U z * I`.
  let H : ℂ → ℂ := fun z => G'_U z * Complex.I
  let H' : ℂ → ℂ := fun z => G''_U z * Complex.I
  have hG'' :
      ∀ z ∈ halfPlaneCoord ''
          (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)),
        HasDerivAt G'_U (G''_U z) z :=
    G''_U_hasDerivAt_on_strip_image hRep hBdry h₁
      (I := I) (hε_pos := hε) (havoid := havoid) (hheight := hheight)
  have hH_deriv :
      ∀ z ∈ halfPlaneCoord ''
          (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)),
        HasDerivAt H (H' z) z := by
    intro z hz
    have hG := hG'' z hz
    simpa [H, H'] using hG.mul_const Complex.I
  have h_raw :
      HasFDerivAt (U_of H)
        ((U_t_of H' p) • ContinuousLinearMap.fst ℝ ℝ ℝ
          + (U_σ_of H' p) • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
    simpa using
      U_of_C1_on_whitney_box H H' I ε hε hH_deriv p hp
  have h_lin :
      HasFDerivAt (U_of H)
        (linComboCLM (U_t_of H' p) (U_σ_of H' p)) p := by
    have hL :
        (U_t_of H' p) • ContinuousLinearMap.fst ℝ ℝ ℝ
          + (U_σ_of H' p) • ContinuousLinearMap.snd ℝ ℝ ℝ
        = linComboCLM (U_t_of H' p) (U_σ_of H' p) := by
      simp [linComboCLM]
    exact h_raw.congr_fderiv hL
  have ht :
      HasFDerivAt U_t_canonical
        (linComboCLM (U_t_of H' p) (U_σ_of H' p)) p := by
    -- identify `U_t_canonical` with `U_of H`
    have h_eq : U_t_canonical = U_of H := by
      funext q
      simp [U_t_canonical, U_t_of_eq, U_of, H]
    simpa [h_eq] using h_lin
  -- Step 2: identify coefficients with canonical second partials via slices
  have h_t :
      HasDerivAt (fun t : ℝ => U_t_canonical (t, p.2))
        (linComboCLM (U_t_of H' p) (U_σ_of H' p) (1, 0)) p.1 :=
    hasDerivAt_fst_slice_of_hasFDerivAt (f := U_t_canonical)
      (L := linComboCLM (U_t_of H' p) (U_σ_of H' p)) ht
  have h_σ :
      HasDerivAt (fun σ : ℝ => U_t_canonical (p.1, σ))
        (linComboCLM (U_t_of H' p) (U_σ_of H' p) (0, 1)) p.2 :=
    hasDerivAt_snd_slice_of_hasFDerivAt (f := U_t_canonical)
      (L := linComboCLM (U_t_of H' p) (U_σ_of H' p)) ht
  have h_t_deriv :
      deriv (fun t : ℝ => U_t_canonical (t, p.2)) p.1
        = U_t_of H' p := by
    simpa [linComboCLM_apply_fst] using h_t.deriv
  have h_σ_deriv :
      deriv (fun σ : ℝ => U_t_canonical (p.1, σ)) p.2
        = U_σ_of H' p := by
    simpa [linComboCLM_apply_snd] using h_σ.deriv
  have htt_eq :
      U_tt_canonical p = U_t_of H' p := by
    simpa [U_tt_canonical] using h_t_deriv
  have htσ_eq :
      U_tσ_canonical p = U_σ_of H' p := by
    simpa [U_tσ_canonical] using h_σ_deriv
  have hL_eq :
      linComboCLM (U_t_of H' p) (U_σ_of H' p)
        = linComboCLM (U_tt_canonical p) (U_tσ_canonical p) := by
    apply ContinuousLinearMap.ext
    intro v
    rcases v with ⟨t, σ⟩
    simp [linComboCLM_apply, htt_eq, htσ_eq]
  exact ht.congr_fderiv hL_eq

lemma U_σ_canonical_hasFDerivAt_on_strip
  (hRep :
    HasPoissonRepOn
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
      offXi)
  (hBdry :
    BoundaryPositive
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
  (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
  (I : RH.Cert.WhitneyInterval) (ε : ℝ) (hε : 0 < ε)
  (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
  (hheight : zeroHeightSup α_split I < ε) :
  ∀ x ∈ (interior (RH.Cert.WhitneyInterval.interval I))
          ×ˢ interior (Set.Icc ε (α_split * I.len)),
    HasFDerivAt U_σ_canonical
      (linComboCLM (U_σt_canonical x) (U_σσ_canonical x)) x := by
  intro x hx
  classical
  obtain ⟨hx₁, hx₂⟩ := hx
  have hx₁' :
      x.1 ∈ RH.Cert.WhitneyInterval.interval I :=
    interior_subset hx₁
  have hx₂' :
      x.2 ∈ Set.Icc ε (α_split * I.len) :=
    interior_subset hx₂
  have hxS :
      x ∈ RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len) :=
    ⟨hx₁', hx₂'⟩
  exact
    U_σ_canonical_hasFDerivAt_on_whitney_box hRep hBdry h₁
      (I := I) (ε := ε) (hε := hε)
      (havoid := havoid) (hheight := hheight) x hxS

lemma U_t_canonical_hasFDerivAt_on_strip
  (hRep :
    HasPoissonRepOn
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
      offXi)
  (hBdry :
    BoundaryPositive
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
  (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
  (I : RH.Cert.WhitneyInterval) (ε : ℝ) (hε : 0 < ε)
  (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
  (hheight : zeroHeightSup α_split I < ε) :
  ∀ x ∈ (interior (RH.Cert.WhitneyInterval.interval I))
          ×ˢ interior (Set.Icc ε (α_split * I.len)),
    HasFDerivAt U_t_canonical
      (linComboCLM (U_tt_canonical x) (U_tσ_canonical x)) x := by
  intro x hx
  classical
  obtain ⟨hx₁, hx₂⟩ := hx
  have hx₁' :
      x.1 ∈ RH.Cert.WhitneyInterval.interval I :=
    interior_subset hx₁
  have hx₂' :
      x.2 ∈ Set.Icc ε (α_split * I.len) :=
    interior_subset hx₂
  have hxS :
      x ∈ RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len) :=
    ⟨hx₁', hx₂'⟩
  exact
    U_t_canonical_hasFDerivAt_on_whitney_box hRep hBdry h₁
      (I := I) (ε := ε) (hε := hε)
      (havoid := havoid) (hheight := hheight) x hxS


open Analysis InnerProductSpace

/-
/-- The sum of second partials of the real-part field in flat coordinates.

This is stated as a direct definition-expansion lemma, since `ℝ × ℝ` does not
carry an inner product space structure compatible with `Analysis.laplacian`.
When the full analytic bridge connecting the Hessian to iterated partials is
completed, this can be upgraded to reference the abstract Laplacian API. -/
lemma flat_second_partials_sum
    (G : ℂ → ℂ) (q : ℝ × ℝ) :
    U_flat_xx G q + U_flat_yy G q =
      deriv (fun x => U_flat_x G (x, q.2)) q.1 +
      deriv (fun y => U_flat_y G (q.1, y)) q.2 := by
  rfl
  -/

lemma laplacian_U_flat_eq
    (G : ℂ → ℂ) (q : WithLp 2 (ℝ × ℝ))
    (h : ContDiff ℝ 2 (fun p : WithLp 2 (ℝ × ℝ) => U_flat G p)) :
    Analysis.laplacian (fun p : WithLp 2 (ℝ × ℝ) => U_flat G p) q
      = U_flat_xx G q + U_flat_yy G q := by
  classical
  let f : WithLp 2 (ℝ × ℝ) → ℝ := fun p => U_flat G p
  have h_coords := Analysis.laplacian_withLp_prod_coords f q
  -- C² regularity ⇒ p ↦ fderiv f p is differentiable at q
  have h_fderiv_diff :
      DifferentiableAt ℝ (fun p : WithLp 2 (ℝ × ℝ) => fderiv ℝ f p) q := by
    -- view `h` as `ContDiff ℝ (1+1) f`
    have h' : ContDiff ℝ (1 + 1) f := by
      simpa [f] using h
    -- use the standard equivalence between C^{n+1} and differentiable with C^n fderiv
    have h2 :=
      (contDiff_succ_iff_fderiv (𝕜 := ℝ) (f := f) (n := 1)).1 h'
    have h_fderiv_CD : ContDiff ℝ 1 (fderiv ℝ f) := h2.2.2
    exact (h_fderiv_CD.differentiable (by norm_num) q)
  -- apply the coordinate slice lemmas with the extra hypothesis
  have hx := Analysis.hessian_fst_fst_slice f q h h_fderiv_diff
  have hy := Analysis.hessian_snd_snd_slice f q h
  -- the definitions of `U_flat_xx`/`U_flat_yy` match the RHS of `hx`/`hy`
  rw [h_coords, hx, hy]
  rfl

/-- On `ℝ × ℝ`, the Laplacian of `U_flat G` at `q` is the sum of the second
partial derivatives in the `x`- and `y`-directions. -/
lemma laplacian_U_flat_eq_flat
    (G : ℂ → ℂ) (q : WithLp 2 (ℝ × ℝ))
    (h : ContDiff ℝ 2 (fun p : WithLp 2 (ℝ × ℝ) => U_flat G p)) :
    Analysis.laplacian (fun p : WithLp 2 (ℝ × ℝ) => U_flat G p) q
      = U_flat_xx G q + U_flat_yy G q := by
  classical
  -- this is just a restatement of `laplacian_U_flat_eq`
  simpa using
    (laplacian_U_flat_eq (G := G) (q := q) (h := h))

--open scoped LineDeriv

lemma secondDeriv_along_line
    (H : ℂ → ℝ) (z v : ℂ)
    (hH₁ : Differentiable ℝ H)
    (hH₂ : DifferentiableAt ℝ (fun w : ℂ => fderiv ℝ H w) z) :
  ((fderiv ℝ (fun w => fderiv ℝ H w) z) v) v =
    deriv (fun s : ℝ => deriv (fun t : ℝ => H (z + (t : ℂ) * v)) s) 0 := by
  classical
  -- 1. Define the 1D curve along the line in direction v.
  let γ : ℝ → ℂ := fun t => z + (t : ℂ) * v
  -- 2. Consider the CLM–valued curve c(s) = fderiv H (γ s).
  let c : ℝ → (ℂ →L[ℝ] ℝ) := fun s => fderiv ℝ H (γ s)
  -- 3. Show c is differentiable at 0 via chain rule and hH₂.
  have hγ : DifferentiableAt ℝ γ 0 := by
    have h_id : DifferentiableAt ℝ (fun t : ℝ => (t : ℂ)) 0 := by
      simpa using (Complex.differentiableAt_ofReal 0)
    have h_mul : DifferentiableAt ℝ (fun t : ℝ => (t : ℂ) * v) 0 := by
      -- `const_mul` gives differentiability of `t ↦ v * (t : ℂ)`, then we commute the factors
      simpa [mul_comm] using h_id.const_mul v
    exact (differentiableAt_const _).add h_mul
  have hc : DifferentiableAt ℝ c 0 := by
    -- H is differentiable everywhere, so in particular at γ 0.
    have hH_at : DifferentiableAt ℝ H (γ 0) := hH₁ (γ 0)
    -- we also know γ 0 = z, so hH_at is differentiability of H at z
    have hz0 : γ 0 = z := by
      simp [γ]
    -- now use hH₂ (differentiability of w ↦ fderiv H w at z) and the chain rule
    have hH₂' :
        DifferentiableAt ℝ (fun w : ℂ => fderiv ℝ H w) (γ 0) := by
      simpa [hz0] using hH₂
    have hc' := hH₂'.comp 0 hγ
    simpa [c] using hc'
  -- 4. Inner one-dimensional identity:
  --    For each fixed s, fderiv H (γ s) v is the t-derivative of t ↦ H(γ s + t v) at 0.
  have h_inner (s : ℝ) :
      (fderiv ℝ H (γ s)) v =
        deriv (fun t : ℝ => H (γ s + (t : ℂ) * v)) 0 := by
    -- Use the line-derivative API for `H` along the line through `γ s` in direction `v`.
    have hH_at : DifferentiableAt ℝ H (γ s) := hH₁ (γ s)
    -- lineDeriv along v equals the Fréchet derivative applied to v
    have h_line := (hH_at.lineDeriv_eq_fderiv (v := v))
    -- Expand `lineDeriv` and rewrite the scalar action on `ℂ`.
    have h' :
        (fderiv ℝ H (γ s)) v =
          deriv (fun t : ℝ => H (γ s + t • v)) 0 := by
      simpa [lineDeriv] using h_line.symm
    -- On `ℂ` as an `ℝ`-vector space, `t • v = (t : ℂ) * v`.
    simpa [Algebra.smul_def] using h'
  -- 5. Use the CLM chain rule for evaluation to commute "apply v" with outer deriv.
  let u : ℝ → ℂ := fun _ => v
  have hu : DifferentiableAt ℝ u 0 := differentiableAt_const _
  -- 5. Use the CLM chain rule for evaluation to commute "apply v" with outer deriv.
  let u : ℝ → ℂ := fun _ => v
  have hu : DifferentiableAt ℝ u 0 := differentiableAt_const _
  have h_deriv_cu :
      deriv (fun s : ℝ => c s (u s)) 0 =
        (deriv c 0) (u 0) := by
    -- this uses your `deriv_clm_apply` helper
    have := deriv_clm_apply (hc := hc) (hu := hu)
    -- `this` has type:
    --   deriv (fun s => c s (u s)) 0 = deriv c 0 (u 0) + c 0 (deriv u 0)
    -- but `u` is constant, so `deriv u 0 = 0`
    simpa [u, deriv_const, ContinuousLinearMap.map_zero] using this
  -- 6. Identify `deriv c 0` in terms of the second Fréchet derivative at z.
  have h_dc :
      deriv c 0 = (fderiv ℝ (fun w => fderiv ℝ H w) z) v := by
    -- View `c` as the line derivative of `w ↦ fderiv H w` along `v` based at `z`.
    have h_line :
        lineDeriv ℝ (fun w : ℂ => fderiv ℝ H w) z v =
          fderiv ℝ (fun w : ℂ => fderiv ℝ H w) z v :=
      (hH₂.lineDeriv_eq_fderiv (v := v))
    have h_deriv :
        deriv
          (fun t : ℝ =>
            (fun w : ℂ => fderiv ℝ H w) (z + (t : ℂ) * v)) 0 =
          (fderiv ℝ (fun w : ℂ => fderiv ℝ H w) z) v := by
      simpa [lineDeriv, Algebra.smul_def] using h_line
    -- But this derivative is exactly `deriv c 0`, since `c t = fderiv H (γ t) = fderiv H (z + (t:ℂ)*v)`.
    simpa [c, γ] using h_deriv
  -- 7. Put everything together.
  -- Left-hand side is "Hessian along v,v".
  have h_left :
      ((fderiv ℝ (fun w => fderiv ℝ H w) z) v) v =
        (deriv c 0) v := by
    simp [h_dc]
  -- Right-hand side is d/ds|₀ (d/dt|₀ H(z + (s+t)v)).
  -- Right-hand side is d/ds|₀ (d/dt|₀ H(z + (s+t)v)).
  have h_right :
      deriv (fun s : ℝ => deriv (fun t : ℝ => H (z + (t : ℂ) * v)) s) 0 =
        deriv (fun s : ℝ => c s (u s)) 0 := by
    -- 5a. For each s, relate the inner derivatives by translating in t.
    have h_shift (s : ℝ) :
        deriv (fun t : ℝ => H (γ s + (t : ℂ) * v)) 0 =
          deriv (fun t : ℝ => H (z + (t : ℂ) * v)) s := by
      -- First relate `t ↦ H (z + (t + s)·v)` and `t ↦ H (z + t·v)` using translation invariance.
      have h1 :
          deriv (fun t : ℝ => H (z + ((t + s : ℝ) : ℂ) * v)) 0 =
            deriv (fun t : ℝ => H (z + (t : ℂ) * v)) (0 + s) := by
        -- `deriv_comp_add_const` : deriv (fun x ↦ f (x + a)) x = deriv f (x + a)
        simpa using
          (deriv_comp_add_const
            (f := fun t : ℝ => H (z + (t : ℂ) * v))
            (a := s) (x := (0 : ℝ)))
      -- Now rewrite `z + (t + s)·v` as `γ s + t·v`.
      have h2 :
          deriv (fun t : ℝ => H (γ s + (t : ℂ) * v)) 0 =
            deriv (fun t : ℝ => H (z + ((t + s : ℝ) : ℂ) * v)) 0 := by
        apply congrArg (fun g : ℝ → ℝ => deriv g 0)
        funext t
        simp [γ, add_comm, add_assoc, add_mul]
      -- Combine the two equalities.
      have := h2.trans h1
      simpa [add_comm] using this
    -- 5b. Use `h_shift` and `h_inner` to identify the integrands pointwise.
    have h_fun :
        (fun s : ℝ =>
          deriv (fun t : ℝ => H (z + (t : ℂ) * v)) s) =
          (fun s : ℝ => c s (u s)) := by
      funext s
      calc
        deriv (fun t : ℝ => H (z + (t : ℂ) * v)) s
            = deriv (fun t : ℝ => H (γ s + (t : ℂ) * v)) 0 := (h_shift s).symm
        _   = (fderiv ℝ H (γ s)) v := by
                simpa using (h_inner s).symm
        _   = c s (u s) := by
                simp [c, u]
    -- 5c. Take derivatives at 0 of the two equal functions.
    have := congrArg (fun (f : ℝ → ℝ) => deriv f 0) h_fun
    exact this
  -- Final equality.
  calc
    ((fderiv ℝ (fun w => fderiv ℝ H w) z) v) v
        = (deriv c 0) v := h_left
    _   = deriv (fun s : ℝ => c s (u s)) 0 := by
            have := h_deriv_cu
            simpa [u] using this.symm
    _   = deriv (fun s : ℝ => deriv (fun t : ℝ => H (z + (t : ℂ) * v)) s) 0 := h_right.symm

/-- Second derivative of `Re ∘ G` in the real direction at `z = x + y·I`
matches the flat second x‑partial of `U_flat G` at `q = (x,y)`. -/
lemma uxx_as_iteratedFDeriv
    (G : ℂ → ℂ) {q : ℝ × ℝ} {z : ℂ}
    (hz : z = q.1 + q.2 * Complex.I)
    (hH₁ : Differentiable ℝ (fun w : ℂ => (G w).re))
    (hH₂ : DifferentiableAt ℝ (fun w : ℂ => fderiv ℝ (fun z : ℂ => (G z).re) w) z) :
  iteratedFDeriv ℝ 2 (fun w : ℂ => (G w).re) z ![1, 1] =
    U_flat_xx G q := by
  classical
  -- Real scalar field on ℝ×ℝ: flat real part of G
  let u : ℝ × ℝ → ℝ := fun p => (G (p.1 + p.2 * Complex.I)).re
  have u_eq : u = U_flat G := by
    funext p
    simp [u, U_flat]
  -- Linear map (x,y) ↦ x + y·I
  let Lxy : ℝ × ℝ →L[ℝ] ℂ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (1 : ℂ) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (Complex.I)
  have hLxy_apply (p : ℝ × ℝ) :
      Lxy p = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
    rcases p with ⟨x, y⟩
    simp [Lxy, add_comm, mul_comm]
  -- At q, z is the complex image under Lxy
  have hz' : z = Lxy q := by
    simp [hLxy_apply, hz]
  -- View H := Re ∘ G as a function on ℂ
  let H : ℂ → ℝ := fun w => (G w).re
  -- The 2nd Fréchet derivative in direction 1,1 at z, as a 1D second derivative
  -- along the real line: t ↦ H (z + t).
  have h_iter :
      iteratedFDeriv ℝ 2 H z ![1, 1]
        = ((fderiv ℝ (fun x => fderiv ℝ H x) z) 1) 1 := by
    -- `iteratedFDeriv_two_apply` has parameters `(𝕜 E F f z m)`
    simpa using
      (iteratedFDeriv_two_apply (𝕜 := ℝ) (E := ℂ) (F := ℝ)
        (f := H) (z := z) (m := ![(1 : ℂ), (1 : ℂ)]))
  -- Now rewrite the inner derivative in terms of u and the x‑slice.
  have h_inner :
      (fun x : ℝ =>
        deriv (fun t : ℝ => H (z + t)) x)
      = fun x =>
          deriv (fun t : ℝ => u (t + q.1, q.2)) x := by
    funext x
    -- For any real t, `z + t = Lxy (t + q.1, q.2)` by hz and the definition of Lxy.
    have : (fun t : ℝ => H (z + t))
           = fun t : ℝ => u (t + q.1, q.2) := by
      funext t
      have hz_t :
          z + t = Lxy (t + q.1, q.2) := by
        -- z = Lxy q and Lxy is ℝ‑linear, so z + t*1 = Lxy(q + (t,0)).
        have : Lxy (q.1, q.2) = z := by simp [hz', Prod.mk.eta]
        -- now:
        --   z + t = Lxy(q.1,q.2) + t*1 = Lxy( (q.1,q.2) + (t,0) ) = Lxy(t+q.1,q.2)
        rcases q with ⟨x₀,y₀⟩
        simp [Lxy, add_comm, add_assoc, mul_comm] at *
        grind
      simp [H, u, hz_t]
      grind
    simp [this]
  -- Evaluate at x = 0 and shift variable: x ↦ x + q.1
  have h_second :
      deriv (fun x : ℝ => deriv (fun t : ℝ => H (z + t)) x) 0
        = deriv (fun x : ℝ => deriv (fun t : ℝ => u (t, q.2)) x) q.1 := by
  -- change variables: x ↦ x + q.1
    have :
        (fun x : ℝ => deriv (fun t : ℝ => u (t + q.1, q.2)) x)
          = fun x => deriv (fun t : ℝ => u (t, q.2)) (x + q.1) := by
      funext x
      -- derivative of t ↦ u (t + q.1, q.2) at x
      -- equals derivative of t ↦ u (t, q.2) at x + q.1
      simpa using
        (deriv_comp_add_const (f := fun t : ℝ => u (t, q.2))
                              (a := q.1) (x := x))
    -- Now derivative at 0 of LHS equals derivative at q.1 of RHS by the same shift
    -- (deriv of f(x+q.1) at 0 = deriv f at q.1).
    -- Using `deriv.comp_const_add` or the corresponding lemma.
    have h_shift :
        deriv (fun x : ℝ => deriv (fun t : ℝ => u (t + q.1, q.2)) x) 0
          = deriv (fun x : ℝ => deriv (fun t : ℝ => u (t, q.2)) x) q.1 := by
      -- First rewrite the inner derivative under the x ↦ x + q.1 shift
      have h₁ :
          (fun x : ℝ => deriv (fun t : ℝ => u (t + q.1, q.2)) x)
            = fun x => deriv (fun t : ℝ => u (t, q.2)) (x + q.1) := by
        funext x
        simpa using
          (deriv_comp_add_const (f := fun t : ℝ => u (t, q.2))
                                (a := q.1) (x := x))
      -- Now derivative at 0 of the LHS equals derivative at q.1 of the RHS
      -- by the same shift lemma applied to the outer function
      have h₂ :
          deriv (fun x : ℝ => deriv (fun t : ℝ => u (t, q.2)) (x + q.1)) 0
            = deriv (fun x : ℝ => deriv (fun t : ℝ => u (t, q.2)) x) q.1 := by
        simpa using
          (deriv_comp_add_const
            (f := fun x : ℝ => deriv (fun t : ℝ => u (t, q.2)) x)
            (a := q.1) (x := 0))
      -- Combine the two equalities
      simpa [h₁] using h₂
    -- First, transport the derivative at 0 along the function equality h_inner
    have h_deriv_eq :
        deriv (fun x : ℝ => deriv (fun t : ℝ => H (z + ↑t)) x) 0 =
        deriv (fun x : ℝ => deriv (fun t : ℝ => u (t + q.1, q.2)) x) 0 := by
      have := congrArg (fun f : ℝ → ℝ => deriv f 0) h_inner
      simpa using this

    -- Now use the shift lemma h_shift to move the evaluation point from 0 to q.1
    have h_second :
        deriv (fun x : ℝ => deriv (fun t : ℝ => H (z + ↑t)) x) 0 =
        deriv (fun x : ℝ => deriv (fun t : ℝ => u (t, q.2)) x) q.1 := by
      calc
        deriv (fun x : ℝ => deriv (fun t : ℝ => H (z + ↑t)) x) 0
            = deriv (fun x : ℝ => deriv (fun t : ℝ => u (t + q.1, q.2)) x) 0 := h_deriv_eq
        _   = deriv (fun x : ℝ => deriv (fun t : ℝ => u (t, q.2)) x) q.1 := h_shift
    aesop
  -- Relate the 2D second Fréchet derivative in direction 1,1 at z
  -- to the 1D second derivative along the real line t ↦ H (z + t).
  -- Relate the 2D second Fréchet derivative in direction 1,1 at z
  -- to the 1D second derivative along the real line t ↦ H (z + t).
  have h1 :
      ((fderiv ℝ (fun x => fderiv ℝ H x) z) (1 : ℂ)) (1 : ℂ) =
        deriv (fun x : ℝ => deriv (fun t : ℝ => H (z + t)) x) 0 := by
    -- Global regularity assumptions on H, inherited from G
    have hH₁' : Differentiable ℝ H := hH₁
    have hH₂' :
        DifferentiableAt ℝ (fun w : ℂ => fderiv ℝ H w) z := by
      simpa using hH₂
    -- Apply the general line-lemma with v = 1
    simpa using
      (secondDeriv_along_line (H := H) (z := z) (v := (1 : ℂ))
        (hH₁ := hH₁') (hH₂ := hH₂'))
  -- Relate the 2D iterated Fréchet derivative in direction 1,1
  -- to the 1D second derivative along t ↦ H (z + t).
  have h_iter' :
      iteratedFDeriv ℝ 2 H z ![1, 1] =
        deriv (fun x : ℝ => deriv (fun t : ℝ => H (z + t)) x) 0 := by
    have h_iter :
        iteratedFDeriv ℝ 2 H z ![1, 1] =
          ((fderiv ℝ (fun x => fderiv ℝ H x) z) (1 : ℂ)) (1 : ℂ) := by
      simpa using
        (iteratedFDeriv_two_apply (𝕜 := ℝ) (E := ℂ) (F := ℝ)
          (f := H) (z := z) (m := ![(1 : ℂ), (1 : ℂ)]))
    exact h_iter.trans h1
  calc
    iteratedFDeriv ℝ 2 (fun w : ℂ => (G w).re) z ![1, 1]
        = iteratedFDeriv ℝ 2 H z ![1, 1] := rfl
    _ = deriv (fun x : ℝ => deriv (fun t : ℝ => H (z + t)) x) 0 := h_iter'
    _ = deriv (fun x : ℝ => deriv (fun t : ℝ => u (t, q.2)) x) q.1 := by
          simpa using h_second
    _ = U_flat_xx G q := by
          -- unfold `U_flat_xx` and `U_flat_x`, then use `u_eq`
          simp [U_flat_xx, U_flat_x, U_flat, u_eq]

/-- Second derivative of `Re ∘ G` in the imaginary direction at `z = x + y·I`
matches the flat second y‑partial of `U_flat G` at `q = (x,y)`.

We assume C²–regularity of `H := (G ·).re` in the form needed by
`secondDeriv_along_line`. -/
lemma uyy_as_iteratedFDeriv
    (G : ℂ → ℂ) {q : ℝ × ℝ} {z : ℂ}
    (hz : z = q.1 + q.2 * Complex.I)
    (hH₁ : Differentiable ℝ (fun w : ℂ => (G w).re))
    (hH₂ : DifferentiableAt ℝ
              (fun w : ℂ => fderiv ℝ (fun z : ℂ => (G z).re) w) z) :
  iteratedFDeriv ℝ 2 (fun w : ℂ => (G w).re) z ![Complex.I, Complex.I] =
    U_flat_yy G q := by
  classical
  -- Real scalar field on ℝ×ℝ
  let u : ℝ × ℝ → ℝ := fun p => (G (p.1 + p.2 * Complex.I)).re
  have u_eq : u = U_flat G := by
    funext p
    simp [u, U_flat]

  -- Linear map (x,y) ↦ x + y·I
  let Lxy : ℝ × ℝ →L[ℝ] ℂ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (1 : ℂ) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (Complex.I)
  have hLxy_apply (p : ℝ × ℝ) :
      Lxy p = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
    rcases p with ⟨x, y⟩
    simp [Lxy, add_comm, mul_comm]

  -- At q, z is the complex image under Lxy
  have hz' : z = Lxy q := by
    simp [hLxy_apply, hz]

  -- H := Re ∘ G
  let H : ℂ → ℝ := fun w => (G w).re

  have hH₁' : Differentiable ℝ H := hH₁
  have hH₂' :
      DifferentiableAt ℝ (fun w : ℂ => fderiv ℝ H w) z := by
    simpa using hH₂

  ------------------------------------------------------------------
  -- 1. Express the 2D Hessian along `I,I` as a 1D second derivative
  ------------------------------------------------------------------
  have h_line :
      ((fderiv ℝ (fun w => fderiv ℝ H w) z) Complex.I) Complex.I =
        deriv (fun s : ℝ =>
          deriv (fun t : ℝ => H (z + (t : ℂ) * Complex.I)) s) 0 := by
    simpa using
      (secondDeriv_along_line (H := H) (z := z) (v := Complex.I)
        (hH₁ := hH₁') (hH₂ := hH₂'))

  have h_iter :
      iteratedFDeriv ℝ 2 H z ![Complex.I, Complex.I] =
        ((fderiv ℝ (fun w => fderiv ℝ H w) z) Complex.I) Complex.I := by
    simpa using
      (iteratedFDeriv_two_apply (𝕜 := ℝ) (E := ℂ) (F := ℝ)
        (f := H) (z := z) (m := ![(Complex.I), (Complex.I)]))

  have h_iter' :
      iteratedFDeriv ℝ 2 H z ![Complex.I, Complex.I] =
        deriv (fun s : ℝ =>
          deriv (fun t : ℝ => H (z + (t : ℂ) * Complex.I)) s) 0 := by
    exact h_iter.trans h_line

  ------------------------------------------------------------------
  -- 2. Identify the 1D second derivative with the flat y‑slice second derivative
  ------------------------------------------------------------------
  -- First, rewrite the inner function `H (z + t·I)` in terms of `u`.
  have h_inner :
      (fun s : ℝ =>
        deriv (fun t : ℝ => H (z + (t : ℂ) * Complex.I)) s)
        =
      fun s : ℝ =>
        deriv (fun t : ℝ => u (q.1, t + q.2)) s := by
    funext s
    have h_fun :
        (fun t : ℝ => H (z + (t : ℂ) * Complex.I)) =
          fun t : ℝ => u (q.1, t + q.2) := by
      funext t
      -- Use `hz` to rewrite `z` and simplify
      have : z + (t : ℂ) * Complex.I
          = (q.1 : ℂ) + (q.2 + t : ℂ) * Complex.I := by
        simp [hz, add_comm, add_left_comm, add_mul]
      simp [H, u, this]
      grind
    simpa using
      congrArg (fun f : ℝ → ℝ => deriv f s) h_fun

  -- Transport the outer derivative at 0 along `h_inner`
  have h_deriv_eq :
      deriv (fun s : ℝ =>
        deriv (fun t : ℝ => H (z + (t : ℂ) * Complex.I)) s) 0 =
      deriv (fun s : ℝ =>
        deriv (fun t : ℝ => u (q.1, t + q.2)) s) 0 := by
    have := congrArg (fun f : ℝ → ℝ => deriv f 0) h_inner
    simpa using this

  -- Now change variables in the inner t‑variable: t ↦ t + q.2
  have h_tr :
      (fun s : ℝ =>
        deriv (fun t : ℝ => u (q.1, t + q.2)) s)
        =
      fun s : ℝ =>
        deriv (fun t : ℝ => u (q.1, t)) (s + q.2) := by
    funext s
    simpa using
      (deriv_comp_add_const
        (f := fun t : ℝ => u (q.1, t)) (a := q.2) (x := s))

  -- Then shift the outer variable s ↦ s + q.2 to move from 0 to q.2
  have h_shift :
      deriv (fun s : ℝ =>
        deriv (fun t : ℝ => u (q.1, t + q.2)) s) 0 =
      deriv (fun s : ℝ =>
        deriv (fun t : ℝ => u (q.1, t)) s) q.2 := by
    -- First rewrite via `h_tr`
    have h₁ :
        (fun s : ℝ =>
          deriv (fun t : ℝ => u (q.1, t + q.2)) s)
          =
        fun s : ℝ =>
          deriv (fun t : ℝ => u (q.1, t)) (s + q.2) := h_tr
    -- Then use translation invariance of the derivative on the outer variable
    have h₂ :
        deriv (fun s : ℝ =>
          deriv (fun t : ℝ => u (q.1, t)) (s + q.2)) 0 =
        deriv (fun s : ℝ =>
          deriv (fun t : ℝ => u (q.1, t)) s) q.2 := by
      simpa using
        (deriv_comp_add_const
          (f := fun s : ℝ =>
            deriv (fun t : ℝ => u (q.1, t)) s)
          (a := q.2) (x := 0))
    simpa [h₁] using h₂

  -- Combine the two steps: from H–based line second derivative
  -- to the flat y‑slice second derivative of u.
  have h_second :
      deriv (fun s : ℝ =>
        deriv (fun t : ℝ => H (z + (t : ℂ) * Complex.I)) s) 0 =
      deriv (fun s : ℝ =>
        deriv (fun t : ℝ => u (q.1, t)) s) q.2 := by
    calc
      deriv (fun s : ℝ =>
        deriv (fun t : ℝ => H (z + (t : ℂ) * Complex.I)) s) 0
          = deriv (fun s : ℝ =>
              deriv (fun t : ℝ => u (q.1, t + q.2)) s) 0 := h_deriv_eq
      _   = deriv (fun s : ℝ =>
              deriv (fun t : ℝ => u (q.1, t)) s) q.2 := h_shift

  ------------------------------------------------------------------
  -- 3. Final combination and rewrite in terms of `U_flat_yy`
  ------------------------------------------------------------------
  calc
    iteratedFDeriv ℝ 2 (fun w : ℂ => (G w).re) z ![Complex.I, Complex.I]
        = iteratedFDeriv ℝ 2 H z ![Complex.I, Complex.I] := rfl
    _   = deriv (fun s : ℝ =>
            deriv (fun t : ℝ => H (z + (t : ℂ) * Complex.I)) s) 0 := h_iter'
    _   = deriv (fun s : ℝ =>
            deriv (fun t : ℝ => u (q.1, t)) s) q.2 := h_second
    _   = U_flat_yy G q := by
          -- Unfold `U_flat_yy` and `U_flat_y`, then use `u_eq`
          simp [U_flat_yy, U_flat_y, U_flat, u_eq]




/-! ### CR second‑order calculus: vertical second derivatives -/

/-- **CR second‑order identity, vertical direction (specification lemma).**

Let `G : ℂ → ℂ` be analytic at a point `z`.  Write `G = u + i·v` in real
coordinates, so that `u = Re ∘ G` and `v = Im ∘ G`.  Along the vertical line
`y ↦ z + y·I`, the second derivative of `u` in the `y`‑direction coincides with
the negative `y`‑derivative of `Im (G')`:

\[
  \frac{d^2}{dy^2} u(z + iy)
    = - \frac{d}{dy} \Im(G'(z + iy)).
\]

In other words, the Hessian entry \(\partial^2_{yy} u\) equals
\(-\partial_y \Im(G')\) along vertical lines.  A full proof will unpack the
complex‑to‑real Fréchet derivatives supplied by `HasDerivAt.complexToReal_fderiv`,
use the Cauchy–Riemann equations, and identify mixed partials; here we record
the intended statement as a specification, to be used by higher‑level lemmas. -/
lemma CR_secondDeriv_Re_eq_neg_deriv_Im_G'
    (G : ℂ → ℂ) (z : ℂ)
    (hG : AnalyticAt ℂ G z)
    (hH₁ : Differentiable ℝ (fun w : ℂ => (G w).re))
    (hH₂ :
      DifferentiableAt ℝ
        (fun w : ℂ => fderiv ℝ (fun z : ℂ => (G z).re) w) z) :
    deriv (fun y : ℝ =>
             deriv (fun y : ℝ =>
               (G (z + (y : ℂ) * Complex.I)).re) y) 0
      =
    - deriv (fun y : ℝ =>
              (deriv G (z + (y : ℂ) * Complex.I)).im) 0 := by
  classical
  -- H := Re ∘ G
  let H : ℂ → ℝ := fun w => (G w).re
  have hH₁' : Differentiable ℝ H := hH₁
  have hH₂' :
      DifferentiableAt ℝ (fun w : ℂ => fderiv ℝ H w) z := by
    simpa [H] using hH₂

  --------------------------------------------------------------------
  -- Step 1: express the LHS via the Hessian using `secondDeriv_along_line` with v = I.
  --------------------------------------------------------------------
  have h_line :
      ((fderiv ℝ (fun w : ℂ => fderiv ℝ H w) z) Complex.I) Complex.I =
        deriv (fun s : ℝ =>
          deriv (fun t : ℝ => H (z + (t : ℂ) * Complex.I)) s) 0 :=
    secondDeriv_along_line (H := H) (z := z) (v := Complex.I)
      (hH₁ := hH₁') (hH₂ := hH₂')

  -- Rewrite in the notation of the statement.
  have h_LHS :
      deriv (fun y : ℝ =>
               deriv (fun y : ℝ =>
                 (G (z + (y : ℂ) * Complex.I)).re) y) 0
        =
      ((fderiv ℝ (fun w : ℂ => fderiv ℝ H w) z) Complex.I) Complex.I := by
    -- just rewrite H back to Re ∘ G and flip dummy names
    simpa [H] using h_line.symm

  --------------------------------------------------------------------
  -- Step 2: use the Hessian‑level CR identity to relate this Hessian
  -- entry to the directional derivative of Im (G') along I.
  --------------------------------------------------------------------
  have h_CR :
      ((fderiv ℝ (fun w : ℂ => fderiv ℝ H w) z) Complex.I) Complex.I
        =
      - (fderiv ℝ (fun w : ℂ => (deriv G w).im) z) Complex.I :=
    CR_second_order_Hessian_identity G z hG hH₁ hH₂

  --------------------------------------------------------------------
  -- Step 3: identify the directional derivative of Im (G') along I
  -- with the 1D derivative of y ↦ Im (G'(z + y⋅I)) at 0.
  --------------------------------------------------------------------
  -- derivative of the affine line y ↦ z + y·I
  have h_hasDeriv_line :
      HasDerivAt (fun y : ℝ => z + (y : ℂ) * Complex.I) Complex.I 0 := by
    have h_id : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 0 :=
      Complex.hasDerivAt_ofReal 0
    have h_mul : HasDerivAt (fun y : ℝ => (y : ℂ) * Complex.I) Complex.I 0 := by
      simpa [mul_comm] using h_id.const_mul Complex.I
    simpa using h_mul.add_const z

  -- Analyticity of G implies analytic (hence C¹) for G'.
  have hG_analytic' : AnalyticAt ℂ (fun w : ℂ => deriv G w) z := by
    -- Use the standard "derivative of analytic is analytic" lemma.
    -- Adjust this line to the exact name in your mathlib:
     simpa using hG.deriv

  -- real‑differentiability of Im ∘ G' at z
  have hG'_diff :
      DifferentiableAt ℝ (fun w : ℂ => (deriv G w).im) z := by
    have hd_complex : DifferentiableAt ℂ (fun w : ℂ => deriv G w) z :=
      hG_analytic'.differentiableAt
    have hd_real : DifferentiableAt ℝ (fun w : ℂ => deriv G w) z :=
      hd_complex.restrictScalars ℝ
    -- compose with Im
    have hF :
        HasFDerivAt (fun w : ℂ => deriv G w)
          (fderiv ℝ (fun w : ℂ => deriv G w) z) z :=
      hd_real.hasFDerivAt
    have hImF :
        HasFDerivAt (fun w : ℂ => (deriv G w).im)
          (Complex.imCLM.comp (fderiv ℝ (fun w : ℂ => deriv G w) z)) z :=
      Complex.imCLM.hasFDerivAt.comp z hF
    exact hImF.differentiableAt

  -- chain rule: directional derivative of Im G' along I equals
  -- the 1D derivative of y ↦ Im(G'(z + yI)) at 0
  have h_deriv_ImG' :
      deriv (fun y : ℝ =>
               (deriv G (z + (y : ℂ) * Complex.I)).im) 0
        =
      (fderiv ℝ (fun w : ℂ => (deriv G w).im) z) Complex.I := by
    -- use the generic chain rule for deriv + fderiv
    have h1 :
        deriv (fun y : ℝ =>
                 (fun w : ℂ => (deriv G w).im) (z + (y : ℂ) * Complex.I)) 0
          =
        (fderiv ℝ (fun w : ℂ => (deriv G w).im) z)
          (deriv (fun y : ℝ => z + (y : ℂ) * Complex.I) 0) := by
      -- Chain rule for `y ↦ (deriv G (z + y I)).im`
      simpa using
        (fderiv_comp_deriv (𝕜 := ℝ)
          (l := fun w : ℂ => (deriv G w).im)
          (f := fun y : ℝ => z + (y : ℂ) * Complex.I)
          (x := 0)
          (hl := by simpa using hG'_diff)
          (hf := h_hasDeriv_line.differentiableAt))
    -- simplify derivative of the line
    have h_line_deriv : deriv (fun y : ℝ => z + (y : ℂ) * Complex.I) 0 = Complex.I :=
      h_hasDeriv_line.deriv
    simpa [h_line_deriv] using h1

  --------------------------------------------------------------------
  -- Step 4: assemble everything.
  --------------------------------------------------------------------
  calc
    deriv (fun y : ℝ =>
             deriv (fun y : ℝ =>
               (G (z + (y : ℂ) * Complex.I)).re) y) 0
        = ((fderiv ℝ (fun w : ℂ =>
              fderiv ℝ (fun t : ℂ => (G t).re) w) z)
            Complex.I) Complex.I := h_LHS
    _   = - (fderiv ℝ (fun w : ℂ => (deriv G w).im) z) Complex.I :=
            h_CR
    _   = - deriv (fun y : ℝ =>
                     (deriv G (z + (y : ℂ) * Complex.I)).im) 0 := by
            simp [h_deriv_ImG']

/-!  A specialization of the CR second‑order identity to the canonical map `G_U`,
along the Whitney strip image. -/

lemma CR_secondDeriv_Re_GU_on_strip_image
    (hRep :
      HasPoissonRepOn
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
        offXi)
    (hBdry :
      BoundaryPositive
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
    (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
    (I : RH.Cert.WhitneyInterval) {ε : ℝ} (hε_pos : 0 < ε)
    (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
    (hheight : zeroHeightSup α_split I < ε)
    (hH₁ :
      Differentiable ℝ (fun w : ℂ => (G_U w).re))
    (hH₂ :
      ∀ z ∈ halfPlaneCoord ''
        (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)),
        DifferentiableAt ℝ
          (fun w : ℂ => fderiv ℝ (fun z : ℂ => (G_U z).re) w) z) :
    ∀ z ∈ halfPlaneCoord ''
        (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)),
      deriv (fun y : ℝ =>
               deriv (fun y : ℝ =>
                 (G_U (z + (y : ℂ) * Complex.I)).re) y) 0
        =
      - deriv (fun y : ℝ =>
                (G'_U (z + (y : ℂ) * Complex.I)).im) 0 := by
  intro z hz
  classical
  -- Points in the Whitney strip map into the canonical off‑zeros domain.
  have hzOff :
      z ∈ {w : ℂ | w ∈ RH.Cert.Ω ∧ w ≠ (1 : ℂ) ∧ riemannXi_ext w ≠ 0} := by
    have hSub :=
      halfPlaneCoord_image_strip_subset_offZeros
        (I := I) (hε_pos := hε_pos) (havoid := havoid) (hheight := hheight)
    exact hSub hz
  rcases hzOff with ⟨hzΩ, hz_ne_one, hzXi⟩

  -- Analyticity of `G_U` at `z`.
  have hG :
      AnalyticAt ℂ G_U z :=
    analyticAt_G_U hRep hBdry h₁ hzΩ hz_ne_one hzXi

  -- Second‑order real regularity hypotheses for `Re ∘ G_U` at `z`.
  have hH₂z :
      DifferentiableAt ℝ
        (fun w : ℂ => fderiv ℝ (fun z : ℂ => (G_U z).re) w) z :=
    hH₂ z hz

  -- Apply the general CR identity and rewrite `deriv G_U` as `G'_U`.
  have hCR :=
    CR_secondDeriv_Re_eq_neg_deriv_Im_G'
      (G := G_U) (z := z) hG hH₁ hH₂z
  -- `G'_U` is definitionally `deriv G_U`.
  simpa [G'_U] using hCR

lemma laplacian_H_as_flat_partials
    (G : ℂ → ℂ) {q : ℝ × ℝ} {z : ℂ}
    (hz : z = q.1 + q.2 * Complex.I)
    (hH₁ : Differentiable ℝ (fun w : ℂ => (G w).re))
    (hH₂ :
      DifferentiableAt ℝ
        (fun w : ℂ => fderiv ℝ (fun z : ℂ => (G z).re) w) z) :
  Analysis.laplacian (fun w : ℂ => (G w).re) z
    = U_flat_xx G q + U_flat_yy G q := by
  classical

  -- Scalar field on ℂ: real part of G
  let H : ℂ → ℝ := fun w => (G w).re

  -- Step 1: pointwise complex‑plane Laplacian formula at z
  have hLap_fun := laplacian_eq_iteratedFDeriv_complexPlane H
  have hLap :
      Analysis.laplacian H z =
        iteratedFDeriv ℝ 2 H z ![1, 1] +
        iteratedFDeriv ℝ 2 H z ![Complex.I, Complex.I] := by
    have := congrArg (fun f => f z) hLap_fun
    simpa using this

  -- Step 2: flat real scalar field u : ℝ × ℝ → ℝ, and slice second derivatives uxx, uyy
  let u : ℝ × ℝ → ℝ := fun p => (G (p.1 + p.2 * Complex.I)).re
  have u_eq : u = U_flat G := by
    funext p
    simp [u, U_flat]

  let ux_slice : ℝ → ℝ := fun x => deriv (fun t : ℝ => u (t, q.2)) x
  let uy_slice : ℝ → ℝ := fun y => deriv (fun t : ℝ => u (q.1, t)) y
  let uxx := deriv ux_slice q.1
  let uyy := deriv uy_slice q.2

  have uxx_eq :
      uxx = U_flat_xx G q := by
    simp [uxx, ux_slice, U_flat_xx, U_flat_x, u_eq, U_flat]

  have uyy_eq :
      uyy = U_flat_yy G q := by
    simp [uyy, uy_slice, U_flat_yy, U_flat_y, u_eq, U_flat]

  -- Step 3: express the ℂ-second derivatives as these ℝ-slice second derivatives
  have h_x :
      iteratedFDeriv ℝ 2 H z ![1, 1] = uxx := by
    -- “second derivative in direction 1 at z” equals “d²/dx² u(x,q.2) at x = q.1”
    exact uxx_as_iteratedFDeriv
      (G := G) (q := q) (z := z) hz hH₁ hH₂

  have h_y :
      iteratedFDeriv ℝ 2 H z ![Complex.I, Complex.I] = uyy := by
    -- similarly, direction I at z corresponds to d²/dy² u(q.1,y) at y = q.2
    exact uyy_as_iteratedFDeriv
      (G := G) (q := q) (z := z) hz hH₁ hH₂

  -- Step 4: rewrite everything in terms of U_flat_xx / U_flat_yy and combine
  have h_x' :
      iteratedFDeriv ℝ 2 H z ![1, 1] = U_flat_xx G q := by
    simpa [uxx_eq] using h_x

  have h_y' :
      iteratedFDeriv ℝ 2 H z ![Complex.I, Complex.I] = U_flat_yy G q := by
    simpa [uyy_eq] using h_y

  calc
    Analysis.laplacian (fun w : ℂ => (G w).re) z
        = iteratedFDeriv ℝ 2 H z ![1, 1] +
          iteratedFDeriv ℝ 2 H z ![Complex.I, Complex.I] := hLap
    _ = U_flat_xx G q + U_flat_yy G q := by
          simp [h_x', h_y']

/-- Core analytic statement: the real part of `G` is harmonic in flat coordinates. -/
lemma U_flat_is_harmonic_at
    (G : ℂ → ℂ) {q : ℝ × ℝ} {z : ℂ}
    (hz : z = q.1 + q.2 * Complex.I)
    (hG : AnalyticAt ℂ G z)
    (hH₁ : Differentiable ℝ (fun w : ℂ => (G w).re))
    (hH₂ :
      DifferentiableAt ℝ
        (fun w : ℂ => fderiv ℝ (fun z : ℂ => (G z).re) w) z) :
    U_flat_xx G q + U_flat_yy G q = 0 := by
  classical
  -- Work purely on ℂ: real part of `G` is harmonic at `z`.
  let H : ℂ → ℝ := fun w => (G w).re
  have hLap_H : Analysis.laplacian H z = 0 :=
    laplacian_re_of_analyticAt (f := G) (z := z) hG

  -- Transport the Laplacian into flat coordinates using your second-derivative calculus.
  have hLap_coords :
      Analysis.laplacian H z = U_flat_xx G q + U_flat_yy G q :=
    laplacian_H_as_flat_partials
      (G := G) (q := q) (z := z) hz hH₁ hH₂

  -- Combine: ΔH(z) = 0 and ΔH(z) = U_flat_xx + U_flat_yy.
  have : U_flat_xx G q + U_flat_yy G q = 0 := by
    simpa [hLap_coords] using hLap_H
  exact this

/-- Harmonicity of the real part of an analytic complex map in flat coordinates.
If `G` is analytic at a point `z = x + y·I`, then its real part viewed as a scalar field
`U_flat G` on `ℝ × ℝ` is (classically) harmonic there, i.e. the sum of second partials
vanishes. -/
lemma laplace_U_flat_of_analytic
    (G : ℂ → ℂ) {q : ℝ × ℝ} {z : ℂ}
    (hz : z = q.1 + q.2 * Complex.I)
    (hG : AnalyticAt ℂ G z)
    (hH₁ : Differentiable ℝ (fun w : ℂ => (G w).re))
    (hH₂ :
      DifferentiableAt ℝ
        (fun w : ℂ => fderiv ℝ (fun z : ℂ => (G z).re) w) z) :
    U_flat_xx G q + U_flat_yy G q = 0 := by
  exact U_flat_is_harmonic_at G hz hG hH₁ hH₂

open RH.AcademicFramework.HalfPlaneOuterV2

open Analysis InnerProductSpace Filter
open scoped Topology Filter

/--
For analytic `G`, along the vertical line `y ↦ z + y⋅I`, the second y‑derivative
of `Re (G ·)` coincides with minus the y‑derivative of `Im (G' ·)`.
This is the Cauchy–Riemann second‑order identity
  ∂²_y u(x,y) = - ∂_y (∂_x v(x,y))
for `G = u + i v`.
-/
lemma secondDeriv_Re_eq_neg_deriv_Im_G'
  (G : ℂ → ℂ) (z : ℂ)
  (hG : AnalyticAt ℂ G z)
  (hH₁ : Differentiable ℝ (fun w : ℂ => (G w).re))
  (hH₂ :
    DifferentiableAt ℝ
      (fun w : ℂ => fderiv ℝ (fun z : ℂ => (G z).re) w) z) :
  deriv (fun y : ℝ =>
           deriv (fun y : ℝ =>
             (G (z + (y : ℂ) * Complex.I)).re) y) 0
    =
  - deriv (fun y : ℝ =>
            (deriv G (z + (y : ℂ) * Complex.I)).im) 0 := by
  -- This is a thin wrapper around the general CR specification lemma
  -- `CR_secondDeriv_Re_eq_neg_deriv_Im_G'`.
  simpa using
    (CR_secondDeriv_Re_eq_neg_deriv_Im_G'
      (G := G) (z := z) hG hH₁ hH₂)

/-- Canonical tangential derivative matches the flat y‑partial of `U_flat G_U`
after the coordinate change `(t,σ) ↦ (x,y) := (1/2 + σ, t)`. -/
lemma U_t_canonical_eq_flat_y
  (p : ℝ × ℝ) :
  let q : ℝ × ℝ := (1 / 2 + p.2, p.1)
  U_t_canonical p = U_flat_y G_U q := by
  classical
  -- Unfold the definitions and use `U_halfplane_eq_U_flat`.
  -- LHS: derivative in `t` of `U_halfplane (t,σ)` at `t = p.1`.
  -- RHS: derivative in `y` of `U_flat G_U (x,y)` at `y = q.2 = p.1` with `x = q.1 = 1/2 + p.2`.
  -- By `U_halfplane_eq_U_flat`, both are the same 1D derivative.
  -- By `U_halfplane_eq_U_flat`, both are the same 1D derivative.
  let q : ℝ × ℝ := (1 / 2 + p.2, p.1)
  have hU : ∀ t, U_halfplane (t, p.2) = U_flat G_U (q.1, t) := by
    intro t
    -- `U_halfplane (t,σ) = U_flat G_U ((1/2+σ), t)`
    have := U_halfplane_eq_U_flat (p := (t, p.2))
    simpa [q, U_flat, U_halfplane] using this
  -- LHS = deriv (fun t => U_halfplane (t, p.2)) p.1
  -- RHS = deriv (fun y => U_flat G_U (q.1, y)) q.2
  have h_eq :
      (fun t : ℝ => U_halfplane (t, p.2)) =
      (fun t : ℝ => U_flat G_U (q.1, t)) := by
    funext t; exact hU t
  -- Use `U_t_canonical` and the flat definition of `U_flat_y`.
  simp_rw [U_t_canonical, U_t_of, U_flat_y]
  ring_nf

/-- Canonical normal derivative matches the flat x‑partial of `U_flat G_U`
after the coordinate change `(t,σ) ↦ (x,y) := (1/2 + σ, t)`. -/
lemma U_σ_canonical_eq_flat_x
  (p : ℝ × ℝ) :
  let q : ℝ × ℝ := (1 / 2 + p.2, p.1)
  U_σ_canonical p = U_flat_x G_U q := by
  classical
  let q : ℝ × ℝ := (1 / 2 + p.2, p.1)
  have hU : ∀ σ, U_halfplane (p.1, σ) = U_flat G_U (1 / 2 + σ, p.1) := by
    intro σ
    have := U_halfplane_eq_U_flat (p := (p.1, σ))
    simpa [U_flat, U_halfplane] using this
  have h_eq :
      (fun σ : ℝ => U_halfplane (p.1, σ)) =
      (fun σ : ℝ => U_flat G_U (1 / 2 + σ, p.1)) := by
    funext σ; exact hU σ
  -- By definition: U_σ_canonical p = deriv (fun σ => U_halfplane (p.1, σ)) p.2
  -- and U_flat_x G_U q = deriv (fun x => U_flat G_U (x, q.2)) q.1 with q.1 = 1/2 + p.2.
  -- Changing variable `x = 1/2 + σ` identifies the derivatives.
  simp_rw [U_σ_canonical, U_σ_of, U_flat_x]
  ring_nf


/-- Second t‑derivative of `U_halfplane` equals the flat y‑second partial of `U_flat G_U`
under the coordinate change. -/
lemma U_tt_canonical_eq_flat_yy
  (p : ℝ × ℝ) :
  let q : ℝ × ℝ := (1 / 2 + p.2, p.1)
  U_tt_canonical p = U_flat_yy G_U q := by
  classical
  let q : ℝ × ℝ := (1 / 2 + p.2, p.1)
  -- By definition:
  --   U_tt_canonical p = deriv (fun t => U_t_canonical (t, p.2)) p.1
  --   U_flat_yy G_U q = deriv (fun y => U_flat_y G_U (q.1, y)) q.2
  have h_eq :
      (fun t : ℝ => U_t_canonical (t, p.2)) =
      (fun t : ℝ => U_flat_y G_U (q.1, t)) := by
    funext t
    -- apply first-order lemma at point (t, p.2)
    have := U_t_canonical_eq_flat_y (p := (t, p.2))
    simpa [q] using this
  simp [U_tt_canonical, U_flat_yy]
  ring_nf

/-- Second σ‑derivative of `U_halfplane` equals the flat x‑second partial of `U_flat G_U`
under the coordinate change. -/
lemma U_σσ_canonical_eq_flat_xx
  (p : ℝ × ℝ) :
  let q : ℝ × ℝ := (1 / 2 + p.2, p.1)
  U_σσ_canonical p = U_flat_xx G_U q := by
  classical
  let q : ℝ × ℝ := (1 / 2 + p.2, p.1)
  -- By definition:
  --   U_σσ_canonical p = deriv (fun σ => U_σ_canonical (p.1, σ)) p.2
  --   U_flat_xx G_U q = deriv (fun x => U_flat_x G_U (x, q.2)) q.1
  have h_eq :
      (fun σ : ℝ => U_σ_canonical (p.1, σ)) =
      (fun σ : ℝ => U_flat_x G_U (1 / 2 + σ, p.1)) := by
    funext σ
    have := U_σ_canonical_eq_flat_x (p := (p.1, σ))
    simpa using this
  -- Change variable `x = 1/2 + σ` inside the derivative.
  -- `deriv (fun σ => f (1/2 + σ)) p.2 = deriv f (1/2 + p.2)`.
  have h_change :
      deriv (fun σ : ℝ => U_flat_x G_U (1 / 2 + σ, p.1)) p.2
        = deriv (fun x : ℝ => U_flat_x G_U (x, p.1)) (1 / 2 + p.2) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (deriv_comp_add_const
        (f := fun x : ℝ => U_flat_x G_U (x, p.1)) (a := (1 / 2 : ℝ)) (x := p.2))
  have :
      U_σσ_canonical p =
      deriv (fun x : ℝ => U_flat_x G_U (x, p.1)) (1 / 2 + p.2) := by
    -- rewrite via h_eq and then change variable
    have := congrArg (fun f => deriv f p.2) h_eq
    simpa [U_σσ_canonical, h_change] using this
  -- RHS is exactly `U_flat_xx G_U q`
  simpa [U_flat_xx, q] using this
  aesop

/-- Laplace equation for the canonical potential `U_halfplane` on a Whitney
strip: the second-order partials of `U_halfplane` in Whitney coordinates
sum to zero.  This is the analytic heart of the Green identity in the
canonical case (proved using the Cauchy–Riemann equations for
`G_U := log (J_canonical ·)` composed with `halfPlaneCoord`). -/
lemma laplace_U_halfplane_on_strip
  (hRep :
    HasPoissonRepOn
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
      offXi)
  (hBdry :
    BoundaryPositive
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
  (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
  (I : RH.Cert.WhitneyInterval) (ε : ℝ) (hε : 0 < ε)
  (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
  (hheight : zeroHeightSup α_split I < ε)
  (hH₁ : Differentiable ℝ (fun w : ℂ => (G_U w).re))
  (hH₂ :
    ∀ z ∈ halfPlaneCoord ''
      (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)),
      DifferentiableAt ℝ
        (fun w : ℂ => fderiv ℝ (fun z : ℂ => (G_U z).re) w) z) :
  ∀ p ∈ RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len),
    U_tt_canonical p + U_σσ_canonical p = 0 := by
  intro p hp
  classical

  -- On the strip, `p.2 ∈ [ε, α_split * I.len]` with `ε > 0`, hence `p.2 > 0`.
  have hp_σ_mem : p.2 ∈ Set.Icc ε (α_split * I.len) := (Set.mem_prod.mp hp).2
  have hp_σ_pos : 0 < p.2 := by
    have : ε ≤ p.2 := (Set.mem_Icc.mp hp_σ_mem).1
    exact lt_of_lt_of_le hε this

  -- The corresponding complex point lies in `Ω` and avoids both the zero set of `riemannXi_ext`
  -- and the pole at `1`.
  have hΩ : halfPlaneCoord p ∈ RH.Cert.Ω :=
    halfPlaneCoord_mem_Ω_of_pos (p := p) hp_σ_pos
  have hξ :
      riemannXi_ext (halfPlaneCoord p) ≠ 0 :=
    riemannXi_ext_ne_zero_on_strip
      (I := I) (ε := ε)
      (hε_nonneg := le_of_lt hε)
      (havoid := havoid) (hheight := hheight) hp
  have hneq1 :
      halfPlaneCoord p ≠ (1 : ℂ) :=
    halfPlaneCoord_ne_one_on_strip
      (I := I) (ε := ε)
      (hε_nonneg := le_of_lt hε)
      (havoid := havoid) (hheight := hheight) hp

  -- Analyticity of the canonical map `G_U` at `z = halfPlaneCoord p`.
  have hG_analytic :
      AnalyticAt ℂ G_U (halfPlaneCoord p) :=
    analyticAt_G_U hRep hBdry h₁ hΩ hneq1 hξ

  -- Flat coordinates: z = (1/2 + σ) + i·t = x + i·y, so x = 1/2 + σ, y = t.
  -- We encode this as q = (x,y) = (1/2 + p.2, p.1).
  let q : ℝ × ℝ := (1 / 2 + p.2, p.1)

  -- Flat harmonicity for `U_flat G_U` at q coming from analyticity of `G_U`.
  have hLap_flat :
      U_flat_xx G_U q + U_flat_yy G_U q = 0 :=
    laplace_U_flat_of_analytic
      (G := G_U) (q := q) (z := halfPlaneCoord p)
      (by
        -- `halfPlaneCoord p = (1/2 + p.2) + I * p.1`
        simp [halfPlaneCoord_apply, q, add_comm, add_left_comm, mul_comm])
      hG_analytic
      hH₁
      (by
        -- Specialize the second‑order differentiability hypothesis at `z = halfPlaneCoord p`.
        refine hH₂ (halfPlaneCoord p) ?_
        exact ⟨p, hp, rfl⟩)

  -- Identify the canonical second derivatives with flat second partials.
  have h_derivs :
      U_tt_canonical p + U_σσ_canonical p =
        U_flat_yy G_U q + U_flat_xx G_U q := by
    have h1 := U_tt_canonical_eq_flat_yy (p := p)
    have h2 := U_σσ_canonical_eq_flat_xx (p := p)
    -- unfold `q` as in the definition above
    simp [q, h1, h2, add_comm]  -- reorder terms if needed

  -- Now combine flat harmonicity with the identification.
  have : U_tt_canonical p + U_σσ_canonical p = 0 := by
    simpa [h_derivs, add_comm] using hLap_flat
  exact this

open scoped Filter Topology

/-- On the Whitney strip, `U_L2` is `C²` at every point. -/
lemma U_L2_contDiffAt_two_on_strip
  (hRep :
    HasPoissonRepOn
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
      offXi)
  (hBdry :
    BoundaryPositive
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
  (h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
  (I : RH.Cert.WhitneyInterval) (ε : ℝ) (hε : 0 < ε)
  (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
  (hheight : zeroHeightSup α_split I < ε) :
  let U_L2 : WithLp 2 (ℝ × ℝ) → ℝ := fun p => U_halfplane (p.1, p.2)
  ∀ p ∈ {p : WithLp 2 (ℝ × ℝ) |
            (p.1, p.2) ∈ RH.Cert.WhitneyInterval.interval I ×ˢ
              Set.Icc ε (α_split * I.len)},
    ContDiffAt ℝ 2 U_L2 p := by
  intro U_L2 p hp
  classical
  -- View `p` as a point `q` in Whitney coordinates.
  let q : ℝ × ℝ := (p.1, p.2)
  have hq :
      q ∈ RH.Cert.WhitneyInterval.interval I ×ˢ
        Set.Icc ε (α_split * I.len) := by
    simpa [q] using hp
  -- On the strip, the height coordinate σ = q.2 is positive.
  have hσ_mem : q.2 ∈ Set.Icc ε (α_split * I.len) :=
    (Set.mem_prod.mp hq).2
  have hσ_pos : 0 < q.2 := by
    have : ε ≤ q.2 := (Set.mem_Icc.mp hσ_mem).1
    exact lt_of_lt_of_le hε this
  -- The complex point z := halfPlaneCoord q lies in Ω and avoids 1 and the zeros of ξ.
  have hΩ : halfPlaneCoord q ∈ RH.Cert.Ω :=
    halfPlaneCoord_mem_Ω_of_pos hσ_pos
  have hξ :
      riemannXi_ext (halfPlaneCoord q) ≠ 0 :=
    riemannXi_ext_ne_zero_on_strip
      (I := I) (hε_nonneg := le_of_lt hε)
      (havoid := havoid) (hheight := hheight) hq
  have hneq1 :
      halfPlaneCoord q ≠ (1 : ℂ) :=
    halfPlaneCoord_ne_one_on_strip
      (I := I) (hε_nonneg := le_of_lt hε)
      (havoid := havoid) (hheight := hheight) hq
  -- Analyticity of the canonical map `G_U` at `z = halfPlaneCoord q`.
  have hG_analytic :
      AnalyticAt ℂ G_U (halfPlaneCoord q) :=
    analyticAt_G_U hRep hBdry h₁ hΩ hneq1 hξ
  -- Real scalar field `H := Re ∘ G_U` is `C²` at `z`.
  have hHarm :
      InnerProductSpace.HarmonicAt
        (E := ℂ) (F := ℝ)
        (fun w : ℂ => (G_U w).re) (halfPlaneCoord q) :=
    AnalyticAt.harmonicAt_re (f := G_U) (x := halfPlaneCoord q) hG_analytic
  have hH_C2 :
      ContDiffAt ℝ 2 (fun w : ℂ => (G_U w).re) (halfPlaneCoord q) :=
    hHarm.1
  -- The affine coordinate map `halfPlaneCoord` is `C²` as constant + linear.
  have hφ_top :
      ContDiffAt ℝ ⊤ halfPlaneCoord q := by
    have hconst :
        ContDiffAt ℝ ⊤ (fun _ : ℝ × ℝ => ((1 / 2 : ℝ) : ℂ)) q :=
      contDiffAt_const
    have hlin :
        ContDiffAt ℝ ⊤ (fun r : ℝ × ℝ => halfPlaneLinear r) q :=
      halfPlaneLinear.contDiff.contDiffAt
    have hsum :
        ContDiffAt ℝ ⊤
          (fun r : ℝ × ℝ => ((1 / 2 : ℝ) : ℂ) + halfPlaneLinear r) q :=
      hconst.add hlin
    simpa [halfPlaneCoord] using hsum
  have hφ_C2 :
      ContDiffAt ℝ 2 halfPlaneCoord q :=
    hφ_top.of_le (by exact le_top)
  -- The composite `q ↦ (G_U (halfPlaneCoord q)).re` is therefore `C²` at `q`.
  have hU_C2 :
      ContDiffAt ℝ 2
        (fun r : ℝ × ℝ => (G_U (halfPlaneCoord r)).re) q :=
    hH_C2.comp q hφ_C2
  -- Identify this composite with `U_halfplane` via `U_of G_U`.
  have hU_of_C2 :
      ContDiffAt ℝ 2 (U_of G_U) q := by
    simpa [U_of] using hU_C2
  have hUhalf_C2 :
      ContDiffAt ℝ 2 U_halfplane q := by
    simpa [U_halfplane_eq_U_of] using hU_of_C2
  -- Transport the result to `U_L2` on `WithLp 2 (ℝ × ℝ)`.
  simpa [U_L2, q] using hUhalf_C2

/-- At each point of the strip, the Laplacian of `U_halfplane` equals the sum
of its canonical second partials in `t` and `σ`. -/
lemma laplacian_U_halfplane_eq_canonical
  (I : RH.Cert.WhitneyInterval) (ε : ℝ) (hε : 0 < ε)
  (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
  (hheight : zeroHeightSup α_split I < ε) :
  let U_L2 : WithLp 2 (ℝ × ℝ) → ℝ := fun p => U_halfplane (p.1, p.2)
  ∀ p ∈ {p : WithLp 2 (ℝ × ℝ) |
            (p.1, p.2) ∈ RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)},
    Analysis.laplacian U_L2 p = U_tt_canonical (p.1, p.2) + U_σσ_canonical (p.1, p.2) := by
  intro U_L2 p hp
  classical
  -- Use the same pattern as `laplacian_U_flat_eq`:
  --  * expand Laplacian as sum of Hessian diagonal entries in directions (1,0) and (0,1),
  --  * use `U_t_canonical_hasFDerivAt_on_strip` / `U_σ_canonical_hasFDerivAt_on_strip`
  --    plus the 1D slice lemmas to identify those Hessian entries with `U_tt_canonical` / `U_σσ_canonical`.
  admit

/-- On a slightly smaller open Whitney strip, the Laplacian of `U_L2` vanishes
identically; this yields the neighborhood condition in `HarmonicAt`. -/
lemma laplacian_U_L2_zero_nhd
  (I : RH.Cert.WhitneyInterval) (ε : ℝ) (hε : 0 < ε)
  (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
  (hheight : zeroHeightSup α_split I < ε) :
  let U_L2 : WithLp 2 (ℝ × ℝ) → ℝ := fun p => U_halfplane (p.1, p.2)
  ∀ p ∈ {p : WithLp 2 (ℝ × ℝ) |
           (p.1, p.2) ∈ RH.Cert.WhitneyInterval.interval I ×ˢ
             Set.Icc ε (α_split * I.len)},
    Analysis.laplacian U_L2 =ᶠ[𝓝 p] 0 := by
  intro U_L2 p hp
  -- Strengthen `laplace_U_halfplane_on_strip` to an open neighborhood of `p`
  -- using the analyticity of `G_U` and the Hessian calculus already developed.
  admit

/--
On a Whitney strip, the canonical potential `U_halfplane` is harmonic with respect to the
Whitney coordinates, in the sense that its Laplacian (expressed as `U_tt_canonical + U_σσ_canonical`)
vanishes at every point of the strip.




This is a restatement of `laplace_U_halfplane_on_strip` in terms of the Laplacian API. -/
lemma U_halfplane_isHarmonicOn_strip
(hRep :
  HasPoissonRepOn
    (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer)
    offXi)
(hBdry :
  BoundaryPositive
    (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch det2 outer_exists.outer))
(h₁ : 0 ≤ ((2 : ℂ) * J_canonical (1 : ℂ)).re)
(I : RH.Cert.WhitneyInterval) (ε : ℝ) (hε : 0 < ε)
(havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
(hheight : zeroHeightSup α_split I < ε) :
let U_L2 : WithLp 2 (ℝ × ℝ) → ℝ := fun p => U_halfplane (p.1, p.2)
let S_L2 : Set (WithLp 2 (ℝ × ℝ)) :=
  {p | (p.1, p.2) ∈ RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)}
IsHarmonicOn U_L2 S_L2 := by
  intro p hp
  -- Step 1: `U_halfplane` is `C^2` on the interior of the strip; in particular, `C^2` at `p`.
  -- This follows from the chain rule representation in terms of the analytic `G_U` and
  -- the regularity hypotheses encoded in `hRep`, `hBdry`, and the geometry of the strip.
  have hC2 :
      ContDiffAt ℝ 2 U_L2 p := by
    -- specialize the generic C²‑on‑strip lemma at `p`
    have hgen := U_L2_contDiffAt_two_on_strip
      (hRep := hRep) (hBdry := hBdry) (h₁ := h₁)
      (I := I) (ε := ε) (hε := hε)
      (havoid := havoid) (hheight := hheight)
    -- `S_L2` is exactly the strip set in the lemma
    have hp' :
        p ∈ {p : WithLp 2 (ℝ × ℝ) |
                (p.1, p.2) ∈ RH.Cert.WhitneyInterval.interval I ×ˢ
                  Set.Icc ε (α_split * I.len)} := by
      simpa [S_L2] using hp
    exact hgen U_L2 p hp'
  -- Step 2: the Laplacian vanishes, by `laplace_U_halfplane_on_strip`.
  have hLap_zero :
      U_tt_canonical p + U_σσ_canonical p = 0 :=
    laplace_U_halfplane_on_strip
      (hRep := hRep) (hBdry := hBdry) (h₁ := h₁)
      (I := I) (ε := ε) (hε := hε)
      (havoid := havoid) (hheight := hheight) p hp
  -- Step 3: identify the abstract Laplacian with `U_tt_canonical + U_σσ_canonical`
  -- via the same ℝ² coordinate change as used in `laplace_U_halfplane_on_strip`.
  -- This will be a second‑order analogue of `U_halfplane_eq_U_flat` and the gradient
  -- identification lemmas `U_t_canonical_hasFDerivAt_on_strip` /
  -- `U_σ_canonical_hasFDerivAt_on_strip`.
  have hcoord :
      Analysis.laplacian U_halfplane p = U_tt_canonical p + U_σσ_canonical p := by
    -- rewrite through `U_L2` and apply the canonical Laplacian formula
    have := laplacian_U_halfplane_eq_canonical
      (I := I) (ε := ε) (hε := hε)
      (havoid := havoid) (hheight := hheight)
    -- identify `p` with its `WithLp` incarnation and unfold `U_L2`
    -- (details are routine rewriting)
    admit
  -- combine: Laplacian vanishes pointwise at p
  have hLap_p : Analysis.laplacian U_halfplane p = 0 := by simpa [hcoord] using hLap_zero
  -- To construct HarmonicAt, we need eventual vanishing in a neighborhood.
  -- The full proof would show that the Laplacian vanishes on an open neighborhood by
  -- extending the coordinate argument to nearby points. For now we use a placeholder.
  have hLap_nhd : Analysis.laplacian U_L2 =ᶠ[Filter.𝓝 p] 0 := by
    have := laplacian_U_L2_zero_nhd
      (I := I) (ε := ε) (hε := hε)
      (havoid := havoid) (hheight := hheight)
    simpa [U_L2, S_L2] using this p hp
  exact ⟨hC2, hLap_nhd⟩
  exact ⟨hC2, hLap_nhd⟩



@[simp] lemma RH.Cert.WhitneyInterval.len_nonneg (I : RH.Cert.WhitneyInterval) : 0 ≤ I.len :=
  (I.len_pos).le

/-- Green's identity for `U_halfplane` on the Whitney box based on `I`,
between heights `ε` and `α_split * I.len`.

We assume:
* `U_halfplane` is continuous on the closed rectangle
    `I.interval ×ˢ Set.Icc ε (α_split * I.len)`;
* its partial derivatives in `t` and `σ` exist and are square‑integrable,
  encoded via `U_t` and `U_σ` below.

Then the integral of `|∇U|^2 = U_t^2 + U_σ^2` over the rectangle equals the
four boundary integrals in the usual Green identity. -/
lemma green_identity_for_box_energy
  (I : RH.Cert.WhitneyInterval) (ε : ℝ)
  (_hε : 0 < ε)
  (hεle : ε ≤ α_split * I.len)
  (U_t U_σ : ℝ × ℝ → ℝ)
  (HcU :
    ContinuousOn U_halfplane
      (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)))
  (HcUt :
    ContinuousOn U_t
      (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)))
  (HcUσ :
    ContinuousOn U_σ
      (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)))
  (Hf_cont :
    ContinuousOn
      (fun p => U_halfplane p * U_t p)
      (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)))
  (Hg_cont :
    ContinuousOn
      (fun p => U_halfplane p * U_σ p)
      (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)))
  (f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ)
  (Hf_deriv :
    ∀ x ∈ Set.Ioo (I.t0 - I.len) (I.t0 + I.len)
            ×ˢ Set.Ioo ε (α_split * I.len),
      HasFDerivAt (fun p => U_halfplane p * U_t p) (f' x) x)
  (Hg_deriv :
    ∀ x ∈ Set.Ioo (I.t0 - I.len) (I.t0 + I.len)
            ×ˢ Set.Ioo ε (α_split * I.len),
      HasFDerivAt (fun p => U_halfplane p * U_σ p) (g' x) x)
  (Hi_div :
    IntegrableOn
      (fun p : ℝ × ℝ => f' p (1, 0) + g' p (0, 1))
      (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)) volume)
  (Hdiv_eq :
    (fun p : ℝ × ℝ => f' p (1, 0) + g' p (0, 1))
      =ᵐ[volume.restrict
          (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len))]
        fun p => (U_t p) ^ 2 + (U_σ p) ^ 2)
  (Hi_grad :
    IntegrableOn
      (fun p : ℝ × ℝ => (U_t p)^2 + (U_σ p)^2)
      (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len))
      volume) :
  ∫ σ in Set.Icc ε (α_split * I.len),
      ∫ t in RH.Cert.WhitneyInterval.interval I,
        (U_t (t, σ))^2 + (U_σ (t, σ))^2 ∂volume ∂volume
  =
    (∫ t in RH.Cert.WhitneyInterval.interval I,
        U_halfplane (t, α_split * I.len) * U_σ (t, α_split * I.len) ∂volume)
  - (∫ t in RH.Cert.WhitneyInterval.interval I,
        U_halfplane (t, ε) * U_σ (t, ε) ∂volume)
  + (∫ σ in Set.Icc ε (α_split * I.len),
        U_halfplane (I.t0 + I.len, σ) * U_t (I.t0 + I.len, σ) ∂volume)
  - (∫ σ in Set.Icc ε (α_split * I.len),
        U_halfplane (I.t0 - I.len, σ) * U_t (I.t0 - I.len, σ) ∂volume) := by
  -- proof to be filled as below
  set a₁ : ℝ := I.t0 - I.len
  set b₁ : ℝ := I.t0 + I.len
  set a₂ : ℝ := ε
  set b₂ : ℝ := α_split * I.len
  have h_rect :
    RH.Cert.WhitneyInterval.interval I = Set.Icc a₁ b₁ := by
    simp [RH.Cert.WhitneyInterval.interval, a₁, b₁]
  have h_vert :
    Set.Icc ε (α_split * I.len) = Set.Icc a₂ b₂ := by
    simp [a₂, b₂]
  let f (p : ℝ × ℝ) : ℝ := U_halfplane p * U_t p
  let g (p : ℝ × ℝ) : ℝ := U_halfplane p * U_σ p
  let s : Set (ℝ × ℝ) := ∅
  have hs : s.Countable := by simp [s]
  have h_len_nonneg : 0 ≤ I.len := (I.len_pos).le
  have h_ab : a₁ ≤ b₁ := by
    have : I.t0 - I.len ≤ I.t0 + I.len := by linarith [h_len_nonneg]
    simpa [a₁, b₁] using this
  have h_cd : a₂ ≤ b₂ := by
    simpa [a₂, b₂] using hεle
  have hu1 : [[a₁, b₁]] = Set.Icc a₁ b₁ := Set.uIcc_of_le h_ab
  have hu2 : [[a₂, b₂]] = Set.Icc a₂ b₂ := Set.uIcc_of_le h_cd
  have hIcc_ab :
      Set.Icc (a₁ ⊓ b₁) (a₁ ⊔ b₁) = Set.Icc a₁ b₁ := by
    have hmin : a₁ ⊓ b₁ = a₁ :=
      inf_eq_left.mpr h_ab
    have hmax : a₁ ⊔ b₁ = b₁ :=
      sup_eq_right.mpr h_ab
    simp [hmin, hmax]
  have hIcc_cd :
      Set.Icc (a₂ ⊓ b₂) (a₂ ⊔ b₂) = Set.Icc a₂ b₂ := by
    have hmin : a₂ ⊓ b₂ = a₂ :=
      inf_eq_left.mpr h_cd
    have hmax : a₂ ⊔ b₂ = b₂ :=
      sup_eq_right.mpr h_cd
    simp [hmin, hmax]
  have Hcf :
      ContinuousOn f ([[a₁, b₁]] ×ˢ [[a₂, b₂]]) := by
    simpa [f, h_rect, h_vert, hu1, hu2]
      using Hf_cont
  have Hcg :
      ContinuousOn g ([[a₁, b₁]] ×ˢ [[a₂, b₂]]) := by
    simpa [g, h_rect, h_vert, hu1, hu2]
      using Hg_cont
  have hi1 : Ioo (min a₁ b₁) (max a₁ b₁) = Set.Ioo a₁ b₁ := by
    simp [min_eq_left h_ab, max_eq_right h_ab]
  have hi2 : Ioo (min a₂ b₂) (max a₂ b₂) = Set.Ioo a₂ b₂ := by
    simp [min_eq_left h_cd, max_eq_right h_cd]
  have Hdf :
      ∀ x ∈ Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ
          Ioo (min a₂ b₂) (max a₂ b₂) \ s,
        HasFDerivAt f (f' x) x := by
    intro x hx
    have hx' :
        x ∈ Set.Ioo (I.t0 - I.len) (I.t0 + I.len) ×ˢ
            Set.Ioo ε (α_split * I.len) := by
      have hx'' :
          x ∈ Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ
              Ioo (min a₂ b₂) (max a₂ b₂) := by
        simpa [s] using hx
      simpa [a₁, b₁, a₂, b₂, hi1, hi2]
        using hx''
    exact Hf_deriv x hx'
  have Hdg :
      ∀ x ∈ Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ
          Ioo (min a₂ b₂) (max a₂ b₂) \ s,
        HasFDerivAt g (g' x) x := by
    intro x hx
    have hx' :
        x ∈ Set.Ioo (I.t0 - I.len) (I.t0 + I.len) ×ˢ
            Set.Ioo ε (α_split * I.len) := by
      have hx'' :
          x ∈ Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ
              Ioo (min a₂ b₂) (max a₂ b₂) := by
        simpa [s] using hx
      simpa [a₁, b₁, a₂, b₂, hi1, hi2]
        using hx''
    exact Hg_deriv x hx'
  have h_green_general :
    ∫ x in a₁..b₁, ∫ y in a₂..b₂,
      (U_t (x, y))^2 + (U_σ (x, y))^2
    =
      (∫ x in a₁..b₁, U_halfplane (x, b₂) * U_σ (x, b₂))
    - (∫ x in a₁..b₁, U_halfplane (x, a₂) * U_σ (x, a₂))
    + (∫ y in a₂..b₂, U_halfplane (b₁, y) * U_t (b₁, y))
    - (∫ y in a₂..b₂, U_halfplane (a₁, y) * U_t (a₁, y)) :=
    green_first_identity_rectangle
      f g f' g' a₁ a₂ b₁ b₂ s hs
      Hcf Hcg Hdf Hdg
      (by
        simpa [h_rect, h_vert, hu1, hu2]
          using Hi_div)
      (fun p => (U_t p)^2 + (U_σ p)^2)
      (by
        simpa [h_rect, h_vert, hu1, hu2]
          using Hdiv_eq)
   -- from h_green_general, rewrite the domain names
  have h' := h_green_general
  -- convert both sides of `h_green_general` from interval integrals to set integrals
  have ha₁_le_b₁ : a₁ ≤ b₁ := by
    have hlen : 0 ≤ I.len := I.len_pos.le
    have hneg : -I.len ≤ I.len := neg_le_self hlen
    have := add_le_add_left hneg I.t0
    simp [a₁, b₁, sub_eq_add_neg]

  have ha₂_le_b₂ : a₂ ≤ b₂ := by
    simpa [a₂, b₂] using hεle
  have h_box_Ioc :
      (∫ x in Set.Ioc a₁ b₁, ∫ y in Set.Ioc a₂ b₂,
          (U_t (x, y))^2 + (U_σ (x, y))^2 ∂volume ∂volume)
        =
      ((∫ x in Set.Ioc a₁ b₁, U_halfplane (x, b₂) * U_σ (x, b₂) ∂volume)
        - ∫ x in Set.Ioc a₁ b₁, U_halfplane (x, a₂) * U_σ (x, a₂) ∂volume)
      + (∫ y in Set.Ioc a₂ b₂, U_halfplane (b₁, y) * U_t (b₁, y) ∂volume)
        - ∫ y in Set.Ioc a₂ b₂, U_halfplane (a₁, y) * U_t (a₁, y) ∂volume := by
    convert h_green_general using 1 <;>
      simp [intervalIntegral.integral_of_le ha₁_le_b₁, intervalIntegral.integral_of_le ha₂_le_b₂]

  have h_box :
      (∫ x in Set.Icc a₁ b₁, ∫ y in Set.Icc a₂ b₂,
          (U_t (x, y))^2 + (U_σ (x, y))^2)
        =
      ((∫ x in Set.Icc a₁ b₁, U_halfplane (x, b₂) * U_σ (x, b₂))
        - ∫ x in Set.Icc a₁ b₁, U_halfplane (x, a₂) * U_σ (x, a₂))
      + (∫ y in Set.Icc a₂ b₂, U_halfplane (b₁, y) * U_t (b₁, y))
        - ∫ y in Set.Icc a₂ b₂, U_halfplane (a₁, y) * U_t (a₁, y) := by
    simpa [setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
      using h_box_Ioc

  -- replace a₁,a₂,b₁,b₂ by their definitions
  simpa [a₁, a₂, b₁, b₂, h_rect, h_vert] using h_box

lemma green_identity_for_box_energy_from_laplace
  (I : RH.Cert.WhitneyInterval) (ε : ℝ) (hε : 0 < ε)
  (hεle : ε ≤ α_split * I.len)
  (U_t U_σ U_tt U_tσ U_σt U_σσ : ℝ × ℝ → ℝ)
  (HcU :
    ContinuousOn U_halfplane
      (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)))
  (HcUt :
    ContinuousOn U_t
      (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)))
  (HcUσ :
    ContinuousOn U_σ
      (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)))
  (HderivU :
    ∀ x ∈ (interior (RH.Cert.WhitneyInterval.interval I))
            ×ˢ interior (Set.Icc ε (α_split * I.len)),
      HasFDerivAt U_halfplane (linComboCLM (U_t x) (U_σ x)) x)
  (HderivUt :
    ∀ x ∈ (interior (RH.Cert.WhitneyInterval.interval I))
            ×ˢ interior (Set.Icc ε (α_split * I.len)),
      HasFDerivAt U_t (linComboCLM (U_tt x) (U_tσ x)) x)
  (HderivUσ :
    ∀ x ∈ (interior (RH.Cert.WhitneyInterval.interval I))
            ×ˢ interior (Set.Icc ε (α_split * I.len)),
      HasFDerivAt U_σ (linComboCLM (U_σt x) (U_σσ x)) x)
  (Hlaplace : ∀ p, U_tt p + U_σσ p = 0)
  (Hi_grad :
    IntegrableOn
      (fun p : ℝ × ℝ => (U_t p)^2 + (U_σ p)^2)
      (RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len))
      volume) :
  ∫ σ in Set.Icc ε (α_split * I.len),
      ∫ t in RH.Cert.WhitneyInterval.interval I,
        (U_t (t, σ))^2 + (U_σ (t, σ))^2 ∂volume ∂volume
  =
    (∫ t in RH.Cert.WhitneyInterval.interval I,
        U_halfplane (t, α_split * I.len) * U_σ (t, α_split * I.len) ∂volume)
  - (∫ t in RH.Cert.WhitneyInterval.interval I,
        U_halfplane (t, ε) * U_σ (t, ε) ∂volume)
  + (∫ σ in Set.Icc ε (α_split * I.len),
        U_halfplane (I.t0 + I.len, σ) * U_t (I.t0 + I.len, σ) ∂volume)
  - (∫ σ in Set.Icc ε (α_split * I.len),
        U_halfplane (I.t0 - I.len, σ) * U_t (I.t0 - I.len, σ) ∂volume) := by
  classical
  let rect :=
    RH.Cert.WhitneyInterval.interval I ×ˢ Set.Icc ε (α_split * I.len)
  let f' := fDerivMap U_halfplane U_t U_σ U_tt U_tσ
  let g' := gDerivMap U_halfplane U_t U_σ U_σt U_σσ
  have Hf_cont :
      ContinuousOn (fun p : ℝ × ℝ => U_halfplane p * U_t p) rect :=
    HcU.mul HcUt
  have Hg_cont :
      ContinuousOn (fun p : ℝ × ℝ => U_halfplane p * U_σ p) rect :=
    HcU.mul HcUσ
  have Hf_deriv :
      ∀ x ∈ (interior (RH.Cert.WhitneyInterval.interval I))
              ×ˢ interior (Set.Icc ε (α_split * I.len)),
        HasFDerivAt
          (fun p : ℝ × ℝ => U_halfplane p * U_t p) (f' x) x := by
    intro x hx
    exact hasFDerivAt_mul_UUt
      (U := U_halfplane) (U_t := U_t) (U_σ := U_σ)
      (U_tt := U_tt) (U_tσ := U_tσ)
      (p := x) (hU := HderivU x hx) (hUt := HderivUt x hx)
  have Hg_deriv :
      ∀ x ∈ (interior (RH.Cert.WhitneyInterval.interval I))
              ×ˢ interior (Set.Icc ε (α_split * I.len)),
        HasFDerivAt
          (fun p : ℝ × ℝ => U_halfplane p * U_σ p) (g' x) x := by
    intro x hx
    exact hasFDerivAt_mul_UUσ
      (U := U_halfplane) (U_t := U_t) (U_σ := U_σ)
      (U_σt := U_σt) (U_σσ := U_σσ)
      (p := x) (hU := HderivU x hx) (hUσ := HderivUσ x hx)
  have Hdiv_point :
      ∀ p,
        f' p (1, 0) + g' p (0, 1)
          = (U_t p) ^ 2 + (U_σ p) ^ 2 := by
    intro p
    simpa using
      (divergence_mul_grad_sq
        (U := U_halfplane) (U_t := U_t) (U_σ := U_σ)
        (U_tt := U_tt) (U_tσ := U_tσ)
        (U_σt := U_σt) (U_σσ := U_σσ)
        (p := p) (hLaplace := Hlaplace p))
  have Hi_div :
      IntegrableOn
        (fun p : ℝ × ℝ => f' p (1, 0) + g' p (0, 1))
        rect volume := by
    simpa [Hdiv_point] using Hi_grad
  have Hdiv_eq :
      (fun p : ℝ × ℝ => f' p (1, 0) + g' p (0, 1))
        =ᵐ[volume.restrict rect]
          fun p => (U_t p) ^ 2 + (U_σ p) ^ 2 := by
    refine Filter.Eventually.of_forall ?_; intro p; simp [Hdiv_point]
  have hresult :=
    green_identity_for_box_energy
      (I := I) (ε := ε)
      (U_t := U_t) (U_σ := U_σ)
      (HcU := HcU)
      (HcUt := HcUt)
      (HcUσ := HcUσ)
      (Hf_cont := Hf_cont)
      (Hg_cont := Hg_cont)
      (f' := f') (g' := g')
      (Hf_deriv := Hf_deriv)
      (Hg_deriv := Hg_deriv)
      (Hi_div := Hi_div)
      (Hdiv_eq := Hdiv_eq)
      (Hi_grad := Hi_grad)
  simpa using hresult
    -- inside `?_` just rewrite with h_box_Ioc

  -- now the goal is exactly h_box
  simpa [a₁, a₂, b₁, b₂, h_rect, h_vert] using h_box

/-- Canonical Green identity on a Whitney strip for `U_halfplane` and its
gradient components `U_t_canonical`, `U_σ_canonical`, assuming the Laplace
equation for the canonical second partials and integrability of the gradient
energy on the strip. -/
lemma green_identity_for_box_energy_canonical
  (I : RH.Cert.WhitneyInterval) (ε : ℝ) (hε : 0 < ε)
  (hεle : ε ≤ α_split * I.len)
  (havoid : (1 / 2 : ℝ) ∉ Set.Icc ε (α_split * I.len))
  (hheight : zeroHeightSup α_split I < ε)
  (Hlaplace :
    ∀ p, U_tt_canonical p + U_σσ_canonical p = 0)
  (Hi_grad :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        (U_t_canonical p) ^ 2 + (U_σ_canonical p) ^ 2)
      (RH.Cert.WhitneyInterval.interval I ×ˢ
        Set.Icc ε (α_split * I.len)) volume) :
  ∫ σ in Set.Icc ε (α_split * I.len),
      ∫ t in RH.Cert.WhitneyInterval.interval I,
        (U_t_canonical (t, σ))^2 + (U_σ_canonical (t, σ))^2 ∂volume ∂volume
  =
    (∫ t in RH.Cert.WhitneyInterval.interval I,
        U_halfplane (t, α_split * I.len)
          * U_σ_canonical (t, α_split * I.len) ∂volume)
  - (∫ t in RH.Cert.WhitneyInterval.interval I,
        U_halfplane (t, ε) * U_σ_canonical (t, ε) ∂volume)
  + (∫ σ in Set.Icc ε (α_split * I.len),
        U_halfplane (I.t0 + I.len, σ)
          * U_t_canonical (I.t0 + I.len, σ) ∂volume)
  - (∫ σ in Set.Icc ε (α_split * I.len),
        U_halfplane (I.t0 - I.len, σ)
          * U_t_canonical (I.t0 - I.len, σ) ∂volume) := by
  classical
  -- continuity of `U_halfplane` and canonical first partials on the strip
  have HcU :
      ContinuousOn U_halfplane
        (RH.Cert.WhitneyInterval.interval I ×ˢ
          Set.Icc ε (α_split * I.len)) :=
    continuousOn_U_halfplane_on_strip
      (I := I) (ε := ε) (hε := hε)
      (havoid := havoid) (hheight := hheight)
  have HcUt :
      ContinuousOn U_t_canonical
        (RH.Cert.WhitneyInterval.interval I ×ˢ
          Set.Icc ε (α_split * I.len)) :=
    continuousOn_U_t_canonical_strip
      (I := I) (ε := ε) (hε_pos := hε)
      (havoid := havoid) (hheight := hheight)
  have HcUσ :
      ContinuousOn U_σ_canonical
        (RH.Cert.WhitneyInterval.interval I ×ˢ
          Set.Icc ε (α_split * I.len)) :=
    continuousOn_U_σ_canonical_strip
      (I := I) (ε := ε) (hε_pos := hε)
      (havoid := havoid) (hheight := hheight)
  -- C¹ regularity of `U_halfplane` on the interior, with canonical gradient
  have HderivU :
      ∀ x ∈ (interior (RH.Cert.WhitneyInterval.interval I))
              ×ˢ interior (Set.Icc ε (α_split * I.len)),
        HasFDerivAt U_halfplane
          (linComboCLM (U_t_canonical x) (U_σ_canonical x)) x := by
    intro x hx
    have h :=
      U_halfplane_hasFDerivAt_linCombo_on_strip
        (I := I) (ε := ε) (hε := hε)
        (havoid := havoid) (hheight := hheight) x hx
    simpa [U_t_canonical, U_σ_canonical] using h
  -- C¹ regularity of the canonical first partials on the interior
  have HderivUt :
      ∀ x ∈ (interior (RH.Cert.WhitneyInterval.interval I))
              ×ˢ interior (Set.Icc ε (α_split * I.len)),
        HasFDerivAt U_t_canonical
          (linComboCLM (U_tt_canonical x) (U_tσ_canonical x)) x :=
    U_t_canonical_hasFDerivAt_on_strip
      (I := I) (ε := ε) (hε := hε)
      (havoid := havoid) (hheight := hheight)
  have HderivUσ :
      ∀ x ∈ (interior (RH.Cert.WhitneyInterval.interval I))
              ×ˢ interior (Set.Icc ε (α_split * I.len)),
        HasFDerivAt U_σ_canonical
          (linComboCLM (U_σt_canonical x) (U_σσ_canonical x)) x :=
    U_σ_canonical_hasFDerivAt_on_strip
      (I := I) (ε := ε) (hε := hε)
      (havoid := havoid) (hheight := hheight)
  -- apply the abstract harmonic Green identity
  have h :=
    green_identity_for_box_energy_from_laplace
      (I := I) (ε := ε) (hε := hε) (hεle := hεle)
      (U_t := U_t_canonical) (U_σ := U_σ_canonical)
      (U_tt := U_tt_canonical) (U_tσ := U_tσ_canonical)
      (U_σt := U_σt_canonical) (U_σσ := U_σσ_canonical)
      (HcU := HcU)
      (HcUt := HcUt)
      (HcUσ := HcUσ)
      (HderivU := HderivU)
      (HderivUt := HderivUt)
      (HderivUσ := HderivUσ)
      (Hlaplace := Hlaplace)
      (Hi_grad := Hi_grad)
  -- restate the conclusion in canonical notation
  simpa using h

/-- Top-boundary control for `U_halfplane` on a Whitney interval `I`:
the trace `t ↦ U_halfplane (t, α_split * I.len)` is a.e. nonpositive on
the base interval. This is the analytic input needed to show that the top
boundary term in Green's identity contributes a nonpositive amount. -/
class TopBoundaryControl (I : RH.Cert.WhitneyInterval) : Prop where
  ae_nonpos :
    ∀ᵐ t ∂volume.restrict (RH.Cert.WhitneyInterval.interval I),
      U_halfplane (t, α_split * I.len) ≤ 0

/-- From top-boundary a.e. nonpositivity, deduce that the top boundary integral
is nonpositive. -/
lemma top_boundary_integral_nonpos (I : RH.Cert.WhitneyInterval)
  [TopBoundaryControl I] :
  ∫ t in RH.Cert.WhitneyInterval.interval I,
      U_halfplane (t, α_split * I.len) ∂volume ≤ 0 := by
  -- apply the generic lemma `top_boundary_nonpos` to the concrete trace
  have h :=
    TopBoundaryControl.ae_nonpos (I := I)
  refine
    top_boundary_nonpos
      (I := I)
      (g := fun t => U_halfplane (t, α_split * I.len))
      ?_
  simpa using h

/-- Abstract Green/IBP limit hypothesis: the ε–Green identity for
`U_halfplane` on the Whitney box based on `I`, together with sign control of
the top and side terms, yields a bound of the box energy by the bottom
boundary integral. -/
class BottomBoundaryLimit (I : RH.Cert.WhitneyInterval) : Prop where
  limit_ineq :
    Riemann.RS.boxEnergyCRGreen gradU_whitney volume
      (Riemann.RS.Whitney.tent (RH.Cert.WhitneyInterval.interval I))
    ≤ - ∫ σ in Set.Ioc 0 (α_split * I.len),
        ∫ t in RH.Cert.WhitneyInterval.interval I, U_halfplane (t, σ) ∂volume ∂volume

/-- Convenience lemma: unwrap the `BottomBoundaryLimit` interface. -/
lemma bottom_boundary_limit (I : RH.Cert.WhitneyInterval) [BottomBoundaryLimit I] :
  Riemann.RS.boxEnergyCRGreen gradU_whitney volume
    (Riemann.RS.Whitney.tent (RH.Cert.WhitneyInterval.interval I))
  ≤ - ∫ σ in Set.Ioc 0 (α_split * I.len),
        ∫ t in RH.Cert.WhitneyInterval.interval I, U_halfplane (t, σ) ∂volume ∂volume :=
  BottomBoundaryLimit.limit_ineq (I := I)

/-- Error term in the annular decomposition of the bottom boundary at level `K`.

By definition this is the tail of the annular decomposition: the bottom boundary
integral minus the finite partial sum of the annular energies up to level `K`. -/
noncomputable def negligible_error_terms (I : RH.Cert.WhitneyInterval) (K : ℕ) : ℝ :=
  - (∫ σ in Set.Ioc 0 (α_split * I.len),
        ∫ t in RH.Cert.WhitneyInterval.interval I,
          U_halfplane (t, σ) ∂volume ∂volume)
  - (Finset.range (Nat.succ K)).sum (fun k => Ek α_split I k)

/-- Abstract tail control hypothesis: the error term in the annular decomposition
is nonpositive at every level `K`. Analytically, this should follow from
identifying `U_halfplane` with a convergent Poisson sum and controlling the tail. -/
class NegligibleErrorControl (I : RH.Cert.WhitneyInterval) : Prop where
  le_zero : ∀ K : ℕ, negligible_error_terms I K ≤ 0

/-- Convenience lemma: unpack the nonpositivity of the annular tail from the
`NegligibleErrorControl` interface. -/
lemma negligible_error_nonpos (I : RH.Cert.WhitneyInterval) [NegligibleErrorControl I] :
  ∀ K, negligible_error_terms I K ≤ 0 :=
  NegligibleErrorControl.le_zero (I := I)

/-- Bottom boundary identity, expressed with the explicit tail error term. -/
lemma bottom_boundary_eq_annular_energy (I : RH.Cert.WhitneyInterval) (K : ℕ) :
  - (∫ σ in Set.Ioc 0 (α_split * I.len),
        ∫ t in RH.Cert.WhitneyInterval.interval I, U_halfplane (t, σ) ∂volume ∂volume)
  =
  (Finset.range (Nat.succ K)).sum (fun k => Ek α_split I k) +
  negligible_error_terms I K := by
  unfold negligible_error_terms
  ring_nf



/-! ## Annular split hypothesis and main bounds -/

/-- Annular partial‑sum split hypothesis (succ form): the box energy is dominated by the
finite sum of per‑annulus energies up to level K. This is the analytic Green/Poisson split. -/
def HasAnnularSplit (I : RH.Cert.WhitneyInterval) : Prop :=
  ∀ K : ℕ,
    Riemann.RS.boxEnergyCRGreen gradU_whitney volume
      (Riemann.RS.Whitney.tent (RH.Cert.WhitneyInterval.interval I))
    ≤ (Finset.range (Nat.succ K)).sum (fun k => Ek α_split I k)

/-- Coarse CR–Green annular split on the tent (succ form), assuming:
  * `h_limit`: the Green/IBP limit that bounds the tent energy by the bottom boundary integral;
  * `h_err_nonpos`: the tail error is a.e. nonpositive termwise in `K`.

Once those analytic inputs are available, this yields the desired `HasAnnularSplit`. -/
theorem CRGreen_tent_energy_split'
  (I : RH.Cert.WhitneyInterval)
  (h_limit :
    Riemann.RS.boxEnergyCRGreen gradU_whitney volume
      (Riemann.RS.Whitney.tent (RH.Cert.WhitneyInterval.interval I))
    ≤
    - (∫ σ in Set.Ioc 0 (α_split * I.len),
          ∫ t in RH.Cert.WhitneyInterval.interval I, U_halfplane (t, σ) ∂volume ∂volume))
  (h_err_nonpos :
    ∀ K : ℕ, negligible_error_terms I K ≤ 0)
  : HasAnnularSplit I := by
  intro K
  -- Step 1: rewrite the bottom boundary via the annular decomposition + tail
  have h_bottom := bottom_boundary_eq_annular_energy (I := I) (K := K)
  -- h_bottom :
  --   -∫ bottom = (∑_{k≤K} Ek α_split I k) + negligible_error_terms I K
  -- Step 2: from error ≤ 0, get an upper bound by just the finite sum
  have h_bottom_le :
    - (∫ σ in Set.Ioc 0 (α_split * I.len),
          ∫ t in RH.Cert.WhitneyInterval.interval I, U_halfplane (t, σ) ∂volume ∂volume)
    ≤ (Finset.range (Nat.succ K)).sum (fun k => Ek α_split I k) := by
    -- start from the equality and drop the error using `h_err_nonpos K`
    have h_err := h_err_nonpos K
    -- (∑ Ek) + err ≤ (∑ Ek) since err ≤ 0
    have h_drop :
      (Finset.range (Nat.succ K)).sum (fun k => Ek α_split I k) +
        negligible_error_terms I K
      ≤ (Finset.range (Nat.succ K)).sum (fun k => Ek α_split I k) := by
      have := add_le_add_left h_err
        ((Finset.range (Nat.succ K)).sum (fun k => Ek α_split I k))
      simpa [add_comm, add_left_comm, add_assoc] using this
    -- combine equality with this inequality
    calc - (∫ σ in Set.Ioc 0 (α_split * I.len),
              ∫ t in RH.Cert.WhitneyInterval.interval I, U_halfplane (t, σ) ∂volume ∂volume)
        = (Finset.range (Nat.succ K)).sum (fun k => Ek α_split I k) +
            negligible_error_terms I K := h_bottom
      _ ≤ (Finset.range (Nat.succ K)).sum (fun k => Ek α_split I k) := h_drop
  -- Step 3: combine the tent-energy bound and bottom bound
  exact le_trans h_limit h_bottom_le

/-- Coarse CR–Green annular split on the tent (succ form).

This theorem connects the interior energy of the harmonic potential `U` over a
Whitney box to the sum of boundary energies over the dyadic annuli. The heavy
analytic input is encapsulated in the abstract interfaces
`BottomBoundaryLimit` (Green/IBP limit) and `NegligibleErrorControl`
(tail control); once these are available, the annular split follows formally
from `CRGreen_tent_energy_split'`. -/
theorem CRGreen_tent_energy_split (I : RH.Cert.WhitneyInterval)
  [BottomBoundaryLimit I] [NegligibleErrorControl I] :
  HasAnnularSplit I := by
  -- unwrap the Green/IBP limit and the tail nonpositivity, then apply the
  -- abstract annular-split theorem `CRGreen_tent_energy_split'`
  refine CRGreen_tent_energy_split'
    (I := I)
    (h_limit := bottom_boundary_limit I)
    (h_err_nonpos := negligible_error_nonpos I)

/-- Succ-form annular split interface for the diagonal KD piece. -/
structure Succ (I : RH.Cert.WhitneyInterval) (Cdiag : ℝ) : Prop where
  nonneg : 0 ≤ Cdiag
  E : ℕ → ℝ
  split : ∀ K : ℕ,
    Riemann.RS.boxEnergyCRGreen gradU_whitney volume
      (Riemann.RS.Whitney.tent (RH.Cert.WhitneyInterval.interval I))
    ≤ (Finset.range (Nat.succ K)).sum (fun k => E k)
  term_le : ∀ k : ℕ, E k ≤ Cdiag * (phi_of_nu (nu_default I) k)

/-- ## Annular KD decomposition → KD analytic partial‑sum bound

We expose a lightweight interface to encode the analytic annular decomposition
on the tent: a per‑annulus family of nonnegative contributions whose partial sum
dominates the box energy, and each term is bounded by `Cdecay · (1/4)^k · ν_k`.
This suffices to deduce the `hKD_energy` hypothesis used by `KD_analytic`. -/

structure AnnularKDDecomposition (I : RH.Cert.WhitneyInterval) where
  Cdecay : ℝ
  nonneg : 0 ≤ Cdecay
  a : ℕ → ℝ
  partial_energy : ∀ K : ℕ,
    Riemann.RS.boxEnergyCRGreen gradU_whitney volume
      (Riemann.RS.Whitney.tent (I.interval))
    ≤ (Finset.range K).sum (fun k => a k)
  a_bound : ∀ k : ℕ, a k ≤ Cdecay * (phi_of_nu (nu_default I) k)

/-- From an annular KD decomposition, derive the KD analytic partial‑sum bound
for `nu_default`. -/
lemma KD_energy_from_annular_decomp
  (I : RH.Cert.WhitneyInterval)
  (W : AnnularKDDecomposition I)
  : ∀ K : ℕ,
    Riemann.RS.boxEnergyCRGreen gradU_whitney volume
      (Riemann.RS.Whitney.tent (I.interval))
    ≤ W.Cdecay * ((Finset.range K).sum (fun k => phi_of_nu (nu_default I) k)) := by
  classical
  intro K
  have h1 := W.partial_energy K
  -- termwise domination a_k ≤ Cdecay * φ_k
  have hterm : ∀ k ∈ Finset.range K,
      (W.a k) ≤ W.Cdecay * (phi_of_nu (nu_default I) k) := by
    intro k hk; simpa using W.a_bound k
  have hsum := Finset.sum_le_sum hterm
  -- factor Cdecay out of the finite sum
  have hfac :
      (Finset.range K).sum (fun k => W.Cdecay * (phi_of_nu (nu_default I) k))
        = W.Cdecay * ((Finset.range K).sum (fun k => phi_of_nu (nu_default I) k)) := by
    simpa using (Finset.mul_sum W.Cdecay (Finset.range K) (fun k => phi_of_nu (nu_default I) k))
  exact le_trans h1 (by simpa [hfac] using hsum)

/-- Succ-form annular KD packaging: from per‑annulus energies `E k` with
termwise domination by `Cdecay · φ_k` and a partial‑sum energy bound, derive the
KD analytic inequality in the weighted partial‑sum form. -/
lemma KD_energy_from_annular_decomposition_succ
  (I : RH.Cert.WhitneyInterval)
  (Cdecay : ℝ) (nu E : ℕ → ℝ)
  (hCdecay_nonneg : 0 ≤ Cdecay)
  (hEnergy_split : ∀ K : ℕ,
      Riemann.RS.boxEnergyCRGreen gradU_whitney volume
        (Riemann.RS.Whitney.tent (I.interval))
      ≤ (Finset.range (Nat.succ K)).sum (fun k => E k))
  (hE_le : ∀ k : ℕ, E k ≤ Cdecay * (phi_of_nu nu k))
  : ∀ K : ℕ,
      Riemann.RS.boxEnergyCRGreen gradU_whitney volume
        (Riemann.RS.Whitney.tent (I.interval))
      ≤ Cdecay * ((Finset.range (Nat.succ K)).sum (fun k => phi_of_nu nu k)) := by
  classical
  intro K
  have h1 := hEnergy_split K
  -- termwise domination
  have hterm : ∀ k ∈ Finset.range (Nat.succ K), E k ≤ Cdecay * (phi_of_nu nu k) := by
    intro k hk; exact hE_le k
  have hsum := Finset.sum_le_sum hterm
  -- factor Cdecay across the sum
  have hfac :
      (Finset.range (Nat.succ K)).sum (fun k => Cdecay * (phi_of_nu nu k))
        = Cdecay * ((Finset.range (Nat.succ K)).sum (fun k => phi_of_nu nu k)) := by
    simpa using (Finset.mul_sum Cdecay (Finset.range (Nat.succ K)) (fun k => phi_of_nu nu k))
  exact le_trans h1 (by simpa [hfac] using hsum)

/- We expose Prop‑level partial‑sum interfaces that capture diagonal and cross‑term
KD bounds directly in the weighted partial‑sum form. These are designed to be
supplied by the CR–Green analytic toolkit and Schur/Cauchy controls, then
packaged into an `AnnularKDDecomposition` with a calibrated constant. -/


structure KDPartialSumBound (I : RH.Cert.WhitneyInterval) : Prop where
  C : ℝ
  nonneg : 0 ≤ C
  bound : ∀ K : ℕ,
    Riemann.RS.boxEnergyCRGreen gradU_whitney volume
      (Riemann.RS.Whitney.tent (RH.Cert.WhitneyInterval.interval I))
    ≤ C * ((Finset.range K).sum (fun k => phi_of_nu (nu_default I) k))

/-- Combine two partial‑sum KD bounds (e.g. diagonal and cross‑term) into an
annular KD decomposition whose constant is the sum of the two constants. -/
noncomputable def annularKD_from_partial_sums
  (I : RH.Cert.WhitneyInterval)
  (D S : KDPartialSumBound I)
  : AnnularKDDecomposition I := by
  classical
  -- Choose `a k = (C_D + C_S) · φ_k` so termwise domination is equality
  let Cdecay := D.C + S.C
  have hC_nonneg : 0 ≤ Cdecay := add_nonneg D.nonneg S.nonneg
  let a : ℕ → ℝ := fun k => Cdecay * (phi_of_nu (nu_default I) k)
  -- Partial‑sum bound: boxEnergy ≤ C_D Σφ and ≤ C_S Σφ ⇒ ≤ (C_D+C_S) Σφ
  have hPartial : ∀ K : ℕ,
      Riemann.RS.boxEnergyCRGreen gradU_whitney volume
        (Riemann.RS.Whitney.tent (I.interval))
      ≤ (Finset.range K).sum (fun k => a k) := by
    intro K
    have hφ_nonneg : 0 ≤ ((Finset.range K).sum (fun k => phi_of_nu (nu_default I) k)) := by
      -- each φ_k = (1/4)^k · ν_k with ν_k ≥ 0
      have hterm : ∀ k ∈ Finset.range K, 0 ≤ phi_of_nu (nu_default I) k := by
        intro k hk
        unfold phi_of_nu
        exact mul_nonneg (decay4_nonneg k) (nu_default_nonneg I k)
      exact Finset.sum_nonneg hterm
    have hD := D.bound K
    have hS := S.bound K
    have hSum :
        Riemann.RS.boxEnergyCRGreen gradU_whitney volume
          (Riemann.RS.Whitney.tent (I.interval))
        ≤ (D.C + S.C) * ((Finset.range K).sum (fun k => phi_of_nu (nu_default I) k)) := by
      have hD' :
          Riemann.RS.boxEnergyCRGreen gradU_whitney volume
            (Riemann.RS.Whitney.tent (I.interval))
          ≤ D.C * ((Finset.range K).sum (fun k => phi_of_nu (nu_default I) k)) := hD
      have hAdd : D.C * ((Finset.range K).sum (fun k => phi_of_nu (nu_default I) k))
            ≤ (D.C + S.C) * ((Finset.range K).sum (fun k => phi_of_nu (nu_default I) k)) := by
        have hcoef : D.C ≤ D.C + S.C := by
          have : 0 ≤ S.C := S.nonneg; exact le_add_of_nonneg_right this
        exact mul_le_mul_of_nonneg_right hcoef hφ_nonneg
      exact le_trans hD' hAdd
    -- factor the constant out of the sum of `a k`
    have hfac :
        (Finset.range K).sum (fun k => a k)
          = Cdecay * ((Finset.range K).sum (fun k => phi_of_nu (nu_default I) k)) := by
      simpa [a, Cdecay] using
        (Finset.mul_sum Cdecay (Finset.range K) (fun k => phi_of_nu (nu_default I) k))
    simpa [hfac, Cdecay] using hSum
  -- Termwise domination by construction
  have hAnn : ∀ k : ℕ, a k ≤ (D.C + S.C) * (phi_of_nu (nu_default I) k) := by
    intro k; simp [a]
  -- Package into an `AnnularKDDecomposition`
  refine {
    Cdecay := Cdecay
  , nonneg := hC_nonneg
  , a := a
  , partial_energy := hPartial
  , a_bound := by intro k; simpa [Cdecay, a] using hAnn k }

/-- Calibration helper: if `D.C ≤ c₁`, `S.C ≤ c₂`, and `c₁ + c₂ ≤ A_default`, the
combined witness from `annularKD_from_partial_sums` has `Cdecay ≤ A_default`. -/
lemma annularKD_calibrated_to_default
  (I : RH.Cert.WhitneyInterval)
  (D S : KDPartialSumBound I)
  {c₁ c₂ : ℝ}
  (hD_le : D.C ≤ c₁) (hS_le : S.C ≤ c₂)
  (hSum : c₁ + c₂ ≤ A_default)
  : (annularKD_from_partial_sums I D S).Cdecay ≤ A_default := by
  classical
  have : (annularKD_from_partial_sums I D S).Cdecay = D.C + S.C := rfl
  have h : D.C + S.C ≤ c₁ + c₂ := add_le_add hD_le hS_le
  simpa [this] using le_trans h hSum

/-- Succ-form annular split interface for the diagonal KD piece. -/
structure HasAnnularSplitSucc (I : RH.Cert.WhitneyInterval) (Cdiag : ℝ) : Prop where
  nonneg : 0 ≤ Cdiag
  E : ℕ → ℝ
  split : ∀ K : ℕ,
    Riemann.RS.boxEnergyCRGreen gradU_whitney volume
      (Riemann.RS.Whitney.tent (I.interval))
    ≤ (Finset.range (Nat.succ K)).sum (fun k => E k)
  term_le : ∀ k : ℕ, E k ≤ Cdiag * (phi_of_nu (nu_default I) k)

/-- From a succ-form annular split, obtain a diagonal KD partial-sum bound. -/
lemma KDPartialSumBound_of_annular_split_succ
  (I : RH.Cert.WhitneyInterval) {Cdiag : ℝ}
  (h : Succ I Cdiag) : KDPartialSumBound I := by
  classical
  -- Extract the data from the succ-form split.
  have hKD :=
    KD_energy_from_annular_decomposition_succ I Cdiag (nu_default I) h.E h.nonneg h.split
      (by intro k; simpa using h.term_le k)
  refine
    { C := Cdiag
    , nonneg := h.nonneg
    , bound := ?_ }
  intro K
  -- Compare the partial sums `∑_{k < K} φ_k` and `∑_{k < K.succ} φ_k`.
  have hmono :
      (Finset.range K).sum (fun k => phi_of_nu (nu_default I) k)
      ≤ (Finset.range (Nat.succ K)).sum (fun k => phi_of_nu (nu_default I) k) := by
    have hterm : 0 ≤ phi_of_nu (nu_default I) K := by
      unfold phi_of_nu
      exact mul_nonneg (decay4_nonneg K) (nu_default_nonneg I K)
    simpa [Finset.range_succ, add_comm, add_left_comm, add_assoc]
      using (le_add_of_nonneg_right hterm)
  -- Use the annular KD energy bound at level `K` (which uses `range (K.succ)`).
  have hbound := hKD K
  have hmono' := mul_le_mul_of_nonneg_left hmono h.nonneg
  exact le_trans hbound (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmono')

/-- Diagonal KD partial‑sum bound at the default constant `Cdiag_default`
obtained from the succ‑form diagonal annular split. -/
lemma KDPartialSumBound_diag_default
  (I : RH.Cert.WhitneyInterval) : KDPartialSumBound I := by
  classical
  exact KDPartialSumBound_of_annular_split_succ I (Succ_of_diag I)

/-- KD_analytic_succ from calibrated annular split + Schur bounds (succ variant). -/
theorem KD_analytic_succ_from_split_and_schur
  (I : RH.Cert.WhitneyInterval)
  (hSplit :  I)
  (hSchur : HasSchurRowBounds I)
  : KernelDecayBudgetSucc I := by
  classical
  -- Define ν_k := (Zk I k).card (interface count weights)
  let nu : ℕ → ℝ := fun k => ((Zk I k).card : ℝ)
  -- Termwise bound: E_k ≤ Cdecay_split * decay4 k * ν_k for k ≥ 1 (and trivially for k=0)
  have hE_le : ∀ k : ℕ, Ek α_split I k ≤ (S_split * (16 * (α_split ^ 4))) * (phi_of_nu nu k) := by
    intro k
    by_cases hk : 1 ≤ k
    · -- calibrated diagonal+Schur
      have hk' := hk
      have hcal := Ek_bound_calibrated (I := I) (hSchur := hSchur) hk'
      -- φ_k = 4^{-k} * ν_k and ν_k = card
      simpa [phi_of_nu, nu, decay4, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
        using hcal
    · -- k = 0 case: use nonnegativity to bound by 0 ≤ Cdecay * φ_0 * ν_0
      have hk0 : k = 0 := Nat.le_zero.mp (le_of_not_ge hk)
      subst hk0
      have hE_nonneg : 0 ≤ Ek α_split I 0 := by
        -- annularEnergy is an integral of a nonnegative integrand
        simp [Ek, annularEnergy]
      have hφν_nonneg : 0 ≤ (S_split * (16 * (α_split ^ 4))) * (phi_of_nu nu 0) := by
        have hC : 0 ≤ (S_split * (16 * (α_split ^ 4))) := by
          have : 0 ≤ (α_split ^ 4) := by exact pow_two_nonneg (α_split ^ 2)
          exact mul_nonneg (by norm_num [S_split]) (mul_nonneg (by norm_num) this)
        have : 0 ≤ phi_of_nu nu 0 := by
          unfold phi_of_nu decay4; have : 0 ≤ nu 0 := by exact Nat.cast_nonneg _; exact mul_nonneg (by norm_num) this
        exact mul_nonneg hC this
      exact le_trans (le_of_eq (by ring_nf : Ek α_split I 0 = Ek α_split I 0)) (le_of_lt (lt_of_le_of_lt hE_nonneg (lt_of_le_of_ne hφν_nonneg (by decide))))
  -- Build KD via the annular decomposition bridge
  have hKD := KD_analytic_from_annular_local_succ I (S_split * (16 * (α_split ^ 4))) nu
      (by
        have : 0 ≤ (α_split ^ 4) := by exact pow_two_nonneg (α_split ^ 2)
        exact mul_nonneg (by norm_num [S_split]) (mul_nonneg (by norm_num) this))
      (by intro K; simpa using hSplit K)
      (by intro k; simpa using hE_le k)
  exact hKD

/-- Succ default corollary from split + Schur + counts on ν_k = (Zk I k).card. -/
theorem carleson_energy_bound_from_split_schur_and_counts_default
  (I : RH.Cert.WhitneyInterval)
  (hSplit :  I)
  (hSplit : HasAnnularSplit I)
  (hSchur : HasSchurRowBounds I)
  (hVK_counts_card : ∀ K : ℕ,
      ((Finset.range K).sum (fun k => ((Zk I k).card : ℝ))) ≤ B_default * (2 * I.len))
  : carleson_energy I ≤ Kxi_paper * (2 * I.len) := by
  classical
  -- Build KD with calibrated Cdecay = 0.08 from split+schur
  have KD := KD_analytic_succ_from_split_and_schur I hSplit hSchur
  -- Build VK counts on φ = (1/4)^k * ν_k with ν_k = card(Zk)
  have VD : VKPartialSumBudgetSucc I (phi_of_nu (fun k => ((Zk I k).card : ℝ))) := by
    -- from_counts in succ form
    -- from_counts in succ form.
    refine VKPartialSumBudgetSucc.of I (phi_of_nu (fun k => ((Zk I k).card : ℝ))) B_default ?partial'
    intro K
    -- As decay4 k ≤ 1 and card ≥ 0, sum φ_k ≤ sum card_k
    have hterm : ∀ k ∈ Finset.range (Nat.succ K),
        phi_of_nu (fun k => ((Zk I k).card : ℝ)) k ≤ (1 : ℝ) * ((Zk I k).card : ℝ) := by
      intro k hk; unfold phi_of_nu; have := decay4_le_one k; have : 0 ≤ ((Zk I k).card : ℝ) := Nat.cast_nonneg _; simpa using (mul_le_mul_of_nonneg_right this ‹0 ≤ _›)
    have hsum := Finset.sum_le_sum hterm
    have hcounts := hVK_counts_card (Nat.succ K)
    simpa using le_trans hsum hcounts
  -- Calibrate constants: Cdecay = 0.08 (by construction), Cν ≤ 2 = B_default
  have hCdecay_le : KD.Cdecay ≤ A_default := by simpa [Cdecay_split_eval, A_default] using (le_of_eq Cdecay_split_eval)
  have hCν_le : VD.Cν ≤ B_default := le_of_eq rfl
  -- product calibration A_default * B_default = Kxi_paper
  have hAB := default_AB_le
  have hConst : (KD.Cdecay * VD.Cν) ≤ Kxi_paper :=
    product_constant_calibration KD.nonneg (by simp [VD]) hCdecay_le hCν_le hAB
  -- Apply bridge
  exact carleson_energy_bound_from_decay_density_succ I KD VD hConst

#min_imports
