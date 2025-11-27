import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.MeasureTheory.Integral.CircleAverage
import Riemann.academic_framework.DiskHardy
import Mathlib

import VD

/-
# Canonical representation and Poisson–Jensen on the unit disc

This file sets up the *statement level* infrastructure for a Nevanlinna-style
canonical representation / Poisson–Jensen theorem on the unit disc.  The actual
analytic proofs are deferred to later work using the `ValueDistribution` API
and Mathlib's `JensenFormula` / `FirstMainTheorem` files.

The goal is to have a clean, mathlib‑style interface that can be used by the
de Branges / upper‑half‑plane layer, in particular to construct the
`UpperHalfPlanePoissonRepresentation` used in `NevanlinnaGrowth.lean`.

## Main definitions

* `Complex.unitDiscSet`: the open unit disc as a subset of `ℂ`.
* `Complex.IsBoundedOnUnitDisc g`: `g` is uniformly bounded on `unitDiscSet`.
* `Complex.IsOfBoundedTypeUnitDisc g`: Nevanlinna "bounded type" class on the
  unit disc, defined as a quotient of bounded analytic functions.
* `Complex.DiskPoissonJensenRepresentation g`: abstract data of a canonical
  representation for `g` on the unit disc, consisting of
  an analytic function `F` with `HasDiskPoissonRepresentation F`, a real
  parameter `α`, and a Poisson‑type formula for `log (‖g z‖ + 1)` on `𝔻`.

## Main theorem (statement level)

* `Complex.disk_PoissonJensen_for_boundedType`:
  If `g` is of bounded type on the unit disc, then it admits a
  `DiskPoissonJensenRepresentation`.  This will be proved later using the
  `ValueDistribution` API and canonical factorisation / Poisson–Jensen on the
  disk or plane.  For now it is recorded as a single `sorry` with a detailed
  TODO comment.

The design mirrors the upper‑half‑plane version in `NevanlinnaGrowth.lean`,
with the intent that the heavy analytic arguments are concentrated in a small
number of clearly marked theorems.
-/

noncomputable section

open MeasureTheory
open MeromorphicOn Metric Real
open scoped UnitDisc

namespace Complex

/-- The open unit disc in `ℂ`, as a subset. -/
def unitDiscSet : Set ℂ := {z : ℂ | ‖z‖ < 1}

@[simp] lemma mem_unitDiscSet {z : ℂ} :
    z ∈ unitDiscSet ↔ ‖z‖ < 1 := Iff.rfl

/-- `unitDiscSet` is the open unit ball of radius `1` in `ℂ`. -/
lemma unitDiscSet_eq_ball :
    unitDiscSet = Metric.ball (0 : ℂ) 1 := by
  ext z
  simp [unitDiscSet, Metric.mem_ball, dist_eq_norm]

/-- The open unit disc is an open subset of `ℂ`. -/
lemma isOpen_unitDiscSet : IsOpen (unitDiscSet) := by
  simpa [unitDiscSet_eq_ball] using (Metric.isOpen_ball (x := (0 : ℂ)) (r := (1 : ℝ)))

/-- A function is bounded on the open unit disc if its norm is uniformly
bounded there.  This is the concrete boundedness condition used in the
ratio definition of the Nevanlinna class on the disc. -/
def IsBoundedOnUnitDisc (g : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ unitDiscSet, ‖g z‖ ≤ C

/-- Nevanlinna bounded‑type class on the unit disc: `g` is a quotient of two
bounded analytic functions on the disc.

More precisely, there exist analytic functions `G` and `H` on the open unit
disc, both bounded there, such that `H` never vanishes on the disc and
`g z = G z / H z` for all `z` with `‖z‖ < 1`.

This matches the classical "ratio of bounded analytic functions" definition
for functions of bounded type on `𝔻`. -/
def IsOfBoundedTypeUnitDisc (g : ℂ → ℂ) : Prop :=
  ∃ G H : ℂ → ℂ,
    AnalyticOn ℂ G unitDiscSet ∧
    AnalyticOn ℂ H unitDiscSet ∧
    IsBoundedOnUnitDisc G ∧
    IsBoundedOnUnitDisc H ∧
    (∀ z ∈ unitDiscSet, H z ≠ 0) ∧
    ∀ z ∈ unitDiscSet, g z = G z / H z

/-- For a bounded-type function `g` on the unit disc, the representing
quotient `G/H` is meromorphic on every smaller closed disc `‖z‖ ≤ r` with
`0 < r < 1`.  We record this as a convenience lemma that will later be used
when applying Jensen's formula and the ValueDistribution machinery on
concentric discs. -/
lemma IsOfBoundedTypeUnitDisc.meromorphic_ratio_on_closedBall
    {g : ℂ → ℂ} (hg : IsOfBoundedTypeUnitDisc g) {r : ℝ}
    (_hr0 : 0 < r) (hr1 : r < 1) :
    ∃ G H : ℂ → ℂ,
      MeromorphicOn G (Metric.closedBall (0 : ℂ) r) ∧
      MeromorphicOn H (Metric.closedBall (0 : ℂ) r) ∧
      MeromorphicOn (fun z : ℂ => G z / H z) (Metric.closedBall (0 : ℂ) r) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) r, g z = G z / H z := by
  classical
  rcases hg with ⟨G, H, hG_an, hH_an, hG_bd, hH_bd, hH_ne, hEq⟩
  -- Closed balls of radius `< 1` lie inside the open unit disc.
  have h_subset :
      Metric.closedBall (0 : ℂ) r ⊆ unitDiscSet := by
    intro z hz
    -- From `z ∈ closedBall 0 r` we get `‖z‖ ≤ r`; together with `r < 1`
    -- this implies `‖z‖ < 1`.
    have hz_le : ‖z‖ ≤ r := by
      -- `mem_closedBall` is stated in terms of the distance.
      have hz' := hz
      -- here `Metric.mem_closedBall` reduces to `dist z 0 ≤ r`
      have hz_dist : dist z (0 : ℂ) ≤ r := by
        simpa [Metric.mem_closedBall] using hz'
      simpa [dist_eq_norm] using hz_dist
    exact lt_of_le_of_lt hz_le hr1
  -- Upgrade analyticity on the open disc to `AnalyticOnNhd` on the disc.
  have hG_nhd_disc :
      AnalyticOnNhd ℂ G unitDiscSet :=
    (isOpen_unitDiscSet.analyticOn_iff_analyticOnNhd).mp hG_an
  have hH_nhd_disc :
      AnalyticOnNhd ℂ H unitDiscSet :=
    (isOpen_unitDiscSet.analyticOn_iff_analyticOnNhd).mp hH_an
  -- Restrict to the smaller closed ball.
  have hG_nhd_ball :
      AnalyticOnNhd ℂ G (Metric.closedBall (0 : ℂ) r) :=
    hG_nhd_disc.mono h_subset
  have hH_nhd_ball :
      AnalyticOnNhd ℂ H (Metric.closedBall (0 : ℂ) r) :=
    hH_nhd_disc.mono h_subset
  -- Hence `G` and `H` are meromorphic on the closed ball.
  have hMeromG :
      MeromorphicOn G (Metric.closedBall (0 : ℂ) r) :=
    hG_nhd_ball.meromorphicOn
  have hMeromH :
      MeromorphicOn H (Metric.closedBall (0 : ℂ) r) :=
    hH_nhd_ball.meromorphicOn
  -- Their quotient is also meromorphic on the closed ball.
  have hMerom_ratio :
      MeromorphicOn (fun z : ℂ => G z / H z)
        (Metric.closedBall (0 : ℂ) r) :=
    (MeromorphicOn.fun_div (s := G) (t := H)
      (U := Metric.closedBall (0 : ℂ) r)
      (hs := hMeromG) (ht := hMeromH))
  -- Finally, record that `g = G/H` on the closed ball (since it lies inside
  -- the original open unit disc where this identity holds).
  refine ⟨G, H, hMeromG, hMeromH, hMerom_ratio, ?_⟩
  intro z hz
  have hz_disc : z ∈ unitDiscSet := h_subset hz
  exact hEq z hz_disc

/-- Jensen's formula specialized to the meromorphic ratio attached to a
bounded-type function `g` on the unit disc.

For each radius `0 < r < 1` we obtain analytic data `G`, `H` and a
meromorphic function `f = G/H` on the closed ball `‖z‖ ≤ r`, together
with Jensen's circle-average identity for `f` at radius `r`.  This is a
preparatory step towards a full Poisson–Jensen / canonical representation
for `g`. -/
lemma IsOfBoundedTypeUnitDisc.jensen_ratio
    {g : ℂ → ℂ} (hg : IsOfBoundedTypeUnitDisc g) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ G H : ℂ → ℂ,
      let f : ℂ → ℂ := fun z => G z / H z
      MeromorphicOn f (Metric.closedBall (0 : ℂ) r) ∧
      circleAverage (log ‖f ·‖) 0 r =
        ∑ᶠ u, divisor f (Metric.closedBall (0 : ℂ) r) u *
          Real.log (r * ‖0 - u‖⁻¹)
        + divisor f (Metric.closedBall (0 : ℂ) r) 0 * Real.log r
        + Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
  classical
  -- Step 1: extract a meromorphic ratio `f = G/H` on the closed ball.
  obtain ⟨G, H, hMeromG, hMeromH, hMerom_ratio, hEq⟩ :=
    IsOfBoundedTypeUnitDisc.meromorphic_ratio_on_closedBall
      (g := g) hg hr0 hr1
  -- Work with `f = G/H`.
  refine ⟨G, H, ?_⟩
  let f : ℂ → ℂ := fun z => G z / H z
  have hf_closed : MeromorphicOn f (Metric.closedBall (0 : ℂ) r) := by
    simpa [f] using hMerom_ratio
  -- Step 2: apply Jensen's formula to `f` on `closedBall 0 |r|`.
  have hr_ne : (r : ℝ) ≠ 0 := ne_of_gt hr0
  have hf_J :
      MeromorphicOn f (Metric.closedBall (0 : ℂ) |r|) := by
    -- Since `r > 0`, `|r| = r`, so the domains coincide.
    simpa [abs_of_pos hr0] using hf_closed
  have hJ := MeromorphicOn.circleAverage_log_norm
    (c := (0 : ℂ)) (R := r) (f := f) hr_ne hf_J
  -- Rewrite the right-hand side so that all occurrences of `closedBall 0 |r|`
  -- become `closedBall 0 r`.
  have hJ' :
      circleAverage (log ‖f ·‖) (0 : ℂ) r =
        ∑ᶠ u, divisor f (Metric.closedBall (0 : ℂ) r) u *
          Real.log (r * ‖0 - u‖⁻¹)
        + divisor f (Metric.closedBall (0 : ℂ) r) 0 * Real.log r
        + Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
    rw [abs_of_pos hr0] at hJ
    apply_fun ((↑) : ℝ → ℂ) at hJ
    rw [circleAverage_def] at hJ ⊢
    simp only [smul_eq_mul, Complex.ofReal_mul] at hJ
    rw [← Complex.real_smul] at hJ
    convert hJ using 3
    · rw [← intervalIntegral.integral_ofReal]
      congr 1
      funext θ
      exact (Complex.ofReal_log (norm_nonneg (f (circleMap 0 r θ)))).symm
    · simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast]

  -- Package the meromorphy on `closedBall 0 r` together with the Jensen
  -- identity as the result.
  refine And.intro hf_closed ?_
  exact hJ'

/-! ### Extension of disk functions to the plane -/

/-- Extend a function on the unit disc to the whole plane by zero outside.

This is a simple extension that preserves meromorphy on the disc interior
and makes the function identically zero outside.  For Nevanlinna theory,
the key point is that this extension is meromorphic on `Set.univ` (with
poles/zeros only in the original disc). -/
def extendByZero (g : ℂ → ℂ) : ℂ → ℂ :=
  fun z => if ‖z‖ < 1 then g z else 0

/-- The extension by zero agrees with `g` on the open unit disc. -/
lemma extendByZero_eq_on_unitDisc (g : ℂ → ℂ) :
    ∀ z ∈ unitDiscSet, extendByZero g z = g z := by
  intro z hz
  simp only [extendByZero, mem_unitDiscSet] at hz ⊢
  simp [hz]

/-- The extension by zero is zero outside the closed unit disc. -/
lemma extendByZero_eq_zero_outside (g : ℂ → ℂ) :
    ∀ z, ‖z‖ ≥ 1 → extendByZero g z = 0 := by
  intro z hz
  simp only [extendByZero]
  simp [not_lt.mpr hz]

/-- If `G` is analytic on the open unit disc, then `extendByZero G` is
meromorphic on any closed ball of radius `< 1`. -/
lemma extendByZero_meromorphicOn_closedBall
    {G : ℂ → ℂ} (hG : AnalyticOn ℂ G unitDiscSet) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    MeromorphicOn (extendByZero G) (Metric.closedBall (0 : ℂ) r) := by
  -- On the closed ball of radius `r < 1`, `extendByZero G = G`, and `G`
  -- is analytic there.
  have h_subset : Metric.closedBall (0 : ℂ) r ⊆ unitDiscSet := by
    intro z hz
    have hz_le : ‖z‖ ≤ r := by
      have hz_dist : dist z (0 : ℂ) ≤ r := by simpa [Metric.mem_closedBall] using hz
      simpa [dist_eq_norm] using hz_dist
    exact lt_of_le_of_lt hz_le hr1
  have hG_nhd : AnalyticOnNhd ℂ G unitDiscSet :=
    (isOpen_unitDiscSet.analyticOn_iff_analyticOnNhd).mp hG
  have hG_ball : AnalyticOnNhd ℂ G (Metric.closedBall (0 : ℂ) r) :=
    hG_nhd.mono h_subset
  -- Now show that `extendByZero G` equals `G` on the closed ball.
  have hEq : ∀ z ∈ Metric.closedBall (0 : ℂ) r, extendByZero G z = G z := by
    intro z hz
    exact extendByZero_eq_on_unitDisc G z (h_subset hz)
  -- Hence `extendByZero G` is analytic (and therefore meromorphic) on the ball.
  have hExt_an : AnalyticOnNhd ℂ (extendByZero G) (Metric.closedBall (0 : ℂ) r) := by
    intro z hz
    have hz_disc : z ∈ unitDiscSet := h_subset hz
    -- We need to show `AnalyticAt ℂ (extendByZero G) z`.
    -- Since `extendByZero G` agrees with `G` in a neighborhood of `z` (the ball),
    -- and `G` is analytic at `z`, so is `extendByZero G`.
    have hOpen : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
    have hz_in_ball : z ∈ Metric.ball (0 : ℂ) 1 := by
      simp only [Metric.mem_ball, dist_zero_right]
      exact h_subset hz
    have hEq_nhd : ∀ w ∈ Metric.ball (0 : ℂ) 1, extendByZero G w = G w := by
      intro w hw
      simp only [Metric.mem_ball, dist_zero_right] at hw
      exact extendByZero_eq_on_unitDisc G w hw
    -- Use `AnalyticAt.congr` with the eventually equal functions.
    have hEv : G =ᶠ[nhds z] extendByZero G := by
      apply Filter.eventually_of_mem (hOpen.mem_nhds hz_in_ball)
      intro w hw
      exact (hEq_nhd w hw).symm
    exact (hG_nhd z hz_disc).congr hEv
  exact hExt_an.meromorphicOn

/-- For a bounded-type function `g = G/H` on the disc, the extension
`extendByZero (G/H)` is meromorphic on any closed ball of radius `< 1`.

This follows from the fact that `G` and `H` are analytic on the disc,
so their quotient is meromorphic, and the extension agrees with the
quotient on the interior. -/
lemma IsOfBoundedTypeUnitDisc.extendByZero_meromorphicOn_closedBall
    {g : ℂ → ℂ} (hg : IsOfBoundedTypeUnitDisc g) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    MeromorphicOn (extendByZero g) (Metric.closedBall (0 : ℂ) r) := by
  rcases hg with ⟨G, H, hG_an, hH_an, _, _, hH_ne, hEq⟩
  -- On the closed ball, `g = G/H` and both are analytic.
  have h_subset : Metric.closedBall (0 : ℂ) r ⊆ unitDiscSet := by
    intro z hz
    have hz_le : ‖z‖ ≤ r := by
      have hz_dist : dist z (0 : ℂ) ≤ r := by simpa [Metric.mem_closedBall] using hz
      simpa [dist_eq_norm] using hz_dist
    exact lt_of_le_of_lt hz_le hr1
  have hG_nhd : AnalyticOnNhd ℂ G unitDiscSet :=
    (isOpen_unitDiscSet.analyticOn_iff_analyticOnNhd).mp hG_an
  have hH_nhd : AnalyticOnNhd ℂ H unitDiscSet :=
    (isOpen_unitDiscSet.analyticOn_iff_analyticOnNhd).mp hH_an
  have hG_ball : AnalyticOnNhd ℂ G (Metric.closedBall (0 : ℂ) r) := hG_nhd.mono h_subset
  have hH_ball : AnalyticOnNhd ℂ H (Metric.closedBall (0 : ℂ) r) := hH_nhd.mono h_subset
  -- The quotient `G/H` is meromorphic on the closed ball.
  have hMerom : MeromorphicOn (fun z => G z / H z) (Metric.closedBall (0 : ℂ) r) :=
    MeromorphicOn.fun_div hG_ball.meromorphicOn hH_ball.meromorphicOn
  -- `extendByZero g` equals `g = G/H` on the closed ball.
  have hEq' : ∀ z ∈ Metric.closedBall (0 : ℂ) r, extendByZero g z = G z / H z := by
    intro z hz
    have hz_disc : z ∈ unitDiscSet := h_subset hz
    rw [extendByZero_eq_on_unitDisc g z hz_disc, hEq z hz_disc]
  -- Hence `extendByZero g` is meromorphic on the closed ball.
  -- We need to show the functions agree on a neighborhood of each point.
  intro z hz
  have hz_disc : z ∈ unitDiscSet := h_subset hz
  have hMerom_at : MeromorphicAt (fun w => G w / H w) z := hMerom z hz
  -- The functions agree in a neighborhood of `z`.
  have hOpen : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  have hz_in_ball : z ∈ Metric.ball (0 : ℂ) 1 := by
    simp only [Metric.mem_ball, dist_zero_right]
    exact h_subset hz
  have hEq_nhd : ∀ w ∈ Metric.ball (0 : ℂ) 1, (fun w => G w / H w) w = extendByZero g w := by
    intro w hw
    simp only [Metric.mem_ball, dist_zero_right] at hw
    have hw_disc : w ∈ unitDiscSet := hw
    rw [extendByZero_eq_on_unitDisc g w hw_disc, hEq w hw_disc]
  have hEv : (fun w => G w / H w) =ᶠ[nhdsWithin z {z}ᶜ] extendByZero g := by
    apply Filter.eventually_of_mem
    · -- The ball is in `nhdsWithin z {z}ᶜ`
      apply Filter.mem_inf_of_left
      exact hOpen.mem_nhds hz_in_ball
    intro w hw
    exact hEq_nhd w hw
  exact hMerom_at.congr hEv

/-! ### Connection to ValueDistribution counting functions

This section establishes the bridge between the local Jensen formula
(which uses divisors on closed balls) and the global ValueDistribution
machinery (which uses counting functions on `Set.univ`).

The key insight is that for a bounded-type function `g` on the disc,
the divisor sums appearing in Jensen's formula can be expressed in terms
of the `ValueDistribution.logCounting` functions, which in turn are
controlled by the Nevanlinna characteristic via the First Main Theorem.
-/

/-- The divisor of the extension `extendByZero (G/H)` on a closed ball
agrees with the divisor of `G/H` on that ball, for `r < 1`.

This follows from the fact that divisors are defined locally via
meromorphic germs, and the two functions agree on a neighborhood
of every point in the closed ball. -/
lemma IsOfBoundedTypeUnitDisc.divisor_extendByZero_eq
    {g : ℂ → ℂ} (hg : IsOfBoundedTypeUnitDisc g) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r,
      divisor (extendByZero g) (Metric.closedBall (0 : ℂ) r) z =
      divisor g (Metric.closedBall (0 : ℂ) r) z := by
  intro z hz
  -- On the closed ball of radius `r < 1`, `extendByZero g = g`.
  have h_subset : Metric.closedBall (0 : ℂ) r ⊆ unitDiscSet := by
    intro w hw
    have hw_le : ‖w‖ ≤ r := by
      have hw_dist : dist w (0 : ℂ) ≤ r := by simpa [Metric.mem_closedBall] using hw
      simpa [dist_eq_norm] using hw_dist
    exact lt_of_le_of_lt hw_le hr1
  -- Both functions agree on the closed ball.
  have _hEq : ∀ w ∈ Metric.closedBall (0 : ℂ) r, extendByZero g w = g w := by
    intro w hw
    exact extendByZero_eq_on_unitDisc g w (h_subset hw)
  -- The divisor only depends on the germ of the function, so they agree.
  -- We need the functions to be meromorphic for the divisor to be defined.
  have _hMerom_ext := IsOfBoundedTypeUnitDisc.extendByZero_meromorphicOn_closedBall hg hr0 hr1
  have _hMerom_g := (IsOfBoundedTypeUnitDisc.meromorphic_ratio_on_closedBall hg hr0 hr1).choose_spec.choose_spec.2.1
  -- The divisor is computed from the order of the meromorphic germ at `z`.
  -- Since both functions have the same germ at `z` (they agree on a neighborhood),
  -- their divisors coincide.
  -- This requires `MeromorphicAt.order_congr` or similar.
  sorry

/-- For a bounded-type function on the disc, the divisor sum in Jensen's
formula can be related to the ValueDistribution counting function.

Specifically, for `f = G/H` meromorphic on the closed ball of radius `r`,
the sum `∑ᶠ u, divisor f (closedBall 0 r) u * log(r * ‖u‖⁻¹)` equals
the difference `logCounting f 0 r - logCounting f ⊤ r` of the counting
functions for zeros and poles, evaluated at radius `r`.

This is the key bridge between the local Jensen formula and the global
Nevanlinna characteristic. -/
lemma jensen_divisor_sum_eq_logCounting
    {f : ℂ → ℂ} {r : ℝ} (hr0 : 0 < r)
    (hf : MeromorphicOn f (Metric.closedBall (0 : ℂ) r)) :
    ∑ᶠ u, divisor f (Metric.closedBall (0 : ℂ) r) u * Real.log (r * ‖0 - u‖⁻¹) =
      ValueDistribution.logCounting f 0 r - ValueDistribution.logCounting f ⊤ r := by
  -- This follows from the definitions of `logCounting` and `divisor`.
  -- The `logCounting` function is defined in terms of the divisor restricted
  -- to the closed ball, with the same logarithmic weighting.
  sorry

/-- The Jensen identity for `extendByZero g` on closed balls.

This combines `jensen_ratio` with the extension machinery to get a
Jensen-type formula for the extended function. -/
lemma IsOfBoundedTypeUnitDisc.jensen_extendByZero
    {g : ℂ → ℂ} (_hg : IsOfBoundedTypeUnitDisc g) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    circleAverage (log ‖extendByZero g ·‖) 0 r =
      circleAverage (log ‖g ·‖) 0 r := by
  -- On the circle of radius `r < 1`, `extendByZero g = g`.
  have h_circle : ∀ θ : ℝ, ‖circleMap (0 : ℂ) r θ‖ = |r| := by
    intro θ
    simp [circleMap, abs_of_pos hr0]
  have h_in_disc : ∀ θ : ℝ, circleMap (0 : ℂ) r θ ∈ unitDiscSet := by
    intro θ
    simp only [mem_unitDiscSet, h_circle θ, abs_of_pos hr0]
    exact hr1
  -- The integrands agree pointwise on the circle.
  have h_eq : ∀ θ : ℝ, log ‖extendByZero g (circleMap 0 r θ)‖ = log ‖g (circleMap 0 r θ)‖ := by
    intro θ
    rw [extendByZero_eq_on_unitDisc g (circleMap 0 r θ) (h_in_disc θ)]
  -- Hence the circle averages are equal.
  simp only [circleAverage_def]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  exact h_eq θ

/-! ### Asymptotic analysis: extracting the linear term

The goal of this section is to establish that for bounded-type functions,
the Nevanlinna characteristic grows at most linearly in `(1 - r)⁻¹`.
This is the key estimate that allows us to extract a "mean type" parameter
and an analytic Poisson term from the Jensen formula.
-/

/-- For a bounded analytic function `G` on the unit disc with bound `C`,
the positive part of `log ‖G‖` is bounded by `log⁺ C`. -/
lemma IsBoundedOnUnitDisc.posLog_norm_le {G : ℂ → ℂ} (hG : IsBoundedOnUnitDisc G) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ unitDiscSet, log⁺ ‖G z‖ ≤ M := by
  obtain ⟨C, hC_pos, hC_bound⟩ := hG
  use log⁺ C
  constructor
  · exact posLog_nonneg
  · intro z hz
    have hGz : ‖G z‖ ≤ C := hC_bound z hz
    exact posLog_le_posLog (norm_nonneg _) hGz

/-- The **Nevanlinna characteristic** of a bounded-type function on the disc
grows at most linearly in `(1 - r)⁻¹` as `r → 1⁻`.

This is the key growth estimate that allows us to extract a linear term
in the Poisson-Jensen representation.  For a bounded-type function `g = G/H`,
both `G` and `H` are bounded analytic, so their Nevanlinna characteristics
are bounded, and the characteristic of `g` grows at most like the sum of
the characteristics of `G` and `H⁻¹`.

The precise statement is: there exists `C > 0` such that for all `r ∈ (0, 1)`,
`circleAverage (log⁺ ‖g ·‖) 0 r ≤ C * (1 - r)⁻¹`.

**Proof sketch**: For `g = G/H` with `G`, `H` bounded analytic,
- `log⁺ ‖g‖ ≤ log⁺ ‖G‖ + log⁺ ‖H⁻¹‖` by subadditivity of `log⁺`.
- `log⁺ ‖G‖` is bounded by `log⁺ (bound of G)`.
- For `log⁺ ‖H⁻¹‖`, we use that `H` is analytic and nonvanishing on the disc,
  so by the minimum modulus principle on compact subsets, `|H|` is bounded
  below. The growth of `log⁺ ‖H⁻¹‖` as `r → 1⁻` is controlled by the
  distance to the boundary, giving the `(1 - r)⁻¹` factor. -/
lemma IsOfBoundedTypeUnitDisc.characteristic_growth
    {g : ℂ → ℂ} (hg : IsOfBoundedTypeUnitDisc g) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ r : ℝ, 0 < r → r < 1 →
        circleAverage (Real.log⁺ ‖g ·‖) 0 r ≤ C * (1 - r)⁻¹ := by
  -- Extract the bounded analytic representation.
  rcases hg with ⟨G, H, _hG_an, _hH_an, hG_bd, _hH_bd, _hH_ne, _hEq⟩
  -- Get the bound on `log⁺ ‖G‖`.
  obtain ⟨M_G, hM_G_pos, _hM_G_bound⟩ := IsBoundedOnUnitDisc.posLog_norm_le hG_bd
  -- The full proof requires:
  -- 1. Bounding `log⁺ ‖g‖ ≤ log⁺ ‖G‖ + log⁺ ‖H⁻¹‖` on the circle.
  -- 2. Using the minimum modulus principle for `H` on closed subdiscs.
  -- 3. Integrating to get the circle average bound.
  -- For now, we provide the existence with a placeholder.
  use M_G + 1
  constructor
  · linarith
  · intro r _hr0 _hr1
    -- Placeholder: the actual bound requires the minimum modulus argument.
    sorry

/-- The **mean type** of a function on the unit disc.

For a function `g` on the disc, the mean type is defined as the limit
`lim_{r → 1⁻} (1 - r) · circleAverage (log⁺ ‖g ·‖) 0 r`
when it exists.

For bounded-type functions, this limit exists and is finite.
For bounded analytic functions, the mean type is zero.
For functions with polynomial growth near the boundary, the mean type
captures the leading growth rate.

This is the disc analogue of the mean type for the upper half-plane,
where one considers `lim_{y → ∞} log⁺ ‖f(iy)‖ / y`.

**Implementation note**: We define `meanTypeDisc g` using `limsup` to ensure
it is always well-defined, even when the limit does not exist. For
bounded-type functions, the `limsup` equals the actual limit. -/
noncomputable def meanTypeDisc (g : ℂ → ℂ) : ℝ :=
  -- Use limsup for well-definedness; for bounded-type functions this is a limit.
  -- The filter `atTop.comap (fun r => (1 - r)⁻¹)` captures `r → 1⁻`.
  Filter.limsup (fun r : ℝ => (1 - r) * circleAverage (Real.log⁺ ‖g ·‖) 0 r)
    (Filter.atTop.comap (fun r => (1 - r)⁻¹))

/-- For a bounded analytic function, the mean type is zero. -/
lemma IsBoundedOnUnitDisc.meanTypeDisc_eq_zero {G : ℂ → ℂ}
    (hG_an : AnalyticOn ℂ G unitDiscSet) (hG_bd : IsBoundedOnUnitDisc G) :
    meanTypeDisc G = 0 := by
  -- Since `G` is bounded, `log⁺ ‖G‖` is bounded, so
  -- `(1 - r) * circleAverage (log⁺ ‖G ·‖) 0 r → 0` as `r → 1⁻`.
  sorry

/-! ### Constructing the analytic Poisson term from Jensen's formula -/

/-- Given a bounded-type function `g` on the disc, construct the analytic
function `F` whose real part gives the "harmonic" part of `log ‖g‖`.

The construction proceeds as follows:
1. For each `r < 1`, Jensen's formula gives us
   `circleAverage (log ‖g ·‖) 0 r = (divisor terms) + log ‖trailing coeff‖`
2. The divisor terms can be rewritten as a Poisson integral plus a
   singular part (the Blaschke factor contribution).
3. Taking the limit as `r → 1⁻`, we extract a harmonic function `u`
   on the disc such that `log ‖g z‖ = u(z) + (singular terms)`.
4. The harmonic function `u` has a Poisson representation, and we
   take `F` to be its analytic completion (unique up to imaginary constant).

For now, we define `F` as a placeholder and will refine the construction. -/
def analyticPoissonPart (g : ℂ → ℂ) : ℂ → ℂ :=
  -- Placeholder: the analytic function whose real part gives the
  -- harmonic part of `log ‖g‖`.  The actual construction requires
  -- solving the Dirichlet problem for the boundary values.
  fun _ => 0

/-- The analytic Poisson part of a bounded-type function is analytic
on the open unit disc. -/
lemma analyticPoissonPart_analyticOn (_g : ℂ → ℂ) :
    AnalyticOn ℂ (analyticPoissonPart _g) unitDiscSet := by
  -- The zero function is analytic everywhere.
  unfold analyticPoissonPart
  exact analyticOn_const

/-- The analytic Poisson part of a bounded-type function has a
Poisson representation on the disc.

This is the key property that allows us to package the harmonic
part of `log ‖g‖` into a `HasDiskPoissonRepresentation` structure. -/
lemma analyticPoissonPart_hasDiskPoissonRepresentation
    {g : ℂ → ℂ} (_hg : IsOfBoundedTypeUnitDisc g) :
    HasDiskPoissonRepresentation (analyticPoissonPart g) := by
  -- The zero function has a trivial Poisson representation.
  -- The actual proof will use the construction from Jensen's formula.
  constructor
  · -- Analyticity on the disc
    unfold analyticPoissonPart
    intro z _hz
    exact analyticAt_const.analyticWithinAt
  · -- Integrability
    intro z
    unfold analyticPoissonPart
    simp only [zero_re, zero_mul]
    exact MeasureTheory.integrableOn_zero
  · -- Poisson formula
    intro z
    unfold analyticPoissonPart
    simp only [zero_re, zero_mul]
    symm
    exact MeasureTheory.integral_zero (α := ℝ) (G := ℝ)

/-- The decomposition of `log ‖g z‖` for a bounded-type function.

For a bounded-type function `g` on the disc, we have the representation:
`log ‖g z‖ = α · (1 - ‖z‖)⁻¹ + (analyticPoissonPart g z).re + (singular terms)`

where:
- `α = meanTypeDisc g` is the mean type,
- `analyticPoissonPart g` is the analytic function with Poisson representation,
- the singular terms come from the Blaschke product (zeros and poles of `g`).

For the smoothed version `log (‖g z‖ + 1)`, the singular terms are absorbed
and we get a cleaner representation. -/
lemma IsOfBoundedTypeUnitDisc.log_norm_decomposition
    {g : ℂ → ℂ} (_hg : IsOfBoundedTypeUnitDisc g) (z : UnitDisc) :
    ∃ (singular : ℝ),
      Real.log ‖g z‖ =
        meanTypeDisc g * (1 - ‖(z : ℂ)‖)⁻¹ +
        (analyticPoissonPart g z).re +
        singular := by
  -- The full proof requires the Jensen formula limit argument.
  -- For now, we use a placeholder that absorbs all terms into `singular`.
  use Real.log ‖g z‖ - meanTypeDisc g * (1 - ‖(z : ℂ)‖)⁻¹ - (analyticPoissonPart g z).re
  ring

/-! ### Disk‑level Poisson–Jensen representation data -/

/-- Disk‑level canonical representation / Poisson–Jensen data for `g`.

This encapsulates the analytic information one expects from Nevanlinna
canonical representation and the Poisson–Jensen formula on the unit disc:

* `F` is analytic on the disc and has a Poisson representation in the sense
  of `HasDiskPoissonRepresentation`,
* there is a real parameter `α` encoding the "mean type" of `g`,
* for each `z : 𝔻` there is a Poisson‑type formula for
  `Real.log (‖g z‖ + 1)` as a sum of a linear growth term and the real part
  of `F z`.

The precise normalization of the linear term is chosen here as
`α * (1 - ‖z‖)⁻¹`, reflecting the standard growth parameter for Nevanlinna
theory on the disc (distance to the boundary).  This normalization can be
adjusted later if needed; the rest of the de Branges layer only uses the
existence of some such representation. -/
def DiskPoissonJensenRepresentation (g : ℂ → ℂ) : Prop :=
  ∃ (F : ℂ → ℂ) (alpha : ℝ),
    HasDiskPoissonRepresentation F ∧
    ∀ z : Complex.UnitDisc,
      Real.log (‖g z‖ + 1) =
        alpha * (1 - ‖(z : ℂ)‖)⁻¹ + (F z).re

/-- **Disk Poisson–Jensen for bounded‑type functions (statement level).**

If `g` is of bounded type on the unit disc (Nevanlinna class on `𝔻`), then
it admits a canonical Poisson–Jensen representation in the sense of
`DiskPoissonJensenRepresentation`.

The proof is **not yet implemented**: it will proceed by

* extending `g` to a meromorphic function on the plane using standard
  Nevanlinna theory on the disc,
* applying the `ValueDistribution` machinery (`FirstMainTheorem` and related
  results) to obtain a canonical representation for `log ‖g‖`,
* extracting an analytic function `F` with `HasDiskPoissonRepresentation F`,
  and a real parameter `α` describing the mean type,
* showing that the resulting formula matches the specification of
  `DiskPoissonJensenRepresentation g`.

For now we only record the statement and leave the analytic core as a TODO. -/
theorem disk_PoissonJensen_for_boundedType
    (g : ℂ → ℂ) (hg : IsOfBoundedTypeUnitDisc g) :
    DiskPoissonJensenRepresentation g := by
  -- TODO (analytic core, via `ValueDistribution.FirstMainTheorem` and
  -- canonical factorisation / Poisson–Jensen on the disc or plane).
  --
  -- Sketch of the intended proof:
  -- * Use `hg` to write `g = G/H` with `G`, `H` bounded analytic and `H ≠ 0`
  --   on the disc.
  -- * Extend `g` (or an appropriate modification) to a meromorphic function
  --   on `ℂ` and apply the Nevanlinna characteristic machinery.
  -- * Invoke the First Main Theorem to control the characteristic and obtain
  --   a canonical representation of `log ‖g‖` in terms of an analytic part
  --   plus an explicit Poisson integral.
  -- * Package the analytic part as a function `F` with
  --   `HasDiskPoissonRepresentation F`, and extract the slope `α` of the main
  --   growth term in the disc radius.
  -- * Verify that the resulting `F` and `α` satisfy the `hLog` identity
  --   above.
  sorry

end Complex

end
