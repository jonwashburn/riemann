import Riemann.Mathlib.Analysis.Harmonic.BMO.Defs



open MeasureTheory Measure Set Filter Real
open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α] {μ : Measure α}

/-! ### John-Nirenberg Inequality -/

variable [ProperSpace α] [IsUnifLocDoublingMeasure μ]

/-- The doubling constant we use throughout. -/
private noncomputable abbrev D := IsUnifLocDoublingMeasure.doublingConstant μ

/-- The key iteration lemma for John-Nirenberg: one step of the CZ decomposition.

Given a ball `B` and level `λ`, we decompose `{x ∈ B : |f(x) - f_B| > 2λ}` into
sub-balls `{Bⱼ}` such that:
1. `∑ μ(Bⱼ) ≤ (1/2) · μ(B)` (geometric decay)
2. On each `Bⱼ`, the oscillation is controlled: `⨍_{Bⱼ} |f - f_{Bⱼ}| ≤ M`

The factor `1/2` comes from the BMO condition and Chebyshev's inequality:
if `⨍_B |f - f_B| ≤ M`, then `μ({|f - f_B| > 2M}) ≤ (1/2) μ(B)`.

**References**: John-Nirenberg (1961), Stein "Harmonic Analysis" Ch. IV -/
theorem johnNirenberg_iteration {f : α → ℝ} {M : ℝ} (hM : 0 < M)
    (hmo : ∀ (x : α) (r : ℝ) (_ : 0 < r),
      ⨍ y in Metric.ball x r, |f y - ⨍ z in Metric.ball x r, f z ∂μ| ∂μ ≤ M)
    {x₀ : α} {r : ℝ} (hr : 0 < r) {lambda : ℝ} (hlambda : M ≤ lambda) :
    μ {x ∈ Metric.ball x₀ r | |f x - ⨍ y in Metric.ball x₀ r, f y ∂μ| > 2 * lambda} ≤
      (1 / 2) * μ (Metric.ball x₀ r) := by
  -- By Chebyshev/Markov inequality: if the average of |g| is at most M,
  -- then the measure of {|g| > 2λ} is at most M/(2λ) · μ(B) ≤ (1/2) · μ(B)
  -- when M ≤ λ.
  --
  -- More precisely, for g = f - f_B:
  --   μ({|g| > 2λ}) ≤ (1/(2λ)) · ∫_B |g| dμ = (μ(B)/(2λ)) · ⨍_B |g| dμ ≤ (M/(2λ)) · μ(B)
  -- Since M ≤ λ, we have M/(2λ) ≤ 1/2.
  sorry

/-- Geometric decay: after `k` iterations, the superlevel set decays by `(1/2)^k`.

This is the inductive consequence of `johnNirenberg_iteration`. -/
theorem johnNirenberg_geometric_decay {f : α → ℝ} {M : ℝ} (hM : 0 < M)
    (hmo : ∀ (x : α) (r : ℝ) (_ : 0 < r),
      ⨍ y in Metric.ball x r, |f y - ⨍ z in Metric.ball x r, f z ∂μ| ∂μ ≤ M)
    {x₀ : α} {r : ℝ} (hr : 0 < r) (k : ℕ) :
    μ {x ∈ Metric.ball x₀ r | |f x - ⨍ y in Metric.ball x₀ r, f y ∂μ| > (k + 1) * M} ≤
      (1 / 2) ^ k * μ (Metric.ball x₀ r) := by
  -- Induction on k:
  -- Base case k = 0: use johnNirenberg_iteration with λ = M
  -- Inductive step: apply CZ decomposition to get sub-balls, then apply IH on each
  induction k with
  | zero =>
    simp only [pow_zero, one_mul, Nat.zero_add, one_mul]
    -- The superlevel set {|f - f_B| > M} has measure ≤ μ(B)
    exact measure_mono (fun x hx => hx.1)
  | succ k ih =>
    -- Decompose the superlevel set {|f - f_B| > (k+1)M} using CZ balls
    -- On each sub-ball B', apply the inductive hypothesis
    -- Sum up using the measure bound from johnNirenberg_iteration
    sorry

/-- **John-Nirenberg inequality**: exponential decay of the distribution function.

For a function `f` with bounded mean oscillation ≤ M on all balls, the superlevel sets
of `|f - f_B|` decay exponentially:

  `μ({x ∈ B : |f(x) - f_B| > t}) ≤ C · μ(B) · exp(-c·t/M)`

where `C = 2` and `c = log(2)/2 ≈ 0.35`.

**Proof**: Use `johnNirenberg_geometric_decay` with `k = ⌊t/M⌋` to get decay `(1/2)^k`.
Since `(1/2)^k = exp(-k log 2) ≤ exp(-(t/M - 1) log 2) = 2 · exp(-t log(2)/M)`.

**Mathematical significance**: This exponential integrability is the defining property
of BMO that makes it useful in harmonic analysis. It implies:
- BMO ⊂ L^p_loc for all p < ∞
- Duality: (H¹)* ≅ BMO (Fefferman-Stein)
- Self-improvement of Gehring-type estimates -/
theorem johnNirenberg_exponential_decay {f : α → ℝ} {x₀ : α} {r : ℝ} (hr : 0 < r)
    {M : ℝ} (hM : 0 < M)
    (hmo : ∀ (x : α) (r : ℝ) (_ : 0 < r),
      ⨍ y in Metric.ball x r, |f y - ⨍ z in Metric.ball x r, f z ∂μ| ∂μ ≤ M)
    {t : ℝ} (ht : 0 < t) :
    μ {x ∈ Metric.ball x₀ r | |f x - ⨍ y in Metric.ball x₀ r, f y ∂μ| > t} ≤
      2 * μ (Metric.ball x₀ r) * ENNReal.ofReal (Real.exp (-t / (2 * M))) := by
  -- Choose k = ⌊t/M⌋ so that t ∈ (k·M, (k+1)·M]
  -- Then use johnNirenberg_geometric_decay:
  --   μ({|f - f_B| > t}) ≤ μ({|f - f_B| > k·M}) ≤ (1/2)^(k-1) · μ(B)
  -- Since (1/2)^(k-1) = 2 · (1/2)^k = 2 · exp(-k·log 2)
  -- and k ≥ t/M - 1, we get:
  --   (1/2)^(k-1) ≤ 2 · exp(-(t/M - 1)·log 2) = 2 · exp(log 2) · exp(-t·log 2/M)
  --                = 4 · exp(-t·log 2/M)
  -- With the constant adjustment c = log(2)/2 ≈ 0.35, we get the stated bound.
  by_cases ht_small : t ≤ M
  · -- For t ≤ M, use the trivial bound μ(superlevel) ≤ μ(B)
    calc μ {x ∈ Metric.ball x₀ r | |f x - ⨍ y in Metric.ball x₀ r, f y ∂μ| > t}
        ≤ μ (Metric.ball x₀ r) := measure_mono (fun x hx => hx.1)
      _ ≤ 2 * μ (Metric.ball x₀ r) * ENNReal.ofReal (Real.exp (-t / (2 * M))) := by
          -- exp(-t/(2M)) ≥ exp(-1/2) > 0.6, so 2 · exp(-t/(2M)) > 1
          have hexp : Real.exp (-t / (2 * M)) ≥ Real.exp (-1/2) := by
            apply Real.exp_le_exp_of_le
            apply div_le_div_of_nonneg_right _ (by linarith : 0 < 2 * M)
            linarith
          have hexp_pos : 0 < Real.exp (-t / (2 * M)) := Real.exp_pos _
          -- 2 · exp(-1/2) ≈ 1.21 > 1
          sorry
  · -- For t > M, use the geometric decay
    push_neg at ht_small
    -- k = ⌈t/M⌉ - 1, so (k+1)·M ≥ t and the superlevel set is contained
    let k := Nat.ceil (t / M) - 1
    have hk : (k + 1) * M ≥ t := by
      simp only [k]
      have h1 : (Nat.ceil (t / M) : ℝ) ≥ t / M := Nat.le_ceil (t / M)
      have h2 : Nat.ceil (t / M) ≥ 1 := by
        rw [Nat.one_le_ceil_iff (by positivity : 0 < M)]
        exact ht_small
      calc ((Nat.ceil (t / M) - 1 : ℕ) + 1 : ℝ) * M
          = (Nat.ceil (t / M) : ℝ) * M := by
            rw [Nat.cast_sub h2, sub_add_cancel]
        _ ≥ (t / M) * M := by nlinarith
        _ = t := by field_simp
    -- Apply geometric decay
    calc μ {x ∈ Metric.ball x₀ r | |f x - ⨍ y in Metric.ball x₀ r, f y ∂μ| > t}
        ≤ μ {x ∈ Metric.ball x₀ r | |f x - ⨍ y in Metric.ball x₀ r, f y ∂μ| > (k + 1) * M} := by
          apply measure_mono
          intro x ⟨hx_mem, hx_large⟩
          exact ⟨hx_mem, lt_of_le_of_lt hk hx_large⟩
      _ ≤ (1 / 2) ^ k * μ (Metric.ball x₀ r) := johnNirenberg_geometric_decay hM hmo hr k
      _ ≤ 2 * μ (Metric.ball x₀ r) * ENNReal.ofReal (Real.exp (-t / (2 * M))) := by
          -- Convert (1/2)^k to exponential form and bound
          sorry

/-! ### BMO to L^p_loc -/

/-- The **layer-cake formula** applied to the John-Nirenberg bound gives
L^p integrability for BMO functions.

For any ball B and any finite p ≥ 1:
  `‖f - f_B‖_{L^p(B)}^p = p ∫_0^∞ t^{p-1} · μ({|f - f_B| > t}) dt`
                        `≤ p ∫_0^∞ t^{p-1} · C·μ(B)·exp(-ct/M) dt`
                        `= C·μ(B)·p·(M/c)^p · Γ(p)`
                        `= C_p · M^p · μ(B)`

Hence `‖f - f_B‖_{L^p(B)} ≤ C_p · M · μ(B)^{1/p}`, and since `f_B` is a constant:
  `‖f‖_{L^p(B)} ≤ ‖f - f_B‖_{L^p(B)} + |f_B| · μ(B)^{1/p}` -/
theorem bmo_memLp_loc {f : α → ℝ} {M : ℝ} (hM : 0 < M)
    (hmo : ∀ (x : α) (r : ℝ) (_ : 0 < r),
      ⨍ y in Metric.ball x r, |f y - ⨍ z in Metric.ball x r, f z ∂μ| ∂μ ≤ M)
    (hf_loc : LocallyIntegrable f μ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    {x₀ : α} {r : ℝ} (hr : 0 < r) :
    MemLp f p (μ.restrict (Metric.ball x₀ r)) := by
  -- Step 1: Show f - f_B is in L^p using John-Nirenberg + layer cake
  -- Step 2: f_B is a constant, hence in L^p on a finite measure set
  -- Step 3: f = (f - f_B) + f_B, use triangle inequality
  sorry

/-- Explicit bound on the L^p norm of a BMO function on a ball.

The constant `C_p` grows like `p` as `p → ∞`, which is optimal. -/
theorem bmo_Lp_bound {f : α → ℝ} {M : ℝ} (hM : 0 < M)
    (hmo : ∀ (x : α) (r : ℝ) (_ : 0 < r),
      ⨍ y in Metric.ball x r, |f y - ⨍ z in Metric.ball x r, f z ∂μ| ∂μ ≤ M)
    (hf_loc : LocallyIntegrable f μ)
    {p : ℝ} (hp : 1 ≤ p)
    {x₀ : α} {r : ℝ} (hr : 0 < r) :
    eLpNorm (fun x => f x - ⨍ y in Metric.ball x₀ r, f y ∂μ) p (μ.restrict (Metric.ball x₀ r)) ≤
      ENNReal.ofReal (4 * p * M) * μ (Metric.ball x₀ r) ^ (1 / p) := by
  -- Use layer-cake formula with John-Nirenberg bound
  -- The integral ∫_0^∞ t^{p-1} exp(-ct/M) dt = (M/c)^p · Γ(p) ≈ (M/c)^p · (p-1)!
  -- This gives the bound with constant C_p ≈ p · (2/log 2)^p · (p-1)! ≈ 4p for moderate p
  sorry
