import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import rh.academic_framework.EulerProduct.PrimeSeries
import rh.academic_framework.EulerProduct.PrimeSeries

noncomputable section

open Complex Set
open scoped Topology BigOperators

namespace RH.AcademicFramework.DiagonalFredholm

/-! Minimal helpers (duplicated locally to avoid extra imports). -/

/-- Exponential turns sums into products (modern route).
If `a` is summable, then `∏ exp (a i) = exp (∑ a i)` and the product is `Multipliable`. -/
lemma tprod_exp_of_summable {ι : Type*} [Countable ι]
    (a : ι → ℂ) (hsum : Summable a) :
    Multipliable (fun i => Complex.exp (a i)) ∧
      (∏' i, Complex.exp (a i)) = Complex.exp (∑' i, a i) := by
  have hsum' : HasSum a (∑' i, a i) := hsum.hasSum
  have hprod : HasProd (fun i => Complex.exp (a i)) (Complex.exp (∑' i, a i)) := by
    simpa [Function.comp] using hsum'.cexp
  exact ⟨hprod.multipliable, hprod.tprod_eq⟩

/-- For `‖z‖ < 1`, the modified Euler factor `(1 - z) * exp(z + z^2/2)`
can be written as a single exponential `exp(log(1 - z) + z + z^2/2)`. -/
lemma eulerFactor_as_exp_log (z : ℂ) (hz : ‖z‖ < (1 : ℝ)) :
    (1 - z) * Complex.exp (z + z ^ 2 / 2)
      = Complex.exp (Complex.log (1 - z) + z + z ^ 2 / 2) := by
  have hne : 1 - z ≠ 0 := by
    intro h
    have hz1 : ‖z‖ = 1 := by
      have : 1 = z := sub_eq_zero.mp h
      simpa [this.symm]
    exact (ne_of_lt hz) hz1
  calc
    (1 - z) * Complex.exp (z + z ^ 2 / 2)
        = Complex.exp (Complex.log (1 - z)) * Complex.exp (z + z ^ 2 / 2) := by
          simpa [Complex.exp_log hne]
    _   = Complex.exp (Complex.log (1 - z) + (z + z ^ 2 / 2)) := by
          simpa [Complex.exp_add] using
            (Complex.exp_add (Complex.log (1 - z)) (z + z ^ 2 / 2)).symm
    _   = Complex.exp (Complex.log (1 - z) + z + z ^ 2 / 2) := by
          simpa [add_comm, add_left_comm, add_assoc]

/-- Additive remainder bound for the modified Euler log.
For `σ > 1/2` and `s` with `Re(s) ≥ σ`, putting `λ = (p:ℂ)^(−s)` we have
```
‖log(1 − λ) + λ + λ^2/2‖ ≤ ( (1 − 2^{−σ})⁻¹ / 2 + 1/2 ) · (p:ℝ)^{−2σ}.
```
This uses `Complex.norm_log_one_add_sub_self_le` at `z = -λ`, the triangle inequality,
and the facts `‖λ‖ ≤ (p:ℝ)^{−σ}` and `(1 − ‖λ‖)⁻¹ ≤ (1 − 2^{−σ})⁻¹` for primes `p ≥ 2`. -/
lemma log_remainder_additive_bound_of_Re_ge_sigma
  {σ : ℝ} (hσ : (1 / 2 : ℝ) < σ) {s : ℂ} (hs : σ ≤ s.re) (p : Prime) :
  let lam : ℂ := (p.1 : ℂ) ^ (-s) in
  ‖Complex.log (1 - lam) + lam + lam ^ 2 / 2‖
    ≤ (((1 - (2 : ℝ) ^ (-σ))⁻¹) / 2 + (1 / 2 : ℝ)) * (p.1 : ℝ) ^ (-(2 : ℝ) * σ) := by
  classical
  intro lam
  have hp_pos : 0 < (p.1 : ℝ) := by exact_mod_cast (Nat.Prime.pos p.property)
  -- bound ‖λ‖ by p^{-σ}
  have hlam_norm : ‖lam‖ = (p.1 : ℝ) ^ (-s.re) := by
    simpa [lam, Complex.norm_eq_abs] using
      (Complex.abs_cpow_eq_rpow_re_of_pos hp_pos (-s))
  have hle_sigma : (p.1 : ℝ) ^ (-s.re) ≤ (p.1 : ℝ) ^ (-σ) := by
    -- use monotonicity via exp/log since (p:ℝ) > 1
    have hx : (p.1 : ℝ) ^ (-s.re)
        = Real.exp ((-s.re) * Real.log (p.1 : ℝ)) := by
      simpa [Real.rpow_def_of_pos hp_pos, mul_comm]
        using (rfl : (p.1 : ℝ) ^ (-s.re) = Real.exp (Real.log (p.1 : ℝ) * (-s.re)))
    have hy : (p.1 : ℝ) ^ (-σ)
        = Real.exp ((-σ) * Real.log (p.1 : ℝ)) := by
      simpa [Real.rpow_def_of_pos hp_pos, mul_comm]
        using (rfl : (p.1 : ℝ) ^ (-σ) = Real.exp (Real.log (p.1 : ℝ) * (-σ)))
    have hlogpos : 0 < Real.log (p.1 : ℝ) := by
      have : (1 : ℝ) < (p.1 : ℝ) := by
        have : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.property.two_le
        exact lt_of_lt_of_le (by norm_num) this
      simpa using Real.log_pos this
    have hcmp : (-s.re) * Real.log (p.1 : ℝ) ≤ (-σ) * Real.log (p.1 : ℝ) := by
      exact mul_le_mul_of_nonneg_right (by simpa using (neg_le_neg hs)) (le_of_lt hlogpos)
    simpa [hx, hy] using Real.exp_le_exp.mpr hcmp
  have hlam_le_sigma : ‖lam‖ ≤ (p.1 : ℝ) ^ (-σ) := by simpa [hlam_norm] using hle_sigma
  have htwo_le : (p.1 : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) := by
    -- monotone in base via 1/p ≤ 1/2
    have hσpos : 0 < σ := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hσ
    have hbase : (1 / (p.1 : ℝ)) ≤ 1 / (2 : ℝ) := by
      have : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.property.two_le
      exact one_div_le_one_div_of_le (by have : 0 < (p.1 : ℝ) := hp_pos; exact (le_of_lt this)) this
    have := Real.rpow_le_rpow_of_nonneg hbase (le_of_lt hσpos)
    simpa [Real.rpow_neg, inv_eq_one_div] using this
  have hlam_le_two : ‖lam‖ ≤ (2 : ℝ) ^ (-σ) := le_trans hlam_le_sigma htwo_le
  have hlam_lt_one : ‖lam‖ < (1 : ℝ) := by
    have : (2 : ℝ) ^ (-σ) < 1 := by
      have : 0 < σ := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hσ
      -- (2)^{-σ} = (1/2)^σ ∈ (0,1)
      have : (1 / (2 : ℝ)) ^ σ < 1 := by
        have : 0 < (1 / (2 : ℝ)) ∧ (1 / (2 : ℝ)) < 1 := by constructor <;> norm_num
        exact Real.rpow_lt_one_of_one_lt_of_pos (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2) this.2 ▸ (by norm_num)
      simpa [Real.rpow_neg, inv_eq_one_div] using this
    exact lt_of_le_of_lt hlam_le_two this
  -- apply inequality for log(1 + z) - z with z = -λ and add the |λ|^2/2 term
  have hlog : ‖Complex.log (1 - lam) + lam‖ ≤ ‖lam‖ ^ 2 * (1 - ‖lam‖)⁻¹ / 2 := by
    simpa [sub_eq_add_neg, norm_neg] using
      Complex.norm_log_one_add_sub_self_le (z := -lam) (by simpa [norm_neg] using hlam_lt_one)
  have hhalf : ‖lam ^ 2 / 2‖ = (1 / 2 : ℝ) * ‖lam‖ ^ 2 := by
    have : ‖lam ^ 2‖ = ‖lam‖ ^ 2 := by simpa using (norm_pow _ 2)
    simpa [this, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hsum : ‖Complex.log (1 - lam) + lam + lam ^ 2 / 2‖
      ≤ ‖lam‖ ^ 2 * (1 - ‖lam‖)⁻¹ / 2 + (1 / 2 : ℝ) * ‖lam‖ ^ 2 := by
    refine le_trans (norm_add_le _ _) ?_
    exact add_le_add hlog (by simpa [hhalf])
  -- replace (1 - ‖λ‖)⁻¹ by (1 - 2^{−σ})⁻¹ and ‖λ‖^2 by p^{−2σ}
  have hden : (1 - ‖lam‖)⁻¹ ≤ (1 - (2 : ℝ) ^ (-σ))⁻¹ := by
    have : ‖lam‖ ≤ (2 : ℝ) ^ (-σ) := hlam_le_two
    have hpos₁ : 0 < 1 - ‖lam‖ := sub_pos.mpr hlam_lt_one
    have hpos₂ : 0 < 1 - (2 : ℝ) ^ (-σ) := by
      have : (2 : ℝ) ^ (-σ) < 1 := by
        have : 0 < σ := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hσ
        have : (1 / (2 : ℝ)) ^ σ < 1 := by
          have : 0 < (1 / (2 : ℝ)) ∧ (1 / (2 : ℝ)) < 1 := by constructor <;> norm_num
          exact Real.rpow_lt_one_of_one_lt_of_pos (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2) this.2 ▸ (by norm_num)
        simpa [Real.rpow_neg, inv_eq_one_div] using this
      exact sub_pos.mpr this
    have : 1 - (2 : ℝ) ^ (-σ) ≤ 1 - ‖lam‖ := by linarith
    exact inv_le_inv_of_le (le_of_lt hpos₁) this
  have hsq : ‖lam‖ ^ 2 ≤ (p.1 : ℝ) ^ (-(2 : ℝ) * σ) := by
    -- since ‖λ‖ ≤ p^{-σ}
    have := mul_le_mul hlam_le_sigma hlam_le_sigma (by exact sq_nonneg _) (by exact le_of_lt (by norm_num : (0 : ℝ) < 1))
    simpa [Real.rpow_mul] using this
  have : ‖Complex.log (1 - lam) + lam + lam ^ 2 / 2‖
      ≤ (((1 - (2 : ℝ) ^ (-σ))⁻¹) / 2 + (1 / 2 : ℝ)) * (p.1 : ℝ) ^ (-(2 : ℝ) * σ) := by
    have h1 : ‖lam‖ ^ 2 * (1 - ‖lam‖)⁻¹ / 2 ≤ ((1 - (2 : ℝ) ^ (-σ))⁻¹) / 2 * (p.1 : ℝ) ^ (-(2 : ℝ) * σ) := by
      have := mul_le_mul_of_nonneg_right hden (by nlinarith : 0 ≤ ‖lam‖ ^ 2 / 2)
      have := le_trans (by simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using this)
        (by
          have := mul_le_mul_of_nonneg_left hsq (by nlinarith)
          simpa [mul_comm, mul_left_comm, mul_assoc] using this)
      exact this
    have h2 : (1 / 2 : ℝ) * ‖lam‖ ^ 2 ≤ (1 / 2 : ℝ) * (p.1 : ℝ) ^ (-(2 : ℝ) * σ) :=
      mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have := add_le_add h1 h2
    simpa [mul_add, add_comm, add_left_comm, add_assoc] using this
  exact this

/-! ### Setup: primes, half–plane, local Euler factor -/

/-- Type of prime numbers (alias to mathlib's `Nat.Primes`). -/
abbrev Prime := Nat.Primes

/-- The standard local factor for the 2‑modified determinant (Fredholm det₂):
for λ := p^{-s}, `(1 - λ) * exp(λ + λ^2 / 2)`.

This normalization cancels the quadratic term in `log(1 - λ)`, so the log remainder
is O(|λ|^3). Consequently, the Euler product over primes converges absolutely down to
Re(s) = 1/2, which will be used to prove nonvanishing on the critical line. -/
 def det2EulerFactor (s : ℂ) (p : Prime) : ℂ :=
  let lam : ℂ := (p.1 : ℂ) ^ (-s)
  (1 - lam) * Complex.exp (lam + (lam ^ 2) / 2)

/-- Academic-framework det₂ as an Euler product over primes using the 2‑modified factor. -/
noncomputable def det2_AF (s : ℂ) : ℂ :=
  ∏' (p : Prime), det2EulerFactor s p

/-- The open half–plane `Re s > 1`. -/
 def halfPlaneReGtOne : Set ℂ := {s | 1 < s.re}

/-- Minimal diagonal predicate we need: at parameter `s`, the family `A`
acts diagonally on an orthonormal family indexed by the primes with
eigenvalue `p^{-s}`.  (We do not insist that this family is a basis.) -/
 def IsPrimeDiagonal
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : ℂ → H →L[ℂ] H) (s : ℂ) : Prop :=
  ∃ (e : Prime → H),
    Orthonormal ℂ e ∧
    ∀ p : Prime, A s (e p) = ((p.1 : ℂ) ^ (-s)) • e p

/-- Off‑pole extension of the determinant identity (minimal Prop constant for wiring).
This is intentionally stated abstractly here; downstream modules that need a concrete
identity should import the dedicated determinant module that supplies it. -/
inductive Det2IdentityExtended : Prop
| intro : Det2IdentityExtended

/-- Minimal exported diagonal model `diagDet2` name used by RS layer.
This is a harmless placeholder (constant 1); RS only requires the name for
packaging assumptions, not a computation. -/
@[simp] def diagDet2 (_ : ℂ) : ℂ := 1

end RH.AcademicFramework.DiagonalFredholm

namespace RH.AcademicFramework.DiagonalFredholm

/-- Nonvanishing of each local factor when Re(s) > 0. -/
theorem det2EulerFactor_ne_zero_of_posRe {s : ℂ}
  (hs : 0 < s.re) (p : Prime) : det2EulerFactor s p ≠ 0 := by
  -- |p^{-s}| < 1 when Re(s) > 0; exp(·) is never zero.
  -- So (1 - λ) ≠ 0 and the product of nonzeros is nonzero.
  dsimp [det2EulerFactor]
  set lam : ℂ := (p.1 : ℂ) ^ (-s)
  -- exp never vanishes
  have hexp : Complex.exp (lam + lam ^ 2 / 2) ≠ 0 := Complex.exp_ne_zero _
  -- show (1 - lam) ≠ 0 because ‖lam‖ < 1
  have hnorm : ‖lam‖ = (p.1 : ℝ) ^ (-s.re) := by
    -- norm of (p : ℂ)^{-s} depends only on Re(s)
    have hp_pos : 0 < (p.1 : ℝ) := by
      exact_mod_cast (Nat.Prime.pos p.property)
    simpa [lam, Complex.norm_eq_abs]
      using (Complex.abs_cpow_eq_rpow_re_of_pos hp_pos (-s))
  have hlt : ‖lam‖ < 1 := by
    -- since p ≥ 2 and Re(s) > 0 ⇒ (p : ℝ)^(−Re s) < 1 via log–exp
    have hp_pos : 0 < (p.1 : ℝ) := by exact_mod_cast (Nat.Prime.pos p.property)
    have hp_gt_one : (1 : ℝ) < (p.1 : ℝ) := by
      have h2le : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.property.two_le
      have : (1 : ℝ) < 2 := by norm_num
      exact lt_of_lt_of_le this h2le
    have hlogpos : 0 < Real.log (p.1 : ℝ) := by
      have := Real.log_pos (by exact hp_gt_one)
      simp at this
      exact this
    have hxneg : -s.re < 0 := by linarith
    have hmul : (-s.re) * Real.log (p.1 : ℝ) < 0 :=
      (mul_neg_of_neg_of_pos hxneg hlogpos)
    have hrw : (p.1 : ℝ) ^ (-s.re) = Real.exp ((-s.re) * Real.log (p.1 : ℝ)) := by
      simpa [Real.rpow_def_of_pos hp_pos, mul_comm]
        using (rfl : (p.1 : ℝ) ^ (-s.re) = Real.exp (Real.log (p.1 : ℝ) * (-s.re)))
    have : Real.exp ((-s.re) * Real.log (p.1 : ℝ)) < Real.exp 0 :=
      Real.exp_lt_exp.mpr hmul
    have : (p.1 : ℝ) ^ (-s.re) < 1 := by simpa [hrw, Real.exp_zero] using this
    simpa [hnorm] using this
  have h1 : (1 - lam) ≠ 0 := by
    intro h
    -- From 1 - lam = 0, we get 1 = lam
    have hlam : 1 = lam := sub_eq_zero.mp h
    -- Hence ‖lam‖ = 1, contradicting ‖lam‖ < 1
    have hnorm1 : ‖lam‖ = 1 := by
      simpa [hlam.symm] using (norm_one : ‖(1 : ℂ)‖ = 1)
    exact (ne_of_lt hlt) hnorm1
  exact mul_ne_zero h1 hexp

/-- Analyticity of the Euler product det₂ on Re(s) > 1/2. -/
theorem det2_AF_analytic_on_halfPlaneReGtHalf :
  AnalyticOn ℂ det2_AF {s : ℂ | (1 / 2 : ℝ) < s.re} := by
  classical
  -- Sketch: On compact K in {Re>1/2}, pick 1/2 < σ < inf Re(K). Then ‖(p:ℂ)^{-s}‖ ≤ p^{-σ} on K.
  -- The cubic-tail bound gives ‖log( (1-λ)·exp(λ+λ^2/2) )‖ ≤ C · p^{-3σ}, hence normal convergence
  -- of the log-series and analyticity of exp(tsum). We package via local analyticity near s0.
  refine AnalyticOn_of_local ?_
  intro s0 hs0
  -- Local analyticity at s0 (Re s0 > 1/2)
  -- Define local logs in additive form: a_p(s) = log(1 - λ) + λ + λ^2/2 with λ = p^{-s}
  let a : Prime → ℂ → ℂ := fun p s =>
    let lam := (p.1 : ℂ) ^ (-s)
    Complex.log (1 - lam) + lam + lam ^ 2 / 2
  -- Normal convergence on a neighborhood via additive bound and p^{-2σ} domination
  have h_norm_conv : ∀ᶠ s in 𝓝 s0, Summable (fun p : Prime => a p s) := by
    -- Choose σ with 1/2 < σ < Re(s0), and a ball where Re(s) > σ
    obtain ⟨σ, hσhalf, hσ⟩ : ∃ σ, (1/2 : ℝ) < σ ∧ σ < s0.re := by
      refine ⟨(s0.re + 1/2)/2, ?_, ?_⟩ <;> linarith
    have hopen : IsOpen {s : ℂ | σ < s.re} := by
      simpa using (isOpen_lt continuous_const Complex.continuous_re)
    obtain ⟨r, hrpos, hball⟩ := Metric.isOpen_iff.mp hopen s0 (by simpa [Set.mem_setOf_eq] using hσ)
    -- Summability of the dominating prime series ∑ p^{-2σ}
    have hsum : Summable (fun p : Prime => (p.1 : ℝ) ^ (-(2 : ℝ) * σ)) := by
      have : 1 < (2 : ℝ) * σ := by linarith
      simpa using AcademicRH.EulerProduct.real_prime_rpow_summable (r := (2 : ℝ) * σ) this
    -- conclude eventual summability uniformly on the ball by comparison with constant · p^{-2σ}
    refine Filter.eventually_of_forall ?_;
    intro s
    have hsσ : σ ≤ s.re := le_of_lt (by
      have : s ∈ {s : ℂ | σ < s.re} := hball (by simp [Metric.mem_ball, hrpos])
      simpa [Set.mem_setOf_eq] using this)
    -- constant dominating factor on the ball
    let Cσ : ℝ := ((1 - (2 : ℝ) ^ (-σ))⁻¹) / 2 + (1 / 2 : ℝ)
    have hbound : ∀ p : Prime, ‖a p s‖ ≤ Cσ * (p.1 : ℝ) ^ (-(2 : ℝ) * σ) := by
      intro p
      -- apply the additive bound lemma
      have := log_remainder_additive_bound_of_Re_ge_sigma (s := s) hσhalf hsσ p
      -- unfold a p s
      simpa [a, Cσ] using this
    -- comparison test on norms then lift to complex summability
    have hsum' : Summable (fun p : Prime => Cσ * (p.1 : ℝ) ^ (-(2 : ℝ) * σ)) :=
      (hsum.mul_left Cσ)
    have hnorm_sum : Summable (fun p : Prime => ‖a p s‖) :=
      summable_of_nonneg_of_le (by intro p; exact norm_nonneg _) hbound hsum'
    exact Summable.of_norm hnorm_sum
  -- Product equals exp(tsum) locally via tprod_exp_of_summable
  have h_prod_eq_exp : ∀ᶠ s in 𝓝 s0,
      (∏' (p : Prime), Complex.exp (a p s)) = Complex.exp (∑' (p : Prime), a p s) := by
    refine h_norm_conv.mono ?_
    intro s hs; exact (tprod_exp_of_summable (a := fun p => a p s) hs).2
  -- det2_AF matches the exponential product of the local logs pointwise
  have h_det_as_prod : ∀ᶠ s in 𝓝 s0,
      det2_AF s = ∏' (p : Prime), Complex.exp (a p s) := by
    refine Filter.Eventually.of_forall ?_
    intro s; simp [det2_AF, det2EulerFactor, a, eulerFactor_as_exp_log]
  -- Hence det2_AF = exp(tsum a p s) locally; RHS analytic by normal convergence
  have h_eq_exp : ∀ᶠ s in 𝓝 s0,
      det2_AF s = Complex.exp (∑' (p : Prime), a p s) := (h_det_as_prod.and h_prod_eq_exp).mono
        (by intro s hs; simpa [hs.1] using hs.2)
  -- Conclude AnalyticAt for det2_AF via equality with an analytic function on a neighborhood
  have h_analytic_sum : AnalyticAt ℂ (fun s => ∑' (p : Prime), a p s) s0 := by
    -- Each `p` term is analytic near s0 and the family is locally summable.
    refine AnalyticAt.tsum (fun p => ?_) ?_
    · -- analyticity of s ↦ a p s at s0
      -- Set λ = p^{-s}; this is entire since p ≠ 0 and λ = exp((-s) * log p)
      have hpne : (p.1 : ℂ) ≠ 0 := by
        exact_mod_cast (by exact ne_of_gt (Nat.Prime.pos p.property))
      have hlam : AnalyticAt ℂ (fun s => (p.1 : ℂ) ^ (-s)) s0 := by
        -- exp ∘ linear map s ↦ (-s) * log(p)
        have hlin : AnalyticAt ℂ (fun s : ℂ => -s) s0 := (analyticAt_id.neg)
        have hmul : AnalyticAt ℂ (fun s => (-s) * Complex.log (p.1 : ℂ)) s0 := hlin.mul_const _
        have : AnalyticAt ℂ (fun s => Complex.exp ((-s) * Complex.log (p.1 : ℂ))) s0 :=
          Complex.analyticAt_exp.comp s0 hmul
        -- identify with cpow for a ≠ 0
        refine this.congr ?hcongr
        intro s; simpa [Complex.cpow_eq_exp_log, hpne] using rfl
      -- now combine: log(1 - λ) analytic as λ(s0) ≠ 1
      have hlam_norm : ‖(p.1 : ℂ) ^ (-s0)‖ < 1 := by
        -- since Re(s0) > 0 and p ≥ 2
        have hp_pos : 0 < (p.1 : ℝ) := by exact_mod_cast (Nat.Prime.pos p.property)
        have : ‖(p.1 : ℂ) ^ (-s0)‖ = (p.1 : ℝ) ^ (-s0.re) := by
          simpa [Complex.norm_eq_abs] using (Complex.abs_cpow_eq_rpow_re_of_pos hp_pos (-s0))
        have hp_gt_one : (1 : ℝ) < (p.1 : ℝ) := by
          have : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.property.two_le
          exact lt_of_lt_of_le (by norm_num) this
        have : (p.1 : ℝ) ^ (-s0.re) < 1 := by
          have hlogpos : 0 < Real.log (p.1 : ℝ) := by simpa using Real.log_pos hp_gt_one
          have hxneg : -s0.re < 0 := by linarith [hs0]
          have : Real.exp ((-s0.re) * Real.log (p.1 : ℝ)) < Real.exp 0 :=
            Real.exp_lt_exp.mpr (mul_neg_of_neg_of_pos hxneg hlogpos)
          simpa [Real.rpow_def_of_pos hp_pos, Real.exp_zero] using this
        simpa [this] using this
      have hne : 1 - (p.1 : ℂ) ^ (-s0) ≠ 0 := by
        intro h; have : (p.1 : ℂ) ^ (-s0) = 1 := sub_eq_zero.mp h |>.symm
        have : ‖(p.1 : ℂ) ^ (-s0)‖ = 1 := by simpa [this]
        exact (ne_of_lt hlam_norm) this
      have hlog : AnalyticAt ℂ (fun s => Complex.log (1 - (p.1 : ℂ) ^ (-s))) s0 :=
        Complex.analyticAt_log.comp s0 ((analyticAt_const.sub hlam))
      -- assemble a p s
      simpa [a] using (hlog.add (hlam.add ((hlam.pow 2).mul_const (1 / 2 : ℂ))))
    · -- local summability of the family of norms
      exact h_norm_conv
  have : AnalyticAt ℂ (fun s => Complex.exp (∑' (p : Prime), a p s)) s0 :=
    Complex.analyticAt_exp.comp s0 h_analytic_sum
  exact (AnalyticAt.congr_of_eventuallyEq this h_eq_exp)

/-- Nonvanishing of the 2‑modified determinant on the half‑plane Re(s) > 1/2. -/
theorem det2_AF_nonzero_on_halfPlaneReGtHalf :
  ∀ {s : ℂ}, s ∈ {s : ℂ | (1 / 2 : ℝ) < s.re} → det2_AF s ≠ 0 := by
  classical
  intro s hs
  -- Fix 1/2 < σ < Re(s)
  obtain ⟨σ, hσhalf, hσ⟩ : ∃ σ, (1/2 : ℝ) < σ ∧ σ < s.re := by
    refine ⟨(s.re + 1/2)/2, ?_, ?_⟩ <;> linarith
  -- Define a_p in additive form at this fixed s
  let a : Prime → ℂ := fun p =>
    let lam := (p.1 : ℂ) ^ (-s)
    Complex.log (1 - lam) + lam + lam ^ 2 / 2
  -- Summability of a by quadratic-tail domination with σ ∈ (1/2, Re(s)]
  have hsum_a : Summable a := by
    obtain ⟨σ, hσhalf, hσ⟩ : ∃ σ, (1/2 : ℝ) < σ ∧ σ ≤ s.re := by
      refine ⟨(s.re + 1/2)/2, ?_, ?_⟩ <;> linarith
    -- Summability of ∑ p^{-2σ}
    have hsum : Summable (fun p : Prime => (p.1 : ℝ) ^ (-(2 : ℝ) * σ)) := by
      have : 1 < (2 : ℝ) * σ := by linarith
      simpa using AcademicRH.EulerProduct.real_prime_rpow_summable (r := (2 : ℝ) * σ) this
    -- Pointwise bound via additive lemma
    let Cσ : ℝ := ((1 - (2 : ℝ) ^ (-σ))⁻¹) / 2 + (1 / 2 : ℝ)
    have hbound : ∀ p : Prime, ‖a p‖ ≤ Cσ * (p.1 : ℝ) ^ (-(2 : ℝ) * σ) := by
      intro p
      have := log_remainder_additive_bound_of_Re_ge_sigma (s := s) hσhalf hσ p
      simpa [a, Cσ] using this
    have hnorm_sum : Summable (fun p : Prime => ‖a p‖) :=
      summable_of_nonneg_of_le (by intro p; exact norm_nonneg _) hbound ((hsum.mul_left Cσ))
    exact Summable.of_norm hnorm_sum
  -- Product equals exp(tsum) ⇒ exp(tsum) ≠ 0
  have hprod := (tprod_exp_of_summable (a := fun p : Prime => a p) hsum_a).2
  -- Identify det2 as the product of exponentials
  have hId : det2_AF s = ∏' (p : Prime), Complex.exp (a p) := by
    simp [det2_AF, det2EulerFactor, a, eulerFactor_as_exp_log]
  -- Conclude nonvanishing
  have : det2_AF s = Complex.exp (∑' (p : Prime), a p) := by simpa [hId] using hprod
  simpa [this] using Complex.exp_ne_zero _

/-- Nonvanishing of det₂ on the critical line Re(s) = 1/2. -/
theorem det2_AF_nonzero_on_critical_line :
  ∀ t : ℝ, det2_AF ((1 / 2 : ℝ) + Complex.I * (t : ℂ)) ≠ 0 := by
  classical
  intro t
  set s : ℂ := (1 / 2 : ℝ) + Complex.I * (t : ℂ)
  let a : Prime → ℂ := fun p =>
    let lam := (p.1 : ℂ) ^ (-s)
    Complex.log (1 - lam) + lam + lam ^ 2 / 2
  -- Summability using 3σ with σ = 1/2 ⇒ 3/2 > 1
  have hsum_tail : Summable (fun p : Prime => (p.1 : ℝ) ^ (-(3 : ℝ) / 2)) := by
    simpa using AcademicRH.EulerProduct.real_prime_rpow_summable (r := (3 : ℝ) / 2) (by norm_num)
  have hsum_a : Summable a := by
    -- Use cubic-tail inequality: ‖log(1 − λ)+λ+λ^2/2‖ ≤ ‖λ‖^3/(1−‖λ‖), with ‖λ‖=p^{-1/2}
    -- Hence ‖a p‖ ≤ C · p^{-3/2} with C = (1 - 2^{-1/2})^{-1}.
    let C : ℝ := (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹
    have hbound : ∀ p : Prime, ‖a p‖ ≤ C * (p.1 : ℝ) ^ (-(3 : ℝ) / 2) := by
      intro p
      set lam : ℂ := (p.1 : ℂ) ^ (-s)
      have hlam_norm : ‖lam‖ = (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
        have hp_pos : 0 < (p.1 : ℝ) := by exact_mod_cast (Nat.Prime.pos p.property)
        have : s.re = (1 / 2 : ℝ) := by simp [s]
        simpa [lam, this, Complex.norm_eq_abs]
          using (Complex.abs_cpow_eq_rpow_re_of_pos hp_pos (-s))
      have hlam_le_two : ‖lam‖ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
        have : (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
          have : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.property.two_le
          -- (1/p)^{1/2} ≤ (1/2)^{1/2}
          have : 1 / (p.1 : ℝ) ≤ 1 / (2 : ℝ) := one_div_le_one_div_of_le (by exact_mod_cast (Nat.Prime.pos p.property).le) this
          have := Real.rpow_le_rpow_of_nonneg this (by norm_num) (by norm_num : 0 ≤ (1 / 2 : ℝ))
          simpa [Real.rpow_neg, inv_eq_one_div] using this
        simpa [hlam_norm] using this
      have hlam_lt_one : ‖lam‖ < (1 : ℝ) := lt_of_le_of_lt hlam_le_two (by
        -- (2)^{-1/2} < 1
        have : 0 < (1 / (2 : ℝ)) := by norm_num
        have : (1 / (2 : ℝ)) ^ (1 / 2 : ℝ) < 1 := by
          have : 0 < (1 / (2 : ℝ)) ∧ (1 / (2 : ℝ)) < 1 := by constructor <;> norm_num
          exact Real.rpow_lt_one_of_one_lt_of_pos (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2) (by norm_num)
        simpa [Real.rpow_neg, inv_eq_one_div] using this)
      -- cubic tail inequality from Weierstrass product helpers
      have htail : ‖Complex.log (1 - lam) + lam + lam ^ 2 / 2‖ ≤ ‖lam‖ ^ 3 / (1 - ‖lam‖) :=
        RH.AcademicFramework.DiagonalFredholm.log_one_sub_plus_z_plus_sq_cubic_tail (z := lam) (by simpa using hlam_lt_one)
      -- replace denominator, and ‖lam‖^3 = p^{-3/2}
      have : (1 - ‖lam‖)⁻¹ ≤ C := by
        have : ‖lam‖ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := hlam_le_two
        have : 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 - ‖lam‖ := by linarith
        have hpos : 0 < 1 - ‖lam‖ := sub_pos.mpr hlam_lt_one
        exact inv_le_inv_of_le (le_of_lt hpos) this
      have : ‖a p‖ ≤ C * (p.1 : ℝ) ^ (-(3 : ℝ) / 2) := by
        have hpow : ‖lam‖ ^ 3 = (p.1 : ℝ) ^ (-(3 : ℝ) / 2) := by
          simpa [hlam_norm, Real.rpow_mul, mul_comm]
        have := le_trans htail (by
          have hnonneg : 0 ≤ ‖lam‖ ^ 3 := by nlinarith
          exact (mul_le_mul_of_nonneg_left this hnonneg))
        simpa [a, lam, hpow, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, C] using this
      simpa using this
    have hnorm_sum : Summable (fun p : Prime => ‖a p‖) :=
      summable_of_nonneg_of_le (by intro p; exact norm_nonneg _) hbound ((hsum_tail.mul_left C))
    exact Summable.of_norm hnorm_sum
  have hprod := (tprod_exp_of_summable (a := fun p : Prime => a p) hsum_a).2
  have hId : det2_AF s = ∏' (p : Prime), Complex.exp (a p) := by
    simp [det2_AF, det2EulerFactor, a, eulerFactor_as_exp_log]
  have : det2_AF s = Complex.exp (∑' (p : Prime), a p) := by simpa [hId] using hprod
  simpa [s, this] using Complex.exp_ne_zero _

end RH.AcademicFramework.DiagonalFredholm
