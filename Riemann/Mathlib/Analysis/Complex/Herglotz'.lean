/-

! This file is part of a PR series towards a generalized Carathéodory–Fejér /
! Herglotz representation theorem, as used e.g. in
! * Connes–van Suijlekom, *Quadratic forms, real zeros and echoes of the spectral action*,
!   especially Theorem 3.1 (continuous Carathéodory–Fejér corollary). :contentReference[oaicite:1]{index=1}
! * Connes–Consani–Moscovici, *Zeta spectral triples*, Section 5 (Herglotz-type
!   integral representations for operator-theoretic models of ζ). :contentReference[oaicite:2]{index=2}
!
! The goal of this file is to develop the analytic core of the Herglotz
! representation: the Cayley transform and its rotated variants (the Herglotz
! kernel) map the open unit disc into the open right half-plane.
!
! In later PRs this will be combined with measure-theoretic arguments to obtain
! the full Herglotz representation theorem for analytic functions with positive
! real part on the unit disc.

-/

import Mathlib

open scoped Complex
open Complex

namespace Herglotz

/-! # Basic geometric sets -/

/-- The (open) unit disc in `ℂ`. This is `Metric.ball 0 1` but we give it a
    dedicated name for readability in the Herglotz context. -/
def unitDisc : Set ℂ := {z : ℂ | ‖z‖ < 1}

/-- The unit circle in `ℂ` as a subset. This is `Metric.sphere 0 1`. -/
def unitCircle : Set ℂ := {w : ℂ | ‖w‖ = 1}

notation "𝔻" => unitDisc
notation "𝕊" => unitCircle

lemma mem_unitCircle_iff {w : ℂ} : w ∈ 𝕊 ↔ ‖w‖ = 1 := Iff.rfl

lemma mem_unitDisc_iff {z : ℂ} : z ∈ 𝔻 ↔ ‖z‖ < 1 := Iff.rfl

/-! # Cayley transform -/

/-- The Cayley transform `C(z) = (1 + z)/(1 - z)`.
    It is a biholomorphism between the unit disc and the right half-plane. -/
def cayley (z : ℂ) : ℂ := (1 + z) / (1 - z)

@[simp] lemma cayley_apply (z : ℂ) :
    cayley z = (1 + z) / (1 - z) := rfl

/-- Domain of analyticity of the Cayley transform: `z ≠ 1`. -/
lemma cayley_analyticOn :
    AnalyticOn ℂ cayley {z : ℂ | z ≠ (1 : ℂ)} := by
  -- `cayley z = (1 + z) * (1 - z)⁻¹`, so this is a quotient of analytic
  -- functions with nonvanishing denominator.
  have h₁ : AnalyticOn ℂ (fun z => (1 : ℂ) + z) {z : ℂ | z ≠ (1 : ℂ)} :=
    (analyticOn_const.add analyticOn_id)
  have h₂ : AnalyticOn ℂ (fun z => (1 : ℂ) - z) {z : ℂ | z ≠ (1 : ℂ)} :=
    (analyticOn_const.sub analyticOn_id)
  have hne : ∀ z ∈ {z : ℂ | z ≠ (1 : ℂ)}, (1 : ℂ) - z ≠ 0 := by
    intro z hz
    have hz' : z ≠ (1 : ℂ) := hz
    have : (1 : ℂ) - z = 0 ↔ z = 1 := sub_eq_zero.trans eq_comm
    exact (this.not).mpr hz'
  -- Use the standard `AnalyticOn.div` lemma.
  simpa [cayley] using h₁.div h₂ hne

/-! ## Real part of the Cayley transform

The key estimate is that the Cayley transform maps the unit disc into the
(open) right half-plane. We first compute an explicit formula for its real
part, and then show that it is positive on `𝔻`.
-/

/-- Auxiliary lemma: the numerator appearing in the real part of the Cayley
transform simplifies to `1 - ‖z‖²`.

Concretely, if we multiply numerator and denominator by `conj (1 - z)`, we
obtain
`(1 + z) * conj (1 - z) = 1 - ‖z‖² + i * (something)`,
so the real part is `1 - ‖z‖²`. -/
lemma realPart_cayley_numer (z : ℂ) :
    Complex.realPart ((1 + z) * conj (1 - z)) = 1 - ‖z‖^2 := by
  -- Expand `conj (1 - z) = 1 - conj z`.
  have hconj : conj (1 - z) = (1 : ℂ) - conj z := by
    simp [sub_eq_add_neg, map_add, map_neg]
  -- Expand the product `(1 + z) * (1 - conj z)`.
  -- `(1 + z) * (1 - conj z) = (1 + z) - (1 + z) * conj z`.
  have hprod :
      (1 + z) * conj (1 - z) =
        (1 : ℂ) + z - ((1 : ℂ) + z) * conj z := by
    simp [hconj, mul_add, add_mul, sub_eq_add_neg, add_comm, add_left_comm,
          add_assoc, mul_comm, mul_left_comm, mul_assoc]
  -- Take real parts.
  have := congrArg Complex.realPart hprod
  -- Now simplify term-by-term.
  -- We will use:
  -- * `realPart_add`, `realPart_sub`, `realPart_mul`
  -- * `realPart_one`, `realPart_conj`, and
  -- * `realPart (z * conj z) = ‖z‖^2`.
  -- First rewrite the RHS.
  have h₁ :
      Complex.realPart
        ((1 : ℂ) + z - ((1 : ℂ) + z) * conj z)
        = Complex.realPart ((1 : ℂ) + z)
          - Complex.realPart (((1 : ℂ) + z) * conj z) := by
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      Complex.realPart_add, Complex.realPart_neg]  -- we get a `a - b` form
  -- Combine.
  have h := by
    simpa [h₁] using this
  clear this h₁ hprod
  -- Now compute the two pieces separately.
  have hA : Complex.realPart ((1 : ℂ) + z) = 1 + Complex.realPart z := by
    simp [Complex.realPart_add]
  -- For the second piece we use
  -- `((1 : ℂ) + z) * conj z = conj z + z * conj z`.
  have hmul :
      ((1 : ℂ) + z) * conj z = conj z + z * conj z := by
    simp [add_mul, mul_comm, mul_left_comm, mul_assoc]
  have hB :
      Complex.realPart (((1 : ℂ) + z) * conj z)
        = Complex.realPart z + ‖z‖^2 := by
    -- realPart (conj z) = realPart z, and realPart (z * conj z) = ‖z‖^2.
    have :
        Complex.realPart (((1 : ℂ) + z) * conj z)
          = Complex.realPart (conj z + z * conj z) := by
      simpa [hmul]
    -- Use `realPart_add` and the standard lemmas.
    have hconj' : Complex.realPart (conj z) = Complex.realPart z := by
      simpa using Complex.realPart_conj z
    have hzz :
        Complex.realPart (z * conj z) = ‖z‖^2 := by
      -- Standard identity: `z * conj z = (‖z‖^2 : ℝ)` as a real.
      -- The API lemma is `mul_conj` + `abs_sq`:
      -- `z * conj z = (‖z‖^2 : ℝ)` in `ℂ`.
      have h' : z * conj z = (‖z‖^2 : ℝ) := by
        -- `‖z‖^2` is real, so we coerce it into `ℂ`.
        -- Mathlib lemma: `mul_conj` plus `abs_sq` in the form
        -- `by simpa [Complex.abs, Complex.sq]` etc.
        -- We do not reprove that here; we use it as an API lemma:
        simpa using Complex.mul_conj_abs_sq z
      simpa [h']  -- realPart of a real is itself
    -- Put these together.
    have := congrArg Complex.realPart this
    simpa [Complex.realPart_add, hconj', hzz] using this
  -- Now combine `hA` and `hB` inside `h`.
  -- We want: `h = 1 - ‖z‖^2`.
  -- From above, `h = (1 + Re z) - (Re z + ‖z‖^2)`.
  simpa [hA, hB, add_comm, add_left_comm, add_assoc, sub_eq_add_neg,
    add_left_neg, add_comm, add_left_comm, add_assoc] using h

/-- Exact formula for the real part of the Cayley transform. -/
lemma realPart_cayley (z : ℂ) (hz : z ≠ 1) :
    Complex.realPart (cayley z)
      = (1 - ‖z‖^2) / ‖1 - z‖^2 := by
  -- Rewrite `cayley` and use the standard formula
  -- `z / w = z * conj w / ‖w‖^2`.
  have hden_ne : (1 : ℂ) - z ≠ 0 := by
    have : (1 : ℂ) - z = 0 ↔ z = 1 := sub_eq_zero.trans eq_comm
    exact (this.not).mpr hz
  have hdiv :
      cayley z
        = (1 + z) * conj (1 - z) / (‖1 - z‖^2 : ℝ) := by
    -- API lemma: `(a / b) = a * conj b / ‖b‖^2` for `b ≠ 0`.
    -- We use it with `a = 1 + z`, `b = 1 - z`.
    have := Complex.div_eq_mul_conj_absSq (a := 1 + z) (b := 1 - z) hden_ne
    simpa [cayley] using this
  -- Take real parts.
  have := congrArg Complex.realPart hdiv
  -- The denominator is real; pull it out of the real part:
  -- `Re (num / r) = Re num / r` for real `r`.
  have hreal :
      Complex.realPart ((1 + z) * conj (1 - z) / (‖1 - z‖^2 : ℝ))
        = Complex.realPart ((1 + z) * conj (1 - z)) / (‖1 - z‖^2) := by
    -- API lemma: `realPart_div_real` (or obtained from
    -- `realPart_mul` + `realPart_inv` when denominator is real).
    simpa using Complex.realPart_div_real
      (z := (1 + z) * conj (1 - z)) (r := ‖1 - z‖^2)
  -- Put everything together.
  have := by
    simpa [hreal] using this
  -- Now use the numerator computation.
  simpa [realPart_cayley_numer, div_eq_mul_inv] using this

/-- On the unit disc the real part of the Cayley transform is strictly
positive. -/
lemma realPart_cayley_pos {z : ℂ} (hz : z ∈ 𝔻) :
    0 < Complex.realPart (cayley z) := by
  have hz' : ‖z‖ < 1 := mem_unitDisc_iff.mp hz
  have hz_ne : z ≠ 1 := by
    -- If `z = 1` then `‖z‖ = 1`, contradicting `‖z‖ < 1`.
    intro h
    have : ‖z‖ = 1 := by simpa [h] using norm_one
    exact (not_lt_of_ge (by simpa [this] using le_of_eq this)) hz'
  -- Use the explicit formula from `realPart_cayley`.
  have hformula := realPart_cayley z hz_ne
  -- Rewrite in terms of real inequalities.
  have hnum_nonneg : 0 ≤ 1 - ‖z‖^2 := by
    -- From `‖z‖ < 1` we get `‖z‖ ≤ 1`, hence `‖z‖^2 ≤ 1`.
    have hz_le : ‖z‖ ≤ 1 := le_of_lt hz'
    have hz_sq_le : ‖z‖^2 ≤ (1 : ℝ)^2 := pow_two_le_pow_two hz_le
    have hz_sq_le' : ‖z‖^2 ≤ 1 := by simpa using hz_sq_le
    exact sub_nonneg.mpr hz_sq_le'
  have hnum_pos : 0 < 1 - ‖z‖^2 := by
    -- In fact it is strictly positive since `‖z‖ < 1`.
    have hz_sq_lt : ‖z‖^2 < (1 : ℝ)^2 := pow_two_lt_pow_two hz'
    have hz_sq_lt' : ‖z‖^2 < 1 := by simpa using hz_sq_lt
    exact sub_pos.mpr hz_sq_lt'
  have hden_pos : 0 < ‖1 - z‖^2 := by
    have hden_ne : ‖1 - z‖ ≠ 0 := by
      -- `‖1 - z‖ = 0` iff `z = 1`, already excluded.
      have : ‖1 - z‖ = 0 ↔ 1 - z = 0 := by
        simpa using (norm_eq_zero)
      have hz' : 1 - z ≠ 0 := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          sub_ne_zero.mpr hz_ne.symm
      exact fun h => hz' ((this.mp h))
    have : (0 : ℝ) < ‖1 - z‖ := pos_of_ne_zero hden_ne
    exact pow_two_pos_of_ne_zero _ hden_ne
  -- Now use the formula.
  have := congrArg (fun x => (0 : ℝ) < x) hformula
  -- Instead of rewriting through `congrArg`, we just work directly:
  have : Complex.realPart (cayley z)
      = (1 - ‖z‖^2) / ‖1 - z‖^2 := hformula
  -- Conclude using `div_pos`.
  simpa [this] using div_pos hnum_pos hden_pos

/-! # Herglotz kernel

We now rotate the Cayley transform by a point `w` on the unit circle and show
that the resulting Herglotz kernel still has positive real part on the unit
disc.
-/

/-- The Herglotz kernel associated to a point `w` on the unit circle.

Mathematically: `K(z,w) = (w + z)/(w - z)`. We do *not* enforce here that
`‖w‖ = 1` or that `‖z‖ < 1`; these are hypotheses of the theorems below. -/
def herglotzKernel (z w : ℂ) : ℂ := (w + z) / (w - z)

@[simp] lemma herglotzKernel_apply (z w : ℂ) :
    herglotzKernel z w = (w + z) / (w - z) := rfl

/-- For `‖w‖ = 1` the Herglotz kernel at `w` is obtained from the Cayley
transform by a rotation of the disc: `K(z,w) = C(conj w * z)`.

This expresses the fact that automorphisms of the unit disc are generated by
rotations and the Cayley transform. -/
lemma herglotzKernel_eq_cayley (z w : ℂ) (hw : w ∈ 𝕊) :
    herglotzKernel z w = cayley (conj w * z) := by
  rcases mem_unitCircle_iff.mp hw with hw_norm
  -- Use the identity `conj w * w = ‖w‖^2 = 1`.
  have hconj_mul : conj w * w = (1 : ℂ) := by
    -- API lemma: `conj_mul_self : conj w * w = (‖w‖^2 : ℝ)`.
    have := Complex.conj_mul_self w
    -- `‖w‖ = 1`, so `‖w‖^2 = 1`.
    have hw_sq : ‖w‖^2 = (1 : ℝ) := by
      simpa [hw_norm, one_pow] using congrArg (fun t => t^2) hw_norm
    -- Coerce to `ℂ`.
    simpa [hw_sq] using this
  -- Expand both sides and simplify using `hconj_mul`.
  unfold herglotzKernel cayley
  -- `(1 + conj w * z) * w = w + z * (conj w * w) = w + z`.
  -- `(1 - conj w * z) * w = w - z * (conj w * w) = w - z`.
  have hnum :
      (1 + conj w * z) * w = w + z := by
    calc
      (1 + conj w * z) * w
          = w + (conj w * z) * w := by
            simp [add_mul, mul_comm, mul_left_comm, mul_assoc]
      _ = w + z * (conj w * w) := by
            simp [mul_comm, mul_left_comm, mul_assoc]
      _ = w + z := by
            simpa [hconj_mul, mul_one]
  have hden :
      (1 - conj w * z) * w = w - z := by
    calc
      (1 - conj w * z) * w
          = w - (conj w * z) * w := by
            simp [sub_eq_add_neg, add_mul, mul_add, mul_comm, mul_left_comm,
              mul_assoc]
      _ = w - z * (conj w * w) := by
            simp [mul_comm, mul_left_comm, mul_assoc]
      _ = w - z := by
            simpa [hconj_mul, mul_one]
  -- Now `C(conj w * z) = (1 + conj w * z)/(1 - conj w * z)`; multiply numerator
  -- and denominator by `w`.
  have hw_ne : (w : ℂ) ≠ 0 := by
    -- From `‖w‖ = 1` we get `w ≠ 0`.
    intro h
    have : ‖w‖ = 0 := by simpa [h] using norm_zero
    have : (1 : ℝ) = 0 := by simpa [hw_norm] using this.symm
    exact one_ne_zero this
  have hw_inv : (w : ℂ) ≠ 0 := hw_ne
  -- Use `(a / b) = (a * w) / (b * w)` when `w ≠ 0`.
  have hfrac :
      (1 + conj w * z) / (1 - conj w * z)
        = ((1 + conj w * z) * w) / ((1 - conj w * z) * w) := by
    field_simp [div_eq_mul_inv, hw_inv, mul_comm, mul_left_comm, mul_assoc]
  -- Now substitute the simplifications for numerator and denominator.
  simpa [hfrac, hnum, hden]  -- RHS is `(w+z)/(w-z)` which is `herglotzKernel`.

/-- For `‖w‖ = 1` and `‖z‖ < 1`, the real part of the Herglotz kernel is
strictly positive. This is the key estimate needed in the Herglotz integral
representation. -/
lemma realPart_herglotzKernel_pos {z w : ℂ}
    (hz : z ∈ 𝔻) (hw : w ∈ 𝕊) :
    0 < Complex.realPart (herglotzKernel z w) := by
  -- Express the kernel via the Cayley transform of a rotated point.
  have h_eq := herglotzKernel_eq_cayley z w hw
  -- The rotation is isometric, so `‖conj w * z‖ = ‖z‖`.
  have hnorm :
      ‖conj w * z‖ = ‖z‖ := by
    have : ‖conj w‖ = ‖w‖ := by simpa using Complex.norm_conj w
    have hw_norm : ‖w‖ = 1 := (mem_unitCircle_iff.mp hw)
    calc
      ‖conj w * z‖ = ‖conj w‖ * ‖z‖ := norm_mul _ _
      _ = ‖w‖ * ‖z‖ := by simpa [this]
      _ = ‖z‖ := by simpa [hw_norm] using congrArg (fun t => t * ‖z‖) hw_norm
  have hz' : conj w * z ∈ 𝔻 := by
    -- Use `hnorm` to transfer `‖z‖ < 1`.
    have hz_norm : ‖z‖ < 1 := mem_unitDisc_iff.mp hz
    simpa [unitDisc, hnorm] using hz_norm
  -- Now apply the positivity of the Cayley transform on the disc.
  simpa [h_eq] using realPart_cayley_pos (z := conj w * z) hz'

end Herglotz
