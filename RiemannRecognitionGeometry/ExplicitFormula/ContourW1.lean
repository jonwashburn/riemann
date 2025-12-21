import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Topology.Separation.Hausdorff
import RiemannRecognitionGeometry.ExplicitFormula.Defs

/-!
# Route 3: a contour-integral *definition template* for `W¹`

This file introduces a small amount of infrastructure for defining a Lagarias/Weil
`W¹` functional via a **rectangular contour integral** (argument-principle style).

It is intentionally lightweight: we only define the contour integral over the boundary
of a rectangle as a combination of `intervalIntegral`s (following
`Mathlib.Analysis.Complex.CauchyIntegral`), and then define a truncated `W¹_{c,T}` for an
abstract `TestSpace` Mellin transform `M[f](s)`.

The hard analytic facts (residue theorem / symmetric zero-sum identification, existence
of the `T → ∞` limit, cancellation bookkeeping) are *not* proved here; this file exists so
later work can state those obligations against a concrete, standard definition.
-/

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open Complex MeasureTheory
open scoped Interval

namespace ContourW1

/-!
## Rectangle boundary integral

We follow Mathlib’s convention: for opposite corners `z,w : ℂ` with `z.re ≤ w.re` and `z.im ≤ w.im`,
the (counterclockwise) boundary integral is represented by:

`bottom - top + right - left`,

where the vertical edges come with an extra factor of `I` from `ds = I·dt`.
-/

/-- The constant \(2\pi i\) as a complex number. -/
def twoPiI : ℂ := ((2 * Real.pi : ℂ) * I)

/-- Boundary integral of `F : ℂ → ℂ` over the rectangle with opposite corners `z,w`. -/
def boundaryRectIntegral (F : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, F (x + z.im * I)) -
    (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) +
      I * (∫ y : ℝ in z.im..w.im, F (w.re + y * I)) -
        I * (∫ y : ℝ in z.im..w.im, F (z.re + y * I))

/-!
## Standard Route‑3 rectangle

For explicit-formula contours, one typically integrates over the rectangle with vertical lines
`Re(s)=1-c` and `Re(s)=c`, and horizontal lines `Im(s)=±T`.
-/

/-- Bottom-left corner of the standard explicit-formula rectangle. -/
def rectZ (c T : ℝ) : ℂ :=
  ((1 - c : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I

/-- Top-right corner of the standard explicit-formula rectangle. -/
def rectW (c T : ℝ) : ℂ :=
  (c : ℂ) + (T : ℂ) * I

/-- Real part of `rectZ`. -/
@[simp] lemma rectZ_re (c T : ℝ) : (rectZ c T).re = 1 - c := by
  simp [rectZ]

/-- Imaginary part of `rectZ`. -/
@[simp] lemma rectZ_im (c T : ℝ) : (rectZ c T).im = -T := by
  simp [rectZ]

/-- Real part of `rectW`. -/
@[simp] lemma rectW_re (c T : ℝ) : (rectW c T).re = c := by
  simp [rectW]

/-- Imaginary part of `rectW`. -/
@[simp] lemma rectW_im (c T : ℝ) : (rectW c T).im = T := by
  simp [rectW]

/-- Expand the rectangle boundary integral for the standard explicit-formula rectangle. -/
lemma boundaryRectIntegral_rectZ_rectW (F : ℂ → ℂ) (c T : ℝ) :
    boundaryRectIntegral F (rectZ c T) (rectW c T) =
      (∫ x : ℝ in (1 - c)..c, F (x + (-T) * I)) -
        (∫ x : ℝ in (1 - c)..c, F (x + (T) * I)) +
          I * (∫ y : ℝ in (-T)..T, F (c + y * I)) -
            I * (∫ y : ℝ in (-T)..T, F ((1 - c) + y * I)) := by
  simp [boundaryRectIntegral, rectZ, rectW, add_comm, mul_comm]

/-!
### Named edge integrals for the standard rectangle
-/

/-- Bottom horizontal edge integral (Im = -T). -/
def horizBottom (F : ℂ → ℂ) (c T : ℝ) : ℂ :=
  ∫ x : ℝ in (1 - c)..c, F (x + (-T) * I)

/-- Top horizontal edge integral (Im = +T). -/
def horizTop (F : ℂ → ℂ) (c T : ℝ) : ℂ :=
  ∫ x : ℝ in (1 - c)..c, F (x + (T) * I)

/-- Right vertical edge integral (Re = c). -/
def vertRight (F : ℂ → ℂ) (c T : ℝ) : ℂ :=
  I * ∫ y : ℝ in (-T)..T, F (c + y * I)

/-- Left vertical edge integral (Re = 1-c). -/
def vertLeft (F : ℂ → ℂ) (c T : ℝ) : ℂ :=
  I * ∫ y : ℝ in (-T)..T, F ((1 - c) + y * I)

/-- The vertical-edge difference (right minus left). -/
def vertDiff (F : ℂ → ℂ) (c T : ℝ) : ℂ :=
  vertRight F c T - vertLeft F c T

lemma boundaryRectIntegral_eq_edges (F : ℂ → ℂ) (c T : ℝ) :
    boundaryRectIntegral F (rectZ c T) (rectW c T) =
      horizBottom F c T - horizTop F c T + vertDiff F c T := by
  simp [boundaryRectIntegral_rectZ_rectW, horizBottom, horizTop, vertRight, vertLeft, vertDiff,
    sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-!
### Functional-equation rewrite on the left vertical edge

This is the algebraic heart of the standard explicit-formula contour manipulation: the left edge
(`Re = 1-c`) can be rewritten in terms of the right edge (`Re = c`) using:
- the Mellin involution identity `M[˜ₘ f](s) = M[f](1-s)`, and
- the functional equation `xi(1-s)=xi(s)` (which gives `logDeriv xi (1-s) = - logDeriv xi s` away
  from zeros).

We keep the hypotheses explicit so later work can plug in `xiLagarias` and prove the required
regularity/nonvanishing conditions.
-/

/--
Rewrite the left vertical edge integral in terms of the right edge, assuming:
- `M[f](1-c+it) = M[˜ₘ f](c-it)`, and
- `logDeriv xi(1-c+it) = - logDeriv xi(c-it)`,
then using the substitution `t ↦ -t` on the interval integral.
-/
theorem vertLeft_eq_neg_vertRight_tilde
    {F : Type} [TestSpace F]
    (xi : ℂ → ℂ) (f : F) (c T : ℝ)
    (hM : ∀ t : ℝ, M[f](((1 - c : ℝ) : ℂ) + (t : ℂ) * I) =
      M[(TestSpace.tilde (F := F) f)]((c : ℂ) + ((-t : ℝ) : ℂ) * I))
    (hLog : ∀ t : ℝ, logDeriv xi (((1 - c : ℝ) : ℂ) + (t : ℂ) * I) =
      - logDeriv xi ((c : ℂ) + ((-t : ℝ) : ℂ) * I)) :
    vertLeft (fun s : ℂ => M[f](s) * logDeriv xi s) c T =
      - vertRight (fun s : ℂ => M[(TestSpace.tilde (F := F) f)](s) * logDeriv xi s) c T := by
  -- Define `g(t) := M[˜f](c+it) * logDeriv xi(c+it)`.
  let g : ℝ → ℂ := fun t =>
    M[(TestSpace.tilde (F := F) f)]((c : ℂ) + (t : ℂ) * I) * logDeriv xi ((c : ℂ) + (t : ℂ) * I)
  -- Expand the vertical-edge definitions and rewrite the left integrand using `hM` and `hLog`.
  -- Then use `intervalIntegral.integral_comp_neg` to replace `∫ g(-t)` with `∫ g(t)`.
  --
  -- The calculation is entirely formal: it is just substitution + ring algebra.
  have ha : (∫ t : ℝ in (-T)..T,
      M[f](((1 - c : ℝ) : ℂ) + (t : ℂ) * I) * logDeriv xi (((1 - c : ℝ) : ℂ) + (t : ℂ) * I)) =
        - ∫ t : ℝ in (-T)..T, g t := by
    -- rewrite the integrand pointwise to `-(g (-t))`, then use symmetry to remove `(-t)`
    have h1 :
        (∫ t : ℝ in (-T)..T,
          M[f](((1 - c : ℝ) : ℂ) + (t : ℂ) * I) * logDeriv xi (((1 - c : ℝ) : ℂ) + (t : ℂ) * I)) =
            - ∫ t : ℝ in (-T)..T, g (-t) := by
      -- `simp` sees `hM`/`hLog` after `funext`-style rewriting
      -- (we keep it explicit to avoid any accidental commutations).
      have : (fun t : ℝ =>
          M[f](((1 - c : ℝ) : ℂ) + (t : ℂ) * I) * logDeriv xi (((1 - c : ℝ) : ℂ) + (t : ℂ) * I)) =
            fun t : ℝ => - g (-t) := by
        ext t
        -- rewrite using the hypotheses
        calc
          M[f](((1 - c : ℝ) : ℂ) + (t : ℂ) * I) * logDeriv xi (((1 - c : ℝ) : ℂ) + (t : ℂ) * I)
              = M[(TestSpace.tilde (F := F) f)]((c : ℂ) + ((-t : ℝ) : ℂ) * I) *
                  (- logDeriv xi ((c : ℂ) + ((-t : ℝ) : ℂ) * I)) := by
                    -- Apply `hM` to the Mellin factor and `hLog` to the log-derivative factor.
                    -- Then just reassociate.
                        calc
                          M[f](((1 - c : ℝ) : ℂ) + (t : ℂ) * I) * logDeriv xi (((1 - c : ℝ) : ℂ) + (t : ℂ) * I)
                              = M[(TestSpace.tilde (F := F) f)]((c : ℂ) + ((-t : ℝ) : ℂ) * I) *
                                  logDeriv xi (((1 - c : ℝ) : ℂ) + (t : ℂ) * I) := by
                                -- rewrite the Mellin factor
                                simpa [mul_assoc] using congrArg (fun z => z * logDeriv xi (((1 - c : ℝ) : ℂ) + (t : ℂ) * I)) (hM t)
                        _ = M[(TestSpace.tilde (F := F) f)]((c : ℂ) + ((-t : ℝ) : ℂ) * I) *
                              (- logDeriv xi ((c : ℂ) + ((-t : ℝ) : ℂ) * I)) := by
                                -- rewrite the log-derivative factor
                                simpa [mul_assoc] using congrArg (fun w => M[(TestSpace.tilde (F := F) f)]((c : ℂ) + ((-t : ℝ) : ℂ) * I) * w) (hLog t)
          _ = - (M[(TestSpace.tilde (F := F) f)]((c : ℂ) + ((-t : ℝ) : ℂ) * I) *
                    logDeriv xi ((c : ℂ) + ((-t : ℝ) : ℂ) * I)) := by
                    ring
          _ = - g (-t) := by
                    simp [g, mul_assoc, mul_left_comm, mul_comm]
      -- Integrate and pull out the minus sign.
      -- First rewrite the integrand as `- g (-t)` under the interval integral.
      have hIntEq :
          (∫ t : ℝ in (-T)..T,
              M[f](((1 - c : ℝ) : ℂ) + (t : ℂ) * I) * logDeriv xi (((1 - c : ℝ) : ℂ) + (t : ℂ) * I)) =
            ∫ t : ℝ in (-T)..T, (- g (-t)) := by
        -- `intervalIntegral` is a function of the integrand, so we can rewrite by `congrArg`.
        simpa using congrArg
          (fun h : ℝ → ℂ => (∫ t : ℝ in (-T)..T, h t)) this
      have hNeg :
          (∫ t : ℝ in (-T)..T, (- g (-t))) = - ∫ t : ℝ in (-T)..T, g (-t) := by
        simp
      have hcomp : (∫ t : ℝ in (-T)..T, g (-t)) = ∫ t : ℝ in (-T)..T, g t := by
        simp
      -- Assemble.
      calc
        (∫ t : ℝ in (-T)..T,
            M[f](((1 - c : ℝ) : ℂ) + (t : ℂ) * I) * logDeriv xi (((1 - c : ℝ) : ℂ) + (t : ℂ) * I))
            = ∫ t : ℝ in (-T)..T, (- g (-t)) := hIntEq
        _ = - ∫ t : ℝ in (-T)..T, g (-t) := hNeg
    -- symmetry on `[-T,T]`
    have hSymm : (∫ t : ℝ in (-T)..T, g (-t)) = ∫ t : ℝ in (-T)..T, g t := by
      simp
    -- substitute
    simpa [hSymm] using h1
  -- Finish: multiply by `I` and match the `vertLeft`/`vertRight` definitions.
  have hI :
      I * ∫ t : ℝ in (-T)..T,
          M[f](((1 - c : ℝ) : ℂ) + (t : ℂ) * I) * logDeriv xi (((1 - c : ℝ) : ℂ) + (t : ℂ) * I) =
        -(I * ∫ t : ℝ in (-T)..T, g t) := by
    -- Multiply `ha` by `I` and simplify `I * (-a) = -(I * a)`.
    have hmul : I * (∫ t : ℝ in (-T)..T,
        M[f](((1 - c : ℝ) : ℂ) + (t : ℂ) * I) * logDeriv xi (((1 - c : ℝ) : ℂ) + (t : ℂ) * I)) =
          I * (-∫ t : ℝ in (-T)..T, g t) := congrArg (fun z : ℂ => I * z) ha
    -- turn `I * (-x)` into `-(I * x)`
    simpa [mul_assoc] using hmul
  -- Unfold `vertLeft`/`vertRight` and rewrite `g`.
  simpa [vertLeft, vertRight, g] using hI

/-- A convenient specialization of `TestSpace.mellin_tilde` for the rectangle left/right edges. -/
lemma mellin_leftEdge_eq_tilde_rightEdge
    {F : Type} [TestSpace F] (f : F) (c t : ℝ) :
    M[f](((1 - c : ℝ) : ℂ) + (t : ℂ) * I) =
      M[(TestSpace.tilde (F := F) f)]((c : ℂ) + ((-t : ℝ) : ℂ) * I) := by
  -- Start from `M[˜ₘ f](s) = M[f](1 - s)` with `s = c - it`.
  have h :=
    (TestSpace.mellin_tilde (f := f) (s := (c : ℂ) + ((-t : ℝ) : ℂ) * I))
  -- Rearrange and simplify `1 - (c - it) = (1-c) + it`.
  -- We also normalize `(-t : ℂ) * I` to `-(t : ℂ) * I` for simp.
  have h' :
      M[(TestSpace.tilde (F := F) f)]((c : ℂ) + ((-t : ℝ) : ℂ) * I) =
        M[f](((1 - c : ℝ) : ℂ) + (t : ℂ) * I) := by
    -- `simp` can see `sub_eq_add_neg` and basic ring simplifications in `ℂ`.
    simp [sub_eq_add_neg, add_assoc, add_comm, mul_comm]
  simpa using h'.symm

/-- `vertLeft_eq_neg_vertRight_tilde` with the Mellin edge identity discharged automatically. -/
theorem vertLeft_eq_neg_vertRight_tilde_of_mellin
    {F : Type} [TestSpace F]
    (xi : ℂ → ℂ) (f : F) (c T : ℝ)
    (hLog : ∀ t : ℝ, logDeriv xi (((1 - c : ℝ) : ℂ) + (t : ℂ) * I) =
      - logDeriv xi ((c : ℂ) + ((-t : ℝ) : ℂ) * I)) :
    vertLeft (fun s : ℂ => M[f](s) * logDeriv xi s) c T =
      - vertRight (fun s : ℂ => M[(TestSpace.tilde (F := F) f)](s) * logDeriv xi s) c T := by
  refine vertLeft_eq_neg_vertRight_tilde (xi := xi) (f := f) (c := c) (T := T)
    (hM := ?_) (hLog := hLog)
  intro t
  simpa using mellin_leftEdge_eq_tilde_rightEdge (f := f) (c := c) (t := t)

/--
`vertLeft_eq_neg_vertRight_tilde` with the Mellin involution discharged automatically and the
log-derivative functional equation supplied as `logDeriv xi (1 - s) = - logDeriv xi s`.
-/
theorem vertLeft_eq_neg_vertRight_tilde_of_mellin_and_logDeriv_one_sub
    {F : Type} [TestSpace F]
    (xi : ℂ → ℂ) (f : F) (c T : ℝ)
    (hFE : ∀ s : ℂ, logDeriv xi (1 - s) = - logDeriv xi s) :
    vertLeft (fun s : ℂ => M[f](s) * logDeriv xi s) c T =
      - vertRight (fun s : ℂ => M[(TestSpace.tilde (F := F) f)](s) * logDeriv xi s) c T := by
  refine vertLeft_eq_neg_vertRight_tilde_of_mellin (xi := xi) (f := f) (c := c) (T := T) (hLog := ?_)
  intro t
  -- Apply the FE identity to `s = c - it` and simplify `1 - (c - it) = (1-c) + it`.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
    (hFE ((c : ℂ) + ((-t : ℝ) : ℂ) * I))

/--
Under the same Mellin/functional-equation hypotheses as `vertLeft_eq_neg_vertRight_tilde`,
the *vertical difference* on the rectangle equals a sum of right-edge integrals for `f` and `˜ₘf`.

This is the algebraic “functional equation cancellation” on the left edge.
-/
theorem vertDiff_eq_vertRight_add_vertRight_tilde
    {F : Type} [TestSpace F]
    (xi : ℂ → ℂ) (f : F) (c T : ℝ)
    (hM : ∀ t : ℝ, M[f](((1 - c : ℝ) : ℂ) + (t : ℂ) * I) =
      M[(TestSpace.tilde (F := F) f)]((c : ℂ) + ((-t : ℝ) : ℂ) * I))
    (hLog : ∀ t : ℝ, logDeriv xi (((1 - c : ℝ) : ℂ) + (t : ℂ) * I) =
      - logDeriv xi ((c : ℂ) + ((-t : ℝ) : ℂ) * I)) :
    vertDiff (fun s : ℂ => M[f](s) * logDeriv xi s) c T =
      vertRight (fun s : ℂ => M[f](s) * logDeriv xi s) c T +
        vertRight (fun s : ℂ => M[(TestSpace.tilde (F := F) f)](s) * logDeriv xi s) c T := by
  -- Expand `vertDiff` and rewrite `vertLeft` using the previous lemma.
  have hleft :
      vertLeft (fun s : ℂ => M[f](s) * logDeriv xi s) c T =
        - vertRight (fun s : ℂ => M[(TestSpace.tilde (F := F) f)](s) * logDeriv xi s) c T :=
    vertLeft_eq_neg_vertRight_tilde (xi := xi) (f := f) (c := c) (T := T) hM hLog
  -- Now `right - left = right - (-right_tilde) = right + right_tilde`.
  simp [vertDiff, hleft, sub_eq_add_neg, add_comm]

/--
`vertDiff_eq_vertRight_add_vertRight_tilde` with the Mellin involution discharged automatically and
the log-derivative functional equation supplied as `logDeriv xi (1 - s) = - logDeriv xi s`.
-/
theorem vertDiff_eq_vertRight_add_vertRight_tilde_of_mellin_and_logDeriv_one_sub
    {F : Type} [TestSpace F]
    (xi : ℂ → ℂ) (f : F) (c T : ℝ)
    (hFE : ∀ s : ℂ, logDeriv xi (1 - s) = - logDeriv xi s) :
    vertDiff (fun s : ℂ => M[f](s) * logDeriv xi s) c T =
      vertRight (fun s : ℂ => M[f](s) * logDeriv xi s) c T +
        vertRight (fun s : ℂ => M[(TestSpace.tilde (F := F) f)](s) * logDeriv xi s) c T := by
  refine vertDiff_eq_vertRight_add_vertRight_tilde (xi := xi) (f := f) (c := c) (T := T)
    (hM := ?_) (hLog := ?_)
  · intro t
    simpa using mellin_leftEdge_eq_tilde_rightEdge (f := f) (c := c) (t := t)
  · intro t
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
      (hFE ((c : ℂ) + ((-t : ℝ) : ℂ) * I))

/-- `vertDiff_eq_vertRight_add_vertRight_tilde` with Mellin involution discharged automatically. -/
theorem vertDiff_eq_vertRight_add_vertRight_tilde_of_mellin
    {F : Type} [TestSpace F]
    (xi : ℂ → ℂ) (f : F) (c T : ℝ)
    (hLog : ∀ t : ℝ, logDeriv xi (((1 - c : ℝ) : ℂ) + (t : ℂ) * I) =
      - logDeriv xi ((c : ℂ) + ((-t : ℝ) : ℂ) * I)) :
    vertDiff (fun s : ℂ => M[f](s) * logDeriv xi s) c T =
      vertRight (fun s : ℂ => M[f](s) * logDeriv xi s) c T +
        vertRight (fun s : ℂ => M[(TestSpace.tilde (F := F) f)](s) * logDeriv xi s) c T := by
  refine vertDiff_eq_vertRight_add_vertRight_tilde (xi := xi) (f := f) (c := c) (T := T)
    (hM := ?_) (hLog := hLog)
  intro t
  simpa using mellin_leftEdge_eq_tilde_rightEdge (f := f) (c := c) (t := t)

/-- The truncated contour functional \(W^{(1)}_{c,T}\) for a given `xi` (via `logDeriv xi`). -/
def W1Trunc {F : Type} [TestSpace F] (xi : ℂ → ℂ) (c T : ℝ) (f : F) : ℂ :=
  (twoPiI)⁻¹ *
    boundaryRectIntegral (fun s : ℂ => M[f](s) * logDeriv xi s) (rectZ c T) (rectW c T)

lemma W1Trunc_def {F : Type} [TestSpace F] (xi : ℂ → ℂ) (c T : ℝ) (f : F) :
    W1Trunc (F := F) xi c T f =
      (twoPiI)⁻¹ *
        boundaryRectIntegral (fun s : ℂ => M[f](s) * logDeriv xi s) (rectZ c T) (rectW c T) := rfl

/-!
## Packaging the limiting functional

To avoid baking in heavy analytic facts, we record the existence of the `T → ∞` limit as an
explicit hypothesis bundle.  Later, we can replace the hypotheses with actual proofs while keeping
the downstream API stable.
-/

/-- A hypothesis bundle asserting that `W1` is the `T → ∞` limit of `W1Trunc`. -/
structure W1LimitAssumptions {F : Type} [TestSpace F] (xi : ℂ → ℂ) (c : ℝ) where
  /-- The (putative) limiting functional. -/
  W1 : F → ℂ
  /-- `W1` is the limit of the truncated contour functional as `T → ∞`. -/
  tendsto_W1Trunc :
    ∀ f : F,
      Filter.Tendsto (fun T : ℝ => W1Trunc (F := F) xi c T f) Filter.atTop (nhds (W1 f))

/-- Uniqueness of the `T → ∞` limit of `W1Trunc` in `ℂ`. -/
theorem W1_eq_of_tendsto_W1Trunc
    {F : Type} [TestSpace F]
    (xi : ℂ → ℂ) (c : ℝ)
    (A : W1LimitAssumptions (F := F) xi c)
    (f : F) (z : ℂ)
    (hz : Filter.Tendsto (fun T : ℝ => W1Trunc (F := F) xi c T f) Filter.atTop (nhds z)) :
    A.W1 f = z := by
  -- `ℂ` is a T₂ space, so limits are unique.
  have h1 := A.tendsto_W1Trunc f
  exact tendsto_nhds_unique h1 hz

/--
If the horizontal edge contributions vanish as `T → ∞`, then the *vertical* contour contribution
converges, and its limit is `(2πi) * W1`.

This is a purely formal “limit algebra” lemma; it does not assume anything about zeros of `xi`.
-/
theorem tendsto_vertDiff_of_horizontal_vanish
    {F : Type} [TestSpace F]
    (xi : ℂ → ℂ) (c : ℝ)
    (A : W1LimitAssumptions (F := F) xi c)
    (f : F)
    (hBot : Filter.Tendsto
      (fun T : ℝ => horizBottom (fun s : ℂ => M[f](s) * logDeriv xi s) c T)
      Filter.atTop (nhds 0))
    (hTop : Filter.Tendsto
      (fun T : ℝ => horizTop (fun s : ℂ => M[f](s) * logDeriv xi s) c T)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun T : ℝ => vertDiff (fun s : ℂ => M[f](s) * logDeriv xi s) c T)
      Filter.atTop (nhds (((2 * Real.pi : ℂ) * I) * A.W1 f)) := by
  -- Start from the convergence of `W1Trunc`.
  have hW := A.tendsto_W1Trunc f
  -- Rewrite `W1Trunc` using the edge decomposition.
  have hW' :
      Filter.Tendsto
        (fun T : ℝ =>
          (twoPiI)⁻¹ *
            (horizBottom (fun s : ℂ => M[f](s) * logDeriv xi s) c T -
                horizTop (fun s : ℂ => M[f](s) * logDeriv xi s) c T +
                  vertDiff (fun s : ℂ => M[f](s) * logDeriv xi s) c T))
        Filter.atTop (nhds (A.W1 f)) := by
    -- `W1Trunc = prefactor * boundaryRectIntegral` and `boundaryRectIntegral = ...`
    simpa [W1Trunc, boundaryRectIntegral_eq_edges, mul_assoc] using hW
  -- Multiply both sides by `(2πi)` to isolate the contour contribution.
  -- We avoid rewriting `((2πi)⁻¹)` explicitly (it expands using `I⁻¹ = -I`); instead, multiply the
  -- convergence statement by the inverse prefactor using `mul_inv_cancel_left₀`.
  set a : ℂ := twoPiI
  have ha : a ≠ 0 := by
    -- `2π ≠ 0` and `I ≠ 0`
    have hpi : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    have h2pi : ((2 : ℂ) * (Real.pi : ℂ)) ≠ 0 := by
      exact mul_ne_zero (by norm_num) hpi
    -- `a = 2πi`
    simp [a, twoPiI, mul_assoc, mul_left_comm, mul_comm]
  -- Multiply the `W1Trunc` limit by `a` on the left; the LHS becomes `a * W1Trunc = boundaryRectIntegral`.
  have hMul :
      Filter.Tendsto
        (fun T : ℝ => a * W1Trunc (F := F) xi c T f)
        Filter.atTop (nhds (a * A.W1 f)) := by
    simpa [a, mul_assoc] using (Filter.Tendsto.const_mul a hW)
  have hRect :
      Filter.Tendsto
        (fun T : ℝ =>
          boundaryRectIntegral (fun s : ℂ => M[f](s) * logDeriv xi s) (rectZ c T) (rectW c T))
        Filter.atTop (nhds (a * A.W1 f)) := by
    -- `a * W1Trunc = a * (twoPiI⁻¹ * boundaryRectIntegral) = boundaryRectIntegral` since `a = twoPiI`.
    have hEq :
        (fun T : ℝ => a * W1Trunc (F := F) xi c T f) =
          (fun T : ℝ =>
            boundaryRectIntegral (fun s : ℂ => M[f](s) * logDeriv xi s) (rectZ c T) (rectW c T)) := by
      funext T
      have ha' : twoPiI ≠ 0 := by simpa [a] using ha
      -- unfold `W1Trunc` and cancel the prefactor
      simp [W1Trunc, a, mul_assoc, mul_left_comm, mul_comm, mul_inv_cancel_left₀ ha']
    simpa [hEq] using hMul
  -- Expand boundary integral into edge contributions.
  have hSum :
      Filter.Tendsto
        (fun T : ℝ =>
          horizBottom (fun s : ℂ => M[f](s) * logDeriv xi s) c T -
            horizTop (fun s : ℂ => M[f](s) * logDeriv xi s) c T +
              vertDiff (fun s : ℂ => M[f](s) * logDeriv xi s) c T)
        Filter.atTop (nhds (a * A.W1 f)) := by
    simpa [boundaryRectIntegral_eq_edges, a] using hRect
  -- Now use the hypotheses `hBot`, `hTop` to cancel the horizontal terms in the limit.
  have hHoriz :
      Filter.Tendsto
        (fun T : ℝ =>
          horizBottom (fun s : ℂ => M[f](s) * logDeriv xi s) c T -
            horizTop (fun s : ℂ => M[f](s) * logDeriv xi s) c T)
        Filter.atTop (nhds 0) := by
    simpa using hBot.sub hTop
  -- `sum = horiz + vertDiff`, so `vertDiff` tends to the same limit.
  -- We use `tendsto_sub` with `hSum` and `hHoriz`.
  have := hSum.sub hHoriz
  -- Simplify `((horiz + vertDiff) - horiz) = vertDiff`.
  simpa [vertDiff, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, a, twoPiI, vertRight, vertLeft] using this

/-!
### Combining functional-equation edge cancellation with the limit algebra
-/

/--
If:
- `W1` is the `T → ∞` limit of `W1Trunc`,
- the horizontal edge integrals vanish as `T → ∞`, and
- the left vertical edge can be rewritten using Mellin involution + functional equation
  (as in `vertDiff_eq_vertRight_add_vertRight_tilde`),
then the *sum* of right-edge integrals for `f` and `˜ₘf` converges to `(2πi) * W1(f)`.
-/
theorem tendsto_vertRight_add_vertRight_tilde_of_horizontal_vanish
    {F : Type} [TestSpace F]
    (xi : ℂ → ℂ) (c : ℝ)
    (A : W1LimitAssumptions (F := F) xi c)
    (f : F)
    (hBot : Filter.Tendsto
      (fun T : ℝ => horizBottom (fun s : ℂ => M[f](s) * logDeriv xi s) c T)
      Filter.atTop (nhds 0))
    (hTop : Filter.Tendsto
      (fun T : ℝ => horizTop (fun s : ℂ => M[f](s) * logDeriv xi s) c T)
      Filter.atTop (nhds 0))
    (hM : ∀ t : ℝ, M[f](((1 - c : ℝ) : ℂ) + (t : ℂ) * I) =
      M[(TestSpace.tilde (F := F) f)]((c : ℂ) + ((-t : ℝ) : ℂ) * I))
    (hLog : ∀ t : ℝ, logDeriv xi (((1 - c : ℝ) : ℂ) + (t : ℂ) * I) =
      - logDeriv xi ((c : ℂ) + ((-t : ℝ) : ℂ) * I)) :
    Filter.Tendsto
      (fun T : ℝ =>
        vertRight (fun s : ℂ => M[f](s) * logDeriv xi s) c T +
          vertRight (fun s : ℂ => M[(TestSpace.tilde (F := F) f)](s) * logDeriv xi s) c T)
      Filter.atTop (nhds (((2 * Real.pi : ℂ) * I) * A.W1 f)) := by
  have hVertDiff :=
    tendsto_vertDiff_of_horizontal_vanish (xi := xi) (c := c) (A := A) (f := f) hBot hTop
  have hEq :
      (fun T : ℝ => vertDiff (fun s : ℂ => M[f](s) * logDeriv xi s) c T) =
        fun T : ℝ =>
          vertRight (fun s : ℂ => M[f](s) * logDeriv xi s) c T +
            vertRight (fun s : ℂ => M[(TestSpace.tilde (F := F) f)](s) * logDeriv xi s) c T := by
    funext T
    simpa using
      vertDiff_eq_vertRight_add_vertRight_tilde (xi := xi) (f := f) (c := c) (T := T) hM hLog
  simpa [hEq] using hVertDiff

end ContourW1

end ExplicitFormula
end RiemannRecognitionGeometry
