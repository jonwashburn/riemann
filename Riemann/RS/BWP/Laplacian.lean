import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Data.Real.CompleteField
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Order.BourbakiWitt
import Mathlib.RingTheory.Finiteness.Prod
/-

# Laplacian and harmonic functions on finite‑dimensional real inner product spaces

We define:

* `hessian ℝ f x` : the second Fréchet derivative (Hessian) of a scalar field
  `f : E → ℝ` at a point `x : E`, as a continuous bilinear map `E →L[ℝ] E →L[ℝ] ℝ`.

* `laplacian ℝ f x` : the Laplacian of `f` at `x`, defined as the trace of the Hessian
  in an orthonormal basis of the finite‑dimensional real inner product space `E`.

* `IsHarmonicOn f s` : a scalar field `f : E → ℝ` is harmonic on a set `s` if it is
  twice continuously differentiable at every point of `s` and its Laplacian vanishes there.

The Laplacian is defined for any finite‑dimensional real inner product space `E`; it is
canonically independent of the choice of orthonormal basis (this is proved via standard
linear algebra but not used in the basic API).

Future extensions include:
* explicit coordinate formulas on `ℝ^n` and `ℝ × ℝ`,
* invariance under linear (and affine) isometries,
* connections with divergence and the Hessian of vector fields,
* the classical result that the real and imaginary parts of analytic functions are harmonic.
-/

noncomputable section

open scoped BigOperators ENNReal

namespace Analysis

/-! ## Hessian -/

section Hessian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Hessian of a scalar field `f : E → ℝ` at `x : E`, defined as the second Fréchet
derivative `fderiv ℝ (fun y => fderiv ℝ f y) x`.

We work over `ℝ` because the Laplacian is a real‑analytic notion. -/
def hessian (f : E → ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fun y => fderiv ℝ f y) x

/-- A convenience lemma: the Hessian is the Fréchet derivative of `fderiv ℝ f`. -/
lemma hessian_def (f : E → ℝ) (x : E) :
    hessian f x = fderiv ℝ (fun y => fderiv ℝ f y) x := rfl

/-- If `f` is constant, then its Hessian vanishes everywhere. -/
lemma hessian_const (c : ℝ) (x : E) :
    hessian (fun _ : E => c) x = 0 := by
  -- First derivative is identically zero, hence so is its derivative.
  ext v w
  simp [hessian]  -- both levels of derivatives are zero

/-- If `f` is affine‑linear, then its Hessian is zero.

More precisely, for any continuous linear map `L : E →L[ℝ] ℝ` and constant `c`, the
Hessian of `x ↦ L x + c` vanishes. -/
lemma hessian_linear_add_const (L : E →L[ℝ] ℝ) (c : ℝ) (x : E) :
    hessian (fun y : E => L y + c) x = 0 := by
  -- `fderiv` of an affine map is constant `L`, so the second derivative is zero.
  ext v w
  have h₁ : fderiv ℝ (fun y : E => L y + c) = fun _ => L := by
    -- derivative is constant in `y`
    funext y
    -- `fderiv` of `y ↦ L y + c` is the same as the derivative of `y ↦ L y`
    -- (the constant term disappears), and this derivative is `L`.
    have hAdd :
        fderiv ℝ (fun y : E => L y + c) y =
          fderiv ℝ (fun y : E => L y) y := by
      rw [fderiv_add_const]
    have hL : fderiv ℝ (fun y : E => L y) y = L := by
      exact L.fderiv
    simp [hAdd, hL]
  -- Now differentiate once more: the derivative of the constant map `fun _ => L` is zero.
  simp [hessian]  -- both derivatives vanish

/-!
If desired, one can use the symmetry results from `FDeriv/Symmetric.lean` to prove that
`hessian f x` is symmetric under suitable hypotheses (`C^2` regularity). We do not need this
yet for the basic Laplacian / harmonic API, so we leave those lemmas for a later development.
-/

end Hessian

/-! ## Laplacian -/

section Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma iteratedFDeriv_two_eq_hessian (f : E → ℝ) (x : E) (m : Fin 2 → E) :
    iteratedFDeriv ℝ 2 f x m = hessian f x (m 0) (m 1) := by
  simpa [hessian] using (iteratedFDeriv_two_apply (𝕜 := ℝ) (f := f) (z := x) m)

variable [FiniteDimensional ℝ E]

/-- Scalar Laplacian on a finite-dimensional real inner product space, re-exported from mathlib. -/
abbrev laplacian (f : E → ℝ) (x : E) : ℝ :=
  InnerProductSpace.laplacian (E := E) (F := ℝ) f x

lemma laplacian_eq_sum_orthonormal
  {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (f : E → ℝ) (x : E) :
    laplacian f x = ∑ i, hessian f x (b i) (b i) := by
  classical
  have h :=
    congrArg (fun g : E → ℝ => g x)
      (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
        (E := E) (F := ℝ) (f := f) (v := b))
  simpa [laplacian, iteratedFDeriv_two_eq_hessian] using h

lemma laplacian_def (f : E → ℝ) (x : E) :
    laplacian f x =
      ∑ i, hessian f x ((stdOrthonormalBasis ℝ E) i)
        ((stdOrthonormalBasis ℝ E) i) :=
  laplacian_eq_sum_orthonormal (b := stdOrthonormalBasis ℝ E) f x

/-!
### Specializations and coordinate bridges

In many applications we work on concrete Hilbert spaces such as the `L²` product
`WithLp 2 (ℝ × ℝ)`.  The following helper lemma simply specializes the general
Laplacian definition to this setting; more refined coordinate identifications
are built on top of it in `DiagonalBounds.lean`.
-/

lemma laplacian_withLp_prod
    (f : WithLp 2 (ℝ × ℝ) → ℝ) (x : WithLp 2 (ℝ × ℝ)) :
    laplacian f x =
      ∑ i, hessian f x
        ((stdOrthonormalBasis ℝ (WithLp 2 (ℝ × ℝ))) i)
        ((stdOrthonormalBasis ℝ (WithLp 2 (ℝ × ℝ))) i) :=
  laplacian_def (E := WithLp 2 (ℝ × ℝ)) f x

/-!
### Bridge to coordinate derivatives
-/

/-- The coordinate unit vectors in `WithLp 2 (ℝ × ℝ)`. -/
private def e₁ : WithLp 2 (ℝ × ℝ) :=
  WithLp.toLp (p := (2 : ℝ≥0∞)) ((1 : ℝ), (0 : ℝ))

private def e₂ : WithLp 2 (ℝ × ℝ) :=
  WithLp.toLp (p := (2 : ℝ≥0∞)) ((0 : ℝ), (1 : ℝ))

/-- The Laplacian on `WithLp 2 (ℝ × ℝ)` expands to the sum of second derivatives along
    the coordinate axes `(1,0)` and `(0,1)`. -/
lemma laplacian_withLp_prod_coords
    (f : WithLp 2 (ℝ × ℝ) → ℝ) (x : WithLp 2 (ℝ × ℝ)) :
    laplacian f x =
      hessian f x e₁ e₁ + hessian f x e₂ e₂ := by
  let bR := OrthonormalBasis.singleton (Fin 1) ℝ
  let B := bR.prod bR
  rw [laplacian_eq_sum_orthonormal B]
  rw [Fintype.sum_sum_type]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  have h1 : B (Sum.inl 0) = e₁ := by
    rw [OrthonormalBasis.prod_apply, Sum.elim_inl]
    simp [bR, e₁]
  have h2 : B (Sum.inr 0) = e₂ := by
    rw [OrthonormalBasis.prod_apply, Sum.elim_inr]
    simp [bR, e₂]
  rw [h1, h2]

/-- Derivative of `x ↦ f(x, y)` matches `fderiv f (x, y) (1, 0)`. -/
lemma deriv_slice_fst_eq_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : WithLp 2 (ℝ × ℝ) → F} {p : WithLp 2 (ℝ × ℝ)}
    (h : DifferentiableAt ℝ f p) :
    deriv (fun x => f (WithLp.toLp (p := (2 : ℝ≥0∞)) (x, p.ofLp.2))) p.ofLp.1 =
      fderiv ℝ f p e₁ := by
  let v : WithLp 2 (ℝ × ℝ) := e₁
  let c : WithLp 2 (ℝ × ℝ) := WithLp.toLp (p := (2 : ℝ≥0∞)) ((0 : ℝ), p.ofLp.2)
  have h_curve : HasDerivAt (fun x : ℝ => x • v + c) v p.ofLp.1 := by
    apply HasDerivAt.add_const
    convert HasDerivAt.smul_const (hasDerivAt_id p.ofLp.1) v using 1
    simp
  have h_eq :
      (fun x : ℝ => x • v + c) =
        (fun x : ℝ => WithLp.toLp (p := (2 : ℝ≥0∞)) (x, p.ofLp.2)) := by
    funext x
    -- `WithLp` doesn't have an `[ext]` lemma; reduce to the underlying `ℝ × ℝ` via `ofLp`.
    apply (WithLp.ofLp_injective (p := (2 : ℝ≥0∞)) (V := (ℝ × ℝ)))
    ext <;> simp [v, c, e₁]
  rw [h_eq] at h_curve
  exact (h.hasFDerivAt.comp_hasDerivAt p.ofLp.1 h_curve).deriv

/-- Derivative of `y ↦ f(x, y)` matches `fderiv f (x, y) (0, 1)`. -/
lemma deriv_slice_snd_eq_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : WithLp 2 (ℝ × ℝ) → F} {p : WithLp 2 (ℝ × ℝ)}
    (h : DifferentiableAt ℝ f p) :
    deriv (fun y => f (WithLp.toLp (p := (2 : ℝ≥0∞)) (p.ofLp.1, y))) p.ofLp.2 =
      fderiv ℝ f p e₂ := by
  let v : WithLp 2 (ℝ × ℝ) := e₂
  let c : WithLp 2 (ℝ × ℝ) := WithLp.toLp (p := (2 : ℝ≥0∞)) (p.ofLp.1, (0 : ℝ))
  have h_curve : HasDerivAt (fun y : ℝ => y • v + c) v p.ofLp.2 := by
    apply HasDerivAt.add_const
    convert HasDerivAt.smul_const (hasDerivAt_id p.ofLp.2) v using 1
    simp
  have h_eq :
      (fun y : ℝ => y • v + c) =
        (fun y : ℝ => WithLp.toLp (p := (2 : ℝ≥0∞)) (p.ofLp.1, y)) := by
    funext y
    -- `WithLp` doesn't have an `[ext]` lemma; reduce to the underlying `ℝ × ℝ` via `ofLp`.
    apply (WithLp.ofLp_injective (p := (2 : ℝ≥0∞)) (V := (ℝ × ℝ)))
    ext <;> simp [v, c, e₂]
  rw [h_eq] at h_curve
  exact (h.hasFDerivAt.comp_hasDerivAt p.ofLp.2 h_curve).deriv

/-- The Hessian entry `hessian f q (1,0) (1,0)` corresponds to the iterated x-derivative.

We assume in addition that the Fréchet derivative `p ↦ fderiv ℝ f p` is differentiable at `q`,
which is the natural `C^2` regularity condition. -/
lemma hessian_fst_fst_slice
    (f : WithLp 2 (ℝ × ℝ) → ℝ) (q : WithLp 2 (ℝ × ℝ))
    (h : ContDiff ℝ 2 f)
    (h_fderiv_diff : DifferentiableAt ℝ (fun p : WithLp 2 (ℝ × ℝ) => fderiv ℝ f p) q) :
    hessian f q e₁ e₁ =
      deriv
        (fun x => deriv (fun x' => f (WithLp.toLp (p := (2 : ℝ≥0∞)) (x', q.ofLp.2))) x)
        q.ofLp.1 := by
  classical
  let v : WithLp 2 (ℝ × ℝ) := e₁
  -- By definition, the Hessian is the Fréchet derivative of the Fréchet derivative.
  have hdef :
      hessian f q v v =
        (fderiv ℝ (fun p : WithLp 2 (ℝ × ℝ) => fderiv ℝ f p) q v) v := rfl
  -- Define `g(p) = fderiv f p v` (directional derivative along `v`).
  let g : WithLp 2 (ℝ × ℝ) → ℝ := fun p => fderiv ℝ f p v
  -- From differentiability of `p ↦ fderiv f p` at `q`, evaluation at `v` is differentiable.
  have h_g_diff : DifferentiableAt ℝ g q :=
    h_fderiv_diff.clm_apply (differentiableAt_const v)

  -- First, identify the Hessian entry as the x-slice derivative of `g`.
  have hg_slice :
      hessian f q v v =
      deriv (fun x => g (WithLp.toLp (p := (2 : ℝ≥0∞)) (x, q.ofLp.2))) q.ofLp.1 := by
    -- Apply the slice lemma to the CLM-valued map `p ↦ fderiv f p`.
    have h_clm :
        deriv (fun x => fderiv ℝ f (WithLp.toLp (p := (2 : ℝ≥0∞)) (x, q.ofLp.2))) q.ofLp.1 =
          fderiv ℝ (fun p : WithLp 2 (ℝ × ℝ) => fderiv ℝ f p) q v := by
      -- `deriv_slice_fst_eq_fderiv` specialized to CLM-valued functions
      have := deriv_slice_fst_eq_fderiv
        (F := WithLp 2 (ℝ × ℝ) →L[ℝ] ℝ)
        (f := fun p : WithLp 2 (ℝ × ℝ) => fderiv ℝ f p)
        (p := q) h_fderiv_diff
      simpa [v] using this

    -- By `hdef`, the Hessian is `((fderiv … q) v) v`.
    -- By `h_clm`, `(fderiv … q) v` is the derivative of the slice.
    -- So applying `v` to both sides gives:
    have h₁ :
        hessian f q v v =
          (deriv (fun x => fderiv ℝ f (WithLp.toLp (p := (2 : ℝ≥0∞)) (x, q.ofLp.2))) q.ofLp.1) v := by
      have := congrArg (fun L => L v) h_clm
      simpa [hdef] using this.symm

    -- Now commute evaluation at `v` past `deriv` using the CLM chain rule.
    have h_comm :
        (deriv (fun x => fderiv ℝ f (WithLp.toLp (p := (2 : ℝ≥0∞)) (x, q.ofLp.2))) q.ofLp.1) v =
        deriv (fun x => fderiv ℝ f (WithLp.toLp (p := (2 : ℝ≥0∞)) (x, q.ofLp.2)) v) q.ofLp.1 := by
      classical
      -- View `x ↦ fderiv f (x, q.2) v` as the composition of
      -- `c x := fderiv f (x, q.2)` with the constant vector `u x := v`,
      -- and apply the chain rule for evaluation of continuous linear maps.
      let c : ℝ → WithLp 2 (ℝ × ℝ) →L[ℝ] ℝ :=
        fun x => fderiv ℝ f (WithLp.toLp (p := (2 : ℝ≥0∞)) (x, q.ofLp.2))
      let u : ℝ → WithLp 2 (ℝ × ℝ) := fun _ => v
      -- differentiability of `c` comes from `h_fderiv_diff` and the slice `x ↦ (x, q.2)`
      have h_slice :
          DifferentiableAt ℝ
            (fun x : ℝ => WithLp.toLp (p := (2 : ℝ≥0∞)) (x, q.ofLp.2)) q.ofLp.1 := by
        have hx : DifferentiableAt ℝ (fun x : ℝ => x) q.ofLp.1 := differentiableAt_id
        have hy : DifferentiableAt ℝ (fun _ : ℝ => q.ofLp.2) q.ofLp.1 := differentiableAt_const _
        have hxy : DifferentiableAt ℝ (fun x : ℝ => (x, q.ofLp.2)) q.ofLp.1 :=
          DifferentiableAt.prodMk hx hy
        -- `WithLp.toLp` is smooth, so composing preserves differentiability.
        have h_toLp :
            DifferentiableAt ℝ (@WithLp.toLp (2 : ℝ≥0∞) (ℝ × ℝ)) (q.ofLp.1, q.ofLp.2) := by
          -- `toLp` is the inverse of a continuous linear equivalence, hence differentiable.
          simpa [WithLp.prodContinuousLinearEquiv_symm_apply] using
            (WithLp.prodContinuousLinearEquiv (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (α := ℝ) (β := ℝ)).symm.differentiableAt
        simpa using h_toLp.comp q.ofLp.1 hxy
      have h_fderiv_diff' :
          DifferentiableAt ℝ (fun p : WithLp 2 (ℝ × ℝ) => fderiv ℝ f p)
            (WithLp.toLp (p := (2 : ℝ≥0∞)) (q.ofLp.1, q.ofLp.2)) := by
        simpa using h_fderiv_diff
      have hc : DifferentiableAt ℝ c q.ofLp.1 :=
        h_fderiv_diff'.comp q.ofLp.1 h_slice
      have hu : DifferentiableAt ℝ u q.ofLp.1 := differentiableAt_const _
      -- Apply CLM chain rule to `x ↦ c x (u x)`.
      have h' := deriv_clm_apply (𝕜 := ℝ) (c := c) (u := u) hc hu
      -- Since `u` is constant, its derivative vanishes and we obtain the desired commutation.
      have h'' :
          deriv (fun x => c x (u x)) q.ofLp.1 =
            deriv c q.ofLp.1 (u q.ofLp.1) := by
        simpa [u, deriv_const, add_comm] using h'
      -- Rewrite in terms of the original functions.
      simpa [c, u] using h''.symm

    -- Combine `h₁` and `h_comm` and unfold `g` to finish.
    have := h₁.trans h_comm
    simpa [g] using this

  -- Now identify `g (x, q.2)` with the scalar derivative in the `x`-direction.
  have h_eq_fun :
      (fun x => g (WithLp.toLp (p := (2 : ℝ≥0∞)) (x, q.ofLp.2))) =
        fun x => deriv (fun x' => f (WithLp.toLp (p := (2 : ℝ≥0∞)) (x', q.ofLp.2))) x := by
    funext x
    change fderiv ℝ f (WithLp.toLp (p := (2 : ℝ≥0∞)) (x, q.ofLp.2)) v =
      deriv (fun x' => f (WithLp.toLp (p := (2 : ℝ≥0∞)) (x', q.ofLp.2))) x
    have h_f_diff : DifferentiableAt ℝ f (WithLp.toLp (p := (2 : ℝ≥0∞)) (x, q.ofLp.2)) :=
      h.differentiable (by norm_num) _
    have hx :=
      (deriv_slice_fst_eq_fderiv (F := ℝ) (f := f)
        (p := WithLp.toLp (p := (2 : ℝ≥0∞)) (x, q.ofLp.2)) h_f_diff)
    -- Rewrite to match our goal.
    simpa [v] using hx.symm

  -- Therefore the outer derivatives agree at `q.1`.
  have h_eq_deriv :
      deriv (fun x => g (WithLp.toLp (p := (2 : ℝ≥0∞)) (x, q.ofLp.2))) q.ofLp.1 =
        deriv
          (fun x => deriv (fun x' => f (WithLp.toLp (p := (2 : ℝ≥0∞)) (x', q.ofLp.2))) x)
          q.ofLp.1 := by
    simp; aesop

  -- Finally combine `hg_slice` with `h_eq_deriv` and unfold `v`.
  have := hg_slice.trans h_eq_deriv
  simpa [v] using this

/-- The Hessian entry `hessian f q (0,1) (0,1)` corresponds to the iterated y-derivative. -/
lemma hessian_snd_snd_slice
    (f : WithLp 2 (ℝ × ℝ) → ℝ) (q : WithLp 2 (ℝ × ℝ))
    (h : ContDiff ℝ 2 f) :
    hessian f q e₂ e₂ =
      deriv
        (fun y => deriv (fun y' => f (WithLp.toLp (p := (2 : ℝ≥0∞)) (q.ofLp.1, y'))) y)
        q.ofLp.2 := by
  let v : WithLp 2 (ℝ × ℝ) := e₂
  rw [hessian_def]
  let g := fderiv ℝ f
  -- From `C^2` regularity of `f`, the map `p ↦ fderiv f p` is `C^1`, hence differentiable.
  have h_g_diff : DifferentiableAt ℝ g q := by
    -- Apply `contDiff_succ_iff_fderiv` with `n = 1`.
    have h' : ContDiff ℝ (1 + 1) f := by
      simpa using h
    have h2 := (contDiff_succ_iff_fderiv (𝕜 := ℝ) (f := f) (n := 1)).1 h'
    -- Extract `ContDiff ℝ 1 (fderiv ℝ f)` from the conjunction.
    have h_fderiv_CD : ContDiff ℝ 1 (fderiv ℝ f) := h2.2.2
    -- Specialize at the point `q`.
    exact (h_fderiv_CD.differentiable (by norm_num) q)
  have step1 := deriv_slice_snd_eq_fderiv (F := WithLp 2 (ℝ × ℝ) →L[ℝ] ℝ) h_g_diff
  rw [← step1]
  have h_comm :
      deriv (fun y => g (WithLp.toLp (p := (2 : ℝ≥0∞)) (q.ofLp.1, y))) q.ofLp.2 v =
        deriv (fun y => g (WithLp.toLp (p := (2 : ℝ≥0∞)) (q.ofLp.1, y)) v) q.ofLp.2 := by
    classical
    -- As in the `x`‑direction case, commute evaluation at `v` past `deriv`
    -- using the chain rule for CLM evaluation.
    let c : ℝ → WithLp 2 (ℝ × ℝ) →L[ℝ] ℝ :=
      fun y => g (WithLp.toLp (p := (2 : ℝ≥0∞)) (q.ofLp.1, y))
    let u : ℝ → WithLp 2 (ℝ × ℝ) := fun _ => v
    -- The slice `y ↦ (q.1, y)` is differentiable.
    have h_slice :
        DifferentiableAt ℝ
          (fun y : ℝ => WithLp.toLp (p := (2 : ℝ≥0∞)) (q.ofLp.1, y)) q.ofLp.2 := by
      have hx : DifferentiableAt ℝ (fun _ : ℝ => q.ofLp.1) q.ofLp.2 := differentiableAt_const _
      have hy : DifferentiableAt ℝ (fun y : ℝ => y) q.ofLp.2 := differentiableAt_id
      have hxy : DifferentiableAt ℝ (fun y : ℝ => (q.ofLp.1, y)) q.ofLp.2 :=
        DifferentiableAt.prodMk hx hy
      have h_toLp :
          DifferentiableAt ℝ (@WithLp.toLp (2 : ℝ≥0∞) (ℝ × ℝ)) (q.ofLp.1, q.ofLp.2) := by
        -- `toLp` is the inverse of a continuous linear equivalence, hence differentiable.
        simpa [WithLp.prodContinuousLinearEquiv_symm_apply] using
          (WithLp.prodContinuousLinearEquiv (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (α := ℝ) (β := ℝ)).symm.differentiableAt
      simpa using h_toLp.comp q.ofLp.2 hxy
    -- Differentiability of `c` at `q.ofLp.2` comes from that of `g` at `q`.
    have h_g_diff' : DifferentiableAt ℝ g (WithLp.toLp (p := (2 : ℝ≥0∞)) (q.ofLp.1, q.ofLp.2)) := by
      simpa using h_g_diff
    have hc : DifferentiableAt ℝ c q.ofLp.2 :=
      h_g_diff'.comp q.ofLp.2 h_slice
    have hu : DifferentiableAt ℝ u q.ofLp.2 := differentiableAt_const _
    -- Apply CLM chain rule to `y ↦ c y (u y)`.
    have h' := deriv_clm_apply (𝕜 := ℝ) (c := c) (u := u) hc hu
    -- Since `u` is constant, its derivative vanishes and we obtain the commutation.
    have h'' :
        deriv (fun y => c y (u y)) q.ofLp.2 =
          deriv c q.ofLp.2 (u q.ofLp.2) := by
      simpa [u, deriv_const, add_comm] using h'
    -- Rewrite in terms of the original functions.
    simpa [c, u] using h''.symm
  rw [h_comm]
  congr; ext y
  change fderiv ℝ f (WithLp.toLp (p := (2 : ℝ≥0∞)) (q.ofLp.1, y)) v = _
  have h_f_diff : DifferentiableAt ℝ f (WithLp.toLp (p := (2 : ℝ≥0∞)) (q.ofLp.1, y)) :=
    h.differentiable (by norm_num) _
  rw [deriv_slice_snd_eq_fderiv h_f_diff]

/-- Laplacian of a constant function is zero. -/
lemma laplacian_const (c : ℝ) (x : E) :
    laplacian (fun _ : E => c) x = 0 := by
  classical
  simp [laplacian_def, hessian_const, Finset.sum_const_zero]

/-- Laplacian of an affine‑linear function is zero. -/
lemma laplacian_linear_add_const (L : E →L[ℝ] ℝ) (c : ℝ) (x : E) :
    laplacian (fun y : E => L y + c) x = 0 := by
  classical
  simp [laplacian_def, hessian_linear_add_const]  -- all terms in the sum are zero

/-- If `f` has vanishing Hessian at `x`, then its Laplacian at `x` is zero. -/
lemma laplacian_of_hessian_eq_zero {f : E → ℝ} {x : E}
    (h : hessian f x = 0) :
    laplacian f x = 0 := by
  classical
  simp [laplacian_def, h]

/-!
Further coordinate descriptions (e.g., on `ℝ × ℝ` as a sum of second partial derivatives)
will be added in future work once the corresponding Hessian / second derivative API in
`mathlib` has been developed to the required level of generality.
-/

/-! ### Specialization to Euclidean space `ℝ^2` -/

section Euclidean2

open Fin Module

/-- The standard 2‑dimensional Euclidean real inner product space. -/
abbrev E2 : Type := EuclideanSpace ℝ (Fin 2)

/-- The real dimension of `E2` is `2`. -/
lemma finrank_E2 : Module.finrank ℝ E2 = 2 := by
  -- `EuclideanSpace ℝ (Fin n)` always has finrank `n`.
  simp [E2]

variable (f : E2 → ℝ) (x : E2)

/-- Second directional derivative of `f` at `x` along the `i`‑th vector of the
standard orthonormal basis, expressed via the Hessian. -/
noncomputable def secondDerivOnStdONB (i : Fin (finrank ℝ E2)) : ℝ :=
  let b := stdOrthonormalBasis ℝ E2
  hessian f x (b i) (b i)

/--
On `ℝ^2` (real Euclidean space), the Laplacian of a scalar field `f` at `x` is the sum
of second directional derivatives along the standard orthonormal basis vectors.
-/
lemma laplacian_eq_sum_secondDeriv_E2 :
    laplacian f x = ∑ i, secondDerivOnStdONB f x i := by
  classical
  -- This is just a restatement of the Laplacian formula in this concrete case.
  simpa [secondDerivOnStdONB] using
    (laplacian_def (E := E2) (f := f) (x := x))

end Euclidean2

end Laplacian

section Isometry

variable
  {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

open scoped BigOperators

/-! ### Hessian chain rule and Laplacian invariance under isometries -/

section ChainRule

open ContinuousLinearMap

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Fréchet derivative of a composition with a continuous linear map.

If `g : F → G` is differentiable at `L x`, then
\[
  fderiv (g ∘ L)(x) = (fderiv g (L x)).comp L.
\]
-/
lemma fderiv_compCLM
    (g : F → G) (L : E →L[ℝ] F) (x : E)
    (hg : DifferentiableAt ℝ g (L x)) :
    fderiv ℝ (fun y : E => g (L y)) x
      = (fderiv ℝ g (L x)).comp L := by
  classical
  -- `L` has derivative `L` at every point.
  have hL : HasFDerivAt (fun y : E => L y) L x := L.hasFDerivAt
  -- `g` has derivative `fderiv g (L x)` at `L x` by hypothesis.
  have hg' : HasFDerivAt g (fderiv ℝ g (L x)) (L x) := hg.hasFDerivAt
  -- Chain rule for the composition `g ∘ L`.
  have hcomp : HasFDerivAt (fun y : E => g (L y))
      ((fderiv ℝ g (L x)).comp L) x :=
    hg'.comp x hL
  -- Turn the `HasFDerivAt` into an equality for `fderiv`.
  exact hcomp.fderiv

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Directional chain rule for the derivative when post‑composing by a fixed continuous
linear map `T : E →L[ℝ] F`.

If `h : E → F →L[ℝ] ℝ` and `hh : HasFDerivAt h (fderiv ℝ h x) x`, then for each `v : E` we have
\[
  fderiv (λ y, (h y).comp T)(x)\,v = (fderiv h x\,v).comp T.
\]
We use this only inside the Hessian chain rule. -/
lemma fderiv_comp_rightCLM
    (h : E → F →L[ℝ] ℝ) (T : E →L[ℝ] F) (x v : E)
    (hh : HasFDerivAt h (fderiv ℝ h x) x) :
    fderiv ℝ (fun y : E => (h y).comp T) x v
      = (fderiv ℝ h x v).comp T := by
  classical
  -- Underlying linear map: post‑composition by `T`.
  let φ_lin : (F →L[ℝ] ℝ) →ₗ[ℝ] (E →L[ℝ] ℝ) :=
    { toFun := fun A => A.comp T
      , map_add' := by
          intro A B; ext x'
          simp
      , map_smul' := by
          intro c A; ext x'
          simp [smul_comp] }
  -- Uniform bound: ‖A.comp T‖ ≤ ‖T‖ * ‖A‖.
  have hφ_bd : ∀ A : F →L[ℝ] ℝ, ‖φ_lin A‖ ≤ ‖T‖ * ‖A‖ := by
    intro A
    have h := opNorm_comp_le (h := A) (f := T)
    simpa [φ_lin, mul_comm] using h
  -- Upgrade to a continuous linear map.
  let φ : (F →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
    LinearMap.mkContinuous φ_lin ‖T‖ (by
      intro A
      simpa using hφ_bd A)
  -- Now `y ↦ (h y).comp T` is `φ ∘ h`. Apply the Fréchet chain rule.
  have hφ : HasFDerivAt (fun A : F →L[ℝ] ℝ => φ A) φ (h x) :=
    φ.hasFDerivAt
  have hcomp : HasFDerivAt (fun y : E => φ (h y)) (φ.comp (fderiv ℝ h x)) x :=
    hφ.comp x hh
  -- Turn this into an equality for `fderiv`.
  have hcomp_fd : fderiv ℝ (fun y : E => φ (h y)) x
        = (φ.comp (fderiv ℝ h x)) :=
    hcomp.fderiv
  -- Evaluate both sides at `v`.
  have hcomp_apply :
      fderiv ℝ (fun y : E => φ (h y)) x v
        = (φ.comp (fderiv ℝ h x)) v := by
    -- apply the equality of linear maps to `v`
    simpa using congrArg (fun L => L v) hcomp_fd
  -- This is exactly the desired directional equality.
  simpa [Function.comp, φ] using hcomp_apply

/-- `fderiv` of a composition with a continuous linear map.

If `g : F → ℝ` is differentiable at `L x`, then
\[
  fderiv (g ∘ L)(x) = (fderiv g (L x)).comp L.
\]
-/
lemma fderiv_compCLM'
    (g : F → ℝ) (L : E →L[ℝ] F) (x : E)
    (hg : DifferentiableAt ℝ g (L x)) :
    fderiv ℝ (fun y : E => g (L y)) x
      = (fderiv ℝ g (L x)).comp L := by
  classical
  -- `L` has derivative `L` at every point.
  have hL : HasFDerivAt (fun y : E => L y) L x := L.hasFDerivAt
  -- `g` has derivative `fderiv g (L x)` at `L x` by hypothesis.
  have hg' : HasFDerivAt g (fderiv ℝ g (L x)) (L x) :=
    hg.hasFDerivAt
  -- Chain rule for the composition `g ∘ L`.
  have hcomp : HasFDerivAt (fun y : E => g (L y))
      ((fderiv ℝ g (L x)).comp L) x :=
    hg'.comp x hL
  -- Turn the `HasFDerivAt` into an equality for `fderiv`.
  exact hcomp.fderiv

lemma hessian_comp_linear
    (g : F → ℝ) (L : E →L[ℝ] F) (x v w : E)
    (hg1 : ∀ y : E, DifferentiableAt ℝ g (L y))
    (hg2 : DifferentiableAt ℝ (fun z : F => fderiv ℝ g z) (L x)) :
  hessian (fun y : E => g (L y)) x v w
    = hessian g (L x) (L v) (L w) := by
  classical
  -- Let f := g ∘ L.
  let f : E → ℝ := fun y => g (L y)

  -- Hessians as second derivatives
  have hf :
      hessian f x v w
        = (fderiv ℝ (fun y : E => fderiv ℝ f y) x v) w := rfl
  have hg_hess :
      hessian g (L x) (L v) (L w)
        = (fderiv ℝ (fun z : F => fderiv ℝ g z) (L x) (L v)) (L w) := rfl

  -- 1st derivative of f via chain rule
  have h_fderiv :
      ∀ y, fderiv ℝ f y = (fderiv ℝ g (L y)).comp L := by
    intro y
    have hgd : DifferentiableAt ℝ g (L y) := hg1 y
    simpa [f] using fderiv_compCLM (g := g) (L := L) (x := y) hgd

  -- define h(y) = fderiv g (L y)
  let h : E → F →L[ℝ] ℝ := fun y => fderiv ℝ g (L y)

  have h_fd :
      ∀ y, fderiv ℝ f y = (h y).comp L := by
    intro y; simpa [h] using h_fderiv y

  -- derivative of h at x
  have hh_deriv :
      fderiv ℝ h x = (fderiv ℝ (fun z : F => fderiv ℝ g z) (L x)).comp L := by
    have hgd2 : DifferentiableAt ℝ (fun z : F => fderiv ℝ g z) (L x) := hg2
    simpa [h] using
      fderiv_compCLM (g := fun z : F => fderiv ℝ g z) (L := L) (x := x) hgd2

  have hh : HasFDerivAt h (fderiv ℝ h x) x := by
    -- h is definitionally (fun z => fderiv ℝ g z) ∘ L
    have h_eq : h = fun y => (fun z : F => fderiv ℝ g z) (L y) := rfl
    rw [h_eq]
    -- Now we need to show fderiv matches what comp gives us
    have hcomp := hg2.hasFDerivAt.comp x L.hasFDerivAt
    convert hcomp using 2
  -- second derivative of f: derivative of y ↦ fderiv f y
  have h_second :
      fderiv ℝ (fun y : E => fderiv ℝ f y) x v
        = (fderiv ℝ (fun z : F => fderiv ℝ g z) (L x) (L v)).comp L := by
    -- rewrite fderiv f via h_fd
    have h_eq :
        fderiv ℝ (fun y : E => fderiv ℝ f y) x v
          = fderiv ℝ (fun y : E => (h y).comp L) x v := by
      have : (fun y : E => fderiv ℝ f y) = fun y : E => (h y).comp L := by
        funext y; simp [h_fd y]
      simp [this]
    have h_post :
        fderiv ℝ (fun y : E => (h y).comp L) x v
          = (fderiv ℝ h x v).comp L :=
      fderiv_comp_rightCLM h L x v hh
    -- compute fderiv h x v using hh_deriv
    have h_pre :
        fderiv ℝ h x v
          = fderiv ℝ (fun z : F => fderiv ℝ g z) (L x) (L v) := by
      -- apply both sides of hh_deriv to v
      have := congrArg (fun (T : E →L[ℝ] F →L[ℝ] ℝ) => T v) hh_deriv
      -- RHS simplifies: ((fderiv ... (L x)).comp L) v = (fderiv ... (L x)) (L v)
      simpa using this
    calc
      fderiv ℝ (fun y : E => fderiv ℝ f y) x v
          = fderiv ℝ (fun y : E => (h y).comp L) x v := h_eq
      _   = (fderiv ℝ h x v).comp L := h_post
      _   = (fderiv ℝ (fun z : F => fderiv ℝ g z) (L x) (L v)).comp L := by
              simp [h_pre]

  -- finally evaluate at w and compare Hessians
  calc
    hessian f x v w
        = (fderiv ℝ (fun y : E => fderiv ℝ f y) x v) w := hf
    _   = ((fderiv ℝ (fun z : F => fderiv ℝ g z) (L x) (L v)).comp L) w := by
            simp [h_second]
    _   = (fderiv ℝ (fun z : F => fderiv ℝ g z) (L x) (L v)) (L w) := rfl
    _   = hessian g (L x) (L v) (L w) := (hg_hess).symm

/-
/--
Chain rule for the Hessian under a continuous linear map `L : E →L[ℝ] F`.

This version is purely formal: it relates the second Fréchet derivatives of `g ∘ L`
and `g` via the chain rule for `fderiv`. Regularity assumptions (`ContDiffAt ℝ 2 g`)
should be expressed in separate lemmas.
-/
lemma hessian_comp_linear'
    (g : F → ℝ) (L : E →L[ℝ] F) (x v w : E) :
    hessian (fun y : E => g (L y)) x v w
      = hessian g (L x) (L v) (L w) := by
  classical
  -- Let `f := g ∘ L`.
  let f : E → ℝ := fun y => g (L y)
  -- Unfold Hessians in terms of second Fréchet derivatives.
  have hf :
      hessian f x v w
        = (fderiv ℝ (fun y : E => fderiv ℝ f y) x v) w := rfl
  have hg_hess :
      hessian g (L x) (L v) (L w)
        = (fderiv ℝ (fun z : F => fderiv ℝ g z) (L x) (L v)) (L w) := rfl
  -- Rewrite the first derivative of `f` using `fderiv_compCLM'`.
  have h_fderiv :
      ∀ y, fderiv ℝ f y = (fderiv ℝ g (L y)).comp L := by
    intro y
    -- you already have `fderiv_compCLM'` for `g : F → ℝ` and `L : E →L[ℝ] F`
    -- once you assume differentiability of `g` at `L y`.
    -- For the formal identity, we treat this as the intended form.
    -- TODO: replace by a genuine chain-rule lemma `fderiv_compCLM'` when available.
    admit
  -- Define `h : E → F →L[ℝ] ℝ` and express `fderiv f` via `h`.
  let h : E → F →L[ℝ] ℝ := fun y => fderiv ℝ g (L y)
  have h_fd :
      ∀ y, fderiv ℝ f y = (h y).comp L := by
    intro y
    simpa [f, h] using h_fderiv y
  -- Second derivative of `f` at `x` in direction `v`:
  -- derivative of `y ↦ fderiv f y` at `x` applied to `v`.
  have h_second :
      fderiv ℝ (fun y : E => fderiv ℝ f y) x v
        = (fderiv ℝ (fun z : F => fderiv ℝ g z) (L x) (L v)).comp L := by
    -- Rewrite the outer `fderiv` using `h_fd` and your directional post‑composition lemma.
    admit
  -- Evaluate at `w` and use the two `hf` / `hg_hess` rewrites.
  calc
    hessian f x v w
        = (fderiv ℝ (fun y : E => fderiv ℝ f y) x v) w := hf
    _   = ((fderiv ℝ (fun z : F => fderiv ℝ g z) (L x) (L v)).comp L) w := by
            simpa [h_second]
    _   = (fderiv ℝ (fun z : F => fderiv ℝ g z) (L x) (L v)) (L w) := rfl
    _   = hessian g (L x) (L v) (L w) := (hg_hess).symm
    -/

/-- Specialization of the Hessian chain rule to a *linear isometry* (as a continuous linear map). -/
lemma hessian_comp_linearIsometry
    (g : F → ℝ) (e : E ≃ₗᵢ[ℝ] F) (x v w : E)
    (hg1 : ∀ y : E, DifferentiableAt ℝ g (e y))
    (hg2 : DifferentiableAt ℝ (fun z : F => fderiv ℝ g z) (e x)) :
    hessian (fun y : E => g (e y)) x v w
      = hessian g (e x) (e v) (e w) := by
  -- Just instantiate `hessian_comp_linear` with `L := (e : E →L[ℝ] F)`.
  simpa using
    (hessian_comp_linear (g := g) (L := (e : E →L[ℝ] F))
      (x := x) (v := v) (w := w)
      (hg1 := hg1) (hg2 := hg2))

/-- Diagonal version of the Hessian chain rule under a linear isometry. -/
lemma hessian_comp_linearIsometry_diag
    (g : F → ℝ) (e : E ≃ₗᵢ[ℝ] F) (x v : E)
    (hg1 : ∀ y : E, DifferentiableAt ℝ g (e y))
    (hg2 : DifferentiableAt ℝ (fun z : F => fderiv ℝ g z) (e x)) :
    hessian (fun y : E => g (e y)) x v v
      = hessian g (e x) (e v) (e v) :=
  hessian_comp_linearIsometry g e x v v hg1 hg2

end ChainRule

/-! ### Laplacian invariance under linear isometries -/

section LaplacianIsometry

open scoped BigOperators InnerProductSpace

variable
  {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/--
Laplacian invariance under a linear isometry: if `e : E ≃ₗᵢ[ℝ] F` is a linear isometry and
`f : F → ℝ`, then
\[
  \Delta (f ∘ e)(x) = \Delta f(e x).
\]
-/
/-
If `e : E ≃ₗᵢ[ℝ] F` is a linear isometry and `f : F → ℝ`, then the Laplacian of the pullback
`x ↦ f (e x)` at `x` equals the Laplacian of `f` at `e x`.

Mathematically: `Δ(f ∘ e)(x) = Δf(e x)`.
-/
lemma laplacian_comp_linearIsometryEquiv
    (e : E ≃ₗᵢ[ℝ] F) (f : F → ℝ) (x : E)
    (hf1 : ∀ y : E, DifferentiableAt ℝ f (e y))
    (hf2 : DifferentiableAt ℝ (fun z : F => fderiv ℝ f z) (e x)) :
    laplacian (fun y : E => f (e y)) x = laplacian f (e x) := by
  classical
  -- Choose an orthonormal basis on `E`.
  let bE := stdOrthonormalBasis ℝ E
  -- Its image under `e` is an orthonormal basis on `F`.
  let bF : OrthonormalBasis _ ℝ F := bE.map e
  -- Express both Laplacians in terms of these bases.
  have hLap_comp :
      laplacian (fun y : E => f (e y)) x
        = ∑ i, hessian (fun y : E => f (e y)) x (bE i) (bE i) :=
    laplacian_eq_sum_orthonormal (b := bE) _ _
  have hLap_f :
      laplacian f (e x)
        = ∑ i, hessian f (e x) (bF i) (bF i) := by
    simpa using
      (laplacian_eq_sum_orthonormal (b := bF) (f := f) (x := e x))
  -- Use the Hessian chain rule along `e` on each diagonal entry.
  have h_diag :
      ∀ i, hessian (fun y : E => f (e y)) x (bE i) (bE i)
            = hessian f (e x) (bF i) (bF i) := by
    intro i
    -- `bF i = e (bE i)` by definition of `map`.
    have hbFi : bF i = e (bE i) := by
      simp [bF]
    -- Chain rule on the diagonal, with differentiability hypotheses `hf1`, `hf2`.
    -- Note: `hf1` and `hf2` match exactly the parameters of `hessian_comp_linearIsometry_diag`.
    rw [hbFi, hessian_comp_linearIsometry_diag (g := f) e x (bE i) hf1 hf2]
  -- Summing over `i` gives the result.
  calc
    laplacian (fun y : E => f (e y)) x
        = ∑ i, hessian (fun y : E => f (e y)) x (bE i) (bE i) := hLap_comp
    _ = ∑ i, hessian f (e x) (bF i) (bF i) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simpa using h_diag i
    _ = laplacian f (e x) := hLap_f.symm

end LaplacianIsometry




end Isometry

/-! ## Harmonic functions -/

section Harmonic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open scoped Topology
open InnerProductSpace Filter

/-- A scalar field `f : E → ℝ` is harmonic on a set `s` if it is twice continuously
Fréchet‑differentiable at every point of `s` and its Laplacian vanishes there.
This is an alias for mathlib's `HarmonicOnNhd`. -/
abbrev IsHarmonicOn (f : E → ℝ) (s : Set E) : Prop :=
  HarmonicOnNhd f s

/-- Being harmonic is a local property that is monotone with respect to the set. -/
lemma IsHarmonicOn.mono {f : E → ℝ} {s t : Set E}
    (h : IsHarmonicOn f t) (hst : s ⊆ t) :
    IsHarmonicOn f s :=
  HarmonicOnNhd.mono h hst

/-- Extract pointwise Laplacian vanishing from harmonicity. -/
lemma IsHarmonicOn.laplacian_eq_zero {f : E → ℝ} {s : Set E} {x : E}
    (h : IsHarmonicOn f s) (hx : x ∈ s) :
    laplacian f x = 0 := by
  have hHarm := h x hx
  exact Filter.EventuallyEq.eq_of_nhds hHarm.2

/-- A constant function is harmonic on any set. -/
lemma IsHarmonicOn_const (c : ℝ) (s : Set E) :
    IsHarmonicOn (fun _ => c) s := by
  intro x _
  refine ⟨contDiffAt_const, ?_⟩
  -- Laplacian of constant is 0
  apply Filter.eventually_of_mem (Filter.univ_mem)
  intro y
  simp [laplacian_const]

/-- An affine function is harmonic on any set. -/
lemma IsHarmonicOn_linear_add_const (L : E →L[ℝ] ℝ) (c : ℝ) (s : Set E) :
    IsHarmonicOn (fun x => L x + c) s := by
  intro x _
  refine ⟨?_, ?_⟩
  · apply ContDiffAt.add
    · apply L.contDiff.contDiffAt
    · apply contDiffAt_const
  · apply Filter.eventually_of_mem (Filter.univ_mem)
    intro y
    simp [laplacian_linear_add_const]

end Harmonic

section GradDiv
open scoped Gradient RealInnerProductSpace

open InnerProductSpace
open scoped BigOperators InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Just a synonym for the mathlib gradient in the real Hilbert setting. -/
abbrev grad (f : E → ℝ) (x : E) : E := ∇ f x

/-- Divergence of a vector field, defined as the trace of its Fréchet derivative. -/
def divergence (F : E → E) (x : E) : ℝ :=
  let b := stdOrthonormalBasis ℝ E
  ∑ i, ⟪fderiv ℝ F x (b i), b i⟫

/-- Characterization of the gradient via the inner product. -/
lemma inner_grad (f : E → ℝ) (x v : E) :
    ⟪grad f x, v⟫ = fderiv ℝ f x v := by
  -- `grad` is the real gradient, defined via `toDual.symm (fderiv f x)`.
  unfold grad gradient
  -- Riesz representation: `⟪(toDual ℝ E).symm ℓ, v⟫ = ℓ v`.
  simp

/-- The Laplacian is the divergence of the gradient.

We need a `C²` hypothesis to justify the chain rule for the Fréchet derivative:
both sides are defined unconditionally, but equality is only guaranteed when
the relevant derivatives exist. -/
lemma laplacian_eq_divergence_grad
    (f : E → ℝ) (x : E) (hf : ContDiffAt ℝ 2 f x) :
    laplacian f x = divergence (fun y => grad f y) x := by
  classical
  -- Work with the standard orthonormal basis.
  let b := stdOrthonormalBasis ℝ E

  -- First, rewrite both sides as sums over `b`.
  have h_lap :
      laplacian f x = ∑ i, hessian f x (b i) (b i) :=
    laplacian_eq_sum_orthonormal (b := b) f x

  have h_div :
      divergence (fun y => grad f y) x
        = ∑ i, ⟪fderiv ℝ (fun y => grad f y) x (b i), b i⟫ := by
    simp [divergence, b]

  -- We reduce to showing equality termwise in the sum.
  have h_diag :
      ∀ i, hessian f x (b i) (b i)
            = ⟪fderiv ℝ (fun y => grad f y) x (b i), b i⟫ := by
    intro i
    -- Define `g := grad f` and the scalar function `h(y) = ⟪g y, b i⟫`.
    let g : E → E := fun y => grad f y
    let h : E → ℝ := fun y => ⟪g y, b i⟫

    -- (1) `h` is `C²` at `x` as a composition of smooth maps, since `f` is `C²`.
    have hg : ContDiffAt ℝ 1 g x := by
      -- `f` is `C²`, so `y ↦ fderiv ℝ f y` is `C¹` at `x`.
      have hf' : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
        (ContDiffAt.fderiv_right (x₀ := x) (f := f) (n := (2 : ℕ∞))
          (m := (1 : ℕ∞)) hf (by norm_cast))  -- 1 + 1 ≤ 2
      -- The inverse Riesz isometry `toDual.symm` is `C^∞`.
      have h_outer :
          ContDiffAt ℝ 1 ((InnerProductSpace.toDual ℝ E).symm) (fderiv ℝ f x) :=
        (InnerProductSpace.toDual ℝ E).symm.contDiff.contDiffAt
      -- Compose `toDual.symm` with `fderiv ℝ f`.
      have h_comp :
          ContDiffAt ℝ 1
            (fun y => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f y)) x :=
        h_outer.comp x hf'
      -- This composite is exactly `g`.
      simpa [g, grad, gradient] using h_comp

    have hh : ContDiffAt ℝ 1 h x := by
      -- `h` is the inner product with a fixed vector applied to `g y`.
      -- First, `z ↦ ⟪z, b i⟫` is `C^∞`, hence `C¹`.
      have hCLM_top : ContDiffAt ℝ ⊤ (fun z : E => ⟪z, b i⟫) (g x) := by
        -- Take `f := id`, `g₀ := fun _ => b i` and use `ContDiffAt.inner`.
        have hf : ContDiffAt ℝ ⊤ (fun z : E => z) (g x) := contDiffAt_id
        have hg₀ : ContDiffAt ℝ ⊤ (fun _ : E => b i) (g x) := contDiffAt_const
        simpa using (hf.inner (𝕜 := ℝ) hg₀)
      -- Downgrade from `C^∞` to `C¹`.
      have hCLM : ContDiffAt ℝ 1 (fun z : E => ⟪z, b i⟫) (g x) :=
        hCLM_top.of_le (by exact le_top)
      -- Now compose with `g`, which is `C¹` at `x`.
      exact hCLM.comp x hg

    -- (2) Derivative of `h` along `b i` via the Hessian:
    -- Using the definition of `hessian`, we have
    -- `fderiv h x (b i) = hessian f x (b i) (b i)`.
    have h₁ :
        fderiv ℝ h x (b i) = hessian f x (b i) (b i) := by
      -- Unfold `h` and `g`: `h y = ⟪grad f y, b i⟫ = ⟪(toDual.symm) (fderiv ℝ f y), b i⟫`.
      -- By the Riesz representation, this equals `(fderiv ℝ f y) ((toDual ℝ E) (b i))`.
      -- But `toDual (b i)` is the functional `⟨·, b i⟩`, so we can also work directly
      -- with the inner product derivative formula.
      -- The key identity is: for any linear functional `L : E →L[ℝ] ℝ`,
      -- `⟪(toDual.symm) L, v⟫ = L v`.
      have toDual_apply : ∀ (L : E →L[ℝ] ℝ) (v : E),
          ⟪(InnerProductSpace.toDual ℝ E).symm L, v⟫ = L v :=
        fun L v => by simp [InnerProductSpace.toDual_symm_apply]
      -- Now apply the chain rule to `g = (toDual.symm) ∘ (fderiv ℝ f)`.
      have hg_eq : g = (InnerProductSpace.toDual ℝ E).symm ∘ (fderiv ℝ f) := rfl
      -- The derivative of `g` at `x` is the composition of derivatives:
      -- `fderiv ℝ g x = (toDual.symm) ∘L (fderiv ℝ (fderiv ℝ f) x)`.
      have hg_diff : DifferentiableAt ℝ (fderiv ℝ f) x := by
        exact (ContDiffAt.fderiv_right (x₀ := x) (f := f) (n := (2 : ℕ∞))
          (m := (1 : ℕ∞)) hf (by norm_cast)).differentiableAt (by simp)
      have hg_fderiv :
          fderiv ℝ g x
            = (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
              (fderiv ℝ (fderiv ℝ f) x) := by
        rw [hg_eq]
        exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.comp_fderiv
      -- Now compute `fderiv ℝ h x (b i)`.
      -- `h y = ⟪g y, b i⟫`, so by the formula we already proved (h₂),
      -- we also have `fderiv ℝ h x (b i) = ⟪fderiv ℝ g x (b i), b i⟫`.
      -- Substitute the expression for `fderiv ℝ g x`:
      calc fderiv ℝ h x (b i)
          = ⟪fderiv ℝ g x (b i), b i⟫ := by
              -- This is what `h₂` will show (we prove it below).
              have hg_diff' : DifferentiableAt ℝ g x := hg.differentiableAt (by simp)
              have hconst : DifferentiableAt ℝ (fun _ : E => b i) x :=
                differentiableAt_const _
              simpa [h, fderiv_const] using
                fderiv_inner_apply ℝ hg_diff' hconst (b i)
        _ = ⟪(InnerProductSpace.toDual ℝ E).symm
              (fderiv ℝ (fderiv ℝ f) x (b i)), b i⟫ := by
              rw [hg_fderiv]
              rfl
        _ = (fderiv ℝ (fderiv ℝ f) x (b i)) (b i) :=
              toDual_apply _ _
        _ = hessian f x (b i) (b i) := by
              simp [hessian]

    -- (3) Derivative of `h` along `b i` via `fderiv g` and the inner product.
    have h₂ :
        fderiv ℝ h x (b i) = ⟪fderiv ℝ g x (b i), b i⟫ := by
      -- `h y = ⟪g y, b i⟫`. Use the general derivative formula for the inner product.
      have hg_diff : DifferentiableAt ℝ g x := by
        -- from `ContDiffAt ℝ 1 g x` we get differentiability since `1 ≤ 1`
        exact hg.differentiableAt (by simp)
      have hconst : DifferentiableAt ℝ (fun _ : E => b i) x :=
        differentiableAt_const _
      have h1 :=
        fderiv_inner_apply ℝ
          hg_diff hconst (b i)
      -- `h1` says:
      -- `fderiv ℝ (fun t => ⟪g t, b i⟫) x (b i)
      --    = ⟪g x, 0⟫ + ⟪fderiv ℝ g x (b i), b i⟫`.
      -- Simplify RHS and rewrite LHS as `fderiv ℝ h x (b i)`.
      simpa [h, fderiv_const] using h1

    -- Combine the two expressions for `fderiv h x (b i)`.
    aesop

  -- Sum the diagonal identities.
  calc
    laplacian f x
        = ∑ i, hessian f x (b i) (b i) := h_lap
    _   = ∑ i, ⟪fderiv ℝ (fun y => grad f y) x (b i), b i⟫ := by
            refine Finset.sum_congr rfl ?_
            intro i _
            exact h_diag i
    _   = divergence (fun y => grad f y) x := h_div.symm

end GradDiv

section ComplexHarmonic

open Complex
open InnerProductSpace

/-- At a point: the real part of an analytic function is harmonic
(i.e. its Laplacian vanishes). -/
lemma laplacian_re_of_analyticAt
    {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    laplacian (fun w : ℂ => (f w).re) z = 0 := by
  classical
  -- Mathlib: real part of an analytic map is harmonic on `ℂ`.
  have hHarm :
      InnerProductSpace.HarmonicAt
        (E := ℂ) (F := ℝ) (fun w : ℂ => (f w).re) z :=
    (AnalyticAt.harmonicAt_re (f := f) (x := z) hf)
  -- `HarmonicAt` says: `ContDiffAt ℝ 2` and Laplacian vanishes in a neighborhood.
  -- Evaluate the eventual equality at `z`.
  have hLap :
      (InnerProductSpace.laplacian (E := ℂ) (F := ℝ)
        (fun w : ℂ => (f w).re)) z = 0 :=
    Filter.EventuallyEq.eq_of_nhds hHarm.2
  -- Our `laplacian` is by definition the scalar Laplacian on `ℂ`.
  simpa [laplacian] using hLap

/-- At a point: the imaginary part of an analytic function is harmonic. -/
lemma laplacian_im_of_analyticAt
    {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    laplacian (fun w : ℂ => (f w).im) z = 0 := by
  classical
  have hHarm :
      InnerProductSpace.HarmonicAt
        (E := ℂ) (F := ℝ) (fun w : ℂ => (f w).im) z :=
    (AnalyticAt.harmonicAt_im (f := f) (x := z) hf)
  have hLap :
      (InnerProductSpace.laplacian (E := ℂ) (F := ℝ)
        (fun w : ℂ => (f w).im)) z = 0 :=
    Filter.EventuallyEq.eq_of_nhds hHarm.2
  simpa [laplacian] using hLap

/-- On a set: the real part of an analytic function is harmonic. -/
lemma isHarmonicOn_re_of_analyticOn
    {f : ℂ → ℂ} {s : Set ℂ} (hf : AnalyticOnNhd ℂ f s) :
    IsHarmonicOn (fun z => (f z).re) s := by
  intro z hz
  exact AnalyticAt.harmonicAt_re (hf z hz)

/-- On a set: the imaginary part of an analytic function is harmonic. -/
lemma isHarmonicOn_im_of_analyticOn
    {f : ℂ → ℂ} {s : Set ℂ} (hf : AnalyticOnNhd ℂ f s) :
    IsHarmonicOn (fun z => (f z).im) s := by
  intro z hz
  exact AnalyticAt.harmonicAt_im (hf z hz)

end ComplexHarmonic
