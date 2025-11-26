import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Riemann.RS.BWP.Laplacian

/-
Auxiliary complex-analytic calculus lemmas used in the Boundary Wedge Proof.

In this file we record:

* an equality-of-mixed-partials statement for scalar fields on `ℂ` viewed as a
  real vector space;
* first-order Cauchy–Riemann identities in Fréchet-derivative form;
* (to be extended) higher-order CR calculus lemmas.

These are the analytic inputs needed in later CR-calculus arguments: under
`C²` regularity, the Hessian at a point is symmetric, so second mixed partials
commute, and the real and imaginary parts of analytic maps satisfy the CR
equations at first order.
-/

noncomputable section

open scoped Topology

namespace Riemann.RS.BoundaryWedgeProof

open Complex ContinuousLinearMap

/-- **Equality of mixed partials on `ℂ` (as an `ℝ`‑vector space).**

Let `u : ℂ → ℝ` be a real‑valued scalar field, and assume that it is
Fréchet-differentiable over `ℝ` everywhere and that its derivative
`w ↦ fderiv ℝ u w` is differentiable at `z`.  Then the second derivative
`fderiv ℝ (fun w ↦ fderiv ℝ u w) z` (the Hessian at `z`) is symmetric, so the
mixed partials along the real and imaginary directions coincide:
\[
  D^2 u(z)[1, I] = D^2 u(z)[I, 1].
\]

In terms of Fréchet derivatives, this says that the bilinear map
`fderiv ℝ (fun w => fderiv ℝ u w) z` is symmetric on the pair of vectors
`1, I`. -/
lemma mixed_partials_eq
    (u : ℂ → ℝ) (z : ℂ)
    (hu₁ : Differentiable ℝ u)
    (hu₂ : DifferentiableAt ℝ (fun w : ℂ => fderiv ℝ u w) z) :
    ((fderiv ℝ (fun w : ℂ => fderiv ℝ u w) z) (1 : ℂ)) Complex.I
      =
    ((fderiv ℝ (fun w : ℂ => fderiv ℝ u w) z) Complex.I) (1 : ℂ) := by
  classical
  -- `f' w := fderiv ℝ u w`, `f'' := fderiv ℝ (fun w => fderiv ℝ u w) z`.
  let f' : ℂ → ℂ →L[ℝ] ℝ := fun w => fderiv ℝ u w
  let f'' : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
    fderiv ℝ (fun w : ℂ => fderiv ℝ u w) z

  -- Global differentiability of `u` supplies `HasFDerivAt u (f' w) w` for all `w`.
  have hf : ∀ w, HasFDerivAt u (f' w) w := by
    intro w
    have hdiff : DifferentiableAt ℝ u w := hu₁ w
    simpa [f'] using hdiff.hasFDerivAt

  -- Differentiability of `w ↦ fderiv u w` at `z` supplies the second derivative.
  have hx : HasFDerivAt f' f'' z := by
    simpa [f', f''] using (hu₂.hasFDerivAt)

  -- Symmetry of the second derivative over `ℝ`.
  have h_symm :=
    second_derivative_symmetric (𝕜 := ℝ) (f := u) (f' := f') (f'' := f'') (x := z)
      (hf := hf) (hx := hx) (1 : ℂ) Complex.I

  -- This is exactly the desired mixed-partials equality.
  simpa [f''] using h_symm

/-- For a complex‑differentiable map `G : ℂ → ℂ`, the ℝ‑Fréchet derivative at `z`
is multiplication by the complex derivative `deriv G z`. -/
lemma hasFDerivAt_of_hasDerivAt_complex
  {G : ℂ → ℂ} {z : ℂ}
  (hG : HasDerivAt G (deriv G z) z) :
  HasFDerivAt G (deriv G z • (1 : ℂ →L[ℝ] ℂ)) z :=
hG.complexToReal_fderiv

/-- First‑order Cauchy–Riemann identities for a complex map `G : ℂ → ℂ` at `z`.

Write `G = u + i·v` in real coordinates, so that `u = Re ∘ G` and `v = Im ∘ G`.
If `G` has complex derivative `G'` at `z`, then the real Fréchet derivatives of
`u` and `v` at `z` satisfy the classical CR identities:
\[
  u_x = (\Re G'),\quad u_y = -(\Im G'),\quad
  v_x = (\Im G'),\quad v_y = (\Re G').
\]
-/
lemma CR_first_order_at
  (G : ℂ → ℂ) (z : ℂ)
  (hG : HasDerivAt G (deriv G z) z) :
  (fderiv ℝ (fun w : ℂ => (G w).re) z (1 : ℂ)) = (deriv G z).re ∧
  (fderiv ℝ (fun w : ℂ => (G w).re) z Complex.I) = -(deriv G z).im ∧
  (fderiv ℝ (fun w : ℂ => (G w).im) z (1 : ℂ)) = (deriv G z).im ∧
  (fderiv ℝ (fun w : ℂ => (G w).im) z Complex.I) = (deriv G z).re := by
  classical
  -- ℝ‑Fréchet derivative of G at z
  have hF :
      HasFDerivAt G (deriv G z • (1 : ℂ →L[ℝ] ℂ)) z :=
    hasFDerivAt_of_hasDerivAt_complex hG

  -- Derivative of Re ∘ G at z
  have hRe :
      HasFDerivAt (fun w : ℂ => (G w).re)
        (Complex.reCLM.comp (deriv G z • (1 : ℂ →L[ℝ] ℂ))) z :=
    (Complex.reCLM.hasFDerivAt.comp z hF)

  -- Derivative of Im ∘ G at z
  have hIm :
      HasFDerivAt (fun w : ℂ => (G w).im)
        (Complex.imCLM.comp (deriv G z • (1 : ℂ →L[ℝ] ℂ))) z :=
    (Complex.imCLM.hasFDerivAt.comp z hF)

  -- Turn these into equalities for fderiv
  have hRe_fderiv :
      fderiv ℝ (fun w : ℂ => (G w).re) z
        = Complex.reCLM.comp (deriv G z • (1 : ℂ →L[ℝ] ℂ)) :=
    hRe.fderiv
  have hIm_fderiv :
      fderiv ℝ (fun w : ℂ => (G w).im) z
        = Complex.imCLM.comp (deriv G z • (1 : ℂ →L[ℝ] ℂ)) :=
    hIm.fderiv

  -- Evaluate at 1 and I using the explicit form of the linear maps
  have hRe_1 :
      fderiv ℝ (fun w : ℂ => (G w).re) z (1 : ℂ)
        = (deriv G z).re := by
    have := congrArg (fun L => L (1 : ℂ)) hRe_fderiv
    -- (reCLM ∘ (a • 1)) 1 = Re (a * 1) = Re a
    simpa [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, one_smul, Complex.reCLM_apply,
      Complex.mul_re, Complex.one_re, Complex.one_im] using this

  have hRe_I :
      fderiv ℝ (fun w : ℂ => (G w).re) z Complex.I
        = -(deriv G z).im := by
    have := congrArg (fun L => L Complex.I) hRe_fderiv
    -- (reCLM ∘ (a • 1)) I = Re (a * I) = -Im a
    have hI :
        (Complex.reCLM.comp
          (deriv G z • (1 : ℂ →L[ℝ] ℂ))) Complex.I
          = - (deriv G z).im := by
      -- Compute explicitly: a • 1 sends v ↦ a * v, then take real part at v = I.
      simp [ContinuousLinearMap.comp_apply, Complex.reCLM_apply,
        Complex.mul_re, Complex.I_re, Complex.I_im]
    simpa [hI] using this

  have hIm_1 :
      fderiv ℝ (fun w : ℂ => (G w).im) z (1 : ℂ)
        = (deriv G z).im := by
    have := congrArg (fun L => L (1 : ℂ)) hIm_fderiv
    -- (imCLM ∘ (a • 1)) 1 = Im (a * 1) = Im a
    simpa [ContinuousLinearMap.comp_apply,
      one_smul, Complex.imCLM_apply,
      Complex.mul_im, Complex.one_re, Complex.one_im] using this

  have hIm_I :
      fderiv ℝ (fun w : ℂ => (G w).im) z Complex.I
        = (deriv G z).re := by
    have := congrArg (fun L => L Complex.I) hIm_fderiv
    -- (imCLM ∘ (a • 1)) I = Im (a * I) = Re a
    have hI :
        (Complex.imCLM.comp
          (deriv G z • (1 : ℂ →L[ℝ] ℂ))) Complex.I
          = (deriv G z).re := by
      simp [ContinuousLinearMap.comp_apply, Complex.imCLM_apply,
        Complex.mul_im, Complex.I_re, Complex.I_im]
    simpa [hI] using this

  exact ⟨hRe_1, hRe_I, hIm_1, hIm_I⟩

/-- First-order CR identities applied to the complex derivative `G'`.

This is just `CR_first_order_at` specialized to the map `G' := deriv G`. -/
lemma CR_first_order_at_deriv
  (G : ℂ → ℂ) (z : ℂ)
  (hG' : HasDerivAt (fun w : ℂ => deriv G w) (deriv (fun w : ℂ => deriv G w) z) z) :
  (fderiv ℝ (fun w : ℂ => (deriv G w).re) z (1 : ℂ)) = (deriv (deriv G) z).re ∧
  (fderiv ℝ (fun w : ℂ => (deriv G w).re) z Complex.I) = -(deriv (deriv G) z).im ∧
  (fderiv ℝ (fun w : ℂ => (deriv G w).im) z (1 : ℂ)) = (deriv (deriv G) z).im ∧
  (fderiv ℝ (fun w : ℂ => (deriv G w).im) z Complex.I) = (deriv (deriv G) z).re := by
  -- Apply `CR_first_order_at` to the function `G' := deriv G`.
  simpa using
    (CR_first_order_at (G := fun w : ℂ => deriv G w) (z := z)
      (hG := hG'))

/-- **Second‑order CR identity at the Hessian level (vertical direction).**

At a point `z`, for an analytic map `G : ℂ → ℂ`, the Hessian entry of
`u := Re ∘ G` in the `I,I`‑direction equals minus the `I`‑directional derivative
of `Im (G')`:

\[
  D^2 u(z)[I,I] = - D(\Im G')(z)[I].
\]

In Fréchet terms:
\[
  (D(Du)(z)\,I)\,I = - D(\Im G')(z)\,I.
\]
-/
lemma CR_second_order_Hessian_identity
  (G : ℂ → ℂ) (z : ℂ)
  (hG : AnalyticAt ℂ G z)
  (hH₁ : Differentiable ℝ (fun w : ℂ => (G w).re))
  (hH₂ :
    DifferentiableAt ℝ
      (fun w : ℂ => fderiv ℝ (fun t : ℂ => (G t).re) w) z) :
  ((fderiv ℝ (fun w : ℂ => fderiv ℝ (fun t : ℂ => (G t).re) w) z) Complex.I) Complex.I
    =
  - (fderiv ℝ (fun w : ℂ => (deriv G w).im) z) Complex.I := by
  classical
  -- `H := Re ∘ G`
  let H : ℂ → ℝ := fun w => (G w).re
  have hH₁' : Differentiable ℝ H := hH₁
  have hH₂' :
      DifferentiableAt ℝ (fun w : ℂ => fderiv ℝ H w) z := by
    simpa [H] using hH₂

  --------------------------------------------------------------------
  -- Step 1: identify the Hessian entry along `I,I` as the directional
  -- derivative of the `I`‑slice `w ↦ ∂H/∂I(w)` in direction `I`.
  --------------------------------------------------------------------
  -- CLM‑valued map of first derivatives
  let g : ℂ → (ℂ →L[ℝ] ℝ) := fun w => fderiv ℝ H w
  have hg_diff : DifferentiableAt ℝ g z := hH₂'
  -- Scalar slice: `I`‑directional derivative of `H`
  let uI : ℂ → ℝ := fun w => g w Complex.I
  -- By definition of the Hessian,
  have h_hess :
      ((fderiv ℝ (fun w : ℂ => fderiv ℝ H w) z) Complex.I) Complex.I
        = fderiv ℝ uI z Complex.I := by
    -- Use the CLM evaluation chain rule along the line in direction `I`.
    -- View `uI w = (g w) (const_I w)`, where `const_I` is constant `I`.
    let c : ℂ → (ℂ →L[ℝ] ℝ) := g
    let u : ℂ → ℂ := fun _ => Complex.I
    have hc : DifferentiableAt ℝ c z := hg_diff
    have hu : DifferentiableAt ℝ u z := differentiableAt_const _
    have h_clm :=
      (hc.hasFDerivAt.clm_apply hu.hasFDerivAt).fderiv
    -- `h_clm` is the Fréchet version of `deriv_clm_apply`.
    -- Evaluate both sides at `Complex.I`.
    have := congrArg (fun (L : ℂ →L[ℝ] ℝ) => L Complex.I) h_clm
    -- On the LHS we recover the Hessian entry; on the RHS `fderiv uI z`.
    -- Unfold `c`, `u`, `g`, `uI`.
    simpa [c, u, g, uI] using this.symm

  --------------------------------------------------------------------
  -- Step 2: use the first‑order CR identities along the vertical line
  -- to identify `uI` with `- Im(G')`, then take the derivative.
  --------------------------------------------------------------------
  -- Analyticity implies complex differentiability near `z`.
  have hG_ev :
      ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ G w :=
    (analyticAt_iff_eventually_differentiableAt (f := G) (c := z)).1 hG
  -- On that neighborhood, CR first‑order identities hold at each `w`.
  have h_CR_event :
      ∀ᶠ w in 𝓝 z,
        uI w = - (deriv G w).im := by
    refine hG_ev.mono ?_
    intro w hw
    -- `HasDerivAt` at `w`
    have hHw : HasDerivAt G (deriv G w) w :=
      hw.hasDerivAt
    -- Apply the pointwise CR lemma at `w`.
    obtain ⟨_, hUy, _, _⟩ :=
      CR_first_order_at (G := G) (z := w) (hG := hHw)
    -- `hUy : fderiv ℝ H w I = -(deriv G w).im`
    have : uI w = fderiv ℝ H w Complex.I := rfl
    simpa [H, uI, this] using hUy
  -- `uI` and `-Im(G')` agree in a neighborhood, hence have the same derivative at `z`.
  have h_deriv_eq :
      fderiv ℝ uI z = fderiv ℝ (fun w : ℂ => - (deriv G w).im) z := by
    refine Filter.EventuallyEq.fderiv_eq ?_
    -- equality as functions near `z`
    exact h_CR_event
  -- Evaluate both sides at the direction `I`.
  have h_dir :
      fderiv ℝ uI z Complex.I
        = fderiv ℝ (fun w : ℂ => - (deriv G w).im) z Complex.I := by
    have := congrArg (fun L => L Complex.I) h_deriv_eq
    simpa using this

  --------------------------------------------------------------------
  -- Step 3: identify the RHS derivative via linearity and conclude.
  --------------------------------------------------------------------
  have h_rhs :
      fderiv ℝ (fun w : ℂ => - (deriv G w).im) z Complex.I
        = - (fderiv ℝ (fun w : ℂ => (deriv G w).im) z) Complex.I := by
    -- derivative of `-F` is `-` derivative of `F`
    simp

  calc
    ((fderiv ℝ (fun w : ℂ => fderiv ℝ (fun t : ℂ => (G t).re) w) z)
        Complex.I) Complex.I
        = fderiv ℝ uI z Complex.I := by
            simpa [H, g, uI] using h_hess
    _   = fderiv ℝ (fun w : ℂ => - (deriv G w).im) z Complex.I := h_dir
    _   = - (fderiv ℝ (fun w : ℂ => (deriv G w).im) z) Complex.I := h_rhs

end Riemann.RS.BoundaryWedgeProof
