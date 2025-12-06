import Riemann.Mathlib.Analysis.Complex.DeBranges.Space
import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna.Space
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib
import PrimeNumberTheoremAnd
import StrongPNT

/-!
# Reproducing Kernel for de Branges Spaces

This file defines the reproducing kernel `K(w, z)` for a de Branges space `B(E)` and proves
its reproducing property: for every `F ∈ B(E)`, `⟨F, K(·, w)⟩ = F(w)`.

The kernel is defined by:
`K(w, z) = (E(z)E#(w̄) - E#(z)E(w̄)) / (2πi(w̄ - z))`
with the appropriate value at the removable singularity `z = w̄`.

## Main definitions

* `DeBranges.kernel`: The function `K(w, z)`.
* `DeBranges.kernel_in_space`: Proof that `z ↦ K(w, z)` belongs to `Space E`.
* `DeBranges.reproducing_property`: Proof that `⟨F, K(·, w)⟩ = F(w)`.

-/

open Complex Real MeasureTheory Filter Topology Function Metric Set
open scoped Complex.ConjugateReflection BigOperators ENNReal Topology InnerProductSpace RealInnerProductSpace

variable (E : HermiteBiehlerFunction)

namespace DeBranges

/-- The numerator of the reproducing kernel `K(w, z)`. -/
noncomputable def kernelNum (w z : ℂ) : ℂ :=
  E z * (E#) (star w) - (E#) z * E (star w)

/-- The denominator of the reproducing kernel `K(w, z)` (without the `2πi` factor). -/
noncomputable def kernelDen (w z : ℂ) : ℂ :=
  star w - z

/-- The reproducing kernel `K(w, z)` associated to the de Branges function `E`.
It is defined as `(E(z)E#(w̄) - E#(z)E(w̄)) / (2πi(w̄ - z))`.
At the removable singularity `z = w̄`, it takes the limit value determined by the derivatives. -/
noncomputable def kernel (w z : ℂ) : ℂ :=
  if z = star w then
    ((deriv E (star w)) * (E#) (star w) - (deriv (E#) (star w)) * E (star w)) / (-2 * π * Complex.I)
  else
    kernelNum E w z / (2 * π * Complex.I * kernelDen w z)

lemma kernelNum_deriv (w : ℂ) :
    deriv (fun z => kernelNum E w z) (star w) =
    deriv E (star w) * (E#) (star w) - deriv (E#) (star w) * E (star w) := by
  simp only [kernelNum]
  have h1 := E.entire.differentiableAt (x := star w).hasDerivAt
  have h2 := (Complex.ConjugateReflection.differentiable_C E.entire).differentiableAt (x := star w).hasDerivAt
  apply HasDerivAt.deriv
  exact (h1.mul_const _).sub (h2.mul_const _)

lemma kernelDen_deriv (w : ℂ) :
    deriv (fun z => kernelDen w z) (star w) = -1 := by
  simp only [kernelDen]
  apply HasDerivAt.deriv
  convert (hasDerivAt_const (star w) (star w)).sub (hasDerivAt_id (star w)) using 1
  rw [zero_sub]

/-- The kernel function `z ↦ K(w, z)` is entire. -/
lemma kernel_entire (w : ℂ) : Differentiable ℂ (fun z => kernel E w z) := by
  let f := fun z => kernelNum E w z / (2 * π * Complex.I * kernelDen w z)
  let c := star w
  let limit_val := ((deriv E c) * (E#) c - (deriv (E#) c) * E c) / (-2 * π * Complex.I)

  -- We claim `kernel` is the extension of `f` with `limit_val` at `c`.
  have h_eq : ∀ z, kernel E w z = update f c limit_val z := by
    intro z
    unfold kernel update
    split_ifs with h
    · subst h; rfl
    · rfl
  rw [funext h_eq]

  -- Apply removable singularity theorem.
  -- Condition 1: Differentiable on punctured neighborhood.
  have h_diff_away : DifferentiableOn ℂ f {z | z ≠ c} := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    unfold f kernelNum kernelDen
    apply DifferentiableAt.div
    · apply DifferentiableAt.sub
      · apply DifferentiableAt.mul (E.entire.differentiableAt) (differentiableAt_const _)
      · apply DifferentiableAt.mul ((Complex.ConjugateReflection.differentiable_C E.entire).differentiableAt) (differentiableAt_const _)
    · apply DifferentiableAt.mul (differentiableAt_const _)
      apply DifferentiableAt.sub (differentiableAt_const _) differentiableAt_id
    · rw [mul_ne_zero_iff]
      constructor
      · simp [Complex.I_ne_zero, pi_ne_zero]
      · simp [sub_eq_zero]; exact fun a ↦ hz (id (Eq.symm a))

  -- Condition 2: Continuous at c (limit exists).
  -- We show lim_{z->c} f(z) = limit_val using derivatives.
  have h_lim : Tendsto f (𝓝[≠] c) (𝓝 limit_val) := by
    -- Simplify f
    have h_f_eq : ∀ᶠ z in 𝓝[≠] c, f z = slope (fun z => kernelNum E w z) c z /
                                      slope (fun z => 2 * π * Complex.I * kernelDen w z) c z := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [slope, f]
      have h_num_c : kernelNum E w c = 0 := by
        simp [kernelNum, c]
        ring
      have h_den_c : 2 * π * Complex.I * kernelDen w c = 0 := by simp [kernelDen, c]
      rw [h_num_c, h_den_c]
      simp only [vsub_eq_sub, sub_zero, smul_eq_mul]
      rw [mul_div_mul_left]
      exact inv_ne_zero (sub_ne_zero.mpr hz)

    refine (tendsto_congr' h_f_eq).mpr ?_

    -- We prove limit is ratio of derivatives
    have h_den_deriv : deriv (fun z ↦ 2 * ↑π * Complex.I * kernelDen w z) c = 2 * ↑π * Complex.I * (-1) := by
      rw [deriv_const_mul]
      · rw [kernelDen_deriv]
      · exact (differentiableAt_const _).sub differentiableAt_id

    have h_num_deriv_eq : deriv (fun z ↦ kernelNum E w z) c = deriv E c * E# c - deriv E# c * E c := by
      rw [kernelNum_deriv]

    have : limit_val = (deriv (fun z ↦ kernelNum E w z) c) / (deriv (fun z ↦ 2 * ↑π * Complex.I * kernelDen w z) c) := by
      rw [h_den_deriv, h_num_deriv_eq]
      simp only [limit_val]
      ring
    rw [this]
    apply Tendsto.div
    · apply hasDerivAt_iff_tendsto_slope.mp
      let K1 := E# c
      let K2 := E c
      have h1 : HasDerivAt E (deriv E c) c := E.entire.differentiableAt.hasDerivAt
      have h2 : HasDerivAt E# (deriv E# c) c := (Complex.ConjugateReflection.differentiable_C E.entire).differentiableAt.hasDerivAt
      convert (h1.mul_const K1).sub (h2.mul_const K2) using 1
    · apply hasDerivAt_iff_tendsto_slope.mp
      let K := 2 * π * Complex.I
      have h_den : HasDerivAt (kernelDen w) (-1) c := by
        convert (hasDerivAt_const c c).sub (hasDerivAt_id c) using 1
        aesop
      convert h_den.const_mul K using 1
    · simp [h_den_deriv, Complex.I_ne_zero, pi_ne_zero]

  intro z
  if h : z = c then
    rw [h]
    -- Prove differentiability at c using removable singularity on a ball
    let s := ball c 1
    have hc_mem : s ∈ 𝓝 c := ball_mem_nhds c zero_lt_one
    have hd : DifferentiableOn ℂ f (s \ {c}) := h_diff_away.mono (fun x hx => hx.2)

    -- Use the theorem
    have H := differentiableOn_update_limUnder_of_isLittleO hc_mem hd
    -- Prove the little o condition
    have ho : (fun z => f z - f c) =o[𝓝[≠] c] fun z => (z - c)⁻¹ := by
      refine Asymptotics.isLittleO_of_tendsto' ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with z hz
        intro h
        exfalso
        apply inv_ne_zero (sub_ne_zero.mpr hz) h
      · -- show `(f z - f c) / (z - c)⁻¹ → 0` as `z → c`, `z ≠ c`
        -- first, `‖z - c‖ → 0` on the punctured neighborhood
        have hz_tend : Tendsto (fun z : ℂ => ‖z - c‖) (𝓝[≠] c) (𝓝 0) := by
          -- `tendsto_norm_sub_self_nhdsNE c` gives convergence to `𝓝[>] 0`,
          -- which is stronger; we weaken it to `𝓝 0`.
          exact (tendsto_norm_sub_self_nhdsNE c).mono_right nhdsWithin_le_nhds
        -- then `‖(f z - f c) * (z - c)‖ → 0` by product of limits
        have h_prod_norm :
            Tendsto (fun z => ‖(f z - f c) * (z - c)‖) (𝓝[≠] c) (𝓝 0) := by
          have : Tendsto (fun z => ‖f z - f c‖ * ‖z - c‖) (𝓝[≠] c)
              (𝓝 (‖limit_val - f c‖ * 0)) :=
            (h_lim.sub_const _).norm.mul hz_tend
          simpa [norm_mul] using this
        -- convert back from norms to the complex-valued limit
        have h_prod :
            Tendsto (fun z => (f z - f c) * (z - c)) (𝓝[≠] c) (𝓝 0) :=
          (tendsto_zero_iff_norm_tendsto_zero).2 h_prod_norm
        -- finally rewrite division as multiplication
        simpa [div_eq_mul_inv, inv_inv] using h_prod
    -- Now apply H
    have H' := H ho
    rw [h_lim.limUnder_eq] at H'
    exact H'.differentiableAt hc_mem
  else
    -- Differentiability away from c
    refine DifferentiableAt.congr_of_eventuallyEq ((h_diff_away z h).differentiableAt (IsOpen.mem_nhds isOpen_ne h)) ?_
    filter_upwards [isOpen_ne.mem_nhds h] with u hu
    simp [update, hu]

/-- Value of the kernel on the diagonal `z = star w` (the removable singularity case). -/
@[simp] lemma kernel_diag (w : ℂ) :
    kernel E w (star w) =
      ((deriv E (star w)) * (E#) (star w) - (deriv (E#) (star w)) * E (star w)) /
        (-2 * π * Complex.I) := by
  -- This is just the `if_pos` branch in the definition.
  simp [kernel]

/-- Value of the kernel off the diagonal `z ≠ star w`. -/
lemma kernel_off_diag (w z : ℂ) (hz : z ≠ star w) :
    kernel E w z = kernelNum E w z / (2 * π * Complex.I * kernelDen w z) := by
  -- This is the `if_neg` branch in the definition.
  have : z ≠ star w := hz
  simp [kernel]
  aesop

/-- Conjugate symmetry of the kernel numerator: `kernelNum(w,z) = conj (kernelNum(z,w))`. -/
lemma kernelNum_conj_symm (w z : ℂ) :
    kernelNum E w z = star (kernelNum E z w) := by
  -- Expand both sides and simplify using the definition of `E#`.
  simp [kernelNum, Complex.ConjugateReflection.apply]  -- expands `E#`
  -- Now we’re comparing explicit scalar expressions; rearrange with `ring`.
  ring

/-- Off-diagonal Hermitian symmetry of the kernel:
`K(w,z) = conj (K(z,w))` when `z ≠ star w`. -/
lemma kernel_conj_symm_off_diag (w z : ℂ) (hz : z ≠ star w) :
    kernel E w z = star (kernel E z w) := by
  -- Off-diagonal expressions on both sides
  have hz' : w ≠ star z := by
    -- taking conjugates of `z = star w` would give `w = star z`
    intro hw
    apply hz
    simp [hw]
  have hden1 : kernelDen w z ≠ 0 := by
    -- `kernelDen w z = star w - z`, so nonzero by `hz`
    simp [kernelDen, sub_eq_zero]; exact id (Ne.symm hz)
  have hden2 : kernelDen z w ≠ 0 := by
    -- `kernelDen z w = star z - w`, so nonzero by `hz'`
    simp [kernelDen, sub_eq_zero]; exact id (Ne.symm hz')
  -- Use the off-diagonal formulas
  have hwz : kernel E w z =
      kernelNum E w z / (2 * π * Complex.I * kernelDen w z) :=
    kernel_off_diag (E := E) w z hz
  have hzw : kernel E z w =
      kernelNum E z w / (2 * π * Complex.I * kernelDen z w) :=
    kernel_off_diag (E := E) z w hz'
  -- Take conjugates of the right-hand side for `K(z,w)`.
  have : star (kernel E z w) =
      star (kernelNum E z w) /
        star (2 * π * Complex.I * kernelDen z w) := by
    -- on `ℂ`, `conj` is multiplicative and respects division
    simp [hzw]
  -- Simplify the conjugated denominator.
  have hden_conj :
      star (2 * π * Complex.I * kernelDen z w)
        = 2 * π * Complex.I * kernelDen w z := by
    -- `star (2πi) = -2πi`, and `conj (star z - w) = z - star w`
    simp [kernelDen, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg]
    grind
  calc
    kernel E w z
        = kernelNum E w z / (2 * π * Complex.I * kernelDen w z) := hwz
    _ = star (kernelNum E z w) / (2 * π * Complex.I * kernelDen w z) := by
          -- use conjugate symmetry of the numerator
          simp [kernelNum_conj_symm (E := E) w z]
    _ = star (kernelNum E z w) /
          star (2 * π * Complex.I * kernelDen z w) := by
          -- rewrite the denominator via `hden_conj`
          simp [hden_conj]
    _ = star (kernel E z w) := by
          -- revert the earlier conjugation computation
          simpa [map_mul, map_div₀] using this.symm



/-- The kernel function `z ↦ K(w, z)` belongs to the de Branges space. -/
lemma kernel_mem_L2 (w : ℂ) :
    MemLp (fun x : ℝ => kernel E w x) (2 : ℝ≥0∞) E.measure := by
  -- TODO: de Branges’ estimate; uses structure of `E` & admissibility machinery.
  sorry

/-- The kernel function `z ↦ K(w, z)` belongs to the de Branges space. -/
lemma kernel_admissible_over_E (w : ℂ) :
    IsDeBrangesAdmissible (fun z : ℂ => kernel E w z / E z) := by
  -- TODO: bounded type + mean type ≤ 0, cf. de Branges, Thm. 11 / 19.
  sorry

/-- The kernel function `z ↦ K(w, z)` belongs to the de Branges space. -/
lemma kernel_admissible_sharp_over_E (w : ℂ) :
    IsDeBrangesAdmissible (fun z : ℂ => (kernel E w)# z / E z) := by
  -- TODO: same as above for the reflected kernel.
  sorry

/-- The kernel function `z ↦ K(w, z)` belongs to the de Branges space. -/
lemma kernel_in_space (w : ℂ) :
    MemSpace E (fun z => kernel E w z) := by
  refine
    { entire := kernel_entire (E := E) w
      mem_L2 := kernel_mem_L2 (E := E) w
      admissible_F_over_E := ?_
      admissible_F_sharp_over_E := ?_ }
  · simpa using kernel_admissible_over_E (E := E) w
  · simpa using kernel_admissible_sharp_over_E (E := E) w

/-- The kernel function as an element of `Space E`. -/
noncomputable def Kernel (w : ℂ) : Space E :=
  ⟨fun z => kernel E w z, kernel_in_space E w⟩

@[simp] lemma Kernel_apply (w z : ℂ) :
    Kernel E w z = kernel E w z :=
  rfl

/-- Point evaluation at `w` as a continuous linear functional, realized via the inner
product with the reproducing kernel. -/
noncomputable def eval (w : ℂ) : Space E →L[ℂ] ℂ :=
  innerSL ℂ (Kernel E w)

/-- `eval w` is exactly the Fréchet–Riesz map applied to the kernel vector `Kernel E w`. -/
lemma eval_eq_toDualMap (w : ℂ) :
    eval (E := E) w =
      InnerProductSpace.toDualMap ℂ (Space E) (Kernel E w) := rfl

@[simp] lemma eval_apply (w : ℂ) (F : Space E) :
    eval (E := E) w F = inner ℂ (Kernel E w) F := rfl

/-- The operator norm of the evaluation functional at `w` equals the norm of the kernel
vector `Kernel E w`. This is the abstract Riesz representation fact in our setting. -/
lemma norm_eval (w : ℂ) :
    ‖eval (E := E) w‖ = ‖Kernel E w‖ := by
  -- `eval w = innerSL ℂ (Kernel E w)` by definition
  simp [eval]

/-- The inner product on `Space E` is the `L²(μ_E)` inner product, written as an integral. -/
lemma inner_eq_L2_integral (F G : Space E) :
    inner ℂ F G =
      ∫ t, inner ℂ (DeBranges.Space.toLp (E := E) F t)
                   (DeBranges.Space.toLp (E := E) G t) ∂ E.measure := by
  -- Unfold the `Space E` inner product, which is defined via `toLp`.
  change ⟪DeBranges.Space.toLp (E := E) F,
          DeBranges.Space.toLp (E := E) G⟫_ℂ
        = _
  -- Now use the `L²` inner product formula.
  simp [MeasureTheory.L2.inner_def]

lemma inner_kernel_L2_integral (F : Space E) (w : ℂ) :
    inner ℂ F (Kernel E w) =
      ∫ t, inner ℂ (DeBranges.Space.toLp (E := E) F t)
                   (DeBranges.Space.toLp (E := E) (Kernel E w) t) ∂ E.measure := by
  simpa using inner_eq_L2_integral (E := E) F (Kernel E w)

lemma inner_kernel_integral_scalar (F : Space E) (w : ℂ) :
    inner ℂ F (Kernel E w) =
      ∫ t, DeBranges.Space.toLp (E := E) (Kernel E w) t *
           star (DeBranges.Space.toLp (E := E) F t) ∂ E.measure := by
  -- Start from the L²-inner-product expression.
  have h0 := inner_kernel_L2_integral (E := E) F w
  -- Rewrite the integrand using the explicit scalar inner product on `ℂ`.
  have hfun :
      (fun t : ℝ =>
        inner ℂ (DeBranges.Space.toLp (E := E) F t)
                 (DeBranges.Space.toLp (E := E) (Kernel E w) t))
        =
      fun t : ℝ =>
        DeBranges.Space.toLp (E := E) (Kernel E w) t *
          star (DeBranges.Space.toLp (E := E) F t) := by
    funext t
    -- On `ℂ`, `⟪x, y⟫ = y * conj x`.
    simp
  -- Turn pointwise equality of integrands into equality of integrals.
  have hint :
      ∫ t, inner ℂ (DeBranges.Space.toLp (E := E) F t)
                   (DeBranges.Space.toLp (E := E) (Kernel E w) t) ∂ E.measure
        =
      ∫ t, DeBranges.Space.toLp (E := E) (Kernel E w) t *
           star (DeBranges.Space.toLp (E := E) F t) ∂ E.measure :=
    (congrArg (fun (f : ℝ → ℂ) => ∫ t, f t ∂ E.measure) hfun)
  -- Combine with `h0`.
  calc
    inner ℂ F (Kernel E w)
        = ∫ t, inner ℂ (DeBranges.Space.toLp (E := E) F t)
                       (DeBranges.Space.toLp (E := E) (Kernel E w) t) ∂ E.measure := h0
    _ = ∫ t, DeBranges.Space.toLp (E := E) (Kernel E w) t *
             star (DeBranges.Space.toLp (E := E) F t) ∂ E.measure := by
          exact hint

/-- For any `F : Space E`, its `toLp` representative coincides a.e. with the original function
on `ℝ` (with respect to `E.measure`). -/
lemma toLp_ae_eq (F : Space E) :
    (fun t : ℝ => DeBranges.Space.toLp (E := E) F t)
      =ᵐ[E.measure] fun t : ℝ => F t := by
  -- This is just `MemLp.coeFn_toLp` specialized to the `Space E` embedding.
  have hF : MemLp (fun t : ℝ => (F t : ℂ)) (2 : ℝ≥0∞) E.measure :=
    DeBranges.Space.mem_L2 (E := E) F
  -- Now unfold `Space.toLp` and apply the general lemma.
  simpa [DeBranges.Space.toLp, hF] using
    (MeasureTheory.MemLp.coeFn_toLp (hf := hF))

/-- Refined scalar integral expression: we can replace `toLp F` by `F` itself a.e. in the
integrand for `⟨F, K_w⟩`. This does not yet touch the kernel side. -/
lemma inner_kernel_integral_scalar_F (F : Space E) (w : ℂ) :
    inner ℂ F (Kernel E w) =
      ∫ t, DeBranges.Space.toLp (E := E) (Kernel E w) t *
           star (F t) ∂ E.measure := by
  -- Start from the scalar integrand formula with `toLp F`.
  have h0 := inner_kernel_integral_scalar (E := E) F w
  -- a.e.-equality `toLp F = F` on `ℝ`.
  have hF_ae :
      (fun t : ℝ => DeBranges.Space.toLp (E := E) F t)
        =ᵐ[E.measure] fun t : ℝ => F t :=
    toLp_ae_eq (E := E) F
  -- Transport this to the conjugated factor.
  have h_conj_ae :
      (fun t : ℝ => star (DeBranges.Space.toLp (E := E) F t))
        =ᵐ[E.measure] fun t : ℝ => star (F t) :=
    hF_ae.mono fun t ht => by simp [ht]
  -- Combine with the kernel factor to get an a.e.-equality of integrands.
  have h_ae :
      (fun t : ℝ =>
        DeBranges.Space.toLp (E := E) (Kernel E w) t *
          star (DeBranges.Space.toLp (E := E) F t))
        =ᵐ[E.measure]
      (fun t : ℝ =>
        DeBranges.Space.toLp (E := E) (Kernel E w) t *
          star (F t)) := by
    -- multiply the a.e.-equality `h_conj_ae` by the kernel factor, pointwise
    filter_upwards [h_conj_ae] with t ht
    simp [ht]
  -- Now replace the integrand using `integral_congr_ae`.
  have hint :
      ∫ t, DeBranges.Space.toLp (E := E) (Kernel E w) t *
           star (DeBranges.Space.toLp (E := E) F t) ∂ E.measure
        =
      ∫ t, DeBranges.Space.toLp (E := E) (Kernel E w) t *
           star (F t) ∂ E.measure :=
    MeasureTheory.integral_congr_ae h_ae
  -- Combine with `h0`.
  calc
    inner ℂ F (Kernel E w)
        = ∫ t, DeBranges.Space.toLp (E := E) (Kernel E w) t *
             star (DeBranges.Space.toLp (E := E) F t) ∂ E.measure := h0
    _ = ∫ t, DeBranges.Space.toLp (E := E) (Kernel E w) t *
             star (F t) ∂ E.measure := by
          simpa using hint

lemma inner_kernel_integral (F : Space E) (w : ℂ) :
    inner ℂ F (Kernel E w) =
      ∫ t, kernel E w t * star (F t) ∂ E.measure := by
  -- Start from the version where only `F` has been “de-Lp’d”.
  have h0 := inner_kernel_integral_scalar_F (E := E) F w
  -- a.e.-equality `toLp (Kernel E w) = Kernel E w` on `ℝ`.
  have hK_ae :
      (fun t : ℝ => DeBranges.Space.toLp (E := E) (Kernel E w) t)
        =ᵐ[E.measure] fun t : ℝ => Kernel E w t :=
    toLp_ae_eq (E := E) (Kernel E w)
  -- Replace `Kernel E w t` by the scalar kernel `kernel E w t`.
  have hK_ae' :
      (fun t : ℝ => DeBranges.Space.toLp (E := E) (Kernel E w) t)
        =ᵐ[E.measure] fun t : ℝ => kernel E w t := by
    refine hK_ae.mono ?_
    intro t ht
    simpa [Kernel_apply] using ht
  -- Lift this to an a.e.-equality of the full integrand.
  have h_ae :
      (fun t : ℝ =>
        DeBranges.Space.toLp (E := E) (Kernel E w) t * star (F t))
        =ᵐ[E.measure]
      (fun t : ℝ =>
        kernel E w t * star (F t)) := by
    filter_upwards [hK_ae'] with t ht
    simp [ht]
  -- Use `integral_congr_ae` to replace the integrand everywhere.
  have hint :
      ∫ t, DeBranges.Space.toLp (E := E) (Kernel E w) t * star (F t) ∂ E.measure
        =
      ∫ t, kernel E w t * star (F t) ∂ E.measure :=
    MeasureTheory.integral_congr_ae h_ae
  -- Combine with the starting formula.
  calc
    inner ℂ F (Kernel E w)
        = ∫ t, DeBranges.Space.toLp (E := E) (Kernel E w) t * star (F t) ∂ E.measure := h0
    _ = ∫ t, kernel E w t * star (F t) ∂ E.measure := by
          simpa using hint

lemma eval_eq_conj_integral_kernel (F : Space E) (w : ℂ) :
    eval (E := E) w F =
      star (∫ t, kernel E w t * star (F t) ∂ E.measure) := by
  -- Start from the scalar integral representation for `⟪F, K_w⟫`.
  have h_inner : inner ℂ F (Kernel E w) =
      ∫ t, kernel E w t * star (F t) ∂ E.measure :=
    inner_kernel_integral (E := E) F w
  -- Relate `⟪K_w, F⟫` and `⟪F, K_w⟫` via conjugate symmetry.
  have h_conj :
      inner ℂ (Kernel E w) F = star (inner ℂ F (Kernel E w)) :=
        Eq.symm (CStarModule.star_inner F (Kernel E w))
  calc
    eval (E := E) w F
        = inner ℂ (Kernel E w) F := rfl
    _ = star (inner ℂ F (Kernel E w)) := h_conj
    _ = star (∫ t, kernel E w t * star (F t) ∂ E.measure) := by
          simp [h_inner]

/-- Cauchy–Schwarz-type bound for point evaluation: `|F(w)| ≤ ‖K_w‖ · ‖F‖`. -/
lemma eval_bound (w : ℂ) (F : Space E) :
    ‖eval (E := E) w F‖ ≤ ‖Kernel E w‖ * ‖F‖ := by
  -- generic op-norm inequality `‖f x‖ ≤ ‖f‖ · ‖x‖`, plus `norm_eval`.
  simpa [norm_eval (E := E) w] using
    (eval (E := E) w).le_opNorm F

/-- Evaluation of the kernel at its own center: `⟨K_w, K_w⟩ = ‖K_w‖²`. -/
lemma eval_kernel_self (w : ℂ) :
    eval (E := E) w (Kernel E w) =
      ((‖Kernel E w‖ ^ 2 : ℝ) : ℂ) := by
  -- By definition of `eval`, this is just the inner product of `K_w` with itself.
  -- `inner_self_eq_norm_sq_to_K` turns that into the squared norm (as a real, coerced to `ℂ`).
  simp [eval_apply, inner_self_eq_norm_sq_to_K]

/-- The reproducing property: `⟨F, K_w⟩ = F(w)`.

This is the de Branges reproducing kernel identity. Its proof is reduced here to
the analytic step of comparing the Cauchy representation integral with the
`L²(μ_E)` inner product. -/
theorem reproducing_property (F : Space E) (w : ℂ) :
    inner ℂ (Kernel E w) F = F w := by
  classical
  -- Step 1: Cauchy representation for `F` at `w` (global de Branges input).
  have hC :
      F w = ∫ t, DeBranges.Nevanlinna.kernel_Cauchy E w t * F t ∂ E.measure :=
    DeBranges.cauchy_representation (E := E) F w
  -- Unfold `kernel_Cauchy` in terms of the reproducing kernel.
  have hC' :
      F w = ∫ t, kernel E w t * F t ∂ E.measure := by
    simpa [DeBranges.kernel_Cauchy] using hC

  -- Step 2: Express the `L²(μ_E)` inner product `⟨F, K_w⟩` as an integral.
  have hI :
      inner ℂ F (Kernel E w) =
        ∫ t, kernel E w t * star (F t) ∂ E.measure :=
    inner_kernel_integral_scalar (E := E) F w

  -- Step 3 (analytic core, to be filled): show that
  --   `⟨F, K_w⟩ = conj (F w)`,
  -- by comparing `hI` with the conjugate of `hC'` using the Hermitian symmetry
  -- of the kernel and de Branges’ growth/Poisson–Nevanlinna theory.
  have h_conj :
      inner ℂ F (Kernel E w) = Complex.conj (F w) := by
    /- TODO:
       * Take the complex conjugate of `hC'` to express `conj (F w)` as an
         integral with integrand involving `conj (kernel E w t * F t)`.
       * Use the Hermitian symmetry of the kernel (cf. `kernel_off_diag`,
         `kernel_diag` and the `kernel_conj_symm`-type lemmas) and the
         admissibility of `F/E`, `F#/E` to identify this integral with
         the `L²(μ_E)` inner product integral `hI`.
       * This is the analytic heart of de Branges’ Theorem 11/19.
    -/
    sorry

  -- Step 4: Use conjugate symmetry of the inner product to flip the arguments.
  -- From `⟨F, K_w⟩ = conj (F w)` we get `⟨K_w, F⟩ = F w`.
  have := congrArg Complex.conj h_conj
  -- `conj (⟨F, K_w⟩) = conj (conj (F w)) = F w`, and
  -- `conj (⟨F, K_w⟩) = ⟨K_w, F⟩` by `inner_conj_symm`.
  simpa [inner_conj_symm] using this




end DeBranges
