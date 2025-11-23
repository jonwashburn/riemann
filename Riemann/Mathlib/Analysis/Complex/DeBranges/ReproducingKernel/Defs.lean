import Mathlib.Analysis.Complex.RemovableSingularity
import Riemann.Mathlib.Analysis.Complex.ConjugateReflection
import Riemann.Mathlib.Analysis.Complex.DeBranges.Basic

/-!
# Reproducing Kernel for de Branges Spaces

This file defines the reproducing kernel `K(w, z)` for a de Branges space `B(E)` and proves
(in the Basic.lean file) its reproducing property: for every `F ∈ B(E)`, `⟨F, K(·, w)⟩ = F(w)`.

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


end DeBranges
