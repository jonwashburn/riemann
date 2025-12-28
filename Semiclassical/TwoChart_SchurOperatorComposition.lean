import TwoChart_SchurComposition

import Mathlib.Tactic

/-!
# `L²` bounds for compositions of Schur kernels/operators

This file is the operator-level companion to `TwoChart_SchurComposition.lean`.

We already have:

* `KernelOp_comp` : a Fubini/associativity identity
  `KernelOp K₁ (KernelOp K₂ u) = KernelOp (compKernel K₁ K₂) u`,
* `SchurData.compKernel` : stability of Schur row/column bounds under
  kernel composition, and
* `schur_l2Energy_le` : the `L²`-energy Schur test on representatives.

The next principled step is to **compose** these ingredients into a single
nontrivial analytic statement:

> the `L²` Schur bound for the composite operator.

This is used repeatedly later (e.g. to estimate powers of remainder operators
and to bound compositions arising in the parametrix identities).

No axioms, no placeholders, and no `sorry`.
-/

namespace TwoChartEgorov

open MeasureTheory

noncomputable section

section

variable {μ : Measure ℝ} [SigmaFinite μ]

/-! ## A convenient multiplicative constant -/

/-- The natural constant appearing in the `L²` Schur bound: `A * B`. -/
def schurEnergyConst {K : ℝ → ℝ → ℂ} (d : SchurData μ K) : ℝ := d.A * d.B

lemma schurEnergyConst_nonneg {K : ℝ → ℝ → ℂ} {d : SchurData μ K} :
    0 ≤ schurEnergyConst (μ := μ) d := by
  dsimp [schurEnergyConst]
  exact mul_nonneg d.A_nonneg d.B_nonneg

lemma schurEnergyConst_mul_comm {K₁ K₂ : ℝ → ℝ → ℂ} (d₁ : SchurData μ K₁) (d₂ : SchurData μ K₂) :
    ((d₁.A * d₂.A) * (d₁.B * d₂.B)) = schurEnergyConst (μ := μ) d₁ * schurEnergyConst (μ := μ) d₂ := by
  dsimp [schurEnergyConst]
  ring

/-! ## `L²` Schur bound for the composition kernel -/

/-- The `L²`-energy Schur bound for the **composition kernel**.

This is a direct application of:

* `SchurData.compKernel` to produce Schur data for `compKernel μ K₁ K₂`, then
* `schur_l2Energy_le` to obtain the `L²`-energy bound.

We keep the integrability hypotheses explicit (as in the rest of the kernel-first
pipeline). In intended applications these are discharged from explicit kernel
majorants (e.g. by `schurDecay`).
-/
theorem schur_l2Energy_le_compKernel
    {K₁ K₂ : ℝ → ℝ → ℂ}
    (d₁ : SchurData μ K₁) (d₂ : SchurData μ K₂)
    (hIntKK : ∀ t tp : ℝ, Integrable (fun s : ℝ => K₁ t s * K₂ s tp) μ)
    (hProdRow : ∀ t : ℝ,
      Integrable (fun p : ℝ × ℝ => (‖K₁ t p.1‖ : ℝ) * ‖K₂ p.1 p.2‖) (μ.prod μ))
    (hProdCol : ∀ tp : ℝ,
      Integrable (fun p : ℝ × ℝ => (‖K₁ p.1 p.2‖ : ℝ) * ‖K₂ p.2 tp‖) (μ.prod μ))
    {u : ℝ → ℂ}
    (hu2 : Integrable (fun s => ‖u s‖ ^ (2:ℕ)) μ)
    (hInt : ∀ t, Integrable (fun s => (compKernel μ K₁ K₂ t s) * u s) μ)
    (hInt_wu2 : ∀ t,
      Integrable (fun s => (‖compKernel μ K₁ K₂ t s‖ : ℝ) * ‖u s‖ ^ (2:ℕ)) μ)
    (hProd : Integrable
      (fun p : ℝ × ℝ => (‖compKernel μ K₁ K₂ p.1 p.2‖ : ℝ) * ‖u p.2‖ ^ (2:ℕ))
      (μ.prod μ)) :
    l2Energy μ (KernelOp μ (compKernel μ K₁ K₂) u)
      ≤ ((d₁.A * d₂.A) * (d₁.B * d₂.B)) * l2Energy μ u := by
  -- Build Schur data for the composed kernel.
  have dcomp : SchurData μ (compKernel μ K₁ K₂) :=
    SchurData.compKernel (μ := μ)
      (d₁ := d₁) (d₂ := d₂)
      (hInt := hIntKK) (hProdRow := hProdRow) (hProdCol := hProdCol)

  -- Apply the `L²` Schur energy inequality.
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (schur_l2Energy_le (μ := μ) (K := compKernel μ K₁ K₂)
      (d := dcomp) (u := u)
      hu2 hInt hInt_wu2 hProd)

/-- Same as `schur_l2Energy_le_compKernel`, but with the constant written as a product
of the individual Schur constants `A₁B₁ * A₂B₂`. -/
theorem schur_l2Energy_le_compKernel'
    {K₁ K₂ : ℝ → ℝ → ℂ}
    (d₁ : SchurData μ K₁) (d₂ : SchurData μ K₂)
    (hIntKK : ∀ t tp : ℝ, Integrable (fun s : ℝ => K₁ t s * K₂ s tp) μ)
    (hProdRow : ∀ t : ℝ,
      Integrable (fun p : ℝ × ℝ => (‖K₁ t p.1‖ : ℝ) * ‖K₂ p.1 p.2‖) (μ.prod μ))
    (hProdCol : ∀ tp : ℝ,
      Integrable (fun p : ℝ × ℝ => (‖K₁ p.1 p.2‖ : ℝ) * ‖K₂ p.2 tp‖) (μ.prod μ))
    {u : ℝ → ℂ}
    (hu2 : Integrable (fun s => ‖u s‖ ^ (2:ℕ)) μ)
    (hInt : ∀ t, Integrable (fun s => (compKernel μ K₁ K₂ t s) * u s) μ)
    (hInt_wu2 : ∀ t,
      Integrable (fun s => (‖compKernel μ K₁ K₂ t s‖ : ℝ) * ‖u s‖ ^ (2:ℕ)) μ)
    (hProd : Integrable
      (fun p : ℝ × ℝ => (‖compKernel μ K₁ K₂ p.1 p.2‖ : ℝ) * ‖u p.2‖ ^ (2:ℕ))
      (μ.prod μ)) :
    l2Energy μ (KernelOp μ (compKernel μ K₁ K₂) u)
      ≤ (schurEnergyConst (μ := μ) d₁) * (schurEnergyConst (μ := μ) d₂) * l2Energy μ u := by
  -- Start from the previous lemma and rewrite the constant.
  have h := schur_l2Energy_le_compKernel (μ := μ) (K₁ := K₁) (K₂ := K₂)
    (d₁ := d₁) (d₂ := d₂)
    (hIntKK := hIntKK) (hProdRow := hProdRow) (hProdCol := hProdCol)
    (u := u) hu2 hInt hInt_wu2 hProd
  -- Commute/reassociate the constants.
  simpa [schurEnergyConst_mul_comm (μ := μ) d₁ d₂, mul_assoc] using h

/-! ## `L²` Schur bound for the composite operator -/

/-- The `L²`-energy Schur bound for the **composite kernel operator**
`KernelOp μ K₁ (KernelOp μ K₂ u)`.

This is the first place where the development uses both:

* the kernel-level composition identity `KernelOp_comp`, and
* the Schur stability of composition (`schur_l2Energy_le_compKernel`).
-/
theorem schur_l2Energy_le_comp
    {K₁ K₂ : ℝ → ℝ → ℂ}
    (d₁ : SchurData μ K₁) (d₂ : SchurData μ K₂)
    (hIntKK : ∀ t tp : ℝ, Integrable (fun s : ℝ => K₁ t s * K₂ s tp) μ)
    (hProdRow : ∀ t : ℝ,
      Integrable (fun p : ℝ × ℝ => (‖K₁ t p.1‖ : ℝ) * ‖K₂ p.1 p.2‖) (μ.prod μ))
    (hProdCol : ∀ tp : ℝ,
      Integrable (fun p : ℝ × ℝ => (‖K₁ p.1 p.2‖ : ℝ) * ‖K₂ p.2 tp‖) (μ.prod μ))
    {u : ℝ → ℂ}
    (hu2 : Integrable (fun s => ‖u s‖ ^ (2:ℕ)) μ)
    (hInt : ∀ t, Integrable (fun s => (compKernel μ K₁ K₂ t s) * u s) μ)
    (hInt_wu2 : ∀ t,
      Integrable (fun s => (‖compKernel μ K₁ K₂ t s‖ : ℝ) * ‖u s‖ ^ (2:ℕ)) μ)
    (hProd : Integrable
      (fun p : ℝ × ℝ => (‖compKernel μ K₁ K₂ p.1 p.2‖ : ℝ) * ‖u p.2‖ ^ (2:ℕ))
      (μ.prod μ))
    (hFub : ∀ t : ℝ,
      Integrable (fun p : ℝ × ℝ => K₁ t p.1 * (K₂ p.1 p.2 * u p.2)) (μ.prod μ)) :
    l2Energy μ (KernelOp μ K₁ (KernelOp μ K₂ u))
      ≤ ((d₁.A * d₂.A) * (d₁.B * d₂.B)) * l2Energy μ u := by
  -- Replace the double kernel operator by the composed-kernel operator.
  have hEq : KernelOp μ K₁ (KernelOp μ K₂ u) = KernelOp μ (compKernel μ K₁ K₂) u :=
    KernelOp_comp (μ := μ) (K₁ := K₁) (K₂ := K₂) (u := u) hFub

  -- Apply the composed-kernel estimate.
  simpa [hEq] using
    (schur_l2Energy_le_compKernel (μ := μ) (K₁ := K₁) (K₂ := K₂)
      (d₁ := d₁) (d₂ := d₂)
      (hIntKK := hIntKK) (hProdRow := hProdRow) (hProdCol := hProdCol)
      (u := u) hu2 hInt hInt_wu2 hProd)

/-- Same as `schur_l2Energy_le_comp`, with the constant written as
`(A₁B₁) * (A₂B₂)`. -/
theorem schur_l2Energy_le_comp'
    {K₁ K₂ : ℝ → ℝ → ℂ}
    (d₁ : SchurData μ K₁) (d₂ : SchurData μ K₂)
    (hIntKK : ∀ t tp : ℝ, Integrable (fun s : ℝ => K₁ t s * K₂ s tp) μ)
    (hProdRow : ∀ t : ℝ,
      Integrable (fun p : ℝ × ℝ => (‖K₁ t p.1‖ : ℝ) * ‖K₂ p.1 p.2‖) (μ.prod μ))
    (hProdCol : ∀ tp : ℝ,
      Integrable (fun p : ℝ × ℝ => (‖K₁ p.1 p.2‖ : ℝ) * ‖K₂ p.2 tp‖) (μ.prod μ))
    {u : ℝ → ℂ}
    (hu2 : Integrable (fun s => ‖u s‖ ^ (2:ℕ)) μ)
    (hInt : ∀ t, Integrable (fun s => (compKernel μ K₁ K₂ t s) * u s) μ)
    (hInt_wu2 : ∀ t,
      Integrable (fun s => (‖compKernel μ K₁ K₂ t s‖ : ℝ) * ‖u s‖ ^ (2:ℕ)) μ)
    (hProd : Integrable
      (fun p : ℝ × ℝ => (‖compKernel μ K₁ K₂ p.1 p.2‖ : ℝ) * ‖u p.2‖ ^ (2:ℕ))
      (μ.prod μ))
    (hFub : ∀ t : ℝ,
      Integrable (fun p : ℝ × ℝ => K₁ t p.1 * (K₂ p.1 p.2 * u p.2)) (μ.prod μ)) :
    l2Energy μ (KernelOp μ K₁ (KernelOp μ K₂ u))
      ≤ (schurEnergyConst (μ := μ) d₁) * (schurEnergyConst (μ := μ) d₂) * l2Energy μ u := by
  have h := schur_l2Energy_le_comp (μ := μ) (K₁ := K₁) (K₂ := K₂)
    (d₁ := d₁) (d₂ := d₂)
    (hIntKK := hIntKK) (hProdRow := hProdRow) (hProdCol := hProdCol)
    (u := u) hu2 hInt hInt_wu2 hProd hFub
  simpa [schurEnergyConst_mul_comm (μ := μ) d₁ d₂, mul_assoc] using h

end

end TwoChartEgorov
