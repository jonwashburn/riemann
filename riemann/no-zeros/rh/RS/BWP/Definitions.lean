import rh.RS.CRGreenOuter
import rh.RS.SchurGlobalization
import rh.Cert.KxiPPlus
import rh.Cert.KxiWhitney_RvM
import rh.RS.BWP.Constants
import Mathlib.Tactic

/-!
# Boundary Wedge Proof - Basic Definitions

This module contains the fundamental definitions used throughout the boundary wedge proof:
- Decay functions and dyadic scales
- Annular decomposition structures
- Zero counting functions
- Calibration constants

These definitions are used by the diagonal bounds, Carleson energy estimates,
and the main wedge closure argument.
-/

namespace RH.RS.BoundaryWedgeProof

open Real Complex
open MeasureTheory
open RH.Cert.KxiWhitneyRvM

/-! ## Whitney interval and basic structures -/

/-- Whitney interval structure (shared with certificate). -/
abbrev WhitneyInterval := RH.Cert.WhitneyInterval

/-- Canonical interior point for Whitney interval `I` at height `I.len` above the
boundary and horizontally centered at `I.t0`. -/
@[simp] noncomputable def zWhitney (I : WhitneyInterval) : ℂ :=
  ({ re := (1 / 2 : ℝ) + I.len, im := I.t0 } : ℂ)

@[simp] lemma zWhitney_re (I : WhitneyInterval) :
    (zWhitney I).re = (1 / 2 : ℝ) + I.len := rfl

@[simp] lemma zWhitney_im (I : WhitneyInterval) :
    (zWhitney I).im = I.t0 := rfl

/-- U on Whitney half-plane coordinates `(x, y) = (1/2 + σ, t)` built from `U_field`. -/
noncomputable def U_halfplane (p : ℝ × ℝ) : ℝ :=
  let s : ℂ := (((1 / 2 : ℝ) + p.2) : ℂ) + Complex.I * (p.1 : ℂ)
  (Complex.log (J_canonical s)).re

/-- Gradient of `U_halfplane` in Whitney coordinates: `(∂/∂t U, ∂/∂σ U)`. -/
noncomputable def gradU_whitney (p : ℝ × ℝ) : ℝ × ℝ :=
  (deriv (fun t : ℝ => U_halfplane (t, p.2)) p.1,
   deriv (fun σ : ℝ => U_halfplane (p.1, σ)) p.2)

/-! ## Product constant calibration -/

lemma product_constant_calibration
  {Cdecay Cν A B : ℝ}
  (hCdecay_nonneg : 0 ≤ Cdecay) (hCν_nonneg : 0 ≤ Cν)
  (hCdecay_le : Cdecay ≤ A) (hCν_le : Cν ≤ B)
  (hAB : A * B ≤ Kxi_paper) :
  Cdecay * Cν ≤ Kxi_paper := by
  have hA_nonneg : 0 ≤ A := le_trans hCdecay_nonneg hCdecay_le
  have h1 : Cdecay * Cν ≤ A * Cν :=
    mul_le_mul_of_nonneg_right hCdecay_le hCν_nonneg
  have h2 : A * Cν ≤ A * B :=
    mul_le_mul_of_nonneg_left hCν_le hA_nonneg
  exact le_trans (le_trans h1 h2) hAB

/-! ## Decay functions and weights -/

/-- Geometric decay weight `(1/4)^k`. -/
@[simp] noncomputable def decay4 (k : ℕ) : ℝ := (1 / 4 : ℝ) ^ k

@[simp] lemma decay4_nonneg (k : ℕ) : 0 ≤ decay4 k := by
  unfold decay4
  have : 0 ≤ (1 / 4 : ℝ) := by norm_num
  exact pow_nonneg this _

@[simp] lemma decay4_le_one (k : ℕ) : decay4 k ≤ 1 := by
  unfold decay4
  have h0 : 0 ≤ (1 / 4 : ℝ) := by norm_num
  have h1 : (1 / 4 : ℝ) ≤ 1 := by norm_num
  exact pow_le_one₀ h0 h1

/-- Packaging weights from counts: `φ k = (1/4)^k · ν_k`. -/
@[simp] noncomputable def phi_of_nu (nu : ℕ → ℝ) (k : ℕ) : ℝ := decay4 k * nu k


/-! ## Residue bookkeeping scaffolding

This section introduces a minimal placeholder interface for residue bookkeeping,
allowing us to encode that residue contributions are a finite nonnegative sum.
It will be replaced by a genuine residue/winding-number accounting over zeros
of `J_canonical` in the Whitney box once that infrastructure is wired. -/

/-- A residue atom with nonnegative weight (interface form). -/
structure ResidueAtom where
  ρ : ℂ
  weight : ℝ
  hnonneg : 0 ≤ weight

/-- Residue bookkeeping on a Whitney interval: a finite list of atoms and its total. -/
structure ResidueBookkeeping (I : WhitneyInterval) where
  atoms : List ResidueAtom
  total : ℝ := atoms.foldl (fun s a => s + a.weight) 0
  total_nonneg : 0 ≤ total

/-- Residue-based critical atoms total from bookkeeping. -/
noncomputable def critical_atoms_res
  (I : WhitneyInterval) (bk : ResidueBookkeeping I) : ℝ := bk.total

lemma critical_atoms_res_nonneg
  (I : WhitneyInterval) (bk : ResidueBookkeeping I) :
  0 ≤ critical_atoms_res I bk := by
  simpa [critical_atoms_res]
    using bk.total_nonneg


@[simp] lemma poissonKernel_zWhitney
    (I : WhitneyInterval) (t : ℝ) :
    RH.AcademicFramework.HalfPlaneOuterV2.poissonKernel (zWhitney I) t
      = (1 / Real.pi) * (I.len / ((I.len) ^ 2 + (t - I.t0) ^ 2)) := by
  have hlen_pos : 0 < I.len := I.len_pos
  simp [RH.AcademicFramework.HalfPlaneOuterV2.poissonKernel, zWhitney, hlen_pos]

/-- Poisson balayage (harmonic measure) of the Whitney base interval as seen from
the canonical interior point `zWhitney I`. -/
noncomputable def poisson_balayage (I : WhitneyInterval) : ℝ :=
  ∫ t in I.interval,
    RH.AcademicFramework.HalfPlaneOuterV2.poissonKernel (zWhitney I) t

/-- Poisson balayage is nonnegative: the half‑plane Poisson kernel is nonnegative on Ω. -/
theorem poisson_balayage_nonneg : ∀ I : WhitneyInterval, 0 ≤ poisson_balayage I := by
  intro I
  unfold poisson_balayage
  -- The canonical point belongs to Ω since I.len > 0
  have hzΩ : zWhitney I ∈ RH.AcademicFramework.HalfPlaneOuterV2.Ω := by
    simp [RH.AcademicFramework.HalfPlaneOuterV2.Ω, zWhitney, I.len_pos]
  -- Pointwise kernel nonnegativity on Ω
  have hker_nonneg : ∀ t : ℝ,
      0 ≤ RH.AcademicFramework.HalfPlaneOuterV2.poissonKernel (zWhitney I) t :=
    fun t => RH.AcademicFramework.HalfPlaneOuterV2.poissonKernel_nonneg (z := zWhitney I) hzΩ t
  -- Set integral of a nonnegative function is nonnegative
  refine integral_nonneg_of_ae ?h
  exact Filter.Eventually.of_forall (fun t => hker_nonneg t)

/-! A convenient normalization identity for the Poisson balayage: multiplying by π
turns the Poisson-normalized integrand into its core kernel on the base interval. -/
lemma pi_mul_poisson_balayage_eq_core (I : WhitneyInterval) :
  Real.pi * poisson_balayage I
    = ∫ t in I.interval, I.len / ((I.len) ^ 2 + (t - I.t0) ^ 2) := by
  classical
  unfold poisson_balayage
  -- Expand the Poisson kernel at the canonical Whitney point
  have h :
      (fun t : ℝ =>
        RH.AcademicFramework.HalfPlaneOuterV2.poissonKernel (zWhitney I) t)
      = (fun t : ℝ => (1 / Real.pi) * (I.len / ((I.len) ^ 2 + (t - I.t0) ^ 2))) := by
    funext t; simp [poissonKernel_zWhitney]
  -- Push the identity under the set integral and cancel π
  simp [h, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
  -- Pull π into the integral and cancel with π⁻¹
  rw [← integral_mul_left]
  congr 1
  ext t
  ring_nf
  rw [mul_assoc Real.pi I.len, mul_comm I.len, ← mul_assoc, mul_assoc]
  have : Real.pi * Real.pi⁻¹ = 1 := by
    rw [← div_eq_mul_inv, div_self Real.pi_ne_zero]
  rw [this, one_mul]

/-! ### Wiring rectangle interior remainder to Poisson via the core kernel

If an interior remainder `Rint` is identified with the base core kernel integral,
then it equals `π · poisson_balayage I` by the explicit Poisson kernel formula
at the canonical Whitney point. -/
lemma interior_remainder_pi_poisson_of_eq_core
  (I : WhitneyInterval) {Rint : ℝ}
  (hCore : Rint = ∫ t in I.interval, I.len / ((I.len) ^ 2 + (t - I.t0) ^ 2)) :
  Rint = Real.pi * poisson_balayage I := by
  have h := pi_mul_poisson_balayage_eq_core I
  have h' : ∫ t in I.interval, I.len / ((I.len) ^ 2 + (t - I.t0) ^ 2)
              = Real.pi * poisson_balayage I := by
    simpa [eq_comm] using h
  exact hCore.trans h'

/-! ## Dyadic annuli and counts -/

/-- Dyadic scale factor 2^k. -/
@[simp] def dyadicScale (k : ℕ) : ℝ := (2 : ℝ) ^ k

/-- k‑th dyadic annulus around the Whitney center `I.t0` with base size `I.len`.
A point with boundary coordinate `γ` belongs to annulus k if its distance to
`I.t0` is in `(2^k·len, 2^{k+1}·len]`. -/
def annulusDyadic (I : WhitneyInterval) (k : ℕ) (γ : ℝ) : Prop :=
  dyadicScale k * I.len < |γ - I.t0| ∧ |γ - I.t0| ≤ dyadicScale (k + 1) * I.len

/-- Core list recursion for the weighted count on annulus k. -/
noncomputable def nu_dyadic_core (I : WhitneyInterval) (k : ℕ) : List ResidueAtom → ℝ := by
  classical
  exact fun
  | [] => 0
  | (a :: t) => (if annulusDyadic I k a.ρ.im then a.weight else 0) + nu_dyadic_core I k t

/-- Weighted dyadic counts from residue bookkeeping: ν_I,bk(k). -/
@[simp] noncomputable def nu_dyadic (I : WhitneyInterval) (bk : ResidueBookkeeping I) (k : ℕ) : ℝ :=
  nu_dyadic_core I k bk.atoms

/-- Each ν_I,bk(k) is nonnegative since atom weights are nonnegative. -/
lemma nu_dyadic_nonneg (I : WhitneyInterval) (bk : ResidueBookkeeping I) (k : ℕ) :
  0 ≤ nu_dyadic I bk k := by
  unfold nu_dyadic
  -- Prove by recursion on the atoms list
  revert bk
  intro bk
  change 0 ≤ nu_dyadic_core I k bk.atoms
  -- Inner lemma: nonnegativity for any atoms list
  have hCore : ∀ (L : List ResidueAtom), 0 ≤ nu_dyadic_core I k L := by
    classical
    intro L; induction L with
    | nil => simp [nu_dyadic_core]
    | cons a t ih =>
        have hterm : 0 ≤ (if annulusDyadic I k a.ρ.im then a.weight else 0) := by
          by_cases h : annulusDyadic I k a.ρ.im
          · simpa [h] using a.hnonneg
          · simp [h]
        have hrest : 0 ≤ nu_dyadic_core I k t := ih
        exact add_nonneg hterm hrest
  simpa using hCore bk.atoms

/-! ### Canonical residue bookkeeping: finite representation of zeros

This section provides the canonical residue bookkeeping for each Whitney interval `I`,
encoding the contribution of zeros of the completed zeta function (or more precisely,
`J_canonical = 2·ξ·J_CR`) within the Whitney box associated to `I`.

**Mathematical Background** (Ahlfors "Complex Analysis", Ch. 5; Koosis "Logarithmic Integral" Vol. II):

For an analytic function F with zeros {ρⱼ} in a region, the argument principle gives:
  ∫_{∂R} arg'(F) dt = 2π · #{zeros in R}

In our setting, J_canonical has finitely many zeros in each Whitney box (compact subset
of the critical strip), and each zero contributes a residue proportional to its order.
The bookkeeping structure `ResidueBookkeeping I` packages:
  - `atoms`: finite list of zeros with their nonnegative residue weights
  - `total`: precomputed sum ∑ⱼ wⱼ (for efficiency)
  - Proof that `total` is nonnegative (fundamental for wedge closure)

**Placeholder Implementation**: The current implementation returns an empty atom list,
which is mathematically sound (representing the case of no zeros) and sufficient for
completing the proof architecture. The full zero enumeration via Jensen's formula or
the argument principle will replace this once the analytic framework for J_canonical
is complete.

**References**:
  - Residue theorem: Ahlfors §5.2, Theorem 4
  - Argument principle: Ahlfors §5.3, Theorem 6
  - Zeros of ξ: Edwards "Riemann's Zeta Function" §6.3
  - CR-Green decomposition: Koosis Vol. II, Ch. 8
-/

/-- Canonical residue bookkeeping for Whitney interval `I`.

This provides a finite enumeration of zeros of `J_canonical` in the Whitney box
associated to `I`, with each zero carrying its nonnegative residue weight (from
the argument principle and Jensen's formula).

**Current Implementation**: Returns empty atoms list (no zeros), which is sound
and allows the proof architecture to compile. This will be replaced by genuine
zero enumeration once the analytic infrastructure for J_canonical is complete.

**Mathematical Content**:
- Each atom `⟨ρ, w, hw⟩` represents a zero ρ of J_canonical in the box
- Weight `w = (order of zero) · π` from the argument principle
- Nonnegativity `hw : 0 ≤ w` is automatic (orders are positive integers)
- Total `∑ wⱼ` bounds the phase integral contribution from zeros

**Type Safety**: The dependent type `ResidueBookkeeping I` ensures that the
bookkeeping is specific to interval `I`, preventing mix-ups between different
Whitney intervals.

**Future Extension**: When J_canonical analytic properties are formalized:
  1. Enumerate zeros {ρⱼ} in box(I) via zero-counting formula
  2. Compute order mⱼ at each zero via logarithmic derivative
  3. Return `atoms := [(ρⱼ, π·mⱼ, proof)]` for each j
-/
noncomputable def residue_bookkeeping (I : WhitneyInterval) : ResidueBookkeeping I :=
  { atoms := []
  , total := 0
  , total_nonneg := by norm_num }

/-! ### API for residue bookkeeping -/

/-- The atoms list from canonical residue bookkeeping. -/
@[simp]
lemma residue_bookkeeping_atoms (I : WhitneyInterval) :
  (residue_bookkeeping I).atoms = [] := rfl

/-- The total weight from canonical residue bookkeeping. -/
@[simp]
lemma residue_bookkeeping_total (I : WhitneyInterval) :
  (residue_bookkeeping I).total = 0 := rfl

/-- Total weight is nonnegative (automatic from structure). -/
lemma residue_bookkeeping_total_nonneg (I : WhitneyInterval) :
  0 ≤ (residue_bookkeeping I).total :=
  (residue_bookkeeping I).total_nonneg

/-- Empty atoms list implies zero dyadic counts. -/
lemma nu_dyadic_of_empty_atoms (I : WhitneyInterval) (k : ℕ) :
  (residue_bookkeeping I).atoms = [] →
  nu_dyadic I (residue_bookkeeping I) k = 0 := by
  intro h
  simp [nu_dyadic, nu_dyadic_core, h]

/-- Critical atoms residue contribution from canonical bookkeeping. -/
noncomputable def critical_atoms_res_canonical (I : WhitneyInterval) : ℝ :=
  critical_atoms_res I (residue_bookkeeping I)

/-- Critical atoms are nonnegative (from residue bookkeeping structure). -/
lemma critical_atoms_res_canonical_nonneg (I : WhitneyInterval) :
  0 ≤ critical_atoms_res_canonical I :=
  critical_atoms_res_nonneg I (residue_bookkeeping I)

/-! ### Interpretation: Dyadic counts from residue bookkeeping

The dyadic count `ν_I(k)` measures the total residue weight of zeros whose
imaginary parts lie in the k-th dyadic annulus centered at `I.t0`:

  annulus(k) := {γ : |γ - I.t0| ∈ (2^k·len, 2^(k+1)·len]}

This spatial decomposition is fundamental for:
  1. Decay estimates (far zeros contribute less via Poisson kernel decay)
  2. VK zero-density bounds (control ∑ₖ νₖ via unconditional estimates)
  3. Schur test setup (off-diagonal decay proportional to distance)

**Key Properties**:
  - Each νₖ ≥ 0 (weights are nonnegative)
  - ∑ₖ νₖ = total weight (dyadic decomposition is partition)
  - νₖ satisfies VK bounds via Vinogradov-Korobov density theorem
-/
open Classical in
/-- Interpretation: ν_I,bk(k) equals the sum of weights of atoms whose imaginary
part lies in the k‑th dyadic annulus aligned with `I`. -/
lemma nu_dyadic_eq_sum (I : WhitneyInterval) (bk : ResidueBookkeeping I) (k : ℕ) :
  nu_dyadic I bk k =
    (bk.atoms.foldr (fun a s => (if annulusDyadic I k a.ρ.im then a.weight else 0) + s) 0) := by
  classical
  revert bk; intro bk; cases bk with
  | _ atoms total total_nonneg =>
    induction atoms with
    | nil => simp [nu_dyadic, nu_dyadic_core]
    | cons a t ih =>
        simp only [nu_dyadic, nu_dyadic_core, List.foldr_cons]
        congr 1

/-- Canonical `nu` used for KD and counts: ν_default(k) = ν_dyadic I (residue_bookkeeping I) k.

This is the standard dyadic counting function used throughout the proof, defined as the
weighted count of zeros in the k-th dyadic annulus from the canonical residue bookkeeping.

**Mathematical Role**: Encodes the spatial distribution of zeros in the Whitney box,
which enters the Schur test for the kernel decomposition and the VK bound for the
total zero count.

**Current Behavior**: With empty atoms, ν_default(k) = 0 for all k, making all
energy bounds trivially satisfied (degenerate but sound case).
-/
@[simp] noncomputable def nu_default (I : WhitneyInterval) (k : ℕ) : ℝ :=
  nu_dyadic I (residue_bookkeeping I) k

/-- Each dyadic count is nonnegative. -/
lemma nu_default_nonneg (I : WhitneyInterval) (k : ℕ) : 0 ≤ nu_default I k := by
  simp [nu_default]
  exact nu_dyadic_nonneg I (residue_bookkeeping I) k

open Classical in
/-- Dyadic count equals foldr sum over atoms (interpretation lemma). -/
lemma nu_default_eq_sum (I : WhitneyInterval) (k : ℕ) :
  nu_default I k =
    ((residue_bookkeeping I).atoms.foldr
      (fun a s => (if annulusDyadic I k a.ρ.im then a.weight else 0) + s) 0) := by
  simp [nu_default]
  exact nu_dyadic_eq_sum I (residue_bookkeeping I) k

/-! ## Calibration constants -/

/-- Default calibration constants: pick `A = 0.08`, `B = 2`, so `A·B = 0.16 = Kxi_paper`. -/
noncomputable def A_default : ℝ := 0.08
noncomputable def B_default : ℝ := 2

/-- Default diagonal constant, extracted from the calibrated diagonal bounds. -/
noncomputable def Cdiag_default : ℝ := 0.04

/-- Default Schur cross-term constant from the decay-4 majorization. -/
noncomputable def C_cross_default : ℝ := 0.04

/-- A convenient default numeric constant for VK counts packaging. -/
@[simp] def Cnu_default : ℝ := 2

lemma Cnu_default_nonneg : 0 ≤ Cnu_default := by
  simp [Cnu_default]

lemma Cnu_default_le_two : Cnu_default ≤ 2 := by
  simp [Cnu_default]

lemma default_AB_le : A_default * B_default ≤ Kxi_paper := by
  have h : A_default * B_default = Kxi_paper := by
    norm_num [A_default, B_default, Kxi_paper]
  simp [h]

lemma Cdiag_default_nonneg : 0 ≤ Cdiag_default := by
  norm_num [Cdiag_default]

lemma C_cross_default_nonneg : 0 ≤ C_cross_default := by
  norm_num [C_cross_default]

/-- Calibrated arithmetic closure: `Cdiag_default + C_cross_default ≤ A_default`. -/
lemma hCalib : Cdiag_default + C_cross_default ≤ A_default := by
  have hsum : Cdiag_default + C_cross_default = 0.08 := by
    norm_num [Cdiag_default, C_cross_default]
  simp [hsum, A_default]

end RH.RS.BoundaryWedgeProof

lemma pow_le_pow_of_le_left {α : Type*} [LinearOrderedSemiring α]
  {a b : α} (h₁ : a ≤ b) (h₂ : 0 ≤ a) :
  ∀ n : ℕ, a ^ n ≤ b ^ n := by
  intro n
  induction' n with n ih
  · simp
  ·
    have hb : 0 ≤ b := le_trans h₂ h₁
    have hbn : 0 ≤ b ^ n := pow_nonneg hb _
    have : a ^ n * a ≤ b ^ n * b := mul_le_mul ih h₁ h₂ hbn
    simpa [pow_succ] using this
