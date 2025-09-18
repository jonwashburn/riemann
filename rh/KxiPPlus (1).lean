
/-
  rh/Cert/KxiPPlus.lean

  CR–Green pairing with admissible windows ⇒ (P+)

  This file packages the analytic estimates (uniform test-energy and cutoff
  pairing bound) together with a Whitney Carleson budget to produce the
  boundary wedge certificate (P+).  The heavy analytic content is abstracted
  into typeclasses; no axioms and no `sorry` are used here.  Constants are
  uniform in the Whitney interval I and independent of hole placements.

  To instantiate for F := 2·J, provide instances of:
    * RH.Cert.CarlesonSystem            (the Whitney Carleson budget ζ ↦ Cζ)
    * RH.Cert.PairingSystem (F := 2·J)  (admissible windows, test energy Aψ, Crem)

  After those instances are available, `PPlusFromCarleson_exists (F := 2*J)`
  gives the desired (P+) certificate with constant depending only on (α, ψ)
  and √Cζ.

  mathlib only; no axioms; no sorry.
-/
import Mathlib

noncomputable section
open scoped BigOperators
open Real

namespace RH
namespace Cert

/-- A Whitney interval on the real axis, recorded by center `t0` and half-length `L > 0`. -/
structure WhitneyInterval : Type :=
  (t0 : ℝ)
  (L  : ℝ)
  (pos : 0 < L)

namespace WhitneyInterval

/-- Closed interval `[t0 - L, t0 + L]`. -/
def set (I : WhitneyInterval) : Set ℝ := {t | |t - I.t0| ≤ I.L}

/-- Length of the Whitney interval (always positive). -/
@[simp] def length (I : WhitneyInterval) : ℝ := 2 * I.L

lemma length_nonneg (I : WhitneyInterval) : 0 ≤ I.length := by
  have : 0 ≤ I.L := le_of_lt I.pos
  have h : 0 ≤ (2:ℝ) := by norm_num
  simpa [WhitneyInterval.length, two_mul, mul_comm] using mul_nonneg h this

lemma length_pos (I : WhitneyInterval) : 0 < I.length := by
  have h : 0 < (2:ℝ) := by norm_num
  simpa [WhitneyInterval.length, two_mul, mul_comm] using mul_pos h I.pos

end WhitneyInterval

/--
`CarlesonSystem` abstracts the Whitney Carleson budget for the energy measure
  μ(E) = ∬_E |∇U|^2 σ dt dσ.
We do not build μ explicitly; we only require its values on Whitney boxes as
a nonnegative function `ζ : WhitneyInterval → ℝ` with a linear bound by |I|.
-/
class CarlesonSystem : Type :=
  (ζ   : WhitneyInterval → ℝ)
  (Cζ  : ℝ)
  (Cζ_nonneg : 0 ≤ Cζ)
  (ζ_nonneg  : ∀ I, 0 ≤ ζ I)
  (budget    : ∀ I, ζ I ≤ Cζ * I.length)

attribute [simp] CarlesonSystem.ζ CarlesonSystem.Cζ

/--
`PairingSystem F ψ α α'` packages the admissible-window family (tagged by `ψ`),
its Poisson test energy, and the CR–Green cutoff pairing bound against the
boundary phase distribution of `F` (in our application, `F := 2·J`).

Only scale-invariant constants appear:
  * `Aψ`  — uniform upper bound for the Poisson test energy (depends on ψ, α′)
  * `Crem` — remainder/Schur constant (depends on α and ψ, not on I nor holes)

The actual analytic details are assumed to hold elsewhere as instances.
-/
class PairingSystem (F : ℂ → ℂ) (ψ : Type) (α α' : ℝ) [CarlesonSystem] : Type :=
  /-- Window type over each Whitney interval. Concrete structure not needed here. -/
  (Window : WhitneyInterval → Type)
  /-- Poisson test energy for a window on `I` (scale-invariant, nonnegative). -/
  (testEnergy : ∀ I, Window I → ℝ)
  (testEnergy_nonneg : ∀ I (φ : Window I), 0 ≤ testEnergy I φ)
  /-- Uniform test-energy cap `Aψ` independent of I, center t0, and hole placements. -/
  (Aψ : ℝ)
  (Aψ_nonneg : 0 ≤ Aψ)
  (uniform_test_energy : ∀ I (φ : Window I), testEnergy I φ ≤ Aψ)
  /-- Cutoff CR–Green pairing bound with the `√μ` factor. -/
  (pairing : ∀ I, Window I → ℝ)
  (Crem : ℝ)
  (Crem_nonneg : 0 ≤ Crem)
  (cutoff_pairing_bound :
      ∀ I (φ : Window I),
        pairing I φ
        ≤ Crem * Real.sqrt (testEnergy I φ) * Real.sqrt (CarlesonSystem.ζ I))

namespace PairingSystem

variables {F : ℂ → ℂ} {ψ : Type} {α α' : ℝ}
variable [CarlesonSystem]
variable [PS : PairingSystem F ψ α α']

/-- Expose the window type from the pairing system. -/
abbrev Window (I : WhitneyInterval) := PS.Window I

/-- Expose the pairing functional. -/
@[simp] def pairing (I : WhitneyInterval) (φ : Window (F:=F) (ψ:=ψ) (α:=α) (α':=α') I) : ℝ :=
  (PS.pairing I φ)

/-- Expose the test energy. -/
@[simp] def testEnergy (I : WhitneyInterval) (φ : Window (F:=F) (ψ:=ψ) (α:=α) (α':=α') I) : ℝ :=
  PS.testEnergy I φ

lemma uniform_test_energy
    (I : WhitneyInterval) (φ : Window (F:=F) (ψ:=ψ) (α:=α) (α':=α') I) :
    PairingSystem.testEnergy (F:=F) (ψ:=ψ) (α:=α) (α':=α') I φ ≤ PS.Aψ :=
  PS.uniform_test_energy I φ

lemma cutoff_pairing_bound
    (I : WhitneyInterval) (φ : Window (F:=F) (ψ:=ψ) (α:=α) (α':=α') I) :
    PairingSystem.pairing (F:=F) (ψ:=ψ) (α:=α) (α':=α') I φ
    ≤ PS.Crem * Real.sqrt (PairingSystem.testEnergy (F:=F) (ψ:=ψ) (α:=α) (α':=α') I φ)
        * Real.sqrt (CarlesonSystem.ζ I) :=
  PS.cutoff_pairing_bound I φ

end PairingSystem

/-- The target certification: a Whitney-uniform `(P+)` wedge bound for `F`. -/
def PPlusFromCarleson_exists (F : ℂ → ℂ) [CarlesonSystem]
    [PairingSystem F ψ α α'] : Prop :=
  ∃ (Ctest : ℝ), 0 ≤ Ctest ∧
    ∀ (I : WhitneyInterval)
      (φ : PairingSystem.Window (F:=F) (ψ:=ψ) (α:=α) (α':=α') I),
        PairingSystem.pairing (F:=F) (ψ:=ψ) (α:=α) (α':=α') I φ
        ≤ Ctest * Real.sqrt (I.length)

/-
  Main theorem: from the abstract CR–Green cutoff bound, the uniform test-energy
  cap, and the Whitney Carleson budget, we deduce the uniform `(P+)` estimate
  with constant `Ctest = Crem · √Aψ · √Cζ`, which depends only on (α, ψ) and Cζ,
  and is independent of I, t0, and the window’s hole placement.
-/
theorem PPlusFromCarleson_exists
    (F : ℂ → ℂ) [CS : CarlesonSystem]
    [PS : PairingSystem F ψ α α'] :
    PPlusFromCarleson_exists (F:=F) (ψ:=ψ) (α:=α) (α':=α') := by
  classical
  -- Shorthands for constants
  let Aψ  : ℝ := PS.Aψ
  have hAψ₀ : 0 ≤ Aψ := PS.Aψ_nonneg
  let Crem : ℝ := PS.Crem
  have hCrem₀ : 0 ≤ Crem := PS.Crem_nonneg
  let Cζ   : ℝ := CS.Cζ
  have hCζ₀ : 0 ≤ Cζ := CS.Cζ_nonneg
  -- Define the global test constant: Crem · √Aψ · √Cζ
  refine ⟨Crem * Real.sqrt Aψ * Real.sqrt Cζ, ?_, ?_⟩
  · -- Nonnegativity of the constant
    have : 0 ≤ Real.sqrt Aψ := Real.sqrt_nonneg _
    have : 0 ≤ Crem * Real.sqrt Aψ := mul_nonneg hCrem₀ (by exact Real.sqrt_nonneg _)
    exact mul_nonneg this (Real.sqrt_nonneg _)
  · -- The Whitney-uniform bound
    intro I φ
    -- Start from cutoff-pairing bound with √(testEnergy)·√(ζ(I))
    have h₁ := PairingSystem.cutoff_pairing_bound (F:=F) (ψ:=ψ) (α:=α) (α':=α') I φ
    -- Control √(testEnergy) by √Aψ
    have hE₀ : 0 ≤ PairingSystem.testEnergy (F:=F) (ψ:=ψ) (α:=α) (α':=α') I φ :=
      PS.testEnergy_nonneg I φ
    have hE   : PairingSystem.testEnergy (F:=F) (ψ:=ψ) (α:=α) (α':=α') I φ ≤ Aψ :=
      PS.uniform_test_energy I φ
    have hE'  : Real.sqrt (PairingSystem.testEnergy (F:=F) (ψ:=ψ) (α:=α) (α':=α') I φ)
                  ≤ Real.sqrt Aψ :=
      Real.sqrt_le_sqrt (by exact hE₀) hE
    -- Control √ζ(I) by √(Cζ · |I|)
    have hζ₀ : 0 ≤ CarlesonSystem.ζ I := CS.ζ_nonneg I
    have hζ  : CarlesonSystem.ζ I ≤ Cζ * I.length := CS.budget I
    have hζ' : Real.sqrt (CarlesonSystem.ζ I)
                ≤ Real.sqrt (Cζ * I.length) :=
      Real.sqrt_le_sqrt hζ₀ hζ
    -- Combine the two monotonicities
    have :=
      mul_le_mul_of_nonneg_left hE' (by exact mul_nonneg_left_of_nonneg hCrem₀ (Real.sqrt_nonneg _))
    have :=
      mul_le_mul_of_nonneg_left hζ' (by
        have : 0 ≤ Crem * Real.sqrt Aψ :=
          mul_nonneg hCrem₀ (Real.sqrt_nonneg _)
        exact this)
    -- Now chain inequalities
    have h₂ :
        Crem
        * Real.sqrt (PairingSystem.testEnergy (F:=F) (ψ:=ψ) (α:=α) (α':=α') I φ)
        * Real.sqrt (CarlesonSystem.ζ I)
        ≤ Crem * Real.sqrt Aψ * Real.sqrt (Cζ * I.length) := by
      -- Use the two previous `mul_le_mul_of_nonneg_left` steps
      -- First step handles the factor `√(testEnergy)`, second handles `√ζ(I)`
      have step1 :
          Crem * Real.sqrt (PairingSystem.testEnergy (F:=F) (ψ:=ψ) (α:=α) (α':=α') I φ)
          ≤ Crem * Real.sqrt Aψ := by
        -- multiply `hE'` on the left by nonneg `Crem`
        exact mul_le_mul_of_nonneg_left hE' hCrem₀
      -- now multiply both sides by nonneg `√ζ(I)` and `√(Cζ·|I|)` accordingly
      have step2 :=
        mul_le_mul_of_nonneg_right step1 (Real.sqrt_nonneg (CarlesonSystem.ζ I))
      have step3 :
          Real.sqrt (CarlesonSystem.ζ I)
          ≤ Real.sqrt (Cζ * I.length) := hζ'
      -- Finish by replacing the rightmost factor using `step3`
      exact
        (le_trans step2
          (by
            have : 0 ≤ Crem * Real.sqrt Aψ :=
              mul_nonneg hCrem₀ (Real.sqrt_nonneg _)
            exact mul_le_mul_of_nonneg_left step3 this))
    -- Finish: replace `√(Cζ·|I|)` by `√Cζ · √|I|`
    have hsplit :
        Real.sqrt (Cζ * I.length) = Real.sqrt Cζ * Real.sqrt (I.length) := by
      have hlen : 0 ≤ I.length := I.length_nonneg
      simpa [Real.sqrt_mul hCζ₀ hlen]
    -- Chain everything together
    calc
      PairingSystem.pairing (F:=F) (ψ:=ψ) (α:=α) (α':=α') I φ
          ≤ Crem * Real.sqrt (PairingSystem.testEnergy (F:=F) (ψ:=ψ) (α:=α) (α':=α') I φ)
                * Real.sqrt (CarlesonSystem.ζ I) := h₁
      _ ≤ Crem * Real.sqrt Aψ * Real.sqrt (Cζ * I.length) := h₂
      _ = Crem * Real.sqrt Aψ * (Real.sqrt Cζ * Real.sqrt (I.length)) := by simpa [hsplit]
      _ = (Crem * Real.sqrt Aψ * Real.sqrt Cζ) * Real.sqrt (I.length) := by ring
      _ = (Crem * Real.sqrt Aψ * Real.sqrt Cζ) * Real.sqrt (WhitneyInterval.length I) := rfl

/-- Specialization: `(P+)` for `F := 2·J` is immediate once instances exist. -/
theorem PPlusFromCarleson_exists_twoJ
    (J : ℂ → ℂ) [CarlesonSystem]
    [PairingSystem (fun s => (2 : ℂ) * J s) ψ α α'] :
    PPlusFromCarleson_exists (F := fun s => (2 : ℂ) * J s) (ψ:=ψ) (α:=α) (α':=α') :=
  PPlusFromCarleson_exists (F := fun s => (2 : ℂ) * J s) (ψ:=ψ) (α:=α) (α':=α')

end Cert
end RH
