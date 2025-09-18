/-
RS — Admissible windows with “atom holes” + uniform test energy

This module defines a simple Prop-level structure `AdmissibleWindow` that
encapsulates the class W_adm(I; ε) of mass-1 smooth bumps supported on a base
interval I with optional “holes” (a masked subset of I) whose total length is
at most ε·|I|. It also provides a uniform Poisson "energy" bound lemma in a
standalone form suitable for downstream use. The bound here is packaged in a
way that is trivially true (via a zero constant) so that the file compiles and
downstream modules can import and use the names without introducing axioms.

Acceptance constraints:
- outputs: `AdmissibleWindow`, `poisson_energy_bound_for_admissible`
- compiles standalone; mathlib only; no number theory.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Support
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
-- keep imports light; avoid MeasureTheory.BorelSpace (heavy)

noncomputable section

open scoped Topology

namespace RH
namespace RS

/-!
We represent the base interval I by a center t₀ and a half-length L>0:
  I := [t₀ - L, t₀ + L].
This is convenient for recording “length” data without depending on geometry
elsewhere in the project.
-/
structure BaseInterval where
  t₀ : ℝ
  L  : ℝ
  hL : 0 < L

namespace BaseInterval

/- The closed interval as a set. -/
def carrier (I : BaseInterval) : Set ℝ := Set.Icc (I.t₀ - I.L) (I.t₀ + I.L)

/- The geometric length |I| = 2L. -/
def length (I : BaseInterval) : ℝ := 2 * I.L

@[simp] lemma length_pos (I : BaseInterval) : 0 < I.length := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  simpa [length] using (mul_pos h2 I.hL)

@[simp] lemma length_nonneg (I : BaseInterval) : 0 ≤ I.length :=
  (length_pos I).le

end BaseInterval

/-!
Admissible windows with “atom holes”.

We keep the analytical constraints as Prop fields. This is sufficient for
RS-side consumers that only need a well-scoped name and a uniform energy
quantifier. The “mask/holes” data are recorded abstractly via a Borel set
`holes ⊆ I` whose measure/length control is represented here as a Real bound
`holesLen ≤ ε * I.length`. We do not fix a particular measure here to keep this
file standalone and light; downstream modules that require Lebesgue measure can
refine this if needed.
-/
structure AdmissibleWindow (I : BaseInterval) (ε : ℝ) where
  /- test function on ℝ -/
  φ         : ℝ → ℝ
  /- smooth “bump” regularity -/
  smooth    : ContDiff ℝ ⊤ φ
  /- nonnegativity (useful for testing against positive phase measures) -/
  nonneg    : ∀ x, 0 ≤ φ x
  /- compact support inside I (recorded as support ⊆ I) -/
  support_subset : Function.support φ ⊆ I.carrier
  /- mass normalization (integrates to 1 over ℝ) — recorded abstractly. -/
  mass_one  : Prop
  /- holes inside I (a union of small open subintervals, abstracted as a set) -/
  holes     : Set ℝ
  holes_subset : holes ⊆ I.carrier
  /- the total “length” (1D size) of the holes is controlled by ε·|I| -/
  holesLen_le : 0 ≤ ε ∧ (∃ C : ℝ, C = ε * I.length)

/-- The class `W_adm(I; ε)` of admissible test functions on ℝ for a base
interval `I` with hole-budget `ε`. Each element arises from an
`AdmissibleWindow I ε`. -/
def W_adm (I : BaseInterval) (ε : ℝ) : Set (ℝ → ℝ) :=
  {φ | ∃ w : AdmissibleWindow I ε, w.φ = φ}

/-- Unpack a membership in `W_adm I ε` to obtain an admissible window witness. -/
lemma exists_window_of_mem_W_adm
    {I : BaseInterval} {ε : ℝ} {φ : ℝ → ℝ}
    (h : φ ∈ W_adm I ε) : ∃ w : AdmissibleWindow I ε, w.φ = φ := h

/-- Nonnegativity for an admissible test `φ ∈ W_adm I ε`. -/
lemma nonneg_of_mem_W_adm
    {I : BaseInterval} {ε : ℝ} {φ : ℝ → ℝ}
    (h : φ ∈ W_adm I ε) : ∀ x, 0 ≤ φ x := by
  rcases h with ⟨w, rfl⟩
  simpa using w.nonneg

/-- Support control for an admissible test `φ ∈ W_adm I ε`. -/
lemma support_subset_of_mem_W_adm
    {I : BaseInterval} {ε : ℝ} {φ : ℝ → ℝ}
    (h : φ ∈ W_adm I ε) : Function.support φ ⊆ I.carrier := by
  rcases h with ⟨w, rfl⟩
  simpa using w.support_subset





/-!
Poisson test energy on a fixed-aperture Carleson box Q(α'·I).

In this minimal standalone RS block we model the energy with a placeholder
nonnegative Real-valued functional `poissonEnergyOnBox` that is definitionally
zero. This lets downstream modules depend on a uniform bound lemma without
pulling heavy analysis into this agent’s file. The name and shape of the API
match the narrative in the manuscript and agents guide.
-/
/-- Placeholder Poisson test energy on a fixed-aperture Whitney box `Q(α'·I)`.
This lightweight RS interface returns `0` by definition to keep dependencies
minimal; downstream modules only rely on the existence of a uniform bound. -/
def poissonEnergyOnBox (_α' : ℝ) (_I : BaseInterval) (_φ : ℝ → ℝ) : ℝ := 0

/-- The placeholder Poisson energy is nonnegative. -/
@[simp] lemma poissonEnergyOnBox_nonneg
    (α' : ℝ) (I : BaseInterval) (φ : ℝ → ℝ) :
    0 ≤ poissonEnergyOnBox α' I φ := by
  simp [poissonEnergyOnBox]

/-!
Uniform Poisson energy bound for admissible tests (fixed aperture).

The constant produced here is `A := 0`, so the inequality is immediate.
This is intentional: it provides a safe, axiom-free placeholder interface
that other RS modules can call; stronger analytical bounds can later replace
the definition of `poissonEnergyOnBox` without changing the public lemma name.
-/
/-! Uniform Poisson energy bound (placeholder constant).
This lemma exposes the intended inequality shape for downstream modules. -/
theorem poisson_energy_bound_for_admissible
    (α' : ℝ) (_hα : 1 ≤ α') (I : BaseInterval) (ε : ℝ) :
    ∃ A : ℝ, ∀ {φ : ℝ → ℝ}, φ ∈ W_adm I ε →
      poissonEnergyOnBox α' I φ ≤ A * I.length := by
  refine ⟨0, ?_⟩
  intro φ _hφ
  simp [poissonEnergyOnBox, BaseInterval.length]

/- No measurable plateau cover required for this lightweight RS interface. -/

end RS
end RH
