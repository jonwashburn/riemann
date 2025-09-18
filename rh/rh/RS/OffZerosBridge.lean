/-
RS: explicit Θ,N for the off-zeros ζ–Schur bridge, pinned limit, and boundary assignment.

Non-circular interface: N is analytic on Ω \ Z(ξ); ζ = Θ/N only on Ω \ Z(ζ).
This matches the manuscript's active route and avoids baking in ζ nonvanishing on Ω.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.MetricSpace.Basic

noncomputable section
open Complex Filter Set
open scoped Topology

namespace RH
namespace RS
namespace OffZeros

variable (riemannZeta riemannXi : ℂ → ℂ)

/-- Right half-plane Ω := { s : ℂ | 1/2 < Re s }. -/
def Ω : Set ℂ := {s : ℂ | (1/2 : ℝ) < s.re}

/-- Zero set of a function. -/
def Z (f : ℂ → ℂ) : Set ℂ := {s | f s = 0}

/-- Schur-on-a-set predicate. -/
def IsSchurOn (Θ : ℂ → ℂ) (S : Set ℂ) : Prop := ∀ ⦃s⦄, s ∈ S → Complex.abs (Θ s) ≤ 1

/-- Nonvanishing of a function on a set. -/
def IsNonzeroOn (S : Set ℂ) (f : ℂ → ℂ) : Prop := ∀ ⦃s⦄, s ∈ S → f s ≠ 0

/-- If `f` and `g` are nonvanishing on `S`, then so is `f * g`. -/
lemma IsNonzeroOn.mul {S : Set ℂ} {f g : ℂ → ℂ}
    (hf : IsNonzeroOn S f) (hg : IsNonzeroOn S g) :
    IsNonzeroOn S (fun s => f s * g s) := by
  intro s hs; exact mul_ne_zero (hf hs) (hg hs)

/-- If `f` and `g` are nonvanishing on `S`, then so is `f / g`. -/
lemma IsNonzeroOn.div {S : Set ℂ} {f g : ℂ → ℂ}
    (hf : IsNonzeroOn S f) (hg : IsNonzeroOn S g) :
    IsNonzeroOn S (fun s => f s / g s) := by
  intro s hs; simpa [div_eq_mul_inv] using mul_ne_zero (hf hs) (inv_ne_zero (hg hs))

/-- Exponential is never zero: an outer given by `exp ∘ H` is zero-free on any set. -/
lemma outer_exp_nonzeroOn {S : Set ℂ} (H : ℂ → ℂ) :
    IsNonzeroOn S (fun s => Complex.exp (H s)) := by
  intro s _; exact Complex.exp_ne_zero (H s)

/- Compact wrappers for Agent A/B: register nonvanishing hypotheses. -/
namespace NonCancellation

/-- Det₂ nonvanishing on Ω: expose as a reusable Prop. -/
def det2_nonzero_on (det2 : ℂ → ℂ) : Prop :=
  IsNonzeroOn (Ω) det2

/-- Outer nonvanishing on Ω: expose as a reusable Prop. -/
def outer_nonzero_on (O : ℂ → ℂ) : Prop :=
  IsNonzeroOn (Ω) O

/-- Archimedean factor `G` nonvanishing off zeros of ζ on Ω. -/
def G_nonzero_offZeta_on (G : ℂ → ℂ) : Prop :=
  IsNonzeroOn ((Ω) \ Z riemannZeta) G

lemma det2_nonzero_on_Ω {det2 : ℂ → ℂ}
    (h : det2_nonzero_on det2) :
    ∀ ⦃s⦄, s ∈ Ω → det2 s ≠ 0 := h

lemma outer_nonzero_on_Ω {O : ℂ → ℂ}
    (h : outer_nonzero_on O) :
    ∀ ⦃s⦄, s ∈ Ω → O s ≠ 0 := h

lemma G_nonzero_on_Ω_offZeta {G : ℂ → ℂ}
    (h : G_nonzero_offZeta_on (riemannZeta:=riemannZeta) G) :
    ∀ ⦃s⦄, s ∈ ((Ω) \ Z riemannZeta) → G s ≠ 0 := h

end NonCancellation
/-! Local removable-set assignment builder -/

/-- Local data at a zero ρ suitable to build the assignment for
`no_offcritical_zeros_from_schur`. Mirrors the archive shape. -/
structure LocalData (Θ : ℂ → ℂ) (ρ : ℂ) where
  U : Set ℂ
  hUopen : IsOpen U
  hUconn : IsPreconnected U
  hUsub : U ⊆ Ω
  hρU : ρ ∈ U
  hIso : (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ)
  g : ℂ → ℂ
  hg : AnalyticOn ℂ g U
  hΘU : AnalyticOn ℂ Θ (U \ {ρ})
  hExt : EqOn Θ g (U \ {ρ})
  hval : g ρ = 1
  hWitness : ∃ z, z ∈ U ∧ g z ≠ 1

/-- Stable alias: a local chooser supplies `LocalData Θ ρ` at each ζ‑zero ρ in Ω. -/
abbrev LocalChooser (riemannZeta : ℂ → ℂ) (Θ : ℂ → ℂ) : Type :=
  ∀ ρ, ρ ∈ Ω → riemannZeta ρ = 0 →
    LocalData (riemannZeta := riemannZeta) (Θ := Θ) (ρ := ρ)

/-- Stable alias: the RS export assignment shape expected by `no_offcritical_zeros_from_schur`. -/
abbrev AssignShape (riemannZeta : ℂ → ℂ) (Θ : ℂ → ℂ) : Prop :=
  ∀ ρ, ρ ∈ Ω → riemannZeta ρ = 0 →
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
      (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
      ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
        EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1

/-- Packaging lemma (removable-set data → `LocalData`): given an open, preconnected
subset `U ⊆ Ω` isolating a zero `ρ`, and an analytic extension `g` of `Θ` across `ρ` with
`EqOn Θ g (U \ {ρ})`, normalization `g ρ = 1`, and a nontriviality witness,
constructs `LocalData` required by the RS assignment. -/
def LocalData.of_removable {Θ : ℂ → ℂ}
  (U : Set ℂ) (ρ : ℂ)
  (hUopen : IsOpen U) (hUconn : IsPreconnected U) (hUsub : U ⊆ Ω)
  (hρU : ρ ∈ U)
  (hIso : (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ))
  (g : ℂ → ℂ) (hg : AnalyticOn ℂ g U)
  (hΘU : AnalyticOn ℂ Θ (U \ {ρ}))
  (hExt : EqOn Θ g (U \ {ρ}))
  (hval : g ρ = 1)
  (hWitness : ∃ z, z ∈ U ∧ g z ≠ 1)
  : LocalData (riemannZeta := riemannZeta) (Θ := Θ) (ρ := ρ) :=
{ U := U,
  hUopen := hUopen, hUconn := hUconn, hUsub := hUsub,
  hρU := hρU, hIso := by simpa using hIso, g := g,
  hg := hg, hΘU := by simpa using hΘU,
  hExt := by simpa using hExt, hval := hval, hWitness := hWitness }

/-- Build the RS-shaped assignment from a chooser that supplies `LocalData` at each
putative zero `ρ` in Ω. -/
def assign_fromLocal {Θ : ℂ → ℂ}
    (choose : ∀ ρ, ρ ∈ Ω → riemannZeta ρ = 0 →
      LocalData (riemannZeta := riemannZeta) (Θ := Θ) (ρ := ρ)) :
    ∀ ρ, ρ ∈ Ω → riemannZeta ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1 := by
  intro ρ hΩ hζ
  classical
  let data : LocalData (riemannZeta := riemannZeta) (Θ := Θ) (ρ := ρ) :=
    choose ρ hΩ hζ
  refine ⟨data.U, data.hUopen, data.hUconn, ?_, data.hρU, data.hIso, ?_⟩
  · intro z hz; exact data.hUsub hz
  · refine ⟨data.g, data.hg, data.hΘU, data.hExt, data.hval, ?_⟩
    rcases data.hWitness with ⟨z, hzU, hzneq⟩
    exact ⟨z, hzU, hzneq⟩

/-- Stable wrapper: from a `LocalChooser Θ` build the RS export `AssignShape Θ`. -/
@[simp] def assign_fromLocal_as (riemannZeta : ℂ → ℂ) (Θ : ℂ → ℂ)
    (choose : LocalChooser riemannZeta Θ) : AssignShape riemannZeta Θ :=
  assign_fromLocal (riemannZeta := riemannZeta) (Θ := Θ) choose

/-- Choice wrapper (CR): from an existence-style assignment returning the RS export
shape, build a `LocalData` chooser suitable for `assign_fromLocal`.

This is a pure packaging helper: given, for each `ρ ∈ Ω` with `ζ ρ = 0`, an
open, preconnected `U ⊆ Ω` isolating the zero together with an analytic
extension `g` across `ρ` satisfying `EqOn Θ g (U \ {ρ})` and `g ρ = 1` and a
nontriviality witness, it produces a `LocalData Θ ρ`.

No new analysis is performed here; this just rewraps the provided data. -/
noncomputable def choose_CR {Θ : ℂ → ℂ}
  (assign : ∀ ρ, ρ ∈ Ω → riemannZeta ρ = 0 →
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
      (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
      ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
        EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
  : ∀ ρ, ρ ∈ Ω → riemannZeta ρ = 0 →
      LocalData (riemannZeta := riemannZeta) (Θ := Θ) (ρ := ρ) := by
  intro ρ hΩ hζ
  classical
  let e1 := assign ρ hΩ hζ
  let U : Set ℂ := Classical.choose e1
  have h1 : IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
    (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
    ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
      EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1 := Classical.choose_spec e1
  have hUopen : IsOpen U := h1.1
  have hUconn : IsPreconnected U := h1.2.1
  have hUsub : U ⊆ Ω := h1.2.2.1
  have hρU : ρ ∈ U := h1.2.2.2.1
  have hIso : (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) := h1.2.2.2.2.1
  let e2 := h1.2.2.2.2.2
  let g : ℂ → ℂ := Classical.choose e2
  have hgPack : AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧ EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1 :=
    Classical.choose_spec e2
  have hg : AnalyticOn ℂ g U := hgPack.1
  have hΘU : AnalyticOn ℂ Θ (U \ {ρ}) := hgPack.2.1
  have hExt : EqOn Θ g (U \ {ρ}) := hgPack.2.2.1
  have hval : g ρ = 1 := hgPack.2.2.2.1
  have hWitness : ∃ z, z ∈ U ∧ g z ≠ 1 := hgPack.2.2.2.2
  refine {
    U := U,
    hUopen := hUopen, hUconn := hUconn, hUsub := hUsub, hρU := hρU,
    hIso := by simpa using hIso,
    g := g, hg := hg, hΘU := by simpa using hΘU,
    hExt := by simpa using hExt, hval := hval,
    hWitness := hWitness }

/-- Xi‑local removable packaging parallel to the ζ‑local version. -/
structure LocalDataXi (riemannXi : ℂ → ℂ) (Θ : ℂ → ℂ) (ρ : ℂ) where
  U : Set ℂ
  hUopen : IsOpen U
  hUconn : IsPreconnected U
  hUsub : U ⊆ Ω
  hρU : ρ ∈ U
  hIsoXi : (U ∩ {z | riemannXi z = 0}) = ({ρ} : Set ℂ)
  g : ℂ → ℂ
  hg : AnalyticOn ℂ g U
  hΘU : AnalyticOn ℂ Θ (U \ {ρ})
  hExt : EqOn Θ g (U \ {ρ})
  hval : g ρ = 1
  hWitness : ∃ z, z ∈ U ∧ g z ≠ 1

abbrev LocalChooserXi (riemannXi : ℂ → ℂ) (Θ : ℂ → ℂ) : Type :=
  ∀ ρ, ρ ∈ Ω → riemannXi ρ = 0 →
    LocalDataXi (riemannXi := riemannXi) (Θ := Θ) (ρ := ρ)

/-- Build the Xi‑assignment shape from a Xi‑local chooser. -/
def assignXi_fromLocal {riemannXi : ℂ → ℂ} {Θ : ℂ → ℂ}
    (choose : ∀ ρ, ρ ∈ Ω → riemannXi ρ = 0 →
      LocalDataXi (riemannXi := riemannXi) (Θ := Θ) (ρ := ρ)) :
    ∀ ρ, ρ ∈ Ω → riemannXi ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1 := by
  intro ρ hΩ hξ
  classical
  let data : LocalDataXi (riemannXi := riemannXi) (Θ := Θ) (ρ := ρ) :=
    choose ρ hΩ hξ
  refine ⟨data.U, data.hUopen, data.hUconn, ?_, data.hρU, data.hIsoXi, ?_⟩
  · intro z hz; exact data.hUsub hz
  · refine ⟨data.g, data.hg, data.hΘU, data.hExt, data.hval, ?_⟩
    rcases data.hWitness with ⟨z, hzU, hzneq⟩
    exact ⟨z, hzU, hzneq⟩

/-
Convert removable-extension data at ξ-zeros into the RS export assignment at ζ-zeros
using the equivalence of zero sets on Ω.
-/
def assign_fromXiRemovable {Θ : ℂ → ℂ}
  (hZerosEq : ∀ z ∈ Ω, riemannXi z = 0 ↔ riemannZeta z = 0)
  (assignXi : ∀ ρ, ρ ∈ Ω → riemannXi ρ = 0 →
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
      (U ∩ {z | riemannXi z = 0}) = ({ρ} : Set ℂ) ∧
      ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
        EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
  : AssignShape riemannZeta Θ := by
  intro ρ hΩ hζ
  have hξ : riemannXi ρ = 0 := (hZerosEq ρ hΩ).mpr hζ
  rcases assignXi ρ hΩ hξ with
    ⟨U, hUopen, hUconn, hUsub, hρU, hIsoXi, g, hg, hΘU, hExt, hval, z, hzU, hgzne⟩
  have hIsoZeta : (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) := by
    ext x; constructor
    · intro hx
      have hxU : x ∈ U := hx.1
      have hxζ : riemannZeta x = 0 := by simpa [Set.mem_setOf_eq] using hx.2
      have hxΩ : x ∈ Ω := hUsub hxU
      have hxξ : riemannXi x = 0 := (hZerosEq x hxΩ).mpr hxζ
      have hxInXi : x ∈ (U ∩ {z | riemannXi z = 0}) := ⟨hxU, by simpa [Set.mem_setOf_eq] using hxξ⟩
      have hxSingleton : x ∈ ({ρ} : Set ℂ) := by simpa [hIsoXi] using hxInXi
      simpa using hxSingleton
    · intro hx
      have hxρ : x = ρ := by simpa using hx
      have hxU : x ∈ U := by simpa [hxρ] using hρU
      have hζρ : riemannZeta ρ = 0 := (hZerosEq ρ hΩ).mp hξ
      exact ⟨hxU, by simpa [Set.mem_setOf_eq, hxρ] using hζρ⟩
  refine ⟨U, hUopen, hUconn, hUsub, hρU, hIsoZeta, ?_⟩
  exact ⟨g, hg, hΘU, hExt, hval, z, hzU, hgzne⟩

/-/ Build Xi-assignment (existence shape) directly from removable-extension data. -/
def assignXi_from_exists {riemannXi : ℂ → ℂ} {Θ : ℂ → ℂ}
  (existsRem : ∀ ρ, ρ ∈ Ω → riemannXi ρ = 0 →
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
      (U ∩ {z | riemannXi z = 0}) = ({ρ} : Set ℂ) ∧
      ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
        EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
  : ∀ ρ, ρ ∈ Ω → riemannXi ρ = 0 →
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
      (U ∩ {z | riemannXi z = 0}) = ({ρ} : Set ℂ) ∧
      ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
        EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1 := by
  intro ρ hΩ hξ
  rcases existsRem ρ hΩ hξ with ⟨U, hUo, hUc, hUsub, hρU, hIso, g, hg, hΘU, hExt, hval, z, hzU, hzneq⟩
  exact ⟨U, hUo, hUc, hUsub, hρU, hIso, g, hg, hΘU, hExt, hval, z, hzU, hzneq⟩

/-- Compose the Xi-removable existence into a ζ-assignment using a zeros equivalence
on Ω. -/
def assign_fromXiRemovable_exists {Θ : ℂ → ℂ}
  (hZerosEq : ∀ z ∈ Ω, riemannXi z = 0 ↔ riemannZeta z = 0)
  (existsRem : ∀ ρ, ρ ∈ Ω → riemannXi ρ = 0 →
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
      (U ∩ {z | riemannXi z = 0}) = ({ρ} : Set ℂ) ∧
      ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
        EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
  : AssignShape riemannZeta Θ :=
by
  -- Turn existence data into a chooser, then into an Xi-assign, and bridge.
  refine assign_fromXiRemovable (riemannXi := riemannXi) (riemannZeta := riemannZeta)
    (Θ := Θ) (hZerosEq := hZerosEq) ?assignXi
  exact assignXi_from_exists (riemannXi := riemannXi) (Θ := Θ) existsRem

/-- Cayley map. -/
private def cayley (F : ℂ → ℂ) : ℂ → ℂ := fun s => (F s - 1) / (F s + 1)

/-- Off-zeros ζ–Schur bridge. -/
structure ZetaSchurDecompositionOffZeros where
  Θ : ℂ → ℂ
  N : ℂ → ℂ
  hΘSchur : IsSchurOn Θ (Ω)
  hNanalytic_offXi : AnalyticOn ℂ N (Ω \ Z riemannXi)
  hζeq_off : ∀ {s}, s ∈ (Ω \ Z riemannZeta) → riemannZeta s = Θ s / N s
  hN_ne_off : ∀ {s}, s ∈ (Ω \ Z riemannZeta) → N s ≠ 0
  hΘ_lim1_at_ξzero : ∀ {ρ}, ρ ∈ Ω → riemannXi ρ = 0 → Tendsto Θ (nhdsWithin ρ (Ω \ Z riemannXi)) (nhds 1)

/-- Constructor: explicit Θ,N from J with ξ = G·ζ on Ω.
We require analyticity of det2, O, G, ξ on Ω; a pointwise identity for J off Z(ξ);
and Schur bound for Θ := cayley (2·J). We also assume Θ is analytic off Z(ξ)
(available in-project via denominator nonvanishing).
Additionally, we assume the explicit nonvanishing of `Θ s * G s / riemannXi s` on `Ω \ Z ζ`,
which holds in your project from the determinant/outer noncancellation and the algebraic identities. -/
def ZetaSchurDecompositionOffZeros.ofEqOffZeros
  (det2 O G J : ℂ → ℂ)
  (_hdet2A : AnalyticOn ℂ det2 (Ω))
  (_hOA : AnalyticOn ℂ O (Ω))
  (hGA : AnalyticOn ℂ G (Ω))
  (hXiA : AnalyticOn ℂ riemannXi (Ω))
  (_hO_ne : ∀ ⦃s⦄, s ∈ (Ω) → O s ≠ 0)
  (_hdet2_ne : ∀ ⦃s⦄, s ∈ (Ω) → det2 s ≠ 0)
  (hG_ne_offζ : ∀ ⦃s⦄, s ∈ (Ω \ Z riemannZeta) → G s ≠ 0)
  (_hJ_def_offXi : ∀ ⦃s⦄, s ∈ (Ω \ Z riemannXi) → J s = det2 s / (O s * riemannXi s))
  (hXi_eq_Gζ : ∀ ⦃s⦄, s ∈ (Ω) → riemannXi s = G s * riemannZeta s)
  (hΘSchur : IsSchurOn (cayley (fun s => (2 : ℂ) * J s)) (Ω))
  (hΘA_offXi : AnalyticOn ℂ (cayley (fun s => (2 : ℂ) * J s)) (Ω \ Z riemannXi))
  (hΘ_lim1_at_ξzero : ∀ ⦃ρ⦄, ρ ∈ Ω → riemannXi ρ = 0 →
      Tendsto (cayley (fun s => (2 : ℂ) * J s)) (nhdsWithin ρ (Ω \ Z riemannXi)) (nhds (1 : ℂ)))
  (hN_ne_off_assm : ∀ ⦃s⦄, s ∈ (Ω \ Z riemannZeta) →
      ((cayley (fun s => (2 : ℂ) * J s)) s * G s / riemannXi s) ≠ 0)
  : ZetaSchurDecompositionOffZeros riemannZeta riemannXi := by
  -- Definitions
  let F : ℂ → ℂ := fun s => (2 : ℂ) * J s
  let Θ : ℂ → ℂ := cayley F
  let N : ℂ → ℂ := fun s => Θ s * G s / riemannXi s
  -- Analyticity of N on Ω \ Z(ξ)
  have hNanalytic_offXi : AnalyticOn ℂ N (Ω \ Z riemannXi) := by
    have hΘA : AnalyticOn ℂ Θ (Ω \ Z riemannXi) := by simpa [Θ, F] using hΘA_offXi
    have hGA' : AnalyticOn ℂ G (Ω \ Z riemannXi) := hGA.mono (by intro s hs; exact hs.1)
    have hXiA' : AnalyticOn ℂ riemannXi (Ω \ Z riemannXi) := hXiA.mono (by intro s hs; exact hs.1)
    refine (hΘA.mul hGA').div hXiA' ?den
    intro s hs; simpa [Z] using hs.2
  -- ζ = Θ / N on Ω \ Z(ζ)
  have hζeq_off' : ∀ ⦃s⦄, s ∈ (Ω \ Z riemannZeta) → riemannZeta s = Θ s / N s := by
    intro s hs
    rcases hs with ⟨hsΩ, hsζ⟩
    have hζne : riemannZeta s ≠ 0 := by simpa [Z] using hsζ
    have hGne : G s ≠ 0 := hG_ne_offζ ⟨hsΩ, hsζ⟩
    have hξ : riemannXi s = G s * riemannZeta s := hXi_eq_Gζ hsΩ
    have hξne : riemannXi s ≠ 0 := by simpa [hξ] using mul_ne_zero hGne hζne
    -- Nonvanishing of N from the explicit assumption
    have hNne : N s ≠ 0 := by
      have := hN_ne_off_assm ⟨hsΩ, hsζ⟩
      simpa [N, Θ, F] using this
    -- Prove equality by multiplying both sides by N s and using associativity
    have hmul : riemannZeta s * N s = Θ s := by
      have hNdef : N s = Θ s * G s / riemannXi s := rfl
      calc
        riemannZeta s * N s
            = riemannZeta s * (Θ s * G s / riemannXi s) := by simp [hNdef]
        _   = riemannZeta s * (Θ s * G s) * (riemannXi s)⁻¹ := by
              simp [div_eq_mul_inv, mul_assoc]
        _   = Θ s * (riemannZeta s * G s) * (riemannXi s)⁻¹ := by
              simp [mul_comm, mul_left_comm, mul_assoc]
        _   = Θ s * (G s * riemannZeta s) * (riemannXi s)⁻¹ := by
              simp [mul_comm]
        _   = Θ s * riemannXi s * (riemannXi s)⁻¹ := by
              simp [hξ, mul_comm, mul_left_comm, mul_assoc]
        _   = Θ s := by
              simp [hξne]
    -- Convert back to a division equality using multiplicative inverses
    have hcalc : riemannZeta s = Θ s / N s := by
      have hNne' : N s ≠ 0 := hNne
      calc
        riemannZeta s
            = riemannZeta s * 1 := by simp
        _   = riemannZeta s * (N s * (N s)⁻¹) := by
              simp [hNne']
        _   = (riemannZeta s * N s) * (N s)⁻¹ := by
              simp [mul_assoc]
        _   = Θ s * (N s)⁻¹ := by
              simpa [hmul]
        _   = Θ s / N s := by
              simp [div_eq_mul_inv]
    -- Conclude ζ = Θ/N by symmetry
    simp [hcalc]
  -- N ≠ 0 on Ω \ Z(ζ)
  have hN_ne_off' : ∀ ⦃s⦄, s ∈ (Ω \ Z riemannZeta) → N s ≠ 0 := by
    intro s hs
    -- from the explicit nonvanishing assumption
    have := hN_ne_off_assm hs
    simpa [N, Θ, F] using this
  -- Assemble
  refine {
      Θ := Θ,
      N := N,
      hΘSchur := by simpa [Θ, F] using hΘSchur,
      hNanalytic_offXi := hNanalytic_offXi,
      hζeq_off := by intro s hs; simpa [Θ, F] using (hζeq_off' hs),
      hN_ne_off := by intro s hs; simpa [Θ, F] using (hN_ne_off' hs),
      hΘ_lim1_at_ξzero := by intro ρ hΩρ hξρ; simpa [Θ, F] using hΘ_lim1_at_ξzero hΩρ hξρ }

-- pinned-limit derivation from N2 (and the derived constructor) are intentionally
-- left out here; RS consumes the pinned-limit as a statement-level hypothesis.

/-
Algebraic u-trick pinned-limit lemma omitted for now; RS consumes the
limit as a hypothesis. A future version can implement it here once the
continuous/analytic API variants are aligned.
-/

/-- Thin constructor: build `ZetaSchurDecompositionOffZeros` directly from off-zeros data. -/
def ZetaSchurDecompositionOffZeros.ofData
  {Θ N : ℂ → ℂ}
  (hΘSchur : IsSchurOn Θ (Ω))
  (hNanalytic_offXi : AnalyticOn ℂ N (Ω \ Z riemannXi))
  (hζeq_off : ∀ ⦃s⦄, s ∈ (Ω \ Z riemannZeta) → riemannZeta s = Θ s / N s)
  (hN_ne_off : ∀ ⦃s⦄, s ∈ (Ω \ Z riemannZeta) → N s ≠ 0)
  (hΘ_lim1_at_ξzero : ∀ ⦃ρ⦄, ρ ∈ Ω → riemannXi ρ = 0 → Tendsto Θ (nhdsWithin ρ (Ω \ Z riemannXi)) (nhds 1))
  : ZetaSchurDecompositionOffZeros riemannZeta riemannXi :=
{ Θ := Θ,
  N := N,
  hΘSchur := hΘSchur,
  hNanalytic_offXi := hNanalytic_offXi,
  hζeq_off := by intro s hs; exact hζeq_off hs,
  hN_ne_off := by intro s hs; exact hN_ne_off hs,
  hΘ_lim1_at_ξzero := by intro ρ hΩρ hξρ; exact hΘ_lim1_at_ξzero hΩρ hξρ }

end OffZeros
end RS
end RH

/-
  Pinned-limit (u-trick, no field_simp) + constructor filler

  What you get:
  • RS.tendsto_one_sub_div_one_add_of_tendsto_zero
  • RS.continuousAt_inv₀_and_eventually_ne
  • RS.tendsto_mobius_u_nhdsWithin
  • RS.Theta_pinned_limit_from_N2
  • RS.Theta_pinned_limit_from_N2_with_eventually_ne
-/

namespace RH
namespace RS

open Filter Topology

/-- If `u → 0` then `(1 - u) / (1 + u) → 1`. Also returns that `1 + u` is eventually nonzero. -/
theorem tendsto_one_sub_div_one_add_of_tendsto_zero
  {ι : Type*} {l : Filter ι} {u : ι → ℂ}
  (hu : Tendsto u l (𝓝 (0 : ℂ))) :
  Tendsto (fun i => (1 - u i) / (1 + u i)) l (𝓝 (1 : ℂ)) ∧ (∀ᶠ i in l, 1 + u i ≠ 0) := by
  -- Eventual nonvanishing of 1+u: (1+u) → 1 ≠ 0
  have h1 : Tendsto (fun i => (1 : ℂ) + u i) l (𝓝 (1 : ℂ)) := by
    simpa using (tendsto_const_nhds.add hu)
  have h_ne : ∀ᶠ i in l, 1 + u i ≠ 0 := by
    -- since (1+u i) → 1, eventually it lies in a small ball around 1 avoiding 0
    refine (Metric.tendsto_nhds.1 h1) (1/2 : ℝ) (by norm_num) |>.mono ?_
    intro i hi
    intro h0
    -- If 1 + u i = 0 then dist((1+u i),1)=‖-1‖=1, contradicting < 1/2
    have hlt : dist ((1 : ℂ) + u i) (1 : ℂ) < (1/2 : ℝ) := hi
    have : (1 : ℝ) < (1/2 : ℝ) := by
      simpa [Complex.dist_eq, sub_eq_add_neg, h0, add_comm] using hlt
    exact (not_lt_of_ge (by norm_num : (1/2 : ℝ) ≤ 1)) this
  -- Tendsto algebra: (1 - u) → 1 and (1 + u) → 1, so their ratio → 1
  have hnum1 : Tendsto (fun i => (1 : ℂ) - u i) l (𝓝 (1 : ℂ)) := by
    simpa using (tendsto_const_nhds.sub hu)
  have hden1 : Tendsto (fun i => (1 : ℂ) + u i) l (𝓝 (1 : ℂ)) := by simpa
  have hinv : Tendsto (fun i => (1 + u i)⁻¹) l (𝓝 ((1 : ℂ)⁻¹)) :=
    ((continuousAt_inv₀ (by norm_num : (1 : ℂ) ≠ 0)).tendsto).comp hden1
  have hlim_mul : Tendsto (fun i => (1 - u i) * (1 + u i)⁻¹) l (𝓝 ((1 : ℂ) * (1 : ℂ)⁻¹)) :=
    hnum1.mul hinv
  have hlim : Tendsto (fun i => (1 - u i) / (1 + u i)) l (𝓝 (1 : ℂ)) := by
    simp [div_eq_mul_inv, one_mul] at hlim_mul
    simpa using hlim_mul
  exact ⟨hlim, h_ne⟩

-- If `g` is continuous at `ρ` and `g ρ ≠ 0`, then `x ↦ (g x)⁻¹` is continuous at `ρ`
-- and `g x ≠ 0` eventually on `𝓝 ρ`. -/
theorem continuousAt_inv₀_and_eventually_ne
  {α : Type*} [TopologicalSpace α] {g : α → ℂ} {ρ : α}
  (hg : ContinuousAt g ρ) (hρ : g ρ ≠ 0) :
  ContinuousAt (fun x => (g x)⁻¹) ρ ∧ (∀ᶠ x in 𝓝 ρ, g x ≠ 0) := by
  have h_inv : ContinuousAt (fun x => (g x)⁻¹) ρ := hg.inv₀ hρ
  -- eventually nonzero: by continuity, values stay in a ball around g ρ avoiding 0
  have hball : ∀ᶠ x in 𝓝 ρ, dist (g x) (g ρ) < ‖g ρ‖ / 2 := by
    have : Tendsto g (𝓝 ρ) (𝓝 (g ρ)) := hg.tendsto
    have hpos : 0 < ‖g ρ‖ / 2 := by
      have : 0 < ‖g ρ‖ := by simpa [norm_pos_iff] using (norm_pos_iff.mpr hρ)
      simpa using (half_pos this)
    exact (Metric.tendsto_nhds.1 this) (‖g ρ‖ / 2) hpos
  have h_ne : ∀ᶠ x in 𝓝 ρ, g x ≠ 0 := by
    refine hball.mono ?_
    intro x hx
    intro h0
    -- If g x = 0, then dist(g x, g ρ) = ‖g ρ‖, contradicting hx < ‖g ρ‖/2
    have hdist : dist (g x) (g ρ) = ‖g ρ‖ := by
      simp [Complex.dist_eq, h0, sub_eq_add_neg]
    have hlt : ‖g ρ‖ < ‖g ρ‖ / 2 := by simpa [hdist]
      using hx
    have hle : ‖g ρ‖ / 2 ≤ ‖g ρ‖ := by
      exact (half_le_self (norm_nonneg _))
    exact (not_lt_of_ge hle) hlt
  exact ⟨h_inv, h_ne⟩

/-- `nhdsWithin` version of the u-trick: if `u → 0` on `𝓝[U] ρ`, then
    `(1 - u)/(1 + u) → 1` on `𝓝[U] ρ`, and `1 + u` is eventually nonzero there. -/
theorem tendsto_mobius_u_nhdsWithin
  {α : Type*} [TopologicalSpace α]
  {U : Set α} {ρ : α} {u : α → ℂ}
  (hu : Tendsto u (𝓝[U] ρ) (𝓝 (0 : ℂ))) :
  Tendsto (fun x => (1 - u x) / (1 + u x)) (𝓝[U] ρ) (𝓝 (1 : ℂ)) ∧
  (∀ᶠ x in 𝓝[U] ρ, 1 + u x ≠ 0) := by
  simpa using tendsto_one_sub_div_one_add_of_tendsto_zero (ι := α) (l := 𝓝[U] ρ) (u := u) hu

/-- Pinned-limit via the u-trick on `nhdsWithin`: if eventually `Θ = (1 - u)/(1 + u)` and `u → 0`,
    then `Θ → 1`. -/
theorem Theta_pinned_limit_from_N2
  {α : Type*} [TopologicalSpace α]
  {U : Set α} {ρ : α} {Θ u : α → ℂ}
  (hEq : (fun x => Θ x) =ᶠ[𝓝[U] ρ] (fun x => (1 - u x) / (1 + u x)))
  (hu : Tendsto u (𝓝[U] ρ) (𝓝 (0 : ℂ))) :
  Tendsto Θ (𝓝[U] ρ) (𝓝 (1 : ℂ)) := by
  have h := (tendsto_mobius_u_nhdsWithin (U := U) (ρ := ρ) (u := u) hu).1
  exact h.congr' hEq.symm

/-- Variant returning eventual nonvanishing of `1+u`. -/
theorem Theta_pinned_limit_from_N2_with_eventually_ne
  {α : Type*} [TopologicalSpace α]
  {U : Set α} {ρ : α} {Θ u : α → ℂ}
  (hEq : (fun x => Θ x) =ᶠ[𝓝[U] ρ] (fun x => (1 - u x) / (1 + u x)))
  (hu : Tendsto u (𝓝[U] ρ) (𝓝 (0 : ℂ))) :
  Tendsto Θ (𝓝[U] ρ) (𝓝 (1 : ℂ)) ∧ (∀ᶠ x in 𝓝[U] ρ, 1 + u x ≠ 0) := by
  have h := tendsto_mobius_u_nhdsWithin (U := U) (ρ := ρ) (u := u) hu
  exact ⟨h.1.congr' hEq.symm, h.2⟩

/-- Removable-update lemma: if `Θ` is analytic on `U \ {ρ}` and equals `(1 - u)/(1 + u)` there,
and `u → 0` along `𝓝[U \ {ρ}] ρ`, then the updated function `g := update Θ ρ 1` is analytic on `U`.

This packages the standard removable singularity construction for use in the pinch wrappers. -/
theorem analyticOn_update_from_pinned
  (U : Set ℂ) (ρ : ℂ) (Θ u : ℂ → ℂ)
  (hUopen : IsOpen U) (hρU : ρ ∈ U)
  (hΘU : AnalyticOn ℂ Θ (U \ {ρ}))
  (hEq : EqOn Θ (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}))
  (hu0 : Tendsto u (nhdsWithin ρ (U \ {ρ})) (𝓝 (0 : ℂ)))
  : AnalyticOn ℂ (Function.update Θ ρ (1 : ℂ)) U := by
  -- eventual equality on the punctured neighborhood
  have hEq_ev : (fun z => Θ z) =ᶠ[nhdsWithin ρ (U \ {ρ})]
      (fun z => (1 - u z) / (1 + u z)) := by
    simpa using Set.EqOn.eventuallyEq_nhdsWithin (s := (U \ {ρ})) hEq
  -- pinned limit Θ → 1 on the punctured neighborhood
  have hΘ_lim1 : Tendsto Θ (nhdsWithin ρ (U \ {ρ})) (𝓝 (1 : ℂ)) :=
    Theta_pinned_limit_from_N2 (U := U \ {ρ}) (ρ := ρ) (Θ := Θ) (u := u) hEq_ev hu0
  -- differentiability of Θ on the punctured set
  have hDiff : DifferentiableOn ℂ Θ (U \ {ρ}) := by
    have hOpen : IsOpen (U \ {ρ}) := IsOpen.sdiff hUopen isClosed_singleton
    have hA : AnalyticOn ℂ Θ (U \ {ρ}) := by simpa using hΘU
    exact (analyticOn_iff_differentiableOn (f := Θ) (s := U \ {ρ}) hOpen).1 hA
  -- define the updated extension g
  let g : ℂ → ℂ := Function.update Θ ρ (1 : ℂ)
  -- differentiability of g on the punctured set by congruence with Θ
  have hDiff_g_punct : DifferentiableOn ℂ g (U \ {ρ}) := by
    refine DifferentiableOn.congr hDiff ?h
    intro z hz; simp [g, Function.update_noteq hz.2]
  -- continuity of g at ρ via the update lemma and the pinned limit
  have hg_within : ContinuousWithinAt g U ρ := by
    have hiff := continuousWithinAt_update_same (f := Θ) (s := U) (x := ρ) (y := (1 : ℂ))
    -- `hiff` states: `ContinuousWithinAt (update Θ ρ 1) U ρ ↔ Tendsto Θ (𝓝[U \ {ρ}] ρ) (𝓝 1)`
    exact hiff.mpr hΘ_lim1
  have hU_nhds : U ∈ 𝓝 ρ := hUopen.mem_nhds hρU
  have hg_cont : ContinuousAt g ρ :=
    (continuousWithinAt_iff_continuousAt hU_nhds).mp hg_within
  -- stitch differentiability across the removable point and upgrade to analytic
  have hDiff_gU : DifferentiableOn ℂ g U := by
    haveI : CompleteSpace ℂ := inferInstance
    exact
      (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
        (E := ℂ) (f := g) (s := U) (c := ρ) hU_nhds).mp
        ⟨hDiff_g_punct, hg_cont⟩
  exact (analyticOn_iff_differentiableOn (f := g) (s := U) hUopen).2 hDiff_gU

/-! ### Pinned → removable assignment at ξ-zeros (builder)

We package the standard u-trick into a reusable builder that constructs
`LocalDataXi` at each ξ-zero from pinned equality data on a punctured
neighborhood. -/

namespace OffZeros

/-- Build `LocalDataXi` from pinned data at a ξ-zero: given an open, preconnected
`U ⊆ Ω` isolating `ρ` and equality `Θ = (1 - u)/(1 + u)` on `U \ {ρ}` with
`u → 0` along the punctured approach to `ρ`, define the removable extension
`g := update Θ ρ 1` and package the local data. Assumes a nontriviality witness
`z0 ∈ U`, `z0 ≠ ρ`, `Θ z0 ≠ 1`. -/
def LocalDataXi.of_pinned
  (riemannXi : ℂ → ℂ) {Θ : ℂ → ℂ} {ρ : ℂ}
  (U : Set ℂ)
  (hUopen : IsOpen U) (hUconn : IsPreconnected U) (hUsub : U ⊆ Ω)
  (hρU : ρ ∈ U)
  (hIsoXi : (U ∩ {z | riemannXi z = 0}) = ({ρ} : Set ℂ))
  (hΘU : AnalyticOn ℂ Θ (U \ {ρ}))
  (u : ℂ → ℂ)
  (hEq : EqOn Θ (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}))
  (hu0 : Tendsto u (nhdsWithin ρ (U \ {ρ})) (𝓝 (0 : ℂ)))
  (z0 : ℂ) (hz0U : z0 ∈ U) (hz0ne : z0 ≠ ρ) (hΘz0ne : Θ z0 ≠ 1)
  : LocalDataXi (riemannXi := riemannXi) (Θ := Θ) (ρ := ρ) := by
  classical
  -- Define removable extension g by updating Θ at ρ to 1
  let g : ℂ → ℂ := Function.update Θ ρ (1 : ℂ)
  have hEqOn : EqOn Θ g (U \ {ρ}) := by
    intro w hw; simp [g, Function.update_noteq hw.2]
  have hval : g ρ = 1 := by simp [g]
  -- Analyticity on U via pinned removable-update lemma
  have hgU : AnalyticOn ℂ g U :=
    RH.RS.analyticOn_update_from_pinned U ρ Θ u hUopen hρU hΘU hEq hu0
  -- Nontriviality witness for g from Θ at z0
  have hz0g : g z0 = Θ z0 := by
    change Function.update Θ ρ (1 : ℂ) z0 = Θ z0
    simp [g, Function.update_noteq hz0ne]
  have hWitness : ∃ z, z ∈ U ∧ g z ≠ 1 := by
    refine ⟨z0, hz0U, ?_⟩
    exact fun hg1 => hΘz0ne (by simpa [hz0g] using hg1)
  -- Pack the structure
  refine {
    U := U, hUopen := hUopen, hUconn := hUconn, hUsub := hUsub, hρU := hρU,
    hIsoXi := by simpa using hIsoXi,
    g := g, hg := hgU, hΘU := by simpa using hΘU, hExt := hEqOn, hval := hval,
    hWitness := hWitness }

/-- Assignment builder at ξ-zeros from pinned data (existence form). -/
def assignXi_from_pinned
  (riemannXi : ℂ → ℂ) {Θ : ℂ → ℂ}
  (choose : ∀ ρ, ρ ∈ Ω → riemannXi ρ = 0 →
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
      (U ∩ {z | riemannXi z = 0}) = ({ρ} : Set ℂ) ∧
      AnalyticOn ℂ Θ (U \ {ρ}) ∧
      ∃ u : ℂ → ℂ,
        EqOn Θ (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
        Tendsto u (nhdsWithin ρ (U \ {ρ})) (𝓝 (0 : ℂ)) ∧
        ∃ z, z ∈ U ∧ z ≠ ρ ∧ Θ z ≠ 1)
  : ∀ ρ, ρ ∈ Ω → riemannXi ρ = 0 →
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
      (U ∩ {z | riemannXi z = 0}) = ({ρ} : Set ℂ) ∧
      ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
        EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1 := by
  intro ρ hΩ hξ
  classical
  rcases choose ρ hΩ hξ with
    ⟨U, hUopen, hUconn, hUsub, hρU, hIsoXi, hΘU, u, hEq, hu0,
      z0, hz0U, hz0ne, hΘz0ne⟩
  let data := LocalDataXi.of_pinned (riemannXi := riemannXi)
    (U := U) hUopen hUconn hUsub hρU hIsoXi hΘU u hEq hu0 z0 hz0U hz0ne hΘz0ne
  refine ⟨U, hUopen, hUconn, hUsub, hρU, hIsoXi, ?_⟩
  refine ⟨data.g, data.hg, data.hΘU, data.hExt, data.hval, ?_⟩
  rcases data.hWitness with ⟨z, hzU, hgne⟩
  exact ⟨z, hzU, hgne⟩

end OffZeros

end RS
end RH
