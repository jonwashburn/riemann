
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Local Stokes theorem on a box: divergence-theorem wrapper

This file is intentionally *thin*: it introduces a single definition for the
"boundary integral" appearing in the divergence theorem on rectangular boxes,
then restates `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'`
with that definition so that the proof is a single `simpa`.

The goal is to serve as the local core for Stokes-type statements, while keeping
all substantive analysis in `Mathlib.MeasureTheory.Integral.DivergenceTheorem`.

In particular:
* We do **not** introduce any new simplex/cube API.
* We do **not** reprove FTC/Fubini.
* The only lemma proofs here are `by simpa [...] using ...`.

See the docstring of `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'`
for the precise hypotheses and the geometric interpretation of the RHS (faces
encoded using `Fin.succAbove` and `Fin.insertNth`).
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace MeasureTheory
namespace Stokes

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ}

/-- The boundary integral on the box `[a,b] ⊆ (Fin (n+1) → ℝ)` corresponding to the
faces `x i = a i` and `x i = b i`.

This is *definitionally aligned* with the right-hand side of
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'`.

* `face i` is the box `[a ∘ i.succAbove, b ∘ i.succAbove] ⊆ (Fin n → ℝ)`;
* the embeddings of faces are `i.insertNth (a i)` and `i.insertNth (b i)`.
-/
def boxBoundaryIntegral
    (a b : Fin (n + 1) → ℝ)
    (f : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) : E :=
  ∑ i : Fin (n + 1),
      ((∫ x : (Fin n → ℝ) in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          f i (i.insertNth (b i) x))
        - ∫ x : (Fin n → ℝ) in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            f i (i.insertNth (a i) x))

/-- A one-line restatement of `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'`.

This is the recommended entry point for downstream Stokes developments: you
provide the coefficient family `f i` and a (Fréchet) derivative family `f' i x`,
and this lemma gives the boundary-term sum over faces.
-/
theorem integral_divergence_eq_boxBoundaryIntegral
    (a b : Fin (n + 1) → ℝ) (hle : a ≤ b)
    (f : Fin (n + 1) → (Fin (n + 1) → ℝ) → E)
    (f' : Fin (n + 1) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] E)
    (s : Set (Fin (n + 1) → ℝ)) (hs : s.Countable)
    (Hc : ∀ i, ContinuousOn (f i) (Set.Icc a b))
    (Hd : ∀ x ∈ (Set.univ.pi fun i : Fin (n + 1) => Set.Ioo (a i) (b i)) \ s,
        ∀ i, HasFDerivAt (f i) (f' i x) x)
    (Hi : IntegrableOn (fun x : (Fin (n + 1) → ℝ) =>
          ∑ i : Fin (n + 1), (f' i x) (Pi.single i 1)) (Set.Icc a b) volume) :
    (∫ x in Set.Icc a b, ∑ i : Fin (n + 1), (f' i x) (Pi.single i 1))
      = boxBoundaryIntegral (n := n) a b f := by
  simpa [boxBoundaryIntegral] using
    (MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'
      (E := E) (n := n) (a := a) (b := b) (hle := hle)
      (f := f) (f' := f') (s := s) (hs := hs)
      (Hc := Hc) (Hd := Hd) (Hi := Hi))

/-- Specialization of `integral_divergence_eq_boxBoundaryIntegral` to the standard unit cube
`[0,1] ⊆ (Fin (n+1) → ℝ)`.

This is often the most convenient form when building Stokes for simplices/cubes,
since the face domains are again unit cubes in one lower dimension.
-/
theorem integral_divergence_eq_boxBoundaryIntegral_unitCube
    (f : Fin (n + 1) → (Fin (n + 1) → ℝ) → E)
    (f' : Fin (n + 1) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] E)
    (s : Set (Fin (n + 1) → ℝ)) (hs : s.Countable)
    (Hc : ∀ i, ContinuousOn (f i) (Set.Icc (0 : Fin (n + 1) → ℝ) 1))
    (Hd : ∀ x ∈ (Set.univ.pi fun i : Fin (n + 1) => Set.Ioo (0 : ℝ) 1) \ s,
        ∀ i, HasFDerivAt (f i) (f' i x) x)
    (Hi : IntegrableOn (fun x : (Fin (n + 1) → ℝ) =>
          ∑ i : Fin (n + 1), (f' i x) (Pi.single i 1))
        (Set.Icc (0 : Fin (n + 1) → ℝ) 1) volume) :
    (∫ x in Set.Icc (0 : Fin (n + 1) → ℝ) 1,
        ∑ i : Fin (n + 1), (f' i x) (Pi.single i 1))
      = boxBoundaryIntegral (n := n) (0 : Fin (n + 1) → ℝ) 1 f := by
  -- `hle : (0 : ℝⁿ⁺¹) ≤ 1` is pointwise `0 ≤ 1`.
  have hle : (0 : Fin (n + 1) → ℝ) ≤ 1 := by
    intro i
    simp
  simpa using
    (integral_divergence_eq_boxBoundaryIntegral (E := E) (n := n)
      (a := (0 : Fin (n + 1) → ℝ)) (b := 1) (hle := hle)
      (f := f) (f' := f') (s := s) (hs := hs) (Hc := Hc) (Hd := Hd) (Hi := Hi))

/-!
## Convenience corollaries

The core divergence theorem in mathlib is formulated with a countable exceptional set
`s` where differentiability may fail. For many downstream use cases, one has
differentiability everywhere on the open box, and it is more convenient to use
the specialization to `s = ∅`.
-/

/-- `integral_divergence_eq_boxBoundaryIntegral` with `s = ∅`.

This is purely a convenience lemma; the proof is `simpa` using the main wrapper.
-/
theorem integral_divergence_eq_boxBoundaryIntegral_of_hasFDerivAt
    (a b : Fin (n + 1) → ℝ) (hle : a ≤ b)
    (f : Fin (n + 1) → (Fin (n + 1) → ℝ) → E)
    (f' : Fin (n + 1) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] E)
    (Hc : ∀ i, ContinuousOn (f i) (Set.Icc a b))
    (Hd : ∀ x ∈ (Set.univ.pi fun i : Fin (n + 1) => Set.Ioo (a i) (b i)),
        ∀ i, HasFDerivAt (f i) (f' i x) x)
    (Hi : IntegrableOn (fun x : (Fin (n + 1) → ℝ) =>
          ∑ i : Fin (n + 1), (f' i x) (Pi.single i 1)) (Set.Icc a b) volume) :
    (∫ x in Set.Icc a b, ∑ i : Fin (n + 1), (f' i x) (Pi.single i 1))
      = boxBoundaryIntegral (n := n) a b f := by
  classical
  simpa using
    (integral_divergence_eq_boxBoundaryIntegral (E := E) (n := n)
      (a := a) (b := b) (hle := hle) (f := f) (f' := f')
      (s := (∅ : Set (Fin (n + 1) → ℝ))) (hs := Set.countable_empty)
      (Hc := Hc)
      (Hd := by
        intro x hx
        -- `hx : x ∈ interior \ ∅` simplifies to `hx : x ∈ interior`.
        simpa using Hd x (by simpa using hx))
      (Hi := Hi))

/-- `integral_divergence_eq_boxBoundaryIntegral_unitCube` with `s = ∅`.

This is purely a convenience lemma; the proof is `simpa` using the unit-cube wrapper.
-/
theorem integral_divergence_eq_boxBoundaryIntegral_unitCube_of_hasFDerivAt
    (f : Fin (n + 1) → (Fin (n + 1) → ℝ) → E)
    (f' : Fin (n + 1) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] E)
    (Hc : ∀ i, ContinuousOn (f i) (Set.Icc (0 : Fin (n + 1) → ℝ) 1))
    (Hd : ∀ x ∈ (Set.univ.pi fun _ : Fin (n + 1) => Set.Ioo (0 : ℝ) 1),
        ∀ i, HasFDerivAt (f i) (f' i x) x)
    (Hi : IntegrableOn (fun x : (Fin (n + 1) → ℝ) =>
          ∑ i : Fin (n + 1), (f' i x) (Pi.single i 1))
        (Set.Icc (0 : Fin (n + 1) → ℝ) 1) volume) :
    (∫ x in Set.Icc (0 : Fin (n + 1) → ℝ) 1,
        ∑ i : Fin (n + 1), (f' i x) (Pi.single i 1))
      = boxBoundaryIntegral (n := n) (0 : Fin (n + 1) → ℝ) 1 f := by
  classical
  simpa using
    (integral_divergence_eq_boxBoundaryIntegral_unitCube (E := E) (n := n)
      (f := f) (f' := f')
      (s := (∅ : Set (Fin (n + 1) → ℝ))) (hs := Set.countable_empty)
      (Hc := Hc)
      (Hd := by
        intro x hx
        simpa using Hd x (by simpa using hx))
      (Hi := Hi))

end Stokes
end MeasureTheory
