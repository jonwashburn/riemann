/-
  Recognition Science: The Meta-Principle
  ======================================

  This file establishes the foundational meta-principle as a DEFINITION,
  not an axiom. From this single logical impossibility, we derive the
  necessity of existence and all subsequent principles.

  We use NO external mathematical libraries - everything emerges from
  the recognition principle itself.

  Author: Jonathan Washburn
  Recognition Science Institute
-/

import Core.MetaPrincipleMinimal
import Core.Finite
import Core.Nat.Card
export Core.MetaPrincipleMinimal (Nothing Recognition MetaPrinciple meta_principle_holds)

namespace RecognitionScience

set_option linter.unusedVariables false

/-!
# The Meta-Principle: Nothing Cannot Recognize Itself

This is not an axiom but a logical definition of impossibility.
We define recognition and nothingness, then show their incompatibility.
-/



/-!
## The Chain of Necessity

From this single impossibility, we derive existence itself.
-/

/-- Something must exist (the logical necessity of existence) -/
@[simp]
theorem something_exists : ∃ (X : Type) (_ : X), True :=
  ⟨Unit, (), True.intro⟩

/-- If recognition occurs, the recognizer cannot be nothing -/
@[simp]
theorem recognizer_exists {B : Type} :
  (∃ (_ : Recognition Nothing B), True) → False := by
  intro ⟨r, _⟩
  cases r.recognizer

/-- If recognition occurs, there must be distinction -/
def DistinctionRequired (A : Type) : Prop :=
  ∃ (a₁ a₂ : A), a₁ ≠ a₂ ∨ ∃ (B : Type) (_ : B) (_ : Recognition A B), True

/-!
## Information and Finiteness

Without assuming mathematical structures, we define information
capacity through type cardinality.
-/

/-- Physical systems must have finite information capacity -/
def PhysicallyRealizable (A : Type) : Prop :=
  Nonempty (Finite A)

/-- Helper: Get the cardinality of a finite type -/
def card (A : Type) (h : Finite A) : Nat := h.n

/-- Continuous types have a transformation with no fixed points and between elements -/
def Continuous (A : Type) : Prop :=
  ∃ (a₀ : A) (f : Unit → A → A),
    (∀ a : A, f () a ≠ a) ∧
    (∀ a : A, ∃ between : A, between ≠ a ∧ between ≠ f () a)

/-- Pigeonhole principle for finite types -/
theorem pigeonhole {A : Type} (h : Finite A) (seq : Nat → A) :
  ∃ (i j : Nat), i < j ∧ j ≤ h.n ∧ seq i = seq j := by
  -- Consider the function g : Fin (h.n + 1) → Fin h.n
  -- defined by g k = h.toFin (seq k)
  let g : Fin (h.n + 1) → Fin h.n := fun k => h.toFin (seq k.val)

  -- By the pigeonhole principle (no_inj_succ_to_self), g cannot be injective
  have g_not_inj : ¬Function.Injective g := Nat.Card.no_inj_succ_to_self g

  -- So there exist distinct i, j : Fin (h.n + 1) with g i = g j
  unfold Function.Injective at g_not_inj
  push_neg at g_not_inj
  obtain ⟨i, j, h_eq, h_ne⟩ := g_not_inj

  -- We have h.toFin (seq i) = h.toFin (seq j) with i ≠ j
  -- Since h.toFin is injective, this means seq i = seq j
  have seq_eq : seq i.val = seq j.val := by
    have : h.fromFin (h.toFin (seq i.val)) = h.fromFin (h.toFin (seq j.val)) := by
      simp [g] at h_eq
      rw [h_eq]
    rwa [h.left_inv, h.left_inv] at this

  -- Order i and j so that i < j
  cases Nat.lt_trichotomy i.val j.val with
  | inl h_lt =>
    -- i < j case
    use i.val, j.val
    constructor
    · exact h_lt
    constructor
    · -- j.val < h.n + 1, so j.val ≤ h.n
      exact Nat.le_of_succ_le_succ j.2
    · exact seq_eq
  | inr h_ge =>
    cases h_ge with
    | inl h_eq_vals =>
      -- i.val = j.val contradicts i ≠ j
      exfalso
      apply h_ne
      ext
      exact h_eq_vals
    | inr h_gt =>
      -- j < i case
      use j.val, i.val
      constructor
      · exact h_gt
      constructor
      · -- i.val < h.n + 1, so i.val ≤ h.n
        exact Nat.le_of_succ_le_succ i.2
      · exact seq_eq.symm

/-!
## The Path to Discreteness

From finiteness, we derive the discrete nature of recognition.
-/

/-- Time steps are discrete natural numbers -/
def TimeStep := Nat

/-- A recognition sequence -/
def RecognitionSequence (A : Type) := TimeStep → A

/-- A deterministic evolution function -/
structure Evolution (A : Type) where
  next : A → A

/-- Generate a sequence from an evolution function -/
def Evolution.toSequence {A : Type} (f : Evolution A) (start : A) : RecognitionSequence A :=
  fun n => Nat.recOn n start (fun _ prev => f.next prev)

/-- Helper: Addition for TimeStep (which is just Nat) -/
instance : Add TimeStep where
  add := Nat.add

/-- Discrete time: sequences must have repetitions -/
theorem discrete_time {A : Type} :
  PhysicallyRealizable A →
  ∀ (seq : RecognitionSequence A),
  ∃ (period : Nat) (hfinite : Finite A), period > 0 ∧ period ≤ hfinite.n ∧
  ∃ (i j : Nat), i < j ∧ j - i = period ∧ seq i = seq j := by
  intro ⟨hfinite⟩ seq
  -- By pigeonhole principle
  have ⟨i, j, hij_lt, hj_le, hij_eq⟩ := pigeonhole hfinite seq
  use j - i, hfinite
  refine ⟨Nat.sub_pos_of_lt hij_lt, ?_, i, j, hij_lt, rfl, hij_eq⟩
  -- period = j - i ≤ j ≤ hfinite.n
  calc j - i ≤ j := Nat.sub_le j i
  _ ≤ hfinite.n := hj_le

end RecognitionScience
