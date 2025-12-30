/-
PR 1: Filtered objects in an abelian category (Deligne, *Théorie de Hodge II*, §1.1).

This file is designed to be a self-contained Mathlib-style contribution providing:

* Decreasing ℤ-indexed filtrations on objects of an abelian category.
* Finiteness (boundedness) of filtrations.
* Shifted filtrations.
* Induced filtrations on subobjects.
* Quotient filtrations on cokernels of monomorphisms.
* Associated graded pieces `Gr`.
* The category of filtered objects and its forgetful functor.

The definitions follow Deligne (1.1.2), (1.1.4), (1.1.5), (1.1.7), (1.1.8).

No analytic or Hodge-theoretic content is introduced here; this is the purely categorical
infrastructure needed for later PRs.
-/

import Mathlib

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/-- A decreasing (i.e. antitone) ℤ-indexed filtration on an object `A`.

This matches Deligne (1.1.2) ("filtration décroissante") where the condition is
`m ≤ n ⇒ F n ≤ F m`.
-/
structure DecFiltration (A : C) where
  /-- The `n`-th step `F n` of the filtration, as a subobject of `A`. -/
  F : ℤ → Subobject A
  /-- The filtration is decreasing: `n ≤ m ⇒ F m ≤ F n`. -/
  antitone' : Antitone F

attribute [simp] DecFiltration.antitone'

namespace DecFiltration

variable {A : C}

/-- Coercion from a filtration to its underlying function `ℤ → Subobject A`. -/
instance : CoeFun (DecFiltration A) (fun _ => ℤ → Subobject A) where
  coe F := F.F

@[simp] lemma antitone (F : DecFiltration A) : Antitone (F : ℤ → Subobject A) :=
  F.antitone'

/-- A filtration is *finite* if it is bounded above by `⊤` and bounded below by `⊥`.

This is Deligne (1.1.4).
-/
def IsFinite [Abelian C] (F : DecFiltration A) : Prop :=
  ∃ a b : ℤ, (∀ n : ℤ, n ≤ a → F n = ⊤) ∧ (∀ n : ℤ, b ≤ n → F n = ⊥)

/-- Shift a decreasing filtration by an integer `k`:
`(F.shift k) n = F (n + k)`.

This corresponds to Deligne's shifted filtrations (1.1.2).
-/
def shift (F : DecFiltration A) (k : ℤ) : DecFiltration A where
  F n := F (n + k)
  antitone' := by
    intro m n h
    exact F.antitone (by omega)

@[simp] lemma shift_apply (F : DecFiltration A) (k n : ℤ) : F.shift k n = F (n + k) := rfl

/-- The associated graded piece `Gr^n(A) = F^n(A) / F^{n+1}(A)`.

This is Deligne (1.1.7) (with ℤ-indexing).

We define it as the cokernel of the canonical monomorphism `F(n+1) → F(n)` induced
by the inequality `F(n+1) ≤ F(n)`.
-/
noncomputable def gr [Abelian C] (F : DecFiltration A) (n : ℤ) : C :=
  let le' : F (n + 1) ≤ F n := F.antitone (by omega)
  cokernel ((F (n + 1)).ofLE (F n) le')

/-- The induced filtration on a subobject `X ⊆ A`.

Deligne (1.1.8) says the induced filtration is characterized by strictness of the
inclusion; categorically it is computed as pullback along the monomorphism `X → A`.
-/
noncomputable def induced [Abelian C] (F : DecFiltration A) (X : Subobject A) :
    DecFiltration (X : C) where
  F n := (Subobject.pullback X.arrow).obj (F n)
  antitone' := by
    intro m n h
    exact (Subobject.pullback X.arrow).monotone (F.antitone h)

@[simp] lemma induced_apply [Abelian C] (F : DecFiltration A) (X : Subobject A) (n : ℤ) :
    F.induced X n = (Subobject.pullback X.arrow).obj (F n) := rfl

/-- The quotient object `A/X` for a subobject `X ⊆ A` in an abelian category.

We define it as the cokernel of the monomorphism `X → A`.
-/
noncomputable def quotientObj [Abelian C] (X : Subobject A) : C :=
  cokernel X.arrow

/-- The quotient map `A → A/X`. -/
noncomputable def quotientπ [Abelian C] (X : Subobject A) : A ⟶ quotientObj X :=
  cokernel.π X.arrow

/-- The quotient filtration on `A/X`.

Deligne (1.1.8) defines the quotient filtration as the unique filtration making the
projection strict; abstractly it is given by mapping each step along the quotient map.

Note: We use the image of the composite `F(n).arrow ≫ quotientπ X` to define the
image of F(n) in the quotient.
-/
noncomputable def quotient [Abelian C] (F : DecFiltration A) (X : Subobject A) :
    DecFiltration (quotientObj X) where
  F n := Subobject.mk (image.ι ((F n).arrow ≫ quotientπ X))
  antitone' := by
    intro m n h
    have hle : F n ≤ F m := F.antitone h
    refine Subobject.mk_le_mk_of_comm (image.lift
      { I := image ((F m).arrow ≫ quotientπ X)
        m := image.ι ((F m).arrow ≫ quotientπ X)
        e := (F n).ofLE (F m) hle ≫ factorThruImage ((F m).arrow ≫ quotientπ X)
        fac := by rw [Category.assoc, image.fac, ← Category.assoc, Subobject.ofLE_arrow] }) ?_
    exact image.lift_fac _

@[simp] lemma quotient_apply [Abelian C] (F : DecFiltration A)
    (X : Subobject A) (n : ℤ) :
    F.quotient X n = Subobject.mk (image.ι ((F n).arrow ≫ quotientπ X)) := rfl

end DecFiltration

/-- A filtered object of a category: an object equipped with a decreasing ℤ-filtration.

This is Deligne's "objet filtré" (1.1.2).
-/
structure FilteredObject (C : Type u) [Category.{v} C] where
  /-- The underlying object. -/
  obj : C
  /-- The decreasing filtration on `obj`. -/
  F : DecFiltration obj

namespace FilteredObject

instance : Coe (FilteredObject C) C where
  coe X := X.obj

/-- The image of a subobject under a morphism, defined via image factorization.

For `S : Subobject A` and `f : A ⟶ B`, this is the subobject of `B` given by
the image of the composite `S.arrow ≫ f`.
-/
noncomputable def imageSubobject [Abelian C] {A B : C} (f : A ⟶ B) (S : Subobject A) :
    Subobject B :=
  Subobject.mk (image.ι (S.arrow ≫ f))

lemma imageSubobject_mono [Abelian C] {A B : C} (f : A ⟶ B) :
    Monotone (imageSubobject f : Subobject A → Subobject B) := by
  intro S T hle
  dsimp [imageSubobject]
  refine Subobject.mk_le_mk_of_comm (image.lift
    { I := image (T.arrow ≫ f)
      m := image.ι (T.arrow ≫ f)
      e := S.ofLE T hle ≫ factorThruImage (T.arrow ≫ f)
      fac := by rw [Category.assoc, image.fac, ← Category.assoc, Subobject.ofLE_arrow] }) ?_
  exact image.lift_fac _

/-- Morphisms of filtered objects (Deligne (1.1.5)).

A morphism `f : (A,F) → (B,G)` is a morphism `A → B` such that for all `n` the image of
`F n` lands inside `G n`.

We express this as `imageSubobject f (A.F n) ≤ B.F n`.
-/
structure Hom [Abelian C] (A B : FilteredObject C) where
  /-- Underlying morphism in `C`. -/
  hom : (A : C) ⟶ (B : C)
  /-- Filtration-compatibility: `f(F^n A) ⊆ F^n B`. -/
  compat : ∀ n : ℤ, imageSubobject hom (A.F n) ≤ B.F n

attribute [simp] Hom.compat

@[ext] lemma Hom.ext [Abelian C] {A B : FilteredObject C} (f g : Hom A B)
    (h : f.hom = g.hom) : f = g := by
  cases f; cases g; simp_all

/-- Identity morphism of a filtered object. -/
noncomputable def id [Abelian C] (A : FilteredObject C) : Hom A A where
  hom := 𝟙 A.obj
  compat := by
    intro n
    dsimp only [imageSubobject]
    -- Goal: Subobject.mk (image.ι ((A.F n).arrow ≫ 𝟙 A.obj)) ≤ A.F n
    -- Since (A.F n).arrow is mono and composing with id preserves this,
    -- factorThruImage is an isomorphism
    have hf : (A.F n).arrow ≫ 𝟙 A.obj = (A.F n).arrow := Category.comp_id _
    haveI hmono : Mono ((A.F n).arrow ≫ 𝟙 A.obj) := by rw [hf]; infer_instance
    haveI : Mono (factorThruImage ((A.F n).arrow ≫ 𝟙 A.obj)) :=
      mono_of_mono_fac (image.fac _)
    haveI : IsIso (factorThruImage ((A.F n).arrow ≫ 𝟙 A.obj)) :=
      isIso_of_mono_of_epi _
    -- Use Subobject.mk_le_of_comm: need g such that g ≫ (A.F n).arrow = image.ι (...)
    apply Subobject.mk_le_of_comm (inv (factorThruImage ((A.F n).arrow ≫ 𝟙 A.obj)))
    -- Need: inv (factorThruImage f) ≫ (A.F n).arrow = image.ι f
    rw [IsIso.inv_comp_eq, image.fac, hf]

/-- Key lemma: imageSubobject (f ≫ g) S ≤ imageSubobject g (imageSubobject f S).

The image of S under f ≫ g is contained in the image under g of the image of S under f.
-/
lemma imageSubobject_comp_le [Abelian C] {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (S : Subobject A) :
    imageSubobject (f ≫ g) S ≤ imageSubobject g (imageSubobject f S) := by
  dsimp only [imageSubobject]
  -- Goal: Subobject.mk (image.ι (S.arrow ≫ f ≫ g)) ≤
  --       Subobject.mk (image.ι ((Subobject.mk (image.ι (S.arrow ≫ f))).arrow ≫ g))

  -- Let T = Subobject.mk (image.ι (S.arrow ≫ f))
  let T := Subobject.mk (image.ι (S.arrow ≫ f))

  -- Name the morphisms we're working with
  let sfg := S.arrow ≫ f ≫ g  -- The original composite
  let sf := S.arrow ≫ f       -- First part
  let Tg := T.arrow ≫ g       -- T.arrow composed with g

  -- Key: (underlyingIso m).inv ≫ (mk m).arrow = m
  -- So (underlyingIso (image.ι sf)).inv ≫ T.arrow = image.ι sf
  have key : (Subobject.underlyingIso (image.ι sf)).inv ≫ T.arrow = image.ι sf :=
    Subobject.underlyingIso_arrow _

  -- Build the MonoFactorisation of sfg through image.ι Tg
  have fac_eq : (factorThruImage sf ≫ (Subobject.underlyingIso (image.ι sf)).inv ≫
      factorThruImage Tg) ≫ image.ι Tg = sfg := by
    rw [Category.assoc, Category.assoc, image.fac]
    -- Goal: factorThruImage sf ≫ (underlyingIso ...).inv ≫ T.arrow ≫ g = sfg
    rw [← Category.assoc (Subobject.underlyingIso _).inv, key]
    -- Goal: factorThruImage sf ≫ image.ι sf ≫ g = sfg
    rw [← Category.assoc, image.fac]
    -- Goal: sf ≫ g = sfg, which is true by definition
    aesop

  let MF : MonoFactorisation sfg := {
    I := image Tg
    m := image.ι Tg
    e := factorThruImage sf ≫ (Subobject.underlyingIso (image.ι sf)).inv ≫ factorThruImage Tg
    fac := fac_eq
  }

  -- Now apply Subobject.mk_le_of_comm with the composed morphism
  refine Subobject.mk_le_of_comm
    (image.lift MF ≫ (Subobject.underlyingIso (image.ι Tg)).inv) ?_
  -- Need: (image.lift MF ≫ (underlyingIso ...).inv) ≫ (Subobject.mk ...).arrow = image.ι sfg
  rw [Category.assoc, Subobject.underlyingIso_arrow, image.lift_fac]

/-- Composition of morphisms of filtered objects. -/
noncomputable def comp [Abelian C] {A B D : FilteredObject C} (f : Hom A B) (g : Hom B D) :
    Hom A D where
  hom := f.hom ≫ g.hom
  compat := by
    intro n
    calc imageSubobject (f.hom ≫ g.hom) (A.F n)
        ≤ imageSubobject g.hom (imageSubobject f.hom (A.F n)) := imageSubobject_comp_le _ _ _
      _ ≤ imageSubobject g.hom (B.F n) := imageSubobject_mono g.hom (f.compat n)
      _ ≤ D.F n := g.compat n

noncomputable instance [Abelian C] : Category (FilteredObject C) where
  Hom A B := Hom A B
  id A := id A
  comp f g := comp f g
  id_comp := by
    intro A B f
    ext
    simp only [FilteredObject.id, FilteredObject.comp, Category.id_comp]
  comp_id := by
    intro A B f
    ext
    simp only [FilteredObject.id, FilteredObject.comp, Category.comp_id]
  assoc := by
    intro A B D E f g h
    ext
    simp only [FilteredObject.comp, Category.assoc]

lemma hom_id [Abelian C] (A : FilteredObject C) : (𝟙 A : A ⟶ A).hom = 𝟙 A.obj := rfl

@[simp] lemma hom_comp [Abelian C] {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- The forgetful functor `FilteredObject C ⥤ C`. -/
@[simps] noncomputable def forget [Abelian C] : FilteredObject C ⥤ C where
  obj A := A.obj
  map f := f.hom
  map_id := by intro A; rfl
  map_comp := by intro A B D f g; rfl

end FilteredObject

/-
PR 2: Opposed filtrations (Deligne, *Théorie de Hodge II*, §1.2.1–§1.2.3).

This file defines the iterated graded pieces for a pair of filtrations and the predicate
that two filtrations are `n`-opposed.

Deligne's definition (1.2.3) says that two finite filtrations `F, G` on an object `A`
are `n`-opposed if

`Gr_F^p Gr_G^q(A) = 0` whenever `p + q ≠ n`.

We define `Gr_F^p Gr_G^q(A)` directly by the symmetric Zassenhaus quotient formula

`(F^p ∩ G^q) / ( (F^{p+1} ∩ G^q) + (F^p ∩ G^{q+1}) )`.

In a later PR (PR 3), one proves the Zassenhaus isomorphisms and the splitting lemma
(Deligne 1.2.5).
-/

--import Mathlib.CategoryTheory.Abelian.Filtration.Basic


namespace DecFiltration

variable {A : C}

/-- The *bigraded* piece associated to two decreasing filtrations `F` and `G`.

This is the Zassenhaus quotient (symmetric in `F` and `G`):

`(F p ⊓ G q) / ((F (p+1) ⊓ G q) ⊔ (F p ⊓ G (q+1)))`.

It is canonically isomorphic to both `Gr_F^p (Gr_G^q A)` and `Gr_G^q (Gr_F^p A)`;
those isomorphisms are formalized in PR 3.
-/
noncomputable def gr₂ [Abelian C] (F G : DecFiltration A) (p q : ℤ) : C :=
  let X : Subobject A := F p ⊓ G q
  let Y : Subobject A := (F (p + 1) ⊓ G q) ⊔ (F p ⊓ G (q + 1))
  have hY : Y ≤ X := by
    -- Each summand is contained in `F p ⊓ G q`.
    refine sup_le ?_ ?_
    · -- `F (p+1) ⊓ G q ≤ F p ⊓ G q`.
      have hp : p ≤ p + 1 := by omega
      have hF : F (p + 1) ≤ F p := F.antitone hp
      exact inf_le_inf hF le_rfl
    · -- `F p ⊓ G (q+1) ≤ F p ⊓ G q`.
      have hq : q ≤ q + 1 := by omega
      have hG : G (q + 1) ≤ G q := G.antitone hq
      exact inf_le_inf le_rfl hG
  cokernel (Y.ofLE X hY)

/-- Two filtrations are `n`-opposed (Deligne 1.2.3) if `Gr_F^p Gr_G^q(A) = 0`
whenever `p+q ≠ n`.

We express vanishing using `IsZero`.
-/
def IsNOpposed [Abelian C] (F G : DecFiltration A) (n : ℤ) : Prop :=
  ∀ p q : ℤ, p + q ≠ n → IsZero (gr₂ F G p q)

/-- Convenience lemma: if `F` and `G` are `n`-opposed then the bigraded piece off the
`p+q=n` diagonal is zero. -/
lemma isZero_gr₂_of_IsNOpposed [Abelian C] {F G : DecFiltration A} {n p q : ℤ}
    (h : IsNOpposed F G n) (hpq : p + q ≠ n) :
    IsZero (gr₂ F G p q) :=
  h p q hpq

end DecFiltration

/-- A *bifiltered object*: an object equipped with two decreasing ℤ-filtrations.

This is Deligne's ambient setting for §1.2.
-/
structure BifilteredObject (C : Type u) [Category.{v} C] where
  obj : C
  F : DecFiltration obj
  G : DecFiltration obj

namespace BifilteredObject

--variable {C}

instance : Coe (BifilteredObject C) C where
  coe X := X.obj

/-- Morphisms of bifiltered objects: morphisms preserving both filtrations.

We use the pullback formulation: `f` preserves `F` if `A.F n ≤ (pullback f).obj (B.F n)`,
which is equivalent to saying the image of `A.F n` under `f` is contained in `B.F n`.
-/
structure Hom [HasPullbacks C] (A B : BifilteredObject C) where
  hom : (A : C) ⟶ (B : C)
  compatF : ∀ n : ℤ, A.F n ≤ (Subobject.pullback hom).obj (B.F n)
  compatG : ∀ n : ℤ, A.G n ≤ (Subobject.pullback hom).obj (B.G n)

variable [HasPullbacks C]

@[ext] lemma Hom.ext {A B : BifilteredObject C} (f g : Hom A B) (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Identity morphism of a bifiltered object. -/
def id (A : BifilteredObject C) : Hom A A where
  hom := 𝟙 A.obj
  compatF := by
    intro n
    simp only [Subobject.pullback_id]
    exact le_rfl
  compatG := by
    intro n
    simp only [Subobject.pullback_id]
    exact le_rfl

/-- Composition of morphisms of bifiltered objects. -/
def comp {A B D : BifilteredObject C} (f : Hom A B) (g : Hom B D) : Hom A D where
  hom := f.hom ≫ g.hom
  compatF := by
    intro n
    calc A.F n
        ≤ (Subobject.pullback f.hom).obj (B.F n) := f.compatF n
      _ ≤ (Subobject.pullback f.hom).obj ((Subobject.pullback g.hom).obj (D.F n)) :=
          (Subobject.pullback f.hom).monotone (g.compatF n)
      _ = (Subobject.pullback (f.hom ≫ g.hom)).obj (D.F n) := by
          rw [Subobject.pullback_comp]
  compatG := by
    intro n
    calc A.G n
        ≤ (Subobject.pullback f.hom).obj (B.G n) := f.compatG n
      _ ≤ (Subobject.pullback f.hom).obj ((Subobject.pullback g.hom).obj (D.G n)) :=
          (Subobject.pullback f.hom).monotone (g.compatG n)
      _ = (Subobject.pullback (f.hom ≫ g.hom)).obj (D.G n) := by
          rw [Subobject.pullback_comp]

instance : Category (BifilteredObject C) where
  Hom A B := Hom A B
  id A := id A
  comp f g := comp f g
  id_comp := by
    intro A B f
    ext
    simp [BifilteredObject.id, BifilteredObject.comp]
  comp_id := by
    intro A B f
    ext
    simp [BifilteredObject.id, BifilteredObject.comp]
  assoc := by
    intro A B D E f g h
    ext
    simp [BifilteredObject.comp, Category.assoc]

/-- The forgetful functor `BifilteredObject C ⥤ C`. -/
@[simps] def forget : BifilteredObject C ⥤ C where
  obj A := A.obj
  map f := f.hom
  map_id := by intro A; rfl
  map_comp := by intro A B D f g; rfl

section Abelian

variable [Abelian C]

/-- The `gr₂` construction for a bifiltered object. -/
noncomputable def gr₂ (A : BifilteredObject C) (p q : ℤ) : C :=
  DecFiltration.gr₂ A.F A.G p q

/-- A bifiltered object is `n`-opposed if its two filtrations are `n`-opposed (Deligne 1.2.3). -/
def IsNOpposed (A : BifilteredObject C) (n : ℤ) : Prop :=
  DecFiltration.IsNOpposed A.F A.G n

end Abelian

end BifilteredObject

end CategoryTheory
