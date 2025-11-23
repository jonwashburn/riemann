-- Mathlib/Analysis/Complex/DeBranges/Space.lean

import Riemann.Mathlib.Analysis.Complex.DeBranges.Basic
import Riemann.Mathlib.Analysis.Complex.DeBranges.NevanlinnaClosure
import Riemann.Mathlib.Analysis.Complex.ConjugateReflection
import Riemann.Mathlib.Analysis.Complex.DeBranges.Measure

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib

/-!
# de Branges spaces

Given a Hermite–Biehler function `E : ℂ → ℂ`, we define the de Branges space `B(E)` as
the set of entire functions `F` such that

* `F` restricted to the real line belongs to `L²(μ_E)`, where `μ_E = |E(x)|⁻² dx`
  is the de Branges measure defined in `DeBranges.Basic`;
* the quotients `F / E` and `F# / E` are admissible in the sense of `IsDeBrangesAdmissible`.

These conditions match one of the standard characterizations of de Branges spaces in the
literature: `F/E` and `F#/E` are of bounded type and nonpositive mean type in the upper
half-plane, and `F/E` has square-integrable boundary values on `ℝ`. See, for example,
de Branges' *Hilbert spaces of entire functions* and subsequent expositions.
-/

open Complex HermiteBiehlerFunction MeasureTheory Function
open scoped Complex.ConjugateReflection InnerProductSpace Topology ENNReal

variable (E : HermiteBiehlerFunction)

namespace DeBranges

/-- Predicate expressing that an entire function `F : ℂ → ℂ` belongs to the de Branges
space associated with a Hermite–Biehler function `E`.

The conditions are:

* `entire`: `F` is entire (holomorphic on `ℂ`);
* `mem_L2`: `F` restricted to `ℝ` is in `L²(μ_E)`, where `μ_E = |E(x)|⁻² dx`;
* `admissible_F_over_E`: the quotient `F/E` is de Branges-admissible in the upper half-plane;
* `admissible_F_sharp_over_E`: the conjugate reflection `F#/E` is de Branges-admissible.

This matches the common analytic definition of the de Branges space `B(E)`. -/
structure MemSpace (F : ℂ → ℂ) : Prop where
  /-- `F` is entire. -/
  entire : Differentiable ℂ F
  /-- `F` restricted to `ℝ` belongs to `L²(μ_E)`. -/
  mem_L2 : MemLp (fun x : ℝ => (F x : ℂ)) (2 : ℝ≥0∞) E.measure
  /-- `F / E` is admissible in the upper half-plane. -/
  admissible_F_over_E :
    IsDeBrangesAdmissible fun z : ℂ => F z / E z
  /-- `F# / E` is admissible in the upper half-plane. -/
  admissible_F_sharp_over_E :
    IsDeBrangesAdmissible fun z : ℂ => (F#) z / E z

namespace MemSpace

variable {E : HermiteBiehlerFunction}

/-- `0` belongs to the de Branges space predicate. -/
lemma zero : MemSpace (E := E) (fun _ : ℂ => (0 : ℂ)) := by
  refine
    { entire := ?_
      mem_L2 := ?_
      admissible_F_over_E := ?_
      admissible_F_sharp_over_E := ?_ }
  · -- entire
    simp
  · -- L² on ℝ w.r.t. `E.measure`
    simp
  · -- admissibility of `0 / E = 0`
    simpa [div_eq_mul_inv] using
      Complex.IsDeBrangesAdmissible.zero
  · -- admissibility of `0#/E = 0`
    simp only [ConjugateReflection.apply, star_zero, zero_div]
    simpa [Matrix.det_conj', star, div_eq_mul_inv] using
      Complex.IsDeBrangesAdmissible.zero

/-- Closed under addition. -/
lemma add {F G : ℂ → ℂ} (hF : MemSpace (E := E) F) (hG : MemSpace (E := E) G) :
    MemSpace (E := E) (fun z => F z + G z) := by
  refine
    { entire := ?_
      mem_L2 := ?_
      admissible_F_over_E := ?_
      admissible_F_sharp_over_E := ?_ }
  · -- entire
    simpa using hF.entire.add hG.entire
  · -- L²: use `MemLp.add`
    have hF_L2 := hF.mem_L2
    have hG_L2 := hG.mem_L2
    -- `MemLp.add` is for pointwise sum on ℝ
    simpa [Pi.add_apply] using
      (MeasureTheory.MemLp.add (f := fun x : ℝ => (F x : ℂ))
                               (g := fun x : ℝ => (G x : ℂ))
                               hF_L2 hG_L2)
  · -- admissibility of `(F+G)/E` from admissibility of `F/E` and `G/E`
    have hF' := hF.admissible_F_over_E
    have hG' := hG.admissible_F_over_E
    simpa [add_div] using hF'.add hG'
  · -- admissibility of `(F+G)#/E`
    have hF' := hF.admissible_F_sharp_over_E
    have hG' := hG.admissible_F_sharp_over_E
    simpa [Matrix.map_add, add_div] using hF'.add hG'

/-- Closed under scalar multiplication by `c : ℂ`. -/
lemma smul {F : ℂ → ℂ} (c : ℂ) (hF : MemSpace (E := E) F) :
    MemSpace (E := E) (fun z => c * F z) := by
  refine
    { entire := ?_
      mem_L2 := ?_
      admissible_F_over_E := ?_
      admissible_F_sharp_over_E := ?_ }
  · -- entire: `z ↦ c * F z` is product of constant and entire function
    have hc : Differentiable ℂ fun _ : ℂ => c := differentiable_const c
    have hF' := hF.entire
    simpa [Pi.mul_def] using hc.mul hF'
  · -- L² on ℝ: use `MemLp.const_mul`
    have hF_L2 := hF.mem_L2
    simpa [Pi.mul_def] using
      (MeasureTheory.MemLp.const_mul (f := fun x : ℝ => (F x : ℂ))
        (p := (2 : ℝ≥0∞)) (μ := E.measure) hF_L2 c)
  · -- admissibility of `(c*F)/E = c * (F/E)`
    have hF' := hF.admissible_F_over_E
    simpa [mul_div_assoc] using hF'.smul c
  · -- admissibility of `(c*F)# / E = c̅ * (F#/E)`
    have hF' := hF.admissible_F_sharp_over_E
    simpa [Matrix.map_smul', mul_div_assoc] using hF'.smul (star c)

/-- Closed under negation. -/
lemma neg {F : ℂ → ℂ} (hF : MemSpace (E := E) F) :
    MemSpace (E := E) (fun z => -F z) := by
  have := smul (-1) hF
  simpa using this

end MemSpace

/-- The de Branges space `B(E)` associated with a Hermite–Biehler function `E`.

It is implemented as the subtype of entire functions `F : ℂ → ℂ` satisfying `MemSpace E F`. -/
def Space : Type _ := {F : ℂ → ℂ // MemSpace E F}

namespace Space

instance : CoeFun (Space E) (fun _ => ℂ → ℂ) :=
  ⟨Subtype.val⟩

@[ext] lemma ext {F G : Space E} (h : ∀ z, F z = G z) : F = G :=
  Subtype.ext (funext h)

instance : Add (Space E) := ⟨fun F G => ⟨F + G, MemSpace.add F.2 G.2⟩⟩
instance : Zero (Space E) := ⟨⟨0, MemSpace.zero⟩⟩
instance : Neg (Space E) := ⟨fun F => ⟨-F, MemSpace.neg F.2⟩⟩
instance : Sub (Space E) := ⟨fun F G => ⟨F - G, by simpa [sub_eq_add_neg] using MemSpace.add F.2 (MemSpace.neg G.2)⟩⟩

noncomputable instance : SMul ℕ (Space E) := ⟨fun n F => ⟨n • F.1, by
  simpa [nsmul_eq_mul] using MemSpace.smul (n : ℂ) F.2⟩⟩

noncomputable instance : SMul ℤ (Space E) := ⟨fun n F => ⟨n • F.1, by
  simpa [zsmul_eq_mul] using MemSpace.smul (n : ℂ) F.2⟩⟩

noncomputable instance : AddCommGroup (Space E) :=
  Function.Injective.addCommGroup Subtype.val Subtype.val_injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- Members of the de Branges space `B(E)` are entire functions. -/
lemma entire (F : Space E) : Differentiable ℂ F :=
  F.property.entire

/-- Members of `B(E)` are continuous functions on `ℂ`. -/
lemma continuous (F : Space E) : Continuous F :=
  (Space.entire (E := E) F).continuous

/-- The restriction of a function in `B(E)` to `ℝ` belongs to `L²(μ_E)`. -/
lemma mem_L2 (F : Space E) :
    MemLp (fun x : ℝ => (F x : ℂ)) (2 : ℝ≥0∞) E.measure :=
  F.property.mem_L2

/-- For `F ∈ B(E)`, the quotient `F/E` is de Branges-admissible in the upper half-plane. -/
lemma admissible_F_over_E (F : Space E) :
    IsDeBrangesAdmissible (fun z : ℂ => F z / E z) :=
  F.property.admissible_F_over_E

/-- For `F ∈ B(E)`, the quotient `F#/E` is de Branges-admissible in the upper half-plane. -/
lemma admissible_F_sharp_over_E (F : Space E) :
    IsDeBrangesAdmissible (fun z : ℂ => (F#) z / E z) :=
  F.property.admissible_F_sharp_over_E

/-! ### Embedding into `L²(μ_E)` and induced inner product -/

/-- The canonical embedding of the de Branges space `B(E)` into the Hilbert
space `L²(μ_E)`, sending `F` to its restriction to `ℝ` viewed as an element of
`Lp ℂ 2 E.measure`. This is the starting point for the Hilbert-space
structure on `Space E` via the embedding approach. -/
noncomputable def toLp (F : Space E) : Lp ℂ 2 E.measure :=
  MemLp.toLp (fun x : ℝ => (F x : ℂ)) (Space.mem_L2 (E := E) F)

/-- The (candidate) inner product on the de Branges space `B(E)`, obtained by
pulling back the `L²(μ_E)` inner product along the embedding `toLp`. At this
stage we treat it as a standalone definition; the full `InnerProductSpace`
instance will be constructed once the algebraic closure properties of
`MemSpace` are available. -/
noncomputable def inner (F G : Space E) : ℂ :=
  ⟪toLp (E := E) F, toLp (E := E) G⟫_ℂ

/-- The embedding `toLp : B(E) → L²(μ_E)` is injective: if two elements of the
de Branges space have the same image in `L²(μ_E)`, then they are equal as
entire functions. This uses continuity on `ℝ`, the fact that `μ_E` has full
support (it is an `IsOpenPosMeasure`), and the identity theorem for entire
functions. -/
lemma toLp_injective : Function.Injective (toLp (E := E)) := by
  classical
  intro F G h
  -- Step 1: equality in `Lp` gives a.e. equality on `ℝ` w.r.t. `μ_E`.
  have hF : MemLp (fun x : ℝ => (F x : ℂ)) (2 : ℝ≥0∞) E.measure :=
    Space.mem_L2 (E := E) F
  have hG : MemLp (fun x : ℝ => (G x : ℂ)) (2 : ℝ≥0∞) E.measure :=
    Space.mem_L2 (E := E) G
  replace h : MemLp.toLp (fun x : ℝ => (F x : ℂ)) hF =
        MemLp.toLp (fun x : ℝ => (G x : ℂ)) hG := h
  have h_ae :
      (fun x : ℝ => (F x : ℂ)) =ᵐ[E.measure] fun x : ℝ => (G x : ℂ) :=
    (MemLp.toLp_eq_toLp_iff (hf := hF) (hg := hG)).1 h

  -- Step 2: use continuity and the fact that `μ_E` is an `IsOpenPosMeasure`
  -- to show equality everywhere on the real line.
  have h_eq_real : ∀ x : ℝ, F x = G x := by
    intro x₀
    by_contra hx₀
    -- Consider the continuous difference on `ℝ`.
    let hDiff : ℝ → ℂ := fun x => (F x : ℂ) - G x
    have hDiff_cont : Continuous hDiff := by
      have hF_cont : Continuous fun x : ℝ => (F x : ℂ) :=
        (Space.continuous (E := E) F).comp continuous_ofReal
      have hG_cont : Continuous fun x : ℝ => (G x : ℂ) :=
        (Space.continuous (E := E) G).comp continuous_ofReal
      simpa [hDiff] using hF_cont.sub hG_cont
    -- `hDiff = 0` almost everywhere w.r.t. `μ_E`.
    have hDiff_ae :
        (fun x : ℝ => hDiff x) =ᵐ[E.measure] fun _ : ℝ => (0 : ℂ) := by
      refine h_ae.mono ?_
      intro x hx
      simp [hDiff, hx]
    -- Hence the set where `hDiff ≠ 0` has measure zero.
    have h_zero :
        E.measure {x : ℝ | hDiff x ≠ 0} = 0 := by
      -- `ae_iff` says `(∀ᵐ x, hDiff x = 0)` iff the complement has measure zero.
      have := (MeasureTheory.ae_iff (μ := E.measure)
          (p := fun x : ℝ => hDiff x = 0)).1 hDiff_ae
      -- `{x | ¬ (hDiff x = 0)} = {x | hDiff x ≠ 0}`.
      simpa [Classical.not_not] using this
    -- But by continuity, `hDiff x₀ ≠ 0` yields a nonempty open set of non-zeros.
    have hx₀' : hDiff x₀ ≠ 0 := by
      have : (F x₀ : ℂ) ≠ G x₀ := by
        simpa using hx₀
      simpa [hDiff] using sub_ne_zero.mpr this
    have h_neighbourhood :
        ∃ U : Set ℝ, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ {x : ℝ | hDiff x ≠ 0} := by
      -- take `U` to be the whole nonzero set
      refine ⟨{x : ℝ | hDiff x ≠ 0}, ?_, ?_, ?_⟩
      · -- openness from continuity of `hDiff`
        have h_open : IsOpen ({z : ℂ | z ≠ (0 : ℂ)}) := isOpen_ne
        simpa [Set.preimage, hDiff] using h_open.preimage hDiff_cont
      · -- `x₀` lies in this set by `hx₀'`
        exact hx₀'
      · -- and `U` is trivially contained in itself
        intro x hx; exact hx
    rcases h_neighbourhood with ⟨U, hUopen, hxU, hUsubset⟩
    -- Since `μ_E` is an `IsOpenPosMeasure`, a nonempty open set has positive measure.
    have hμ_pos :
        0 < E.measure U := by
      haveI : Measure.IsOpenPosMeasure E.measure := inferInstance
      simpa using
        (IsOpen.measure_pos (μ := E.measure) (U := U) hUopen ⟨x₀, hxU⟩)
    -- But `U ⊆ {x | hDiff x ≠ 0}` and that set has measure zero.
    have hμ_zero :
        E.measure U = 0 := by
      have hsubset : U ⊆ {x : ℝ | hDiff x ≠ 0} := hUsubset
      exact measure_mono_null hsubset h_zero
    -- This is a contradiction: `μ_E U > 0` but `μ_E U = 0`.
    exact absurd hμ_zero (ne_of_gt hμ_pos)

  -- Step 3: Use analytic continuation (identity theorem) to upgrade equality on `ℝ`
  -- to equality on the whole complex plane.
  apply Space.ext (E := E)
  intro z
  -- Consider `H := F - G`, an entire function vanishing on `ℝ`.
  have h_entire : Differentiable ℂ fun w : ℂ => (F w : ℂ) - G w :=
    (Space.entire (E := E) F).sub (Space.entire (E := E) G)
  have h_zero_on_R : ∀ x : ℝ, (F x : ℂ) - G x = 0 := by
    intro x
    have := h_eq_real x
    simp [this]  -- already present
  -- Promote to analytic-on-ℂ:
  have h_analytic :
      AnalyticOnNhd ℂ (fun w : ℂ => (F w : ℂ) - G w) Set.univ := by
    -- `analyticOnNhd_univ_iff_differentiable` from `CauchyIntegral.lean`
    have := (Complex.analyticOnNhd_univ_iff_differentiable
      (f := fun w : ℂ => (F w : ℂ) - G w))
    exact (this.mpr h_entire)
  have h_zero_analytic :
      AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) Set.univ := by
    -- constant maps are analytic
    have : Differentiable ℂ fun _ : ℂ => (0 : ℂ) := differentiable_const _
    simp [Complex.analyticOnNhd_univ_iff_differentiable]
  -- Identity theorem along a sequence in `ℝ \ {0}` accumulating at `0`.
  have h_frequently :
      ∃ᶠ z in 𝓝[≠] (0 : ℂ),
        (fun w : ℂ => (F w : ℂ) - G w) z = (0 : ℂ) := by
    rw [Filter.frequently_iff]
    intro U hU
    rcases mem_nhdsWithin.mp hU with ⟨V, hV_open, h0V, hVsub⟩
    have hV_nhds : V ∈ 𝓝 0 := hV_open.mem_nhds h0V
    rcases Metric.mem_nhds_iff.mp hV_nhds with ⟨ε, hε, hBall⟩
    use (ε / 2 : ℝ)
    have hx_ne : ((ε / 2 : ℝ) : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]
      linarith
    have hx_mem : ((ε / 2 : ℝ) : ℂ) ∈ V := by
      apply hBall
      simp only [Metric.mem_ball, Complex.dist_eq, sub_zero]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      linarith
    refine ⟨hVsub ⟨hx_mem, hx_ne⟩, ?_⟩
    dsimp only
    exact h_zero_on_R (ε / 2)
  have h_eq_fun :
      (fun w : ℂ => (F w : ℂ) - G w) = fun _ : ℂ => (0 : ℂ) :=
    AnalyticOnNhd.eq_of_frequently_eq
      h_analytic h_zero_analytic h_frequently
  -- Conclude the equality at the given point `z`.
  have := congrArg (fun f : ℂ → ℂ => f z) h_eq_fun
  have : (F z : ℂ) - G z = 0 := this
  exact sub_eq_zero.mp this

noncomputable instance : MetricSpace (Space E) :=
  MetricSpace.induced (toLp (E := E)) (toLp_injective (E := E)) inferInstance

noncomputable instance : NormedAddCommGroup (Space E) :=
  { (inferInstance : AddCommGroup (Space E)),
    (inferInstance : MetricSpace (Space E)) with
    norm := fun F => ‖toLp (E := E) F‖
    dist_eq := by
      intro F G
      erw [dist_eq_norm (toLp (E := E) F) (toLp (E := E) G)]
      simp only [toLp]
      rw [← MemLp.toLp_sub (Space.mem_L2 (E := E) F) (Space.mem_L2 (E := E) G)]
      rfl }

lemma norm_def (F : Space E) :
    ‖F‖ = ‖toLp (E := E) F‖ := rfl

lemma toLp_isometry : Isometry (toLp (E := E)) := by
  intro F G
  rfl


end Space
end DeBranges
