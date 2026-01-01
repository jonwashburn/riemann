import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna
import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna.Cayley

open Complex UpperHalfPlane
open scoped Topology
namespace Complex


/-
The proof strategy in analysis (not yet Lean):
Use the Nevanlinna canonical representation for functions of bounded type in the upper half-plane. This expresses
log
⁡
∣
f
(
z
)
∣
log∣f(z)∣
as a sum of a harmonic function with explicit growth (linear in Im z) plus a Poisson integral of a finite measure. The coefficient of Im z in this linear part is precisely the mean type.
Show that the contribution of the Poisson integral is uniformly o(Im z) as Im z → ∞ along non-tangential paths (this is a standard estimate).
Conclude that
lim sup
⁡
ℑ
z
→
∞
log
⁡
∣
f
(
z
)
∣
ℑ
z
ℑz→∞
limsup
​

ℑz
log∣f(z)∣
​

is independent of the non-tangential approach, so taking z = i y recovers the same value as UpperHalfPlane.atImInfty.
To formalize this in Lean, you would:
Develop (or import) the canonical representation for bounded-type functions on the upper half-plane.
Define a function F : ℍ → ℝ by F z = (Real.log (‖f z‖ + 1)) / z.im.
Prove that the limsup of F along UpperHalfPlane.atImInfty equals the limsup of y ↦ (log (‖f(i y)‖ + 1))/y along atTop. This uses comparison lemmas between the vertical line and non-tangential sectors in ℍ.
This is nontrivial but structurally straightforward once you have the Nevanlinna machinery in place.
-/
/-! ### Growth estimates for functions of bounded type -/

/-!
## Abstract Poisson–Jensen representation on the upper half-plane

In order to keep the analytic backbone (Nevanlinna canonical representation /
Poisson–Jensen) modular, we package precisely the hypotheses needed to deduce
the growth inequality `limsups_atImInfty_le_meanType` from a Poisson
representation transported along the Cayley transform.

The actual existence of such a representation for every bounded‑type function
is a deep theorem (to be proved later, using the `ValueDistribution` API and
canonical factorisation).  The lemmas in this section are *purely formal* and
express how that theorem will be used in the growth argument.
-/

open MeasureTheory

open Filter

/-- Canonical Poisson–Jensen data for an upper-half-plane function `f`.

This is the abstract form of the representation one obtains from Nevanlinna
canonical factorisation plus Poisson–Jensen:

* there is an analytic disk-function `F` with disk Poisson representation,
* there is a real number `α` which agrees with the vertical mean type
  `Complex.meanType f`,
* for every `z : ℍ` we have
  \[
    \log(‖f(z)‖+1) = α ⋅ \Im z + \Re (F ∘ \mathcal{C})(z),
  \]
  where `\mathcal{C}` is the Cayley transform `toUnitDisc`,
* the Poisson term `Re (F ∘ \mathcal{C})(z)` is `o(Im z)` along
  `UpperHalfPlane.atImInfty`.

The existence of such data for every bounded‑type `f` is the true analytic
content of the upper half‑plane Poisson–Jensen theorem and will be supplied
later via `ValueDistribution`.  Here we only record the consequences for
growth along `atImInfty`. -/
structure UpperHalfPlanePoissonRepresentation (f : ℂ → ℂ) where
  F : ℂ → ℂ
  alpha : ℝ
  hAlpha : (alpha : EReal) = meanType f
  hPoisson : Complex.HasDiskPoissonRepresentation F
  hLog :
    ∀ z : ℍ,
      Real.log (‖f z‖ + 1) =
        alpha * (z.im : ℝ) + (Complex.cayleyPullback F z).re
  hLittleO :
    Tendsto (fun z : ℍ =>
        (Complex.cayleyPullback F z).re / (z.im : ℝ))
      UpperHalfPlane.atImInfty (nhds 0)

/-- Nontriviality of the filter `UpperHalfPlane.atImInfty`.  This is a general
fact about the upper half‑plane and does *not* depend on the function `f`. -/
lemma UpperHalfPlane.atImInfty_neBot :
    (UpperHalfPlane.atImInfty : Filter ℍ).NeBot := by
  classical
  -- Show that `comap im atTop` is nontrivial by exhibiting, for each basis
  -- element `Set.Ici A`, a point with imaginary part ≥ `A`.
  refine Filter.comap_neBot ?_
  intro S hS
  -- Unpack a basis element of `atTop` and choose a large enough height `y`.
  obtain ⟨A, hA⟩ := Filter.mem_atTop_sets.mp hS
  set y : ℝ := max A 1 + 1
  have hy_ge_two : (2 : ℝ) ≤ y := by
    have hmax : (1 : ℝ) ≤ max A 1 := le_max_right _ _
    have : (2 : ℝ) ≤ max A 1 + 1 := by linarith
    simpa [y] using this
  have hy_pos : 0 < y := lt_of_lt_of_le zero_lt_two hy_ge_two
  have hy_mem : A ≤ y := by
    have h₁ : A ≤ max A 1 := le_max_left _ _
    have : A ≤ max A 1 + 1 := by linarith
    simpa [y] using this
  -- Build a point `z : ℍ` with imaginary part exactly `y`.
  have hIm : (Complex.I * (y : ℂ)).im = y := by simp
  let z : ℍ := ⟨Complex.I * (y : ℂ), by simpa [hIm] using hy_pos⟩
  have hz_im : UpperHalfPlane.im z = y := by
    simp [z, UpperHalfPlane.im, hIm]
  have hz_mem : UpperHalfPlane.im z ∈ Set.Ici A := by
    simpa [hz_im, Set.mem_Ici] using hy_mem
  exact ⟨z, hA (UpperHalfPlane.im z) hz_mem⟩

/-- Given canonical Poisson–Jensen data in the sense of
`UpperHalfPlanePoissonRepresentation`, the growth along `atImInfty` is
controlled by the mean type.  This is the formal heart of the argument; the
existence of the representation itself is proved elsewhere. -/
lemma UpperHalfPlanePoissonRepresentation.limsup_atImInfty_le_meanType
    {f : ℂ → ℂ} (h : UpperHalfPlanePoissonRepresentation f) :
    Filter.limsup
      (fun z : ℍ =>
        ((Real.log (‖f z‖ + 1)) / (z.im : ℝ) : EReal))
      UpperHalfPlane.atImInfty ≤
    meanType f := by
  classical
  -- Real-valued growth function and Poisson term ratio.
  let G : ℍ → ℝ :=
    fun z => (Real.log (‖f z‖ + 1)) / (z.im : ℝ)
  let R : ℍ → ℝ :=
    fun z => (Complex.cayleyPullback h.F z).re / (z.im : ℝ)

  have h_decomp_real (z : ℍ) :
      G z = h.alpha + R z := by
    -- Start from the canonical representation for `log(‖f z‖+1)`.
    have hlog := h.hLog z
    -- Divide both sides by `Im z > 0`.
    have hz_pos : 0 < (z.im : ℝ) := z.property
    -- First rewrite the quotient using the canonical representation.
    have hG :
        G z =
          (h.alpha * (z.im : ℝ) + (Complex.cayleyPullback h.F z).re) /
            (z.im : ℝ) := by
      simp [G, hlog]
    -- Now split the fraction and cancel the common factor in the first term.
    calc
      G z
          = (h.alpha * (z.im : ℝ)) / (z.im : ℝ) +
              (Complex.cayleyPullback h.F z).re / (z.im : ℝ) := by
                simpa [add_div] using hG
      _ = h.alpha + R z := by
        have hz_ne : (z.im : ℝ) ≠ 0 := ne_of_gt hz_pos
        have hcancel :
            (h.alpha * (z.im : ℝ)) / (z.im : ℝ) = h.alpha := by
          -- Simple field cancellation in `ℝ`, using `Im z ≠ 0`.
          field_simp [hz_ne]
        simp [R, hcancel]

  -- Rephrase the decomposition in `EReal`, along `atImInfty`.
  have h_eq :
      (fun z : ℍ =>
          ((Real.log (‖f z‖ + 1)) / (z.im : ℝ) : EReal)) =ᶠ[UpperHalfPlane.atImInfty]
      (fun z : ℍ => ((h.alpha + R z : ℝ) : EReal)) := by
    refine Filter.Eventually.of_forall ?_
    intro z
    -- Convert the real equality `G z = alpha + R z` to an equality in `EReal`.
    have := h_decomp_real z
    simpa [G] using congrArg (fun x : ℝ => (x : EReal)) this

  -- The ratio `R z` tends to 0 along `atImInfty` by assumption.
  have h_R_tendsto : Tendsto R UpperHalfPlane.atImInfty (nhds (0 : ℝ)) :=
    h.hLittleO

  -- Hence the EReal-valued version of `R` also tends to 0.
  have h_R_tendsto_E :
      Tendsto (fun z : ℍ => (R z : EReal))
        UpperHalfPlane.atImInfty (nhds (0 : EReal)) := by
    refine Tendsto.comp (g := fun x : ℝ => (x : EReal))
      continuous_coe_real_ereal.continuousAt ?_
    simpa using h_R_tendsto

  -- The sum `h.alpha + R z` tends to `h.alpha`.
  have h_sum_tendsto :
      Tendsto (fun z : ℍ => h.alpha + R z)
        UpperHalfPlane.atImInfty (nhds h.alpha) := by
    -- First view this as `Tendsto (fun z ↦ h.alpha + R z) atImInfty (𝓝 (h.alpha + 0))`,
    -- then simplify the target.
    have h' :
        Tendsto (fun z : ℍ => h.alpha + R z)
          UpperHalfPlane.atImInfty (nhds (h.alpha + 0)) :=
      tendsto_const_nhds.add h_R_tendsto
    simpa using h'

  have h_sum_tendsto_E :
      Tendsto (fun z : ℍ => ((h.alpha + R z : ℝ) : EReal))
        UpperHalfPlane.atImInfty (nhds (h.alpha : EReal)) := by
    refine Tendsto.comp (g := fun x : ℝ => (x : EReal))
      continuous_coe_real_ereal.continuousAt ?_
    simpa using h_sum_tendsto

  -- Use nontriviality of `atImInfty` to identify its limsup with the limit.
  have h_neBot : (UpperHalfPlane.atImInfty : Filter ℍ).NeBot :=
    UpperHalfPlane.atImInfty_neBot
  haveI : (UpperHalfPlane.atImInfty : Filter ℍ).NeBot := h_neBot

  have h_limsup_eq :
      Filter.limsup
        (fun z : ℍ => ((h.alpha + R z : ℝ) : EReal))
        UpperHalfPlane.atImInfty =
      (h.alpha : EReal) :=
    Filter.Tendsto.limsup_eq h_sum_tendsto_E

  -- Translate this statement in terms of the original growth function.
  have h_G_limsup :
      Filter.limsup
        (fun z : ℍ =>
          ((Real.log (‖f z‖ + 1)) / (z.im : ℝ) : EReal))
        UpperHalfPlane.atImInfty =
      (h.alpha : EReal) := by
    -- First replace the limsup using the EReal decomposition, then apply `h_limsup_eq`.
    have h_congr :
        Filter.limsup
          (fun z : ℍ =>
            ((Real.log (‖f z‖ + 1)) / (z.im : ℝ) : EReal))
          UpperHalfPlane.atImInfty =
        Filter.limsup
          (fun z : ℍ => ((h.alpha + R z : ℝ) : EReal))
          UpperHalfPlane.atImInfty :=
      Filter.limsup_congr h_eq
    have := h_congr.trans h_limsup_eq
    simpa using this

  -- Finally, compare with `meanType f` via the identification of `alpha`.
  -- We only need `≤`, so we rewrite and apply `le_of_eq`.
  have : Filter.limsup
      (fun z : ℍ =>
        ((Real.log (‖f z‖ + 1)) / (z.im : ℝ) : EReal))
      UpperHalfPlane.atImInfty =
    meanType f := by
    simpa [h.hAlpha] using h_G_limsup
  exact le_of_eq this

/-- **Upper-half-plane Poisson–Jensen theorem (existence level).**

If `f` is of bounded type in the upper half-plane, then it admits canonical
Poisson–Jensen data in the sense of `UpperHalfPlanePoissonRepresentation`.

The analytic proof of this fact (via canonical factorisation and the
`ValueDistribution` API) is deferred; here we only register the statement
and use it as an abstract hypothesis in the growth lemmas below. -/
def exists_upperHalfPlanePoissonRepresentation_of_boundedType
    {f : ℂ → ℂ} (hf : IsOfBoundedTypeUpperHalfPlane f) :
    UpperHalfPlanePoissonRepresentation f := by
  -- TODO (analytic core):
  --   Construct the disk function `F` and parameter `α` appearing in the
  --   classical canonical representation of `f`, check that `F` satisfies
  --   `HasDiskPoissonRepresentation`, identify `α` with `meanType f`, and
  --   transport the representation to the upper half-plane via the Cayley
  --   transform and `cayleyPullback`.  This is a substantial Nevanlinna
  --   theory argument and will be supplied later.
  sorry

/--
Growth inequality for functions of bounded type (Phragmén–Lindelöf direction).
The global growth in the upper half-plane is controlled by the growth along the
imaginary axis.

The analytic heart of the argument is the existence of a Poisson–Jensen
representation as in `UpperHalfPlanePoissonRepresentation`; once such data has
been constructed (using ValueDistribution + canonical factorisation), this
lemma follows immediately from
`UpperHalfPlanePoissonRepresentation.limsup_atImInfty_le_meanType`.
-/
lemma IsOfBoundedTypeUpperHalfPlane.limsup_atImInfty_le_meanType
    {f : ℂ → ℂ} (hf : IsOfBoundedTypeUpperHalfPlane f) :
    Filter.limsup
      (fun z : ℍ =>
        ((Real.log (norm (f z) + 1)) / (z.im : ℝ) : EReal))
      UpperHalfPlane.atImInfty ≤
    meanType f := by
  classical
  -- TODO (analytic core): construct the representation data required by
  -- `UpperHalfPlanePoissonRepresentation` from `hf`, using the
  -- `ValueDistribution` API and canonical factorisation on the disk, then
  -- transport it to the upper half‑plane via the Cayley transform and the
  -- lemmas in `Cayley.lean`.
  have hRep : UpperHalfPlanePoissonRepresentation f :=
    exists_upperHalfPlanePoissonRepresentation_of_boundedType hf
  exact UpperHalfPlanePoissonRepresentation.limsup_atImInfty_le_meanType
    (f := f) hRep

open Filter

/--
The growth along the imaginary axis is bounded by the global growth
measured along `UpperHalfPlane.atImInfty`.

This is a purely filter‑theoretic “path vs. ambient” comparison: the
vertical ray `y ↦ i y` gives a filter on `ℍ` that is subordinate to
`UpperHalfPlane.atImInfty`, hence the limsup along the ray is ≤ the
global limsup along `atImInfty`.
-/
lemma IsOfBoundedTypeUpperHalfPlane.meanType_le_limsup_atImInfty
    {f : ℂ → ℂ} (_ : IsOfBoundedTypeUpperHalfPlane f) :
    meanType f ≤
    Filter.limsup
      (fun z : ℍ =>
        ((Real.log (norm (f z) + 1)) / (z.im : ℝ) : EReal))
      UpperHalfPlane.atImInfty := by
  classical
  -- Abbreviations for the two growth functions.
  let γ : ℝ → ℂ := fun y => Complex.I * (y : ℂ)
  let u : ℝ → EReal :=
    fun y => ((Real.log (‖f (γ y)‖ + 1)) / y : EReal)
  let G : ℍ → EReal :=
    fun z => ((Real.log (‖f z‖ + 1)) / (z.im : ℝ) : EReal)
  let ψ : ℝ → ℍ := fun y => UpperHalfPlane.ofComplex (γ y)

  -- Rewrite the left-hand side `meanType f` in terms of `u`.
  -- This is just the definition from `Nevanlinna.lean`.
  have h_mean_def :
      meanType f = Filter.limsup u Filter.atTop := by
    -- `meanType f` was defined with `I * y`, which matches `γ y`.
    simp [meanType, u, γ]

  -- Step 1: along the vertical path `ψ`, the two growth functions coincide
  -- eventually (for large positive `y`), so the corresponding limsups agree.
  have h_eq :
      (fun y : ℝ => u y) =ᶠ[Filter.atTop]
      (fun y : ℝ => G (ψ y)) := by
    -- For large `y`, we have `y > 0`, hence `Im (I*y) = y > 0`,
    -- so `ofComplex (I*y)` is just the point `⟨I*y, _⟩` in `ℍ`.
    refine (eventually_gt_atTop (0 : ℝ)).mono ?_
    intro y hy
    have hy_pos : 0 < y := hy
    -- Imaginary part of `I * y` is `y`.
    have h_im_pos : 0 < (γ y).im := by
      -- `γ y = I * (y : ℂ)`, and `im (I * z) = z.re`.
      have : (γ y).im = y := by
        simp [γ]
      simpa [this] using hy_pos
    -- Identify `ψ y` explicitly in `ℍ`.
    have hψ :
        ψ y = ⟨γ y, h_im_pos⟩ := by
      unfold ψ
      -- `ofComplex` applied to a point with positive imaginary part
      -- just returns that point as an element of `ℍ`.
      simpa [UpperHalfPlane.ofComplex_apply_of_im_pos, γ] using
        (UpperHalfPlane.ofComplex_apply_of_im_pos
          (z := γ y) h_im_pos)
    -- Coercion of `ψ y` back to `ℂ` and its imaginary part.
    have hcoe : (ψ y : ℂ) = γ y := by
      simpa using congrArg (fun z : ℍ => (z : ℂ)) hψ
    have him : (ψ y).im = y := by
      -- Use `hψ` to rewrite `(ψ y).im` as the imaginary part of the underlying complex number.
      rw [hψ]
      -- Now `(ψ y).im` is just the imaginary part of `γ y = I * y`.
      simp [UpperHalfPlane.im, γ]
    -- Now compute both sides and see they coincide.
    simp [u, G, γ, ψ, hcoe, him]

  -- Use `limsup_congr` to transfer the eventual equality to limsups.
  have h_limsup_eq :
      Filter.limsup u Filter.atTop =
        Filter.limsup (fun y : ℝ => G (ψ y)) Filter.atTop :=
    Filter.limsup_congr h_eq

  -- Step 2: show that the path filter `map ψ atTop` is subordinate to
  -- `UpperHalfPlane.atImInfty`, so that the limsup along the path is
  -- ≤ the limsup along `atImInfty`.

  -- First, the intermediate path in `ℂ`:
  -- `γ y = I * (y : ℂ)` tends to `comap Complex.im atTop` as `y → +∞`,
  -- because `im (γ y) = y`.
  have h_tend_γ :
      Tendsto γ Filter.atTop (Filter.comap Complex.im Filter.atTop) := by
    -- By `tendsto_comap_iff`, this is equivalent to
    -- `Tendsto (Complex.im ∘ γ) atTop atTop`.
    -- But `im (I*y) = y`, so this is just `tendsto_id`.
    have h_id : Tendsto (fun y : ℝ => y) Filter.atTop Filter.atTop :=
      tendsto_id
    -- Identify the composition explicitly.
    have hcomp :
        (fun y : ℝ => Complex.im (γ y)) = fun y : ℝ => y := by
      funext y
      simp [γ]
    -- Rewrite `h_id` in terms of `Complex.im ∘ γ`.
    have h_im : Tendsto (fun y : ℝ => Complex.im (γ y))
        Filter.atTop Filter.atTop := by
      simpa [hcomp] using h_id
    -- Convert back to a statement about `γ` and `comap Complex.im atTop`.
    exact tendsto_comap_iff.mpr h_im
  -- Now compose with `UpperHalfPlane.ofComplex` to get a path into `ℍ`.
  have h_tend_ψ :
      Tendsto ψ Filter.atTop UpperHalfPlane.atImInfty := by
    -- `atImInfty = atTop.comap UpperHalfPlane.im`, and
    -- `UpperHalfPlane.tendsto_comap_im_ofComplex` tells us that
    -- mapping by `ofComplex` sends `comap Complex.im atTop` into `atImInfty`.
    have h_of :
        Tendsto UpperHalfPlane.ofComplex
          (Filter.comap Complex.im Filter.atTop)
          UpperHalfPlane.atImInfty :=
      UpperHalfPlane.tendsto_comap_im_ofComplex
    -- Compose `γ` then `ofComplex`.
    exact h_of.comp h_tend_γ

  -- From `Tendsto ψ atTop atImInfty` we get `map ψ atTop ≤ atImInfty`.
  have h_filter_le :
      Filter.map ψ Filter.atTop ≤ UpperHalfPlane.atImInfty :=
    h_tend_ψ

  -- Step 3: use `limsup` monotonicity with respect to filter inclusion.
  -- We need to rewrite the limsup along the path in terms of `map ψ atTop`.
  have h_limsup_path :
      Filter.limsup (fun y : ℝ => G (ψ y)) Filter.atTop =
        Filter.limsup G (Filter.map ψ Filter.atTop) := by
    -- Unfold `limsup` and use `map_map`.
    unfold Filter.limsup
    -- `map (fun y ↦ G (ψ y)) atTop = map G (map ψ atTop)`.
    rfl

  -- Monotonicity of limsup under filter inclusion.
  have h_le_path_to_global :
      Filter.limsup G (Filter.map ψ Filter.atTop) ≤
        Filter.limsup G UpperHalfPlane.atImInfty :=
    Filter.limsup_le_limsup_of_le
      (β := EReal)
      (f := Filter.map ψ Filter.atTop)
      (g := UpperHalfPlane.atImInfty)
      (u := G)
      h_filter_le
      (hf := by isBoundedDefault)
      (hg := by isBoundedDefault)

  -- Combine everything:
  -- `meanType f = limsup u atTop = limsup (G ∘ ψ) atTop
  --             = limsup G (map ψ atTop) ≤ limsup G atImInfty`.
  have h_chain :
      meanType f ≤
        Filter.limsup
          (fun z : ℍ =>
            ((Real.log (‖f z‖ + 1)) / (z.im : ℝ) : EReal))
          UpperHalfPlane.atImInfty := by
    -- Rewrite `meanType f` and the path limsup.
    have := congrArg id h_mean_def
    -- Put the pieces together.
    calc
      meanType f
          = Filter.limsup u Filter.atTop := h_mean_def
      _ = Filter.limsup (fun y : ℝ => G (ψ y)) Filter.atTop :=
            h_limsup_eq
      _ = Filter.limsup G (Filter.map ψ Filter.atTop) :=
            h_limsup_path
      _ ≤ Filter.limsup G UpperHalfPlane.atImInfty :=
            h_le_path_to_global
      _ = Filter.limsup
            (fun z : ℍ =>
              ((Real.log (‖f z‖ + 1)) / (z.im : ℝ) : EReal))
            UpperHalfPlane.atImInfty := rfl

  exact h_chain

/--
The growth along the imaginary axis is bounded by the global growth.
This holds generally for any function, as the imaginary axis is a specific path.

This is just a restatement of `meanType_le_limsup_atImInfty` with slightly
different formatting of the right-hand side.
-/
lemma IsOfBoundedTypeUpperHalfPlane.meanType_le_limsup_atImInfty'
    {f : ℂ → ℂ} (hf : IsOfBoundedTypeUpperHalfPlane f) :
    meanType f ≤
    Filter.limsup (fun z : ℍ =>
      ((Real.log (norm (f z) + 1)) / (z.im : ℝ) : EReal)) UpperHalfPlane.atImInfty := by
  -- This is exactly `meanType_le_limsup_atImInfty` with the arguments unfolded.
  exact IsOfBoundedTypeUpperHalfPlane.meanType_le_limsup_atImInfty (f := f) hf

section BoundedGrowth

variable {f : ℂ → ℂ}

/-- A function that is bounded on the upper half-plane has mean type `0`. -/
lemma meanType_of_isBoundedOnUpperHalfPlane
    (hf : IsBoundedOnUpperHalfPlane f) :
    meanType f = 0 := by
  classical
  rcases hf with ⟨C, hC0, hCbound⟩
  let u : ℝ → EReal :=
    fun y => ((Real.log (‖f (Complex.I * y)‖ + 1)) / y : EReal)
  let ψ : ℝ → EReal :=
    fun y => ((Real.log (C + 1)) / y : EReal)
  have h_eventually_le : u ≤ᶠ[Filter.atTop] ψ := by
    refine (eventually_gt_atTop (0 : ℝ)).mono ?_
    intro y hy
    have hy_pos : 0 < y := hy
    have hz_mem :
        Complex.I * (y : ℂ) ∈ upperHalfPlaneSet := by
      simp [upperHalfPlaneSet, hy_pos]
    have hnorm : ‖f (Complex.I * y)‖ ≤ C := hCbound _ hz_mem
    have h_pos_arg :
        0 < ‖f (Complex.I * y)‖ + 1 := by
      have : (0 : ℝ) ≤ ‖f (Complex.I * y)‖ := norm_nonneg _
      exact add_pos_of_nonneg_of_pos this zero_lt_one
    have h_pos_const : 0 < C + 1 := add_pos_of_nonneg_of_pos hC0 zero_lt_one
    have h_add_le : ‖f (Complex.I * y)‖ + 1 ≤ C + 1 :=
      add_le_add_left hnorm 1
    have h_log_le :
        Real.log (‖f (Complex.I * y)‖ + 1) ≤ Real.log (C + 1) :=
          (Real.log_le_log_iff h_pos_arg h_pos_const).mpr h_add_le
    --  Real.log_le_log h_pos_arg h_pos_const h_add_le
    have h_div :
        (Real.log (‖f (Complex.I * y)‖ + 1)) / y
          ≤ (Real.log (C + 1)) / y :=
      (div_le_div_iff_of_pos_right hy_pos).mpr h_log_le
    exact EReal.coe_le_coe_iff.mpr h_div
  have h_limψ :
      Filter.limsup ψ Filter.atTop = 0 := by
    apply Filter.Tendsto.limsup_eq
    rw [← EReal.coe_zero]
    refine Tendsto.comp (g := fun x : ℝ => (x : EReal))
        continuous_coe_real_ereal.continuousAt ?_
    simpa [ψ, one_div, div_eq_mul_inv, mul_comm] using
      (tendsto_inv_atTop_zero.const_mul (Real.log (C + 1)))
  have h_le :
      Filter.limsup u Filter.atTop ≤ 0 := by
    have := Filter.limsup_le_limsup h_eventually_le
    simpa [h_limψ, u, ψ] using this
  have h_eventually_nonneg :
      (fun _ : ℝ => (0 : EReal)) ≤ᶠ[Filter.atTop] u := by
    refine (eventually_gt_atTop (0 : ℝ)).mono ?_
    intro y hy
    have hy_pos : 0 < y := hy
    have h_log_nonneg :
        0 ≤ Real.log (‖f (Complex.I * y)‖ + 1) := by
      refine Real.log_nonneg ?_
      have : (0 : ℝ) ≤ ‖f (Complex.I * y)‖ := norm_nonneg _
      have : 1 ≤ ‖f (Complex.I * y)‖ + 1 := by linarith
      simp
    have h_div_nonneg :
        0 ≤ (Real.log (‖f (Complex.I * y)‖ + 1)) / y :=
      div_nonneg h_log_nonneg (le_of_lt hy_pos)
    exact EReal.coe_le_coe_iff.mpr h_div_nonneg
  have h_ge :
      0 ≤ Filter.limsup u Filter.atTop := by
    have := Filter.limsup_le_limsup h_eventually_nonneg
    simpa [limsup_zero_ereal_atTop] using this
  have h_eq :
      Filter.limsup u Filter.atTop = 0 := le_antisymm h_le h_ge
  simpa [meanType, u] using h_eq

/-- If `f` is bounded on the upper half-plane, the global limsup along `atImInfty`
is also `0`. -/
lemma limsup_atImInfty_of_isBoundedOnUpperHalfPlane
    (hf : IsBoundedOnUpperHalfPlane f) :
    Filter.limsup
      (fun z : ℍ =>
        ((Real.log (‖f z‖ + 1)) / (z.im : ℝ) : EReal))
      UpperHalfPlane.atImInfty = 0 := by
  classical
  rcases hf with ⟨C, hC0, hCbound⟩
  have h_neBot :
      (UpperHalfPlane.atImInfty : Filter ℍ).NeBot := by
    classical
    refine comap_neBot ?_
    intro S hS
    obtain ⟨A, hA⟩ := Filter.mem_atTop_sets.mp hS
    set y : ℝ := max A 1 + 1
    have hy_ge_two : (2 : ℝ) ≤ y := by
      have hmax : (1 : ℝ) ≤ max A 1 := le_max_right _ _
      linarith [hmax]
    have hy_pos : 0 < y := lt_of_lt_of_le zero_lt_two hy_ge_two
    have hy_mem : A ≤ y := by
      have h₁ : A ≤ max A 1 := le_max_left _ _
      linarith [h₁]
    have hIm : (Complex.I * (y : ℂ)).im = y := by simp
    let z : ℍ := ⟨Complex.I * (y : ℂ), by simpa [hIm] using hy_pos⟩
    have hz_im : UpperHalfPlane.im z = y := by
      simp [z, UpperHalfPlane.im, hIm]
    have hz_mem : UpperHalfPlane.im z ∈ Set.Ici A := by
      simpa [hz_im, Set.mem_Ici] using hy_mem
    exact ⟨z, hA (UpperHalfPlane.im z) hz_mem⟩
  haveI : (UpperHalfPlane.atImInfty : Filter ℍ).NeBot := h_neBot
  let G : ℍ → EReal :=
    fun z =>
      ((Real.log (‖f z‖ + 1)) / (z.im : ℝ) : EReal)
  let ψ : ℍ → EReal :=
    fun z =>
      ((Real.log (C + 1)) / (z.im : ℝ) : EReal)
  have h_pointwise_le : ∀ z : ℍ, G z ≤ ψ z := by
    intro z
    have hz_mem :
        (z : ℂ) ∈ upperHalfPlaneSet := by
      simpa [upperHalfPlaneSet] using (show 0 < (z : ℂ).im from z.property)
    have hnorm : ‖f z‖ ≤ C := hCbound _ hz_mem
    have h_pos_arg : 0 < ‖f z‖ + 1 := by
      have : (0 : ℝ) ≤ ‖f z‖ := norm_nonneg _
      exact add_pos_of_nonneg_of_pos this zero_lt_one
    have h_pos_const : 0 < C + 1 := add_pos_of_nonneg_of_pos hC0 zero_lt_one
    have h_add_le : ‖f z‖ + 1 ≤ C + 1 :=
      add_le_add_left hnorm 1
    have h_log_le :
        Real.log (‖f z‖ + 1) ≤ Real.log (C + 1) :=
      (Real.log_le_log_iff h_pos_arg h_pos_const).mpr h_add_le
    have hz_pos : 0 < (z.im : ℝ) := z.property
    have h_div :
        (Real.log (‖f z‖ + 1)) / (z.im : ℝ)
          ≤ (Real.log (C + 1)) / (z.im : ℝ) :=
      (div_le_div_iff_of_pos_right hz_pos).mpr h_log_le
    exact EReal.coe_le_coe_iff.mpr h_div
  have h_limsup_le :
      Filter.limsup G UpperHalfPlane.atImInfty ≤
        Filter.limsup ψ UpperHalfPlane.atImInfty :=
    Filter.limsup_le_limsup (Filter.Eventually.of_forall h_pointwise_le)
  have hψ :
      Filter.limsup ψ UpperHalfPlane.atImInfty = 0 := by
    have h_real :
        Tendsto (fun t : ℝ => ((Real.log (C + 1)) / t : ℝ))
          Filter.atTop (𝓝 (0 : ℝ)) := by
      simpa [one_div, div_eq_mul_inv, mul_comm] using
        (tendsto_inv_atTop_zero.const_mul (Real.log (C + 1)))
    have h_realE :
        Tendsto (fun t : ℝ => ((Real.log (C + 1)) / t : EReal))
          Filter.atTop (𝓝 (0 : EReal)) := by
      refine Tendsto.comp (g := fun x : ℝ => (x : EReal))
          continuous_coe_real_ereal.continuousAt ?_
      simpa using h_real
    have h_im :
        Tendsto UpperHalfPlane.im UpperHalfPlane.atImInfty Filter.atTop := by
      change Filter.map UpperHalfPlane.im UpperHalfPlane.atImInfty ≤ Filter.atTop
      simpa [UpperHalfPlane.atImInfty] using
        map_comap_le (m := UpperHalfPlane.im) (g := (Filter.atTop : Filter ℝ))
    have h_tendsto := h_realE.comp h_im
    apply Filter.Tendsto.limsup_eq
    exact h_tendsto
  have h_upper :
      Filter.limsup G UpperHalfPlane.atImInfty ≤ 0 := by
    simpa [G, ψ, hψ] using h_limsup_le
  have h_eventually_nonneg :
      (fun _ : ℍ => (0 : EReal)) ≤ᶠ[UpperHalfPlane.atImInfty] G := by
    refine Filter.Eventually.of_forall ?_
    intro z
    have hz_pos : 0 < (z.im : ℝ) := z.property
    have h_log_nonneg :
        0 ≤ Real.log (‖f z‖ + 1) := by
      refine Real.log_nonneg ?_
      have : (0 : ℝ) ≤ ‖f z‖ := norm_nonneg _
      have : 1 ≤ ‖f z‖ + 1 := by linarith
      simp
    have h_div_nonneg :
        0 ≤ (Real.log (‖f z‖ + 1)) / (z.im : ℝ) :=
      div_nonneg h_log_nonneg (le_of_lt hz_pos)
    exact EReal.coe_le_coe_iff.mpr h_div_nonneg
  have h_lower :
      0 ≤ Filter.limsup G UpperHalfPlane.atImInfty := by
    have := Filter.limsup_le_limsup h_eventually_nonneg
    simpa [G, Filter.limsup_const (0 : EReal)] using this
  have h_eq :
      Filter.limsup G UpperHalfPlane.atImInfty = 0 :=
    le_antisymm h_upper h_lower
  simpa [G] using h_eq

end BoundedGrowth

/--
A key property of the Nevanlinna class: the growth rate along the imaginary axis
determines the maximal growth rate in the upper half-plane (relative to the imaginary part).
This follows from the canonical representation of functions of bounded type.
-/
lemma IsOfBoundedTypeUpperHalfPlane.limsup_eq_meanType
    {f : ℂ → ℂ} (hf : IsOfBoundedTypeUpperHalfPlane f) :
    Filter.limsup
      (fun z : ℍ =>
        ((Real.log (norm (f z) + 1)) / (z.im : ℝ) : EReal))
      UpperHalfPlane.atImInfty =
    meanType f := by
  apply le_antisymm
  · exact hf.limsup_atImInfty_le_meanType
  · exact meanType_le_limsup_atImInfty' hf

lemma meanType_eq_limsup_atImInfty
    {f : ℂ → ℂ} (hf : IsOfBoundedTypeUpperHalfPlane f) :
  Complex.meanType f =
    Filter.limsup
      (fun z : ℍ =>
        ((Real.log (norm (f z) + 1)) / (z.im : ℝ) : EReal))
      UpperHalfPlane.atImInfty := by
  -- Just restate `hf.limsup_eq_meanType` with `meanType` on the left.
  simpa using (hf.limsup_eq_meanType).symm

theorem IsOfBoundedTypeUpperHalfPlane.meanType_eq_atImInfty
    {f : ℂ → ℂ} (hf : IsOfBoundedTypeUpperHalfPlane f) :
  Complex.meanType f =
    Complex.meanType_atImInfty (fun z : ℍ => f z) := by
  -- `meanType_atImInfty` is *defined* as that same EReal limsup.
  have h := meanType_eq_limsup_atImInfty (f := f) hf
  simpa [meanType_atImInfty] using h


/-- For `f` of bounded type in the upper half-plane (Nevanlinna class),
the "vertical" mean type equals the "global" mean type along non-tangential
approach to `i∞`. -/
theorem IsOfBoundedTypeUpperHalfPlane.meanType_eq_atImInfty'
    {f : ℂ → ℂ} (hf : IsOfBoundedTypeUpperHalfPlane f) :
  Complex.meanType f =
    Complex.meanType_atImInfty (fun z : ℍ => f z) := by
  exact IsOfBoundedTypeUpperHalfPlane.meanType_eq_atImInfty (f := f) hf


end Complex
