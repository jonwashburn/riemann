import Riemann.PhysLean.SpinGlass.SKModel
import Riemann.PhysLean.SpinGlass.GuerraBound
import Riemann.PhysLean.SpinGlass.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Data.Fintype.Pi
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory ProbabilityTheory Real BigOperators SpinGlass SpinGlass.Algebra
open PhysLean.Probability.GaussianIBP

namespace SpinGlass

/-!
# Section 1.4: General Replica Calculus and Latala's Argument

To prove concentration, we must manage functions of `n` replicas.
Differentiation increases the number of replicas by 2.

**Terminology:** this file implements the **interpolation / smart path** machinery
(Talagrand Vol. I, §§1.3–1.4). It is *not* the cavity method (Talagrand Vol. I, §1.6),
which is an induction on `N`.
-/

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable (N : ℕ) (β h q : ℝ)
variable (sk : SKDisorder (Ω := Ω) N β h) (sim : SimpleDisorder (Ω := Ω) N β q)

section ReplicaCalculus

variable (n : ℕ)

/-- The space of `n` replicas: (Fin n → Config N). -/
abbrev ReplicaSpace := Fin n → Config N

/-- A function of `n` replicas. -/
abbrev ReplicaFun := ReplicaSpace N n → ℝ

/-- A generic two-replica interaction kernel `U(σ,τ)` (Talagrand’s `U_{ℓ,ℓ'}`). -/
abbrev InteractionKernel := Config N → Config N → ℝ

/--
Interpolated Hamiltonian (Guerra):
\[
H_t = \sqrt{t}\,U + \sqrt{1-t}\,V + H_{\text{field}}.
\]

The external field term uses the **magnetization-dependent** energy
`magnetic_field_vector` (not a constant shift).
-/
noncomputable def H_gauss (t : ℝ) : Ω → EnergySpace N :=
  fun w =>
    (Real.sqrt t) • sk.U w
      + (Real.sqrt (1 - t)) • sim.V w

noncomputable def H_field : EnergySpace N :=
  magnetic_field_vector (N := N) h

noncomputable def H_t (t : ℝ) : Ω → EnergySpace N :=
  fun w =>
    H_gauss (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w
      + H_field (N := N) (h := h)

/-!
### Joint Gaussian packaging for `(U,V)`

To apply Hilbert-space Gaussian IBP to functions depending on **both** processes `U` and `V`,
we package the pair `(sk.U, sim.V)` as a single `IsGaussianHilbert` random variable valued in
the `L²`-product space `WithLp 2 (EnergySpace N × EnergySpace N)`.

This construction uses the independence assumption `sk.U ⟂ᵢ sim.V` and the existing coordinate
models `sk.hU` and `sim.hV`.
-/

/-- The joint Gaussian vector `(U,V)` in the `L²`-product space. -/
noncomputable def UV : Ω → WithLp 2 (EnergySpace N × EnergySpace N) :=
  fun ω => WithLp.toLp 2 (sk.U ω, sim.V ω)

/-- `UV` is a centered Gaussian Hilbert random variable when `U` and `V` are independent. -/
noncomputable def isGaussianHilbert_UV
    (hIndep : ProbabilityTheory.IndepFun sk.U sim.V (ℙ : Measure Ω)) :
    IsGaussianHilbert (UV (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)) := by
  classical
  -- abbreviate the two coordinate models
  let hU := sk.hU
  let hV := sim.hV
  -- Build the combined coordinate family on a sigma index (Bool chooses which process).
  let κ : Bool → Type* := fun
    | true => hU.ι
    | false => hV.ι
  let X : (b : Bool) → (j : κ b) → Ω → ℝ :=
    fun b =>
      match b with
      | true => fun j => hU.c j
      | false => fun j => hV.c j
  have mX : ∀ b j, Measurable (X b j) := by
    intro b j
    cases b <;> simpa [X] using (by
      first | exact hV.c_meas j | exact hU.c_meas j)
  have h2 : ∀ b, ProbabilityTheory.iIndepFun (X b) (ℙ : Measure Ω) := by
    intro b
    cases b <;> simpa [X] using (by
      first | exact hV.c_indep | exact hU.c_indep)
  -- Independence across `b : Bool` of the *tuples* `(X b ·)`.
  have h1 : ProbabilityTheory.iIndepFun (fun b ω => (X b · ω)) (ℙ : Measure Ω) := by
    -- For `Bool`, mutual independence reduces to the 2-variable case.
    -- We derive independence of the coordinate-tuples from independence of `(U,V)` by composition.
    have hφ : Measurable (fun u : EnergySpace N => fun i : hU.ι => inner ℝ u (hU.w i)) := by
      refine measurable_pi_lambda _ ?_
      intro i
      -- `u ↦ ⟪u, w i⟫` is continuous, hence measurable.
      have hcont : Continuous (fun u : EnergySpace N => inner ℝ u (hU.w i)) := by
        have hpair : Continuous (fun u : EnergySpace N => (u, hU.w i)) :=
          (continuous_id.prodMk continuous_const)
        simpa using (continuous_inner.comp hpair)
      exact hcont.measurable
    have hψ : Measurable (fun v : EnergySpace N => fun j : hV.ι => inner ℝ v (hV.w j)) := by
      refine measurable_pi_lambda _ ?_
      intro j
      have hcont : Continuous (fun v : EnergySpace N => inner ℝ v (hV.w j)) := by
        have hpair : Continuous (fun v : EnergySpace N => (v, hV.w j)) :=
          (continuous_id.prodMk continuous_const)
        simpa using (continuous_inner.comp hpair)
      exact hcont.measurable
    have hInd_tuples :
        ProbabilityTheory.IndepFun
          (fun ω : Ω => fun i : hU.ι => hU.c i ω)
          (fun ω : Ω => fun j : hV.ι => hV.c j ω)
          (ℙ : Measure Ω) := by
      -- Start from `IndepFun (φ ∘ U) (ψ ∘ V)` and rewrite with `coord_eq_c`.
      have hcomp :
          ProbabilityTheory.IndepFun (fun ω => (fun u => fun i : hU.ι => inner ℝ u (hU.w i)) (sk.U ω))
            (fun ω => (fun v => fun j : hV.ι => inner ℝ v (hV.w j)) (sim.V ω))
            (ℙ : Measure Ω) :=
        (ProbabilityTheory.IndepFun.comp hIndep hφ hψ)
      -- Replace the composed maps by the coordinate-tuples `hU.c` and `hV.c`.
      refine ProbabilityTheory.IndepFun.congr hcomp ?_ ?_
      · -- left tuple
        refine Filter.Eventually.of_forall (fun ω => ?_)
        funext i
        have hcoord : PhysLean.Probability.GaussianIBP.coord hU.w sk.U i = hU.c i := by
          funext ω'
          simpa using
            congrArg (fun f => f i ω')
              (PhysLean.Probability.GaussianIBP.coord_eq_c (g := sk.U) hU)
        -- evaluate at `ω`
        simpa [PhysLean.Probability.GaussianIBP.coord] using congrArg (fun f => f ω) hcoord
      · -- right tuple
        refine Filter.Eventually.of_forall (fun ω => ?_)
        funext j
        have hcoord : PhysLean.Probability.GaussianIBP.coord hV.w sim.V j = hV.c j := by
          funext ω'
          simpa using
            congrArg (fun f => f j ω')
              (PhysLean.Probability.GaussianIBP.coord_eq_c (g := sim.V) hV)
        simpa [PhysLean.Probability.GaussianIBP.coord] using congrArg (fun f => f ω) hcoord
    -- Now prove `iIndepFun` on `Bool` by cases on the finset.
    refine
      (ProbabilityTheory.iIndepFun_iff (m := fun b => inferInstance)
        (f := fun b ω => (X b · ω)) (μ := (ℙ : Measure Ω))).2 ?_
    intro s f' hs
    classical
    -- `Bool` finsets are: `∅`, `{false}`, `{true}`, `{false,true}`.
    by_cases hfalse : false ∈ s
    · by_cases htrue : true ∈ s
      · -- both are present
        have hs' :
            (ℙ : Measure Ω) (f' false ∩ f' true) =
              (ℙ : Measure Ω) (f' false) * (ℙ : Measure Ω) (f' true) := by
          -- Use independence of the two tuples.
          have hInd_bool :
              ProbabilityTheory.IndepFun (fun ω => (X false · ω)) (fun ω => (X true · ω))
                (ℙ : Measure Ω) := by
            simpa [X] using hInd_tuples.symm
          -- Convert to independence of the corresponding measurable sets.
          have hInd_ms :
              ProbabilityTheory.Indep
                (MeasurableSpace.comap (fun ω => (X false · ω)) (inferInstance))
                (MeasurableSpace.comap (fun ω => (X true · ω)) (inferInstance))
                (ℙ : Measure Ω) := by
            simpa [ProbabilityTheory.IndepFun] using
              (ProbabilityTheory.IndepFun_iff_Indep (f := fun ω => (X false · ω))
                (g := fun ω => (X true · ω)) (μ := (ℙ : Measure Ω))).1 hInd_bool
          have hA :
              MeasurableSet[
                MeasurableSpace.comap (fun ω => (X false · ω)) (inferInstance)] (f' false) := by
            simpa using hs false hfalse
          have hB :
              MeasurableSet[
                MeasurableSpace.comap (fun ω => (X true · ω)) (inferInstance)] (f' true) := by
            simpa using hs true htrue
          have hIndSet :
              ProbabilityTheory.IndepSet (f' false) (f' true) (ℙ : Measure Ω) :=
            hInd_ms.indepSet_of_measurableSet hA hB
          simpa [Set.inter_comm] using hIndSet.measure_inter_eq_mul
        -- reduce the general `Finset` intersection/product to the `{false,true}` case
        have hs_eq : s = ({false, true} : Finset Bool) := by
          ext b
          cases b <;> simp [hfalse, htrue]
        subst hs_eq
        -- Rewrite `⋂ i, f' i` as `f' false ∩ f' true` and use `hs'`.
        have hInter : (⋂ i : Bool, f' i) = f' false ∩ f' true := by
          ext ω; simp
        simpa [hInter] using hs'
      · -- only `false` present
        have hs_eq : s = ({false} : Finset Bool) := by
          ext b
          cases b <;> simp [hfalse, htrue]
        subst hs_eq
        simp
    · -- `false` not in `s`
      by_cases htrue : true ∈ s
      · have hs_eq : s = ({true} : Finset Bool) := by
          ext b
          cases b <;> simp [hfalse, htrue]
        subst hs_eq
        simp
      · -- neither present
        have hs_eq : s = (∅ : Finset Bool) := by
          ext b
          cases b <;> simp [hfalse, htrue]
        subst hs_eq
        simp
  -- Combine the families using `iIndepFun_uncurry` and transport to a sum-indexed family.
  have h_uncurry :
      ProbabilityTheory.iIndepFun (fun (p : (b : Bool) × κ b) ω => X p.1 p.2 ω) (ℙ : Measure Ω) :=
    ProbabilityTheory.iIndepFun_uncurry (P := (ℙ : Measure Ω)) (X := X) mX h1 h2
  -- Surjective map from the sigma index `(b, j)` to the sum index.
  let g : (b : Bool) × κ b → hU.ι ⊕ hV.ι :=
    fun
      | ⟨true, i⟩ => Sum.inl i
      | ⟨false, j⟩ => Sum.inr j
  have hg : Function.Surjective g := by
    intro s
    cases s with
    | inl i => exact ⟨⟨true, i⟩, rfl⟩
    | inr j => exact ⟨⟨false, j⟩, rfl⟩
  have h_sum :
      ProbabilityTheory.iIndepFun (fun i ω => (Sum.elim hU.c hV.c i) ω) (ℙ : Measure Ω) := by
    -- `h_uncurry` is an independence statement on a surjective precomposition of the sum-family.
    have hpre :
        ProbabilityTheory.iIndepFun (fun p ω => (Sum.elim hU.c hV.c (g p)) ω) (ℙ : Measure Ω) := by
      -- `h_uncurry` is expressed using `X`; transport it to the `Sum.elim` presentation.
      refine
        (ProbabilityTheory.iIndepFun.congr (μ := (ℙ : Measure Ω))
            (f := fun p ω => X p.1 p.2 ω)
            (g := fun p ω => (Sum.elim hU.c hV.c (g p)) ω) ?_) h_uncurry
      intro p
      refine Filter.Eventually.of_forall (fun ω => ?_)
      cases p with
      | mk b j =>
        cases b <;> rfl
    refine ProbabilityTheory.iIndepFun.of_precomp (μ := (ℙ : Measure Ω)) (g := g) hg ?_
    exact hpre
  -- Assemble the `IsGaussianHilbert` structure.
  refine
    { ι := hU.ι ⊕ hV.ι
      fintype_ι := inferInstance
      w := hU.w.prod hV.w
      τ := Sum.elim hU.τ hV.τ
      c := Sum.elim hU.c hV.c
      c_meas := by
        intro i
        cases i <;> simpa using (by
          first | exact hU.c_meas _ | exact hV.c_meas _)
      c_gauss := by
        intro i
        cases i <;> simpa using (by
          first | exact hU.c_gauss _ | exact hV.c_gauss _)
      c_indep := by
        simpa using h_sum
      repr := by
        -- The ONB sum splits into the two component ONB sums.
        funext ω
        apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
        simp [UV, hU.repr, hV.repr, OrthonormalBasis.prod_apply, WithLp.ofLp]
        -- Reduce to an equality in the underlying product `EnergySpace × EnergySpace`.
        ext i
        · -- fst component
          -- push `Prod.fst` through both sums and simplify the zero-component
          have hfstU :
              (∑ x : hU.ι, hU.c x ω • (hU.w x, (0 : EnergySpace N))).1
                = ∑ x : hU.ι, hU.c x ω • hU.w x := by
            -- push `fst` through the sum; each term projects to `c • w`
            simpa using
              (Prod.fst_sum (s := (Finset.univ : Finset hU.ι))
                (f := fun x : hU.ι => hU.c x ω • (hU.w x, (0 : EnergySpace N))))
          have hfstV :
              (∑ x : hV.ι, hV.c x ω • ((0 : EnergySpace N), hV.w x)).1 = 0 := by
            -- push `Prod.fst` through the sum; each term is `0`
            calc
              (∑ x : hV.ι, hV.c x ω • ((0 : EnergySpace N), hV.w x)).1
                  = ∑ x : hV.ι, (hV.c x ω • ((0 : EnergySpace N), hV.w x)).1 := by
                      simpa using
                        (Prod.fst_sum (s := (Finset.univ : Finset hV.ι))
                          (f := fun x : hV.ι => hV.c x ω • ((0 : EnergySpace N), hV.w x)))
              _ = ∑ x : hV.ι, (0 : EnergySpace N) := by simp
              _ = 0 := by simp
          -- evaluate at configuration `i`
          have hfstU' :
              (∑ i' : hU.ι, hU.c i' ω • hU.w i') i
                = (∑ x : hU.ι, hU.c x ω • (hU.w x, (0 : EnergySpace N))).1 i := by
            simpa using (congrArg (fun H : EnergySpace N => H i) hfstU.symm)
          -- reduce the RHS to the `U`-term using `hfstV`
          have hfstV' : ((∑ x : hV.ι, hV.c x ω • ((0 : EnergySpace N), hV.w x)).1) i = 0 := by
            -- evaluate `hfstV` at the configuration `i`
            simpa using congrArg (fun H : EnergySpace N => H i) hfstV
          -- close the goal by rewriting the `U`-part via `hfstU'`
          -- and killing the `V`-part via `hfstV'`
          calc
            (WithLp.toLp 2
                (∑ j : hU.ι, hU.c j ω • hU.w j, ∑ j : hV.ι, hV.c j ω • hV.w j)).1 i
                = (∑ x : hU.ι, hU.c x ω • (hU.w x, (0 : EnergySpace N))).1 i := by
                    simpa [WithLp.toLp] using hfstU'
            _ =
                (∑ x : hU.ι, hU.c x ω • (hU.w x, (0 : EnergySpace N))
                  + ∑ x : hV.ι, hV.c x ω • ((0 : EnergySpace N), hV.w x)).1 i := by
                    aesop
        · -- snd component
          have hsndU :
              (∑ x : hU.ι, hU.c x ω • (hU.w x, (0 : EnergySpace N))).2 = 0 := by
            calc
              (∑ x : hU.ι, hU.c x ω • (hU.w x, (0 : EnergySpace N))).2
                  = ∑ x : hU.ι, (hU.c x ω • (hU.w x, (0 : EnergySpace N))).2 := by
                      simpa using
                        (Prod.snd_sum (s := (Finset.univ : Finset hU.ι))
                          (f := fun x : hU.ι => hU.c x ω • (hU.w x, (0 : EnergySpace N))))
              _ = ∑ x : hU.ι, (0 : EnergySpace N) := by simp
              _ = 0 := by simp
          have hsndV :
              (∑ x : hV.ι, hV.c x ω • ((0 : EnergySpace N), hV.w x)).2
                = ∑ x : hV.ι, hV.c x ω • hV.w x := by
            simpa using
              (Prod.snd_sum (s := (Finset.univ : Finset hV.ι))
                (f := fun x : hV.ι => hV.c x ω • ((0 : EnergySpace N), hV.w x)))
          have hsndV' :
              (∑ i' : hV.ι, hV.c i' ω • hV.w i') i
                = (∑ x : hV.ι, hV.c x ω • ((0 : EnergySpace N), hV.w x)).2 i := by
            exact congrArg (fun H : EnergySpace N => H i) hsndV.symm
          have hsndU' : ((∑ x : hU.ι, hU.c x ω • (hU.w x, (0 : EnergySpace N))).2) i = 0 := by
            simpa using congrArg (fun H : EnergySpace N => H i) hsndU
          -- close the goal by rewriting the `V`-part via `hsndV'`
          -- and killing the `U`-part via `hsndU'`
          calc
            (WithLp.toLp 2
                (∑ j : hU.ι, hU.c j ω • hU.w j, ∑ j : hV.ι, hV.c j ω • hV.w j)).2 i
                = (∑ j : hV.ι, hV.c j ω • hV.w j) i := by
                    simp [WithLp.toLp]
            _ = (∑ x : hV.ι, hV.c x ω • ((0 : EnergySpace N), hV.w x)).2 i := by
                  exact hsndV'
            _ =
                (∑ x : hU.ι, hU.c x ω • (hU.w x, (0 : EnergySpace N))
                  + ∑ x : hV.ι, hV.c x ω • ((0 : EnergySpace N), hV.w x)).2 i := by
                    aesop
    }

/--
**Equation (1.17)**: The Gibbs average of a function of `n` replicas.
⟨f⟩ = (1/Z^n) ∑_{σ^1...σ^n} f(σ) exp(-∑ H(σ^l))
-/
noncomputable def gibbs_average_n_det (H : EnergySpace N) (f : ReplicaFun N n) : ℝ :=
  ∑ σs : ReplicaSpace N n, f σs * ∏ l, gibbs_pmf N H (σs l)

noncomputable def gibbs_average_n (t : ℝ) (f : ReplicaFun N n) : Ω → ℝ :=
  fun w =>
    let H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w
    gibbs_average_n_det (N := N) (n := n) H f

/-!
### Basic bounds for `gibbs_average_n_det`

These are used both for integrability and for “moderate growth” hypotheses in Gaussian IBP.
-/

lemma abs_gibbs_average_n_det_le (H : EnergySpace N) (f : ReplicaFun N n) :
    |gibbs_average_n_det (N := N) (n := n) H f| ≤ ∑ σs : ReplicaSpace N n, |f σs| := by
  classical
  -- Triangle inequality, using `0 ≤ gibbs_pmf ≤ 1`.
  have hnonneg :
      ∀ σs : ReplicaSpace N n, 0 ≤ ∏ l, gibbs_pmf N H (σs l) :=
    fun σs => by
      classical
      refine Finset.prod_nonneg ?_
      intro l _hl
      exact SpinGlass.gibbs_pmf_nonneg (N := N) (H := H) (σ := σs l)
  have hprod_le_one :
      ∀ σs : ReplicaSpace N n, (∏ l, gibbs_pmf N H (σs l)) ≤ (1 : ℝ) :=
    fun σs => by
      classical
      -- `∏ l, p_l ≤ 1` since each `0 ≤ p_l ≤ 1`.
      have hfac : ∀ l : Fin n, gibbs_pmf N H (σs l) ≤ 1 := by
        intro l
        have hZpos : 0 < Z N H := SpinGlass.Z_pos (N := N) (H := H)
        have hterm_le : Real.exp (-H (σs l)) ≤ Z N H := by
          -- a single term is bounded by the sum `Z`
          have :=
            Finset.single_le_sum
              (s := (Finset.univ : Finset (Config N)))
              (f := fun τ => Real.exp (-H τ))
              (hf := fun τ _hτ => (Real.exp_pos _).le)
              (a := σs l) (h := Finset.mem_univ (σs l))
          simpa [Z] using this
        have := (div_le_one hZpos).2 hterm_le
        simpa [SpinGlass.gibbs_pmf] using this
      simpa using
        (Finset.prod_le_one (s := (Finset.univ : Finset (Fin n)))
          (f := fun l => gibbs_pmf N H (σs l))
          (fun l _hl => SpinGlass.gibbs_pmf_nonneg (N := N) (H := H) (σ := σs l))
          (fun l _hl => hfac l))
  calc
    |gibbs_average_n_det (N := N) (n := n) H f|
        = |∑ σs : ReplicaSpace N n, f σs * ∏ l, gibbs_pmf N H (σs l)| := by
            rfl
    _ ≤ ∑ σs : ReplicaSpace N n, |f σs * ∏ l, gibbs_pmf N H (σs l)| := by
          -- finset triangle inequality
          simpa using
            (Finset.abs_sum_le_sum_abs
              (f := fun σs : ReplicaSpace N n => f σs * ∏ l, gibbs_pmf N H (σs l))
              (s := (Finset.univ : Finset (ReplicaSpace N n))))
    _ = ∑ σs : ReplicaSpace N n, (|f σs| * |∏ l, gibbs_pmf N H (σs l)|) := by
          refine Finset.sum_congr rfl (fun σs _hσs => ?_)
          simp [abs_mul]
    _ ≤ ∑ σs : ReplicaSpace N n, |f σs| := by
          refine Finset.sum_le_sum ?_
          intro σs _hσs
          have habs :
              |∏ l, gibbs_pmf N H (σs l)| = ∏ l, gibbs_pmf N H (σs l) := by
            have h0 : 0 ≤ ∏ l, gibbs_pmf N H (σs l) := hnonneg σs
            simp [abs_of_nonneg h0]
          have hle1 : |∏ l, gibbs_pmf N H (σs l)| ≤ 1 := by
            simpa [habs] using hprod_le_one σs
          simpa using (mul_le_mul_of_nonneg_left hle1 (abs_nonneg (f σs)))

/-- Expected Gibbs average: ν_t(f) = E[ ⟨f⟩_t ]. -/
noncomputable def nu (t : ℝ) (f : ReplicaFun N n) : ℝ :=
  ∫ w, gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w ∂ℙ

/-- Lift a function of `n` replicas to `n + k` replicas by ignoring the last `k`. -/
def liftReplicaFun (k : ℕ) (f : ReplicaFun N n) : ReplicaFun N (n + k) :=
  fun σs => f (fun i => σs (Fin.castAdd k i))

/--
The product Gibbs weights on `n` replicas sum to `1`.

This is the finite-dimensional fact that the `n`-replica Gibbs measure is the product of `n`
copies of the one-replica Gibbs measure.
-/
lemma sum_prod_gibbs_pmf_eq_one (H : EnergySpace N) :
    (∑ σs : ReplicaSpace N n, ∏ l, gibbs_pmf N H (σs l)) = 1 := by
  classical
  -- Induction on `n`, splitting `Fin (n+1) → Config N` into head/tail via `Fin.consEquiv`.
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let p : Config N → ℝ := gibbs_pmf N H
      have hs1 : (∑ σ : Config N, p σ) = 1 := by
        simpa [p] using (SpinGlass.sum_gibbs_pmf (N := N) (H := H))
      let e : (Config N × (Fin n → Config N)) ≃ (Fin (n + 1) → Config N) :=
        Fin.consEquiv (fun _ : Fin (n + 1) => Config N)
      have hrew :
          (∑ σs : (Fin (n + 1) → Config N), ∏ l : Fin (n + 1), p (σs l))
            = ∑ x : (Config N × (Fin n → Config N)), ∏ l : Fin (n + 1), p (e x l) := by
        -- `Fintype.sum_equiv` lets us change variables along the equivalence `e`.
        simpa using
          (Fintype.sum_equiv e
              (f := fun x => ∏ l : Fin (n + 1), p (e x l))
              (g := fun σs => ∏ l : Fin (n + 1), p (σs l))
              (h := fun x => rfl)).symm
      -- Compute the RHS by iterating sums over `(σ₀, σtail)` and factoring.
      calc
        (∑ σs : (Fin (n + 1) → Config N), ∏ l : Fin (n + 1), p (σs l))
            = ∑ x : (Config N × (Fin n → Config N)), ∏ l : Fin (n + 1), p (e x l) := hrew
        _ = ∑ σ₀ : Config N, ∑ σtail : (Fin n → Config N),
              p σ₀ * (∏ i : Fin n, p (σtail i)) := by
              -- Expand the sum over the product type, then split the `Fin (n+1)` product.
              classical
              -- First rewrite the sum over pairs as an iterated sum.
              simp [Fintype.sum_prod_type, e, p, Fin.prod_univ_succ]
        _ = ∑ σ₀ : Config N, p σ₀ * (∑ σtail : (Fin n → Config N), ∏ i : Fin n, p (σtail i)) := by
              classical
              -- Pull out the constant scalar `p σ₀` from the inner sum.
              simp [Finset.mul_sum]
        _ = ∑ σ₀ : Config N, p σ₀ * 1 := by
              -- Use the induction hypothesis for the tail sum.
              simpa [p] using congrArg (fun r => ∑ σ₀ : Config N, p σ₀ * r) ih
        _ = ∑ σ₀ : Config N, p σ₀ := by simp
        _ = 1 := hs1

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/--
Uniform bound on the n-replica Gibbs average:
\[
|\langle f\rangle_{t,n}| \le \max_{\sigma^1,\dots,\sigma^n} |f(\sigma^1,\dots,\sigma^n)|.
\]
-/
lemma abs_gibbs_average_n_le (t : ℝ) (f : ReplicaFun N n) (w : Ω) :
    |gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w|
      ≤ ∑ σs : ReplicaSpace N n, |f σs| := by
  classical
  -- crude but sufficient: triangle inequality and `0 ≤ ∏ l, gibbs_pmf ...`.
  have hnonneg :
      ∀ σs : ReplicaSpace N n,
        0 ≤ ∏ l, gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) :=
    fun σs => by
      classical
      -- product of nonnegative terms
      have : ∀ l : Fin n,
          0 ≤ gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) :=
        fun l => SpinGlass.gibbs_pmf_nonneg (N := N) (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σ := σs l)
      -- move to finset product
      simpa using Finset.prod_nonneg (fun l _hl => this l)
  -- triangle inequality
  calc
    |gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w|
        = |∑ σs : ReplicaSpace N n,
            f σs * ∏ l,
              gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)| := by
            rfl
    _ ≤ ∑ σs : ReplicaSpace N n,
          |f σs * ∏ l,
              gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)| := by
          classical
          -- Apply the finset triangle inequality on `univ`.
          simpa using
            (Finset.abs_sum_le_sum_abs
              (f := fun σs : ReplicaSpace N n =>
                f σs * ∏ l, gibbs_pmf N
                  (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))
              (s := (Finset.univ : Finset (ReplicaSpace N n))))
    _ = ∑ σs : ReplicaSpace N n,
          (|f σs| * |∏ l,
              gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)|) := by
          refine Finset.sum_congr rfl ?_
          intro σs _hσs
          simp [abs_mul]
    _ ≤ ∑ σs : ReplicaSpace N n, |f σs| := by
          -- use `|∏ ...| = ∏ ... ≤ 1`, but we only need a crude bound by `1`.
          -- Since each factor is a probability, it is ≤ 1.
          classical
          -- compare termwise on the finset `univ` and `simp` back to the `Fintype` sum.
          simpa using
            (Finset.sum_le_sum (s := (Finset.univ : Finset (ReplicaSpace N n))) (fun σs _hσs => by
              have hle1 : |∏ l,
                  gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)| ≤ 1 := by
                -- crude: each factor `gibbs_pmf` is ≤ 1, hence product ≤ 1
                have hfac : ∀ l : Fin n,
                    gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) ≤ 1 := by
                  intro l
                  have hZpos :
                      0 < Z N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) :=
                    SpinGlass.Z_pos (N := N)
                      (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
                  have hterm_le :
                      Real.exp (-(H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))
                        ≤ Z N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) := by
                    -- a single term is bounded by the sum `Z`
                    classical
                    -- use `Finset.single_le_sum` on `s = univ`, `f = exp(-H)`
                    have :=
                      Finset.single_le_sum
                        (s := (Finset.univ : Finset (Config N)))
                        (f := fun τ =>
                          Real.exp (-(H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ))
                        (hf := fun τ _hτ => (Real.exp_pos _).le)
                        (a := (σs l)) (h := Finset.mem_univ (σs l))
                    simpa [Z] using this
                  have := (div_le_one hZpos).2 hterm_le
                  simpa [SpinGlass.gibbs_pmf] using this
                -- absolute value is redundant since factors are nonnegative
                have habs :
                    |∏ l,
                        gibbs_pmf N
                          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)|
                      =
                    ∏ l,
                        gibbs_pmf N
                          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) := by
                  have hnonneg' : 0 ≤ ∏ l,
                      gibbs_pmf N
                        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) :=
                    hnonneg σs
                  simp [abs_of_nonneg hnonneg']
                have hprod :
                    ∏ l,
                        gibbs_pmf N
                          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)
                      ≤ (1 : ℝ) := by
                  -- `∏ l, a_l ≤ 1` if each `0 ≤ a_l` and `a_l ≤ 1`.
                  classical
                  simpa using
                    (Finset.prod_le_one (s := (Finset.univ : Finset (Fin n)))
                      (f := fun l =>
                        gibbs_pmf N
                          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))
                      (fun l _hl => SpinGlass.gibbs_pmf_nonneg (N := N)
                        (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
                        (σ := σs l))
                      (fun l _hl => hfac l))
                simpa [habs] using hprod
              -- finish the termwise inequality: `|f| * |w| ≤ |f|`
              have : |f σs| * |∏ l,
                  gibbs_pmf N
                    (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)|
                    ≤ |f σs| := by
                -- multiply the bound `|w| ≤ 1` by the nonnegative factor `|f|`
                simpa using (mul_le_mul_of_nonneg_left hle1 (abs_nonneg (f σs)))
              -- close
              simpa [mul_assoc] using this))

-- From the above crude bound, integrability under the probability measure is immediate.
lemma integrable_gibbs_average_n (t : ℝ) (f : ReplicaFun N n) :
    Integrable (fun w => gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w) := by
  classical
  -- A uniform (in `w`) bound, hence an a.e. bound.
  have hbound :
      ∀ w, ‖gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w‖
        ≤ ∑ σs : ReplicaSpace N n, ‖f σs‖ := by
    intro w
    simpa [Real.norm_eq_abs] using
      (abs_gibbs_average_n_le (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) (n := n) (t := t) (f := f) w)
  -- Measurability of the Gibbs average is by finite sums/products of measurable functions.
  have hU_meas : Measurable (sk.U) := sk.hU.repr_measurable
  have hV_meas : Measurable (sim.V) := sim.hV.repr_measurable
  have hHt_meas :
      Measurable (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t) := by
    -- linear combination of measurable maps + constant
    have h1 : Measurable (fun w => (Real.sqrt t) • sk.U w) := hU_meas.const_smul (Real.sqrt t)
    have h2 : Measurable (fun w => (Real.sqrt (1 - t)) • sim.V w) := hV_meas.const_smul (Real.sqrt (1 - t))
    have h3 : Measurable (fun _w : Ω => H_field (N := N) (h := h)) := measurable_const
    -- Keep the addition parenthesization aligned with the definition of `H_t`:
    -- `H_t = (√t • U + √(1-t) • V) + H_field`.
    simpa [H_t, H_gauss] using ((h1.add h2).add h3)
  have h_gibbs_pmf_meas :
      ∀ (σ : Config N),
        Measurable fun w =>
          gibbs_pmf N
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) σ := by
    intro σ
    -- unfold `gibbs_pmf` and use measurability of evaluation, exp, the finite sum `Z`, and division.
    have hEval : Measurable fun w =>
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) σ :=
      (evalCLM (N := N) σ).measurable.comp hHt_meas
    have hNum : Measurable fun w =>
        Real.exp (-
          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) σ) :=
      (Real.continuous_exp.measurable.comp (measurable_neg.comp hEval))
    have hZ : Measurable fun w =>
        Z N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) := by
      classical
      -- `Z` is a finite sum of exponentials of measurable evaluations.
      have hterm : ∀ τ : Config N,
          Measurable fun w =>
            Real.exp (-
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ) := by
        intro τ
        have hEvalτ : Measurable fun w =>
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ :=
          (evalCLM (N := N) τ).measurable.comp hHt_meas
        exact (Real.continuous_exp.measurable.comp (measurable_neg.comp hEvalτ))
      -- now apply `Finset.measurable_sum` on `Finset.univ`.
      simpa [Z] using
        (Finset.measurable_sum (s := (Finset.univ : Finset (Config N)))
          (f := fun τ w =>
            Real.exp (-
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ))
          (hf := by intro τ _hτ; simpa using hterm τ))
    -- division is measurable
    simpa [SpinGlass.gibbs_pmf] using hNum.div hZ
  have hMeas :
      Measurable (fun w =>
        gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w) := by
    classical
    -- Expand the finite sum over replica configurations.
    -- We work with the `Finset.univ` presentation to use `Finset.measurable_sum/prod`.
    have hterm :
        ∀ σs : ReplicaSpace N n,
          Measurable fun w =>
            f σs * ∏ l : Fin n,
              gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) := by
      intro σs
      -- measurability of the product over replicas
      have hprod :
          Measurable fun w =>
            ∏ l : Fin n,
              gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) := by
        -- rewrite as a finset product and use `Finset.measurable_prod`
        classical
        simpa using
          (Finset.measurable_prod (s := (Finset.univ : Finset (Fin n)))
            (f := fun l w =>
              gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))
            (hf := by
              intro l _hl
              simpa using h_gibbs_pmf_meas (σs l)))
      simpa [mul_assoc] using (measurable_const.mul hprod)
    -- sum over `σs`
    simpa [gibbs_average_n] using
      (Finset.measurable_sum (s := (Finset.univ : Finset (ReplicaSpace N n)))
        (f := fun σs w =>
          f σs * ∏ l : Fin n,
            gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))
        (hf := by intro σs _hσs; simpa using hterm σs))
  have hAESM :
      AEStronglyMeasurable
        (fun w =>
          gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w) ℙ :=
    hMeas.aestronglyMeasurable
  -- Finish by boundedness on a finite measure space.
  have hBoundAE :
      ∀ᵐ w ∂ℙ, ‖gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w‖
        ≤ ∑ σs : ReplicaSpace N n, ‖f σs‖ :=
    Filter.Eventually.of_forall hbound
  exact Integrable.of_bound (μ := (ℙ : Measure Ω)) hAESM _ hBoundAE

/--
The Covariance function U(σ^l, σ^l') appearing in the derivative.
U_{l,l'} = E[u(σ^l)u(σ^l')] - E[v(σ^l)v(σ^l')].
For SK: U_{l,l'} = (β²/2)(R_{l,l'}^2 - q).
-/
def U_interaction (U : InteractionKernel (N := N)) (l l' : Fin n) (σs : ReplicaSpace N n) : ℝ :=
  U (σs l) (σs l')

noncomputable def U_kernel_SK : InteractionKernel (N := N) :=
  fun σ τ =>
    let R := overlap N σ τ
    (β^2 / 2) * (R^2 - q)

noncomputable def U_interaction_SK (l l' : Fin n) (σs : ReplicaSpace N n) : ℝ :=
  U_interaction (N := N) (n := n) (U := U_kernel_SK (N := N) (β := β) (q := q)) l l' σs

/-!
### The Derivative of the Gibbs Average with respect to the Hamiltonian

This is an essential building block for deriving the replica‑derivative formula (Talagrand Lemma
1.4.2). Given a function `f : ReplicaFun N n` and a test direction `v : EnergySpace N`, the
directional derivative of the Gibbs average with respect to the Hamiltonian `H` in direction `v` is:

  `∑_{σs} f(σs) * ∑_l p_l * (⟨v⟩ - v(σ^l))`

where `p_l` is the product Gibbs weight over replicas **except** replica `l`.
-/

/--
The derivative of the Gibbs weight `∏ l, gibbs_pmf N H (σs l)` with respect to `H` in direction `v`.
Mathematically:
\[
  \frac{d}{dε}\bigg|_{ε=0} ∏_l p_{H + ε v}(σ^l)
    = ∏_l p_H(σ^l) \cdot \sum_l \bigl(\langle v \rangle_H - v(σ^l)\bigr),
\]
where \(\langle v \rangle_H = \sum_\sigma p_H(\sigma) v(\sigma)\).
-/
lemma fderiv_prod_gibbs_pmf_apply (H v : EnergySpace N) (σs : ReplicaSpace N n) :
    fderiv ℝ (fun H' => ∏ l : Fin n, gibbs_pmf N H' (σs l)) H v =
      (∏ l : Fin n, gibbs_pmf N H (σs l)) *
        ∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)) := by
  classical
  -- `gibbs_pmf N (·) σ` is smooth in `H` and its derivative was computed in `fderiv_gibbs_pmf_apply`.
  -- We differentiate the product using `fderiv_finset_prod`.
  have hdiff : ∀ l : Fin n,
      DifferentiableAt ℝ (fun H' => gibbs_pmf N H' (σs l)) H := by
    intro l
    exact SpinGlass.differentiableAt_gibbs_pmf (N := N) (H := H) (σ := σs l)
  have h_fderiv_prod :=
    fderiv_finset_prod
      (𝕜 := ℝ) (E := EnergySpace N) (𝔸' := ℝ) (u := (Finset.univ : Finset (Fin n)))
      (g := fun l H' => gibbs_pmf N H' (σs l))
      (fun l _hl => hdiff l)
  rw [h_fderiv_prod]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  -- Substitute the explicit derivative `fderiv_gibbs_pmf_apply` for each term.
  have hterm : ∀ l : Fin n,
      (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l, gibbs_pmf N H (σs j)) *
        fderiv ℝ (fun H' => gibbs_pmf N H' (σs l)) H v
      = (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l, gibbs_pmf N H (σs j)) *
          (gibbs_pmf N H (σs l) *
            ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))) := by
    intro l
    simp [SpinGlass.fderiv_gibbs_pmf_apply]
  -- Simplify the sum over `l`.
  calc
    ∑ l ∈ (Finset.univ : Finset (Fin n)),
        (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l, gibbs_pmf N H (σs j)) *
          fderiv ℝ (fun H' => gibbs_pmf N H' (σs l)) H v
      = ∑ l ∈ (Finset.univ : Finset (Fin n)),
          (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l, gibbs_pmf N H (σs j)) *
            (gibbs_pmf N H (σs l) *
              ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))) := by
          refine Finset.sum_congr rfl (fun l _hl => ?_)
          simpa using hterm l
    _ = ∑ l ∈ (Finset.univ : Finset (Fin n)),
          (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l, gibbs_pmf N H (σs j)) *
            (gibbs_pmf N H (σs l) *
              ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))) := by
          rfl
    _ = ∑ l ∈ (Finset.univ : Finset (Fin n)),
          (∏ j : Fin n, gibbs_pmf N H (σs j)) *
            ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)) := by
            refine Finset.sum_congr rfl (fun l _hl => ?_)
            -- `(∏_{j ≠ l} p_j) * p_l = ∏_j p_j`
            have herase : (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l, gibbs_pmf N H (σs j)) *
                gibbs_pmf N H (σs l)
                = ∏ j : Fin n, gibbs_pmf N H (σs j) := by
              classical
              simpa using
                (Finset.prod_erase_mul
                  (s := (Finset.univ : Finset (Fin n)))
                  (f := fun j => gibbs_pmf N H (σs j))
                  (a := l) (Finset.mem_univ l))
            -- pull `((∑ τ, ...) - v (σs l))` out to the far right, then rewrite the left factor via `herase`
            have := congrArg (fun a => a * (((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)))) herase
            -- the remaining goal is purely associativity/commutativity
            -- (we keep it explicit to avoid fragile `simp` behaviour)
            simpa [mul_assoc, mul_left_comm, mul_comm] using this
    _ = (∏ j : Fin n, gibbs_pmf N H (σs j)) *
          ∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)) := by
            -- factor the constant `∏_j p_j` out of the sum
            -- (`∑ l : Fin n, …` is definitional equal to `∑ l ∈ Finset.univ, …`.)
            simpa using
              (Finset.mul_sum (s := (Finset.univ : Finset (Fin n)))
                (f := fun l => (∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))
                (a := (∏ j : Fin n, gibbs_pmf N H (σs j)))).symm

/-- Differentiability of the product Gibbs weight as a function of the Hamiltonian. -/
lemma differentiableAt_prod_gibbs_pmf (H : EnergySpace N) (σs : ReplicaSpace N n) :
    DifferentiableAt ℝ (fun H' => ∏ l : Fin n, gibbs_pmf N H' (σs l)) H := by
  classical
  -- Use `HasFDerivAt.finset_prod` and the differentiability of `gibbs_pmf`.
  have hg :
      ∀ l ∈ (Finset.univ : Finset (Fin n)),
        HasFDerivAt (fun H' => gibbs_pmf N H' (σs l))
          (fderiv ℝ (fun H' => gibbs_pmf N H' (σs l)) H) H := by
    intro l _hl
    exact (SpinGlass.differentiableAt_gibbs_pmf (N := N) (H := H) (σ := σs l)).hasFDerivAt
  have hHas :=
    (HasFDerivAt.finset_prod (u := (Finset.univ : Finset (Fin n)))
      (g := fun l H' => gibbs_pmf N H' (σs l))
      (g' := fun l => fderiv ℝ (fun H' => gibbs_pmf N H' (σs l)) H)
      (x := H) hg).differentiableAt
  -- The `Fintype` product is definitional equal to the `Finset.univ` product.
  simpa using hHas

/-- Directional derivative of `gibbs_average_n_det` with respect to the Hamiltonian. -/
lemma fderiv_gibbs_average_n_det_apply (H v : EnergySpace N) (f : ReplicaFun N n) :
    fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f) H v =
      ∑ σs : ReplicaSpace N n,
        f σs * (∏ l : Fin n, gibbs_pmf N H (σs l)) *
          ∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)) := by
  classical
  let u : Finset (ReplicaSpace N n) := Finset.univ
  let A : ReplicaSpace N n → EnergySpace N → ℝ :=
    fun σs H' => f σs * ∏ l : Fin n, gibbs_pmf N H' (σs l)

  have hA_diff : ∀ σs ∈ u, DifferentiableAt ℝ (A σs) H := by
    intro σs _hσs
    have hprod :
        DifferentiableAt ℝ (fun H' => ∏ l : Fin n, gibbs_pmf N H' (σs l)) H :=
      differentiableAt_prod_gibbs_pmf (N := N) (n := n) (H := H) σs
    simpa [A] using (DifferentiableAt.const_mul hprod (f σs))

  have hfderiv_sum :
      fderiv ℝ (fun H' : EnergySpace N => ∑ σs ∈ u, A σs H') H
        = ∑ σs ∈ u, fderiv ℝ (A σs) H := by
    simpa [u] using (fderiv_fun_sum (u := u) (A := A) (x := H) hA_diff)

  -- Rewrite `gibbs_average_n_det` in terms of the finset sum `∑ σs ∈ u, A σs`.
  -- (This is definitional because `u = Finset.univ`.)
  have hrewrite :
      (fun H' : EnergySpace N => gibbs_average_n_det (N := N) (n := n) H' f)
        = fun H' : EnergySpace N => ∑ σs ∈ u, A σs H' := by
    funext H'
    simp [gibbs_average_n_det, u, A]

  -- Apply the `fderiv_fun_sum` formula and compute termwise using `fderiv_const_mul`
  -- and `fderiv_prod_gibbs_pmf_apply`.
  -- We keep the algebra explicit to avoid `simp` producing the alternative form
  -- `n * E[v] - ∑ v(σ^l)`.
  rw [hrewrite]
  -- replace the `Fintype` sum with the `Finset.univ` sum
  have : fderiv ℝ (fun H' : EnergySpace N => ∑ σs ∈ u, A σs H') H v =
      (∑ σs ∈ u, fderiv ℝ (A σs) H) v := by
    -- rewrite via `hfderiv_sum`
    simp [hfderiv_sum]
  -- now expand the RHS at direction `v`
  -- and simplify each term
  simp [this, u, A, fderiv_const_mul, differentiableAt_prod_gibbs_pmf,
    fderiv_prod_gibbs_pmf_apply, mul_assoc, mul_left_comm, mul_comm, mul_add, sub_eq_add_neg,
    Finset.mul_sum]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/--
Differentiability of the `gibbs_average_n` in the Hamiltonian `H`.
-/
lemma differentiableAt_gibbs_average_n (t : ℝ) (f : ReplicaFun N n) (w : Ω) :
    DifferentiableAt ℝ
      (fun H' => ∑ σs : ReplicaSpace N n, f σs * ∏ l, gibbs_pmf N H' (σs l))
      (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) := by
  classical
  let H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w
  -- Each term in the finite sum is differentiable (product of differentiable factors).
  have hterm : ∀ σs : ReplicaSpace N n,
      DifferentiableAt ℝ (fun H' => f σs * ∏ l, gibbs_pmf N H' (σs l)) H := by
    intro σs
    -- First, differentiate the product Gibbs weight in `H'`.
    have hprod :
        DifferentiableAt ℝ (fun H' => ∏ l : Fin n, gibbs_pmf N H' (σs l)) H := by
      -- Prove `HasFDerivAt` for the finset product and take `differentiableAt`.
      have hg :
          ∀ l ∈ (Finset.univ : Finset (Fin n)),
            HasFDerivAt (fun H' => gibbs_pmf N H' (σs l))
              (fderiv ℝ (fun H' => gibbs_pmf N H' (σs l)) H) H := by
        intro l _hl
        exact
          (SpinGlass.differentiableAt_gibbs_pmf (N := N) (H := H) (σ := σs l)).hasFDerivAt
      have hHas :=
        (HasFDerivAt.finset_prod (u := (Finset.univ : Finset (Fin n)))
          (g := fun l H' => gibbs_pmf N H' (σs l))
          (g' := fun l => fderiv ℝ (fun H' => gibbs_pmf N H' (σs l)) H)
          (x := H) hg).differentiableAt
      -- The `Fintype` product is definitional equal to the `Finset.univ` product.
      simpa using hHas
    -- Multiply by the constant factor `f σs`.
    exact DifferentiableAt.const_mul hprod (f σs)

  -- Now differentiate the finite sum over replica configurations.
  -- The `Fintype` sum is definitional equal to the `Finset.univ` sum.
  have hsum :
      DifferentiableAt ℝ
        (fun H' => ∑ σs ∈ (Finset.univ : Finset (ReplicaSpace N n)),
          f σs * ∏ l, gibbs_pmf N H' (σs l)) H := by
    refine
      (DifferentiableAt.fun_sum (𝕜 := ℝ) (E := EnergySpace N) (F := ℝ)
        (u := (Finset.univ : Finset (ReplicaSpace N n)))
        (A := fun σs : ReplicaSpace N n => fun H' : EnergySpace N =>
          f σs * ∏ l, gibbs_pmf N H' (σs l))
        (x := H) ?_)
    intro σs _hσs
    simpa using hterm σs

  simpa using hsum

end ReplicaCalculus

end SpinGlass
