import Riemann.PhysLean.SpinGlass.Defs
import Riemann.PhysLean.SpinGlass.Calculus
import Riemann.Mathlib.Probability.Distributions.Gaussian_IBP_Hilbert
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Riemann.PhysLean.SpinGlass.Replicas
import Notes.Papers.CW.GIBP

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
open PhysLean.Probability.GaussianIBP
open SpinGlass

namespace ArithmeticSpinGlass

/-!
# Rigorous Asymmetric Guerra Interpolation

We prove the derivative formula for the free energy of an arithmetic spin glass.
Interpolation: H_t = H_arith + √t G.
We use the fact that EnergySpace M is a finite-dimensional ℝ-Hilbert space.
-/

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {M : ℕ} {β : ℝ}

/-- The vector of Gibbs weights w_σ(H) as a Fréchet-differentiable map. -/
noncomputable def gibbs_weight_map (M : ℕ) : EnergySpace M → EnergySpace M :=
  fun H => WithLp.toLp 2 (fun σ : Config M => SpinGlass.gibbs_pmf M H σ)

/--
Pointwise derivative of the Gibbs weight vector.
For a Hamiltonian H and direction V:
D_H [exp(βH(σ))/Z] (V) = β w_σ (V(σ) - ⟨V⟩_H).
-/
theorem fderiv_gibbs_pmf (H : EnergySpace M) (σ : Config M) :
    fderiv ℝ (fun H' : EnergySpace M => SpinGlass.gibbs_pmf M H' σ) H =
      (SpinGlass.gibbs_pmf M H σ) •
        ((∑ τ : Config M, (SpinGlass.gibbs_pmf M H τ) • SpinGlass.evalCLM (N := M) τ) -
          SpinGlass.evalCLM (N := M) σ) := by
  classical
  ext h
  -- Evaluate the Fréchet derivative on an arbitrary direction `h`.
  -- Then use the explicit directional derivative formula from `SpinGlass/Defs.lean`.
  have hderiv :
      (fderiv ℝ (fun H' : EnergySpace M => SpinGlass.gibbs_pmf M H' σ) H) h =
        (SpinGlass.gibbs_pmf M H σ) *
          ((∑ τ : Config M, (SpinGlass.gibbs_pmf M H τ) * h τ) - h σ) := by
    simpa using (SpinGlass.fderiv_gibbs_pmf_apply (N := M) (H := H) (h := h) σ)
  -- Now simplify the RHS linear-map expression when applied to `h`.
  -- `evalCLM τ h = h τ` by definition, and sums/subtractions act pointwise.
  simp [hderiv, SpinGlass.evalCLM, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sum_apply, smul_eq_mul, mul_comm]

set_option maxHeartbeats 0
/--
The expected free energy functional: φ(t) = 𝔼 [ (1/M) log Z(H_arith + √t G) ].
-/
noncomputable def phi (H_arith : EnergySpace M) (G : Ω → EnergySpace M) (t : ℝ) : ℝ :=
  ∫ ω, SpinGlass.free_energy_density (N := M) ((-β) • (H_arith + (Real.sqrt t) • G ω)) ∂ℙ

/--
**Theorem 1.1 (Cipollina-Washburne): Exact Asymmetric Derivative.**

The derivative of the interpolated free energy for an arithmetic Hamiltonian
with matching Gaussian background.
-/
theorem asymmetric_guerra_derivative
    (H_arith : EnergySpace M)
    (G : Ω → EnergySpace M)
    (hG : IsGaussianHilbert G)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (phi (M := M) (β := β) H_arith G)
      ((β^2 / (2 * (M : ℝ))) * ∫ ω,
        let H := (-β) • (H_arith + (Real.sqrt t) • G ω)
        let μ : Config M → ℝ := fun σ => SpinGlass.gibbs_pmf M H σ
        let Cov : Config M → Config M → ℝ :=
          fun σ τ => inner ℝ (covOp hG (SpinGlass.std_basis M σ)) (SpinGlass.std_basis M τ)
        (∑ σ, μ σ * Cov σ σ) - (∑ σ, ∑ τ, μ σ * μ τ * Cov σ τ)
      ∂ℙ) t := by
  classical
  -- Abbreviations for the interpolation Hamiltonian and the Gibbs weights.
  let Ht : ℝ → Ω → EnergySpace M :=
    fun s ω => (-β) • (H_arith + (Real.sqrt s) • G ω)
  let μt : Ω → (Config M → ℝ) :=
    fun ω σ => SpinGlass.gibbs_pmf M (Ht t ω) σ

  -- Step 1: differentiate under the integral sign.
  -- Define the integrand family `F s ω = free_energy_density (Ht s ω)`.
  let F : ℝ → Ω → ℝ := fun s ω => SpinGlass.free_energy_density (N := M) (Ht s ω)
  let F' : ℝ → Ω → ℝ :=
    fun s ω =>
      (fderiv ℝ (fun H : EnergySpace M => SpinGlass.free_energy_density (N := M) H) (Ht s ω))
        ((-β) • ((1 / (2 * Real.sqrt s)) • G ω))

  -- Localize to a ball inside `(0,∞)` so that `1/√s` is controlled.
  let ε : ℝ := t / 2
  have hε_pos : 0 < ε := by dsimp [ε]; linarith
  have hball_pos : ∀ x ∈ Metric.ball t ε, 0 < x := by
    intro x hx
    have hx' : |x - t| < ε := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm, ε] using hx
    have hx2 : t - x < ε := (abs_sub_lt_iff.1 hx').2
    -- `x > t - ε = t/2`.
    have : t / 2 < x := by
      have : t - x < t / 2 := by simpa [ε] using hx2
      linarith
    linarith

  -- Measurability of `F s` near `t` (in fact, for all `s`).
  have hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) (ℙ : Measure Ω) := by
    have hG_meas : Measurable G := hG.repr_measurable
    have hcont_fe : Continuous (fun H : EnergySpace M => SpinGlass.free_energy_density (N := M) H) :=
      (SpinGlass.contDiff_free_energy_density (N := M)).continuous
    refine Filter.Eventually.of_forall (fun s => ?_)
    have hHt_meas : Measurable (fun ω => Ht s ω) := by
      -- `Ht s` is a continuous affine combination of the measurable map `G`.
      have h :
          Measurable (fun ω => (-β) • H_arith + ((-β) * Real.sqrt s) • G ω) :=
        measurable_const.add (hG_meas.const_smul ((-β) * Real.sqrt s))
      -- Rewrite back to the original `Ht` definition.
      simpa [Ht, smul_add, smul_smul, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm,
        add_comm] using h
    exact (hcont_fe.measurable.comp hHt_meas).aestronglyMeasurable

  -- Integrability of `F t` (via moderate growth + Gaussian integrability).
  have hF_int : Integrable (F t) (ℙ : Measure Ω) := by
    -- Use the linear-growth bound for `free_energy_density` and integrability of `‖G‖`.
    have hMG := SpinGlass.hasModerateGrowth_free_energy_density (N := M)
    -- `‖Ht t‖` is integrable since `Ht t` is affine in `G`.
    have hG_norm_int : Integrable (fun ω => ‖G ω‖) (ℙ : Measure Ω) := by
      simpa using (integrable_norm_of_gaussian (g := G) (hg := hG))
    have hHt_norm_int : Integrable (fun ω => ‖Ht t ω‖) (ℙ : Measure Ω) := by
      -- `‖(-β) • (H_arith + √t • G ω)‖ ≤ |β| * (‖H_arith‖ + √t * ‖G ω‖)`.
      have h_le : ∀ ω, ‖Ht t ω‖ ≤ |β| * (‖H_arith‖ + Real.sqrt t * ‖G ω‖) := by
        intro ω
        -- Start from `‖Ht t‖ = |β| * ‖H_arith + √t • G‖` and use triangle inequality.
        have hβ : ‖Ht t ω‖ = |β| * ‖H_arith + (Real.sqrt t) • G ω‖ := by
          -- Keep the scalar multiplication intact (avoid rewriting `(-β) • (a + b)` first).
          dsimp [Ht]
          simpa [abs_neg] using
            (norm_smul (-β) (H_arith + (Real.sqrt t) • G ω))
        calc
          ‖Ht t ω‖ = |β| * ‖H_arith + (Real.sqrt t) • G ω‖ := hβ
          _ ≤ |β| * (‖H_arith‖ + ‖(Real.sqrt t) • G ω‖) := by
                gcongr
                exact norm_add_le _ _
          _ = |β| * (‖H_arith‖ + Real.sqrt t * ‖G ω‖) := by
                simp [norm_smul]
      -- Integrability of the RHS.
      have hR : Integrable (fun ω => |β| * (‖H_arith‖ + Real.sqrt t * ‖G ω‖)) (ℙ : Measure Ω) := by
        have hconst : Integrable (fun _ : Ω => |β| * ‖H_arith‖) (ℙ : Measure Ω) := by
          simpa using (integrable_const (|β| * ‖H_arith‖))
        have hlin : Integrable (fun ω => |β| * (Real.sqrt t * ‖G ω‖)) (ℙ : Measure Ω) := by
          simpa [mul_assoc] using hG_norm_int.const_mul (|β| * Real.sqrt t)
        -- combine
        simpa [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using hconst.add hlin
      -- conclude by domination
      refine Integrable.mono' hR ?_ ?_
      · -- measurability of `‖Ht t‖` comes from measurability of `Ht t`
        have hHt_meas : Measurable (fun ω => Ht t ω) := by
          have hG_meas : Measurable G := hG.repr_measurable
          have h :
              Measurable (fun ω => (-β) • H_arith + ((-β) * Real.sqrt t) • G ω) :=
            measurable_const.add (hG_meas.const_smul ((-β) * Real.sqrt t))
          simpa [Ht, smul_add, smul_smul, mul_assoc, mul_left_comm, mul_comm, add_assoc,
            add_left_comm, add_comm] using h
        exact (hHt_meas.norm).aestronglyMeasurable
      · -- domination
        refine Filter.Eventually.of_forall (fun ω => ?_)
        simpa [Real.norm_eq_abs] using (h_le ω)
    -- Now combine with the linear-growth bound on `free_energy_density`.
    -- `|F t ω| ≤ C * (1 + ‖Ht t ω‖) ^ m`, and polynomial profiles of `‖G‖` are integrable.
    have h_int_dom : Integrable (fun ω => hMG.C * (1 + ‖Ht t ω‖) ^ hMG.m) (ℙ : Measure Ω) := by
      -- Bound `1 + ‖Ht t ω‖` by an affine expression in `‖G ω‖`.
      let z0 : EnergySpace M := (-β) • H_arith
      let L : EnergySpace M →L[ℝ] EnergySpace M :=
        (Real.sqrt t * (-β)) • (1 : EnergySpace M →L[ℝ] EnergySpace M)
      have hHt_aff : ∀ ω, Ht t ω = z0 + L (G ω) := by
        intro ω
        simp [Ht, z0, L, smul_add, smul_smul, mul_comm]
      have h_one_add : ∀ ω, 1 + ‖Ht t ω‖ ≤ (1 + ‖z0‖ + ‖L‖) * (1 + ‖G ω‖) := by
        intro ω
        -- Apply the general affine bound `one_add_norm_comp_affine_le'`.
        simpa [hHt_aff ω] using
          (PhysLean.Probability.GaussianIBP.CoordLine.AffineModerateGrowth.one_add_norm_comp_affine_le'
            (z := z0) (L := L) (x := G ω))
      have h_pow : ∀ ω,
          (1 + ‖Ht t ω‖) ^ hMG.m ≤ ((1 + ‖z0‖ + ‖L‖) * (1 + ‖G ω‖)) ^ hMG.m := by
        intro ω
        have hbase : 0 ≤ 1 + ‖Ht t ω‖ := by nlinarith [norm_nonneg (Ht t ω)]
        exact Real.pow_le_pow_of_le_left hbase (h_one_add ω) _
      -- The RHS is integrable since `(1 + ‖G‖)^m` is integrable for Gaussian `G`.
      have h_int_G : Integrable (fun ω => (1 + ‖G ω‖) ^ hMG.m) (ℙ : Measure Ω) := by
        simpa using (PhysLean.Probability.GaussianIBP.integrable_one_add_norm_pow (hg := hG) (m := hMG.m))
      have h_int_rhs :
          Integrable (fun ω => hMG.C * (((1 + ‖z0‖ + ‖L‖) * (1 + ‖G ω‖)) ^ hMG.m)) (ℙ : Measure Ω) := by
        -- Use `(a*b)^m = a^m * b^m`.
        have h' :
            Integrable (fun ω =>
              hMG.C * (((1 + ‖z0‖ + ‖L‖) ^ hMG.m) * (1 + ‖G ω‖) ^ hMG.m)) (ℙ : Measure Ω) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (h_int_G.const_mul ((1 + ‖z0‖ + ‖L‖) ^ hMG.m)).const_mul hMG.C
        simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm] using h'
      -- Dominate by the RHS using `h_pow`.
      refine Integrable.mono' h_int_rhs ?_ ?_
      · -- measurability of the dominated function
        have hG_meas : Measurable G := hG.repr_measurable
        have hHt_meas : Measurable (fun ω => Ht t ω) := by
          have h :
              Measurable (fun ω => (-β) • H_arith + ((-β) * Real.sqrt t) • G ω) :=
            measurable_const.add (hG_meas.const_smul ((-β) * Real.sqrt t))
          simpa [Ht, smul_add, smul_smul, mul_assoc, mul_left_comm, mul_comm, add_assoc,
            add_left_comm, add_comm] using h
        exact (((hHt_meas.norm.const_add 1).pow_const hMG.m).const_mul hMG.C).aestronglyMeasurable
      · refine Filter.Eventually.of_forall (fun ω => ?_)
        have hC : 0 ≤ hMG.C := le_of_lt hMG.Cpos
        have hbase_nonneg : 0 ≤ 1 + ‖Ht t ω‖ := by nlinarith [norm_nonneg (Ht t ω)]
        have hbase_abs : |1 + ‖Ht t ω‖| = 1 + ‖Ht t ω‖ := abs_of_nonneg hbase_nonneg
        have hCabs : |hMG.C| = hMG.C := abs_of_nonneg hC
        -- Reduce the goal to a plain inequality and apply `h_pow`, then multiply by `hMG.C ≥ 0`.
        have hmul : hMG.C * (1 + ‖Ht t ω‖) ^ hMG.m
            ≤ hMG.C * ((1 + ‖z0‖ + ‖L‖) * (1 + ‖G ω‖)) ^ hMG.m :=
          mul_le_mul_of_nonneg_left (h_pow ω) hC
        simpa [Real.norm_eq_abs, abs_mul, abs_pow, hCabs, hbase_abs,
          mul_assoc, mul_left_comm, mul_comm] using hmul
    have hFt_meas : AEStronglyMeasurable (F t) (ℙ : Measure Ω) := by
      -- same measurability argument as in `hF_meas`, specialized to `t`
      have hG_meas : Measurable G := hG.repr_measurable
      have hcont_fe :
          Continuous (fun H : EnergySpace M => SpinGlass.free_energy_density (N := M) H) :=
        (SpinGlass.contDiff_free_energy_density (N := M)).continuous
      have hHt_meas : Measurable (fun ω => Ht t ω) := by
        have h :
            Measurable (fun ω => (-β) • H_arith + ((-β) * Real.sqrt t) • G ω) :=
          measurable_const.add (hG_meas.const_smul ((-β) * Real.sqrt t))
        simpa [Ht, smul_add, smul_smul, mul_assoc, mul_left_comm, mul_comm, add_assoc,
          add_left_comm, add_comm] using h
      exact (hcont_fe.measurable.comp hHt_meas).aestronglyMeasurable
    -- Apply domination to get integrability.
    refine Integrable.mono h_int_dom hFt_meas ?_
    refine ae_of_all _ (fun ω => ?_)
    have hbound := hMG.F_bound (Ht t ω)
    -- convert `|·|` bound to `‖·‖` bound in ℝ
    have hCabs : |hMG.C| = hMG.C := abs_of_nonneg (le_of_lt hMG.Cpos)
    have hbase : 0 ≤ 1 + ‖Ht t ω‖ := by nlinarith [norm_nonneg (Ht t ω)]
    have h1abs : |1 + ‖Ht t ω‖| = 1 + ‖Ht t ω‖ := abs_of_nonneg hbase
    simpa [F, Real.norm_eq_abs, hCabs, h1abs] using hbound

  -- A uniform domination bound for `F'` on the ball (using the uniform operator-norm bound on `fderiv`).
  -- On the ball, `x ≥ t/2`, so `1/(2√x) ≤ 1/(2√(t/2))`.
  let cInvSqrt : ℝ := 1 / (2 * Real.sqrt (t / 2))
  have hcInvSqrt_nonneg : 0 ≤ cInvSqrt := by
    have : 0 ≤ 2 * Real.sqrt (t / 2) := by positivity
    exact one_div_nonneg.2 this
  let bound : Ω → ℝ := fun ω => (|β| / (M : ℝ)) * (cInvSqrt * ‖G ω‖)
  have hbound_int : Integrable bound (ℙ : Measure Ω) := by
    have hG_norm_int : Integrable (fun ω => ‖G ω‖) (ℙ : Measure Ω) := by
      simpa using (integrable_norm_of_gaussian (g := G) (hg := hG))
    -- constants factor out
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using
      (hG_norm_int.const_mul ((|β| / (M : ℝ)) * cInvSqrt))

  have hF'_meas : AEStronglyMeasurable (F' t) (ℙ : Measure Ω) := by
    -- We avoid measurability of `ContinuousLinearMap` evaluation by rewriting `F'` explicitly
    -- using `fderiv_free_energy_density_apply` (a finite sum of measurable coordinates).
    have hmeas : Measurable (F' t) := by
      -- Expand the derivative and reduce to measurability of a finite sum.
      classical
      -- First, show measurability of `Ht t`.
      have hG_meas : Measurable G := hG.repr_measurable
      have hHt_meas : Measurable (fun ω => Ht t ω) := by
        have h :
            Measurable (fun ω => (-β) • H_arith + ((-β) * Real.sqrt t) • G ω) :=
          measurable_const.add (hG_meas.const_smul ((-β) * Real.sqrt t))
        simpa [Ht, smul_add, smul_smul, mul_assoc, mul_left_comm, mul_comm, add_assoc,
          add_left_comm, add_comm] using h
      -- Each Gibbs weight `ω ↦ gibbs_pmf … σ` is measurable by continuity in `H`.
      have hpmf_meas :
          ∀ σ : Config M, Measurable fun ω => SpinGlass.gibbs_pmf M (Ht t ω) σ := by
        intro σ
        have hcont : Continuous fun H : EnergySpace M => SpinGlass.gibbs_pmf M H σ :=
          (SpinGlass.contDiff_gibbs_pmf (N := M) (σ := σ)).continuous
        exact hcont.measurable.comp hHt_meas
      -- Coordinates of the direction vector are measurable.
      have hdir_meas : Measurable fun ω =>
          (-β) • ((1 / (2 * Real.sqrt t)) • G ω) := by
        exact (hG_meas.const_smul (1 / (2 * Real.sqrt t))).const_smul (-β)
      -- Now rewrite `F' t ω` using the explicit `fderiv` formula.
      have hrewrite : ∀ ω, F' t ω =
          (-(1 / (M : ℝ))) *
            ∑ σ : Config M,
              (SpinGlass.gibbs_pmf M (Ht t ω) σ) * ((-β) • ((1 / (2 * Real.sqrt t)) • G ω)) σ := by
        intro ω
        -- unfold `F'` and use `fderiv_free_energy_density_apply`
        simp [F', SpinGlass.fderiv_free_energy_density_apply]
      -- The RHS is measurable (finite sum of products of measurable functions).
      have hmeas_rhs :
          Measurable fun ω =>
            (-(1 / (M : ℝ))) *
              ∑ σ : Config M,
                (SpinGlass.gibbs_pmf M (Ht t ω) σ) * ((-β) • ((1 / (2 * Real.sqrt t)) • G ω)) σ := by
        -- `measurable` handles constants, multiplication, and finite sums once the pieces are measurable.
        -- We provide measurability of the summand explicitly.
        have hcoord_meas :
            ∀ σ : Config M, Measurable fun ω =>
              ((-β) • ((1 / (2 * Real.sqrt t)) • G ω)) σ := by
          intro σ
          -- coordinate projection is a continuous linear map, hence measurable
          have :
              Measurable fun ω =>
                (SpinGlass.evalCLM (N := M) σ) ((-β) • ((1 / (2 * Real.sqrt t)) • G ω)) :=
            (SpinGlass.evalCLM (N := M) σ).measurable.comp hdir_meas
          simpa [SpinGlass.evalCLM] using this
        refine measurable_const.mul ?_
        refine (Finset.measurable_sum (s := (Finset.univ : Finset (Config M))) ?_)
        intro σ _hσ
        exact (hpmf_meas σ).mul (hcoord_meas σ)
      -- Conclude by rewriting `F' t` to the measurable RHS.
      have hfun : (F' t) = fun ω =>
          (-(1 / (M : ℝ))) *
            ∑ σ : Config M,
              (SpinGlass.gibbs_pmf M (Ht t ω) σ) * ((-β) • ((1 / (2 * Real.sqrt t)) • G ω)) σ := by
        funext ω
        exact hrewrite ω
      simpa [hfun] using hmeas_rhs
    exact hmeas.aestronglyMeasurable

  have h_bound :
      ∀ᵐ ω ∂(ℙ : Measure Ω), ∀ x ∈ Metric.ball t ε, ‖F' x ω‖ ≤ bound ω := by
    refine ae_of_all _ (fun ω x hx => ?_)
    -- On the ball we have `t/2 ≤ x`, hence `1/(2√x) ≤ 1/(2√(t/2))`.
    have hxpos : 0 < x := hball_pos x hx
    have hx_ge : t / 2 ≤ x := by
      have hx' : |x - t| < ε := by
        simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm, ε] using hx
      have hx2 : t - x < ε := (abs_sub_lt_iff.1 hx').2
      have hx2' : t - x < t / 2 := by
        simpa [ε] using hx2
      have : t / 2 < x := by
        linarith [hx2']
      exact le_of_lt this
    have hsqrt_le : Real.sqrt (t / 2) ≤ Real.sqrt x := Real.sqrt_le_sqrt hx_ge
    have hpos : 0 < 2 * Real.sqrt (t / 2) := by
      have : 0 < Real.sqrt (t / 2) := Real.sqrt_pos.2 (by nlinarith [ht] : 0 < t / 2)
      nlinarith
    have hle : 2 * Real.sqrt (t / 2) ≤ 2 * Real.sqrt x := by nlinarith [hsqrt_le]
    have hinv : 1 / (2 * Real.sqrt x) ≤ 1 / (2 * Real.sqrt (t / 2)) := by
      simpa [one_div] using (one_div_le_one_div_of_le hpos hle)
    -- Bound `‖F' x ω‖` using the explicit `fderiv_free_energy_density_apply` formula.
    -- First rewrite the derivative.
    have hderiv :=
      SpinGlass.fderiv_free_energy_density_apply (N := M) (H := Ht x ω)
        (h := (-β) • ((1 / (2 * Real.sqrt x)) • G ω))
    -- Use `|∑ μσ hσ| ≤ ‖h‖` and `∑ μσ = 1`.
    have hs1 : (∑ σ : Config M, SpinGlass.gibbs_pmf M (Ht x ω) σ) = 1 :=
      SpinGlass.sum_gibbs_pmf (N := M) (H := Ht x ω)
    have hsum_bound :
        |∑ σ : Config M,
            SpinGlass.gibbs_pmf M (Ht x ω) σ * (( (-β) • ((1 / (2 * Real.sqrt x)) • G ω)) σ)|
          ≤ ‖(-β) • ((1 / (2 * Real.sqrt x)) • G ω)‖ := by
      -- `|∑ gσ hσ| ≤ ∑ gσ |hσ| ≤ ‖h‖ * ∑ gσ = ‖h‖`.
      have h_abs_le :
          |∑ σ : Config M,
              SpinGlass.gibbs_pmf M (Ht x ω) σ * (( (-β) • ((1 / (2 * Real.sqrt x)) • G ω)) σ)|
            ≤ ∑ σ : Config M,
                |SpinGlass.gibbs_pmf M (Ht x ω) σ * (( (-β) • ((1 / (2 * Real.sqrt x)) • G ω)) σ)| := by
        simpa using
          (Finset.abs_sum_le_sum_abs
            (f := fun σ : Config M =>
              SpinGlass.gibbs_pmf M (Ht x ω) σ * (( (-β) • ((1 / (2 * Real.sqrt x)) • G ω)) σ))
            (s := (Finset.univ : Finset (Config M))))
      have h_abs_term :
          (∑ σ : Config M,
              |SpinGlass.gibbs_pmf M (Ht x ω) σ *
                  (( (-β) • ((1 / (2 * Real.sqrt x)) • G ω)) σ)|)
            = ∑ σ : Config M,
                (SpinGlass.gibbs_pmf M (Ht x ω) σ) *
                  |(( (-β) • ((1 / (2 * Real.sqrt x)) • G ω)) σ)| := by
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        have hg : 0 ≤ SpinGlass.gibbs_pmf M (Ht x ω) σ :=
          SpinGlass.gibbs_pmf_nonneg (N := M) (H := Ht x ω) σ
        simp [abs_mul, abs_of_nonneg hg, mul_assoc, mul_left_comm, mul_comm]
      have hterm : ∀ σ : Config M,
          (SpinGlass.gibbs_pmf M (Ht x ω) σ) * |(( (-β) • ((1 / (2 * Real.sqrt x)) • G ω)) σ)|
            ≤ (SpinGlass.gibbs_pmf M (Ht x ω) σ) * ‖(-β) • ((1 / (2 * Real.sqrt x)) • G ω)‖ := by
        intro σ
        have hσ : |(( (-β) • ((1 / (2 * Real.sqrt x)) • G ω)) σ)| ≤ ‖(-β) • ((1 / (2 * Real.sqrt x)) • G ω)‖ :=
          SpinGlass.abs_apply_le_norm (N := M) ((-β) • ((1 / (2 * Real.sqrt x)) • G ω)) σ
        exact mul_le_mul_of_nonneg_left hσ
          (SpinGlass.gibbs_pmf_nonneg (N := M) (H := Ht x ω) σ)
      have hsum' :=
        Finset.sum_le_sum (s := (Finset.univ : Finset (Config M))) (fun σ _ => hterm σ)
      have hfactor :
          (∑ σ : Config M,
              (SpinGlass.gibbs_pmf M (Ht x ω) σ) * ‖(-β) • ((1 / (2 * Real.sqrt x)) • G ω)‖)
            = (∑ σ : Config M, SpinGlass.gibbs_pmf M (Ht x ω) σ) *
                ‖(-β) • ((1 / (2 * Real.sqrt x)) • G ω)‖ := by
        simpa using
          (Finset.sum_mul (s := (Finset.univ : Finset (Config M)))
            (f := fun σ : Config M => SpinGlass.gibbs_pmf M (Ht x ω) σ)
            (a := ‖(-β) • ((1 / (2 * Real.sqrt x)) • G ω)‖)).symm
      calc
        |∑ σ : Config M,
            SpinGlass.gibbs_pmf M (Ht x ω) σ *
              (( (-β) • ((1 / (2 * Real.sqrt x)) • G ω)) σ)|
            ≤ ∑ σ : Config M,
                |SpinGlass.gibbs_pmf M (Ht x ω) σ *
                    (( (-β) • ((1 / (2 * Real.sqrt x)) • G ω)) σ)| := h_abs_le
        _ = ∑ σ : Config M,
              (SpinGlass.gibbs_pmf M (Ht x ω) σ) *
                |(( (-β) • ((1 / (2 * Real.sqrt x)) • G ω)) σ)| := h_abs_term
        _ ≤ (∑ σ : Config M, SpinGlass.gibbs_pmf M (Ht x ω) σ) *
              ‖(-β) • ((1 / (2 * Real.sqrt x)) • G ω)‖ := by
              -- Avoid `simp` rewriting the norm; just rewrite the RHS using `hfactor`.
              exact le_trans hsum' (le_of_eq hfactor)
        _ = ‖(-β) • ((1 / (2 * Real.sqrt x)) • G ω)‖ := by simp [hs1]
    have hF'_bound :
        ‖F' x ω‖ ≤ (1 / (M : ℝ)) * ‖(-β) • ((1 / (2 * Real.sqrt x)) • G ω)‖ := by
      -- unfold `F'` and use `hderiv` + `hsum_bound`
      have : |F' x ω| ≤ (1 / (M : ℝ)) * ‖(-β) • ((1 / (2 * Real.sqrt x)) • G ω)‖ := by
        -- `F' x ω = -(1/M) * sum ...`
        -- take abs and use `hsum_bound`
        have : F' x ω = -(1 / (M : ℝ)) * ∑ σ : Config M,
            (SpinGlass.gibbs_pmf M (Ht x ω) σ) *
              (( (-β) • ((1 / (2 * Real.sqrt x)) • G ω)) σ) := by
          -- Use the explicit `fderiv` formula `hderiv` without unfolding `free_energy_density`,
          -- otherwise `simp` may rewrite the linear map application in an inconvenient form.
          simpa [F'] using hderiv
        -- Now bound.
        calc
          |F' x ω| = |(1 / (M : ℝ))| *
              |∑ σ : Config M, SpinGlass.gibbs_pmf M (Ht x ω) σ *
                  (( (-β) • ((1 / (2 * Real.sqrt x)) • G ω)) σ)| := by
                rw [this, abs_mul, abs_neg]
          _ ≤ (1 / (M : ℝ)) *
              ‖(-β) • ((1 / (2 * Real.sqrt x)) • G ω)‖ := by
                have hM : 0 ≤ (1 / (M : ℝ)) := by
                  exact one_div_nonneg.2 (by exact_mod_cast (Nat.cast_nonneg M))
                have habsM : |(1 / (M : ℝ))| = (1 / (M : ℝ)) := abs_of_nonneg hM
                rw [habsM]
                exact
                  (mul_le_mul_of_nonneg_left hsum_bound hM)
      simpa [Real.norm_eq_abs] using this
    -- Finally bound the direction norm by `|β| * cInvSqrt * ‖G ω‖`.
    have hdir_norm :
        ‖(-β) • ((1 / (2 * Real.sqrt x)) • G ω)‖
          ≤ |β| * (cInvSqrt * ‖G ω‖) :=
      (set_option maxHeartbeats 600000 in by
      -- `‖a • b‖ = |a| * ‖b‖` and use `hinv`.
      have h1 : ‖(-β) • ((1 / (2 * Real.sqrt x)) • G ω)‖
          = |β| * |1 / (2 * Real.sqrt x)| * ‖G ω‖ := by
            -- `norm_smul` twice; keep the result in a multiplicative normal form (no `ring` needed).
            simp [norm_smul, mul_assoc]
      have h2 : |1 / (2 * Real.sqrt x)| ≤ cInvSqrt := by
        have hnonneg : 0 ≤ 1 / (2 * Real.sqrt x) := by
          have hden : 0 ≤ 2 * Real.sqrt x := by
            exact mul_nonneg (by norm_num) (Real.sqrt_nonneg x)
          exact one_div_nonneg.2 hden
        have hle : 1 / (2 * Real.sqrt x) ≤ cInvSqrt := by
          simpa [cInvSqrt] using hinv
        -- remove the absolute value using nonnegativity
        calc
          |1 / (2 * Real.sqrt x)| = 1 / (2 * Real.sqrt x) := abs_of_nonneg hnonneg
          _ ≤ cInvSqrt := hle
      calc
        ‖(-β) • ((1 / (2 * Real.sqrt x)) • G ω)‖
            = |β| * |1 / (2 * Real.sqrt x)| * ‖G ω‖ := h1
        _ ≤ |β| * cInvSqrt * ‖G ω‖ := by
          have hβ : 0 ≤ |β| := abs_nonneg β
          have hG' : 0 ≤ ‖G ω‖ := norm_nonneg _
          have h' : |β| * |1 / (2 * Real.sqrt x)| ≤ |β| * cInvSqrt :=
            mul_le_mul_of_nonneg_left h2 hβ
          have h'' : (|β| * |1 / (2 * Real.sqrt x)|) * ‖G ω‖ ≤ (|β| * cInvSqrt) * ‖G ω‖ :=
            mul_le_mul_of_nonneg_right h' hG'
          simpa [mul_assoc] using h''
        _ = |β| * (cInvSqrt * ‖G ω‖) := by simp [mul_assoc]
      )
    -- Combine everything and match `bound`.
    have : ‖F' x ω‖ ≤ bound ω := by
      have hM : 0 ≤ (1 / (M : ℝ)) := by
        exact one_div_nonneg.2 (by exact_mod_cast (Nat.cast_nonneg M))
      have h' : (1 / (M : ℝ)) * ‖(-β) • ((1 / (2 * Real.sqrt x)) • G ω)‖
          ≤ (|β| / (M : ℝ)) * (cInvSqrt * ‖G ω‖) := by
        -- use `hdir_norm` and rearrange
        have : (1 / (M : ℝ)) * ‖(-β) • ((1 / (2 * Real.sqrt x)) • G ω)‖
              ≤ (1 / (M : ℝ)) * (|β| * (cInvSqrt * ‖G ω‖)) := by
          exact mul_le_mul_of_nonneg_left hdir_norm hM
        -- rewrite `(1/M)*|β|` as `|β|/M`
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
      exact le_trans hF'_bound h'
    simpa using this


  -- Pointwise differentiability on the ball.
  have h_diff :
      ∀ᵐ ω ∂(ℙ : Measure Ω), ∀ x ∈ Metric.ball t ε,
        HasDerivAt (fun s => F s ω) (F' x ω) x := by
    refine ae_of_all _ (fun ω x hx => ?_)
    have hxpos : 0 < x := hball_pos x hx
    -- Derivative of `s ↦ Ht s ω`.
    have hHt : HasDerivAt (fun s => Ht s ω)
        ((-β) • ((1 / (2 * Real.sqrt x)) • G ω)) x := by
      -- `Ht s ω = (-β) • (H_arith + (sqrt s) • G ω)`
      have hsqrt : HasDerivAt (fun s : ℝ => Real.sqrt s) (1 / (2 * Real.sqrt x)) x :=
        Real.hasDerivAt_sqrt (ne_of_gt hxpos)
      have hsmul : HasDerivAt (fun s : ℝ => (Real.sqrt s) • G ω)
          ((1 / (2 * Real.sqrt x)) • G ω) x := by
        simpa using (hsqrt.smul_const (G ω))
      have hadd : HasDerivAt (fun s : ℝ => H_arith + (Real.sqrt s) • G ω)
          ((1 / (2 * Real.sqrt x)) • G ω) x := by
        simpa using (hsmul.const_add H_arith)
      -- Scale by `(-β)`.
      -- Avoid `simp` here: it will expand the affine expression and then erase the constant term
      -- using `hasDerivAt_const_add_iff`, producing a different (but equivalent) statement.
      dsimp [Ht]
      exact hadd.const_smul (-β)
    -- Chain rule through `free_energy_density`.
    have hFdiff :
        DifferentiableAt ℝ (fun H : EnergySpace M => SpinGlass.free_energy_density (N := M) H) (Ht x ω) := by
      -- `ContDiff` gives `ContDiffAt`, and `ContDiffAt` implies `DifferentiableAt` for order `≥ 1`.
      have hcontAt :
          ContDiffAt ℝ 1 (fun H : EnergySpace M => SpinGlass.free_energy_density (N := M) H) (Ht x ω) :=
        (SpinGlass.contDiff_free_energy_density (N := M)).contDiffAt.of_le (by simp)
      exact hcontAt.differentiableAt (by simp)
    have hcomp :=
      (HasFDerivAt.comp_hasDerivAt (x := x) (f := fun s => Ht s ω)
        (l := fun H => SpinGlass.free_energy_density (N := M) H)
        (l' := fderiv ℝ (fun H : EnergySpace M => SpinGlass.free_energy_density (N := M) H) (Ht x ω))
        hFdiff.hasFDerivAt hHt)
    simpa [F, F'] using hcomp

  -- Apply the dominated differentiation lemma.
  have hMain :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (ℙ : Measure Ω)) (F := F) (F' := F') (x₀ := t) (bound := bound) (ε := ε)
      hε_pos hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2

  -- Step 2: rewrite the derivative using the explicit first derivative of the free energy
  -- and Gaussian IBP for the weighted coordinate expectations.
  -- First, compute `F' t ω` explicitly.
  have hF'_explicit : ∀ ω,
      F' t ω = (β / (2 * (M : ℝ) * Real.sqrt t)) * (∑ σ : Config M, (μt ω σ) * (G ω σ)) := by
    intro ω
    -- Expand `F'` and use `SpinGlass.fderiv_free_energy_density_apply`.
    have hderiv :=
      SpinGlass.fderiv_free_energy_density_apply (N := M) (H := Ht t ω)
        (h := (-β) • ((1 / (2 * Real.sqrt t)) • G ω))
    -- rewrite and simplify
    simp [F', F, Ht, μt, SpinGlass.free_energy_density, mul_assoc, mul_left_comm, mul_comm,
      smul_eq_mul, Finset.mul_sum] at *
    grind

  -- Apply Gaussian IBP for each coordinate and sum over `σ`.
  have hIBP_coord :
      ∀ σ : Config M,
        (∫ ω, (μt ω σ) * (G ω σ) ∂ℙ)
          = (β * Real.sqrt t) * ∫ ω,
              let Cov : Config M → ℝ := fun τ =>
                inner ℝ (covOp hG (SpinGlass.std_basis M σ)) (SpinGlass.std_basis M τ)
              (μt ω σ) * (Cov σ - ∑ τ : Config M, (μt ω τ) * (Cov τ)) ∂ℙ := by
    intro σ
    -- Apply the Hilbert-space Gaussian IBP with `h = std_basis σ` and test function `Fσ`.
    let Fσ : EnergySpace M → ℝ :=
      fun G_vec =>
        SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • G_vec)) σ
    have hFσ_diff : ContDiff ℝ 1 Fσ := by
      -- `Fσ` is smooth as a composition of smooth maps.
      have hpmf : ContDiff ℝ 1 (fun H : EnergySpace M => SpinGlass.gibbs_pmf M H σ) :=
        (SpinGlass.contDiff_gibbs_pmf (N := M) (σ := σ)).of_le (by simp)
      have haff : ContDiff ℝ 1 (fun G_vec : EnergySpace M => (-β) • (H_arith + (Real.sqrt t) • G_vec)) := by
        have hlin : ContDiff ℝ 1 (fun G_vec : EnergySpace M => H_arith + (Real.sqrt t) • G_vec) :=
          contDiff_const.add (contDiff_id.const_smul (Real.sqrt t))
        simpa [smul_add, smul_smul, mul_assoc] using hlin.const_smul (-β)
      simpa [Fσ] using hpmf.comp haff
    -- Moderate growth: bounded function with bounded derivative.
    have hFσ_growth : HasModerateGrowth Fσ := by
      classical
      -- Choose a uniform constant dominating both `|Fσ|` and `‖fderiv Fσ‖`.
      let C : ℝ := 2 * |β| * Real.sqrt t + 2
      refine ⟨C, 0, ?_, ?_, ?_⟩
      · -- `C > 0`.
        have : 0 ≤ 2 * |β| * Real.sqrt t := by positivity
        nlinarith
      · -- `|Fσ z| ≤ C`.
        intro z
        have : |Fσ z| ≤ 1 := by
          -- `0 ≤ gibbs_pmf ≤ 1`.
          have h0 : 0 ≤ SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) σ :=
            SpinGlass.gibbs_pmf_nonneg (N := M) (H := (-β) • (H_arith + (Real.sqrt t) • z)) σ
          have h1 : SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) σ ≤ 1 :=
            SpinGlass.gibbs_pmf_le_one (N := M) (H := (-β) • (H_arith + (Real.sqrt t) • z)) σ
          -- Unfold `Fσ` without rewriting the Hamiltonian; then remove `abs` using nonnegativity.
          dsimp [Fσ]
          rw [abs_of_nonneg h0]
          exact h1
        have hC : (1 : ℝ) ≤ C := by
          dsimp [C]
          have : 0 ≤ 2 * |β| * Real.sqrt t := by positivity
          linarith
        simpa [pow_zero] using le_trans this (by nlinarith [hC])
      · -- Derivative bound: `‖fderiv Fσ z‖ ≤ C`.
        intro z
        -- bound `‖fderiv Fσ z‖` by `2 * |β| * √t`.
        have hderiv :
            ‖fderiv ℝ Fσ z‖ ≤ 2 * |β| * Real.sqrt t := by
          -- Use `opNorm_le_bound` and the explicit derivative formula.
          refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
          -- compute the derivative in direction `v` by chain rule, then use `SpinGlass.fderiv_gibbs_pmf_apply`.
          have hchain :
              (fderiv ℝ Fσ z) v =
                (fderiv ℝ (fun H : EnergySpace M => SpinGlass.gibbs_pmf M H σ)
                    ((-β) • (H_arith + (Real.sqrt t) • z)))
                  ((-β * Real.sqrt t) • v) := by
            -- `Fσ = (gibbs_pmf … σ) ∘ (affine map)`
            -- the affine map has derivative `v ↦ (-β*√t) • v`.
            have haff : HasFDerivAt (fun G_vec : EnergySpace M => (-β) • (H_arith + (Real.sqrt t) • G_vec))
                ((Real.sqrt t * (-β)) • (1 : EnergySpace M →L[ℝ] EnergySpace M)) z := by
              -- affine map derivative is constant
              have hlin :
                  HasFDerivAt (fun G_vec : EnergySpace M => (Real.sqrt t) • G_vec)
                    ((Real.sqrt t) • (1 : EnergySpace M →L[ℝ] EnergySpace M)) z := by
                simpa using ((Real.sqrt t) • (1 : EnergySpace M →L[ℝ] EnergySpace M)).hasFDerivAt
              have hadd :
                  HasFDerivAt (fun G_vec : EnergySpace M => H_arith + (Real.sqrt t) • G_vec)
                    ((Real.sqrt t) • (1 : EnergySpace M →L[ℝ] EnergySpace M)) z := by
                simpa using hlin.const_add H_arith
              have hsmul :
                  HasFDerivAt (fun G_vec : EnergySpace M => (-β) • (H_arith + (Real.sqrt t) • G_vec))
                    ((-β) • ((Real.sqrt t) • (1 : EnergySpace M →L[ℝ] EnergySpace M))) z :=
                hadd.const_smul (-β)
              -- normalize the scalar factor on the derivative
              simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using hsmul
            -- now chain rule for `fderiv`
            -- (use the characterization of `fderiv` via `HasFDerivAt` since everything is differentiable)
            have hpmf_diff :
                DifferentiableAt ℝ (fun H : EnergySpace M => SpinGlass.gibbs_pmf M H σ)
                  ((-β) • (H_arith + (Real.sqrt t) • z)) :=
              (SpinGlass.differentiableAt_gibbs_pmf (N := M) (H := (-β) • (H_arith + (Real.sqrt t) • z)) σ)
            have hcomp :=
              (HasFDerivAt.comp z
                (f := fun G_vec : EnergySpace M => (-β) • (H_arith + (Real.sqrt t) • G_vec))
                (g := fun H : EnergySpace M => SpinGlass.gibbs_pmf M H σ)
                hpmf_diff.hasFDerivAt haff)
            -- Evaluate the resulting `fderiv` on `v`.
            simpa [Fσ, Function.comp, mul_assoc, mul_left_comm, mul_comm] using
              congrArg (fun L => L v) hcomp.fderiv
          -- Now bound the value.
          -- First, use the explicit derivative formula for `gibbs_pmf`.
          have hpmf :=
            SpinGlass.fderiv_gibbs_pmf_apply (N := M)
              (H := (-β) • (H_arith + (Real.sqrt t) • z))
              (h := ((-β * Real.sqrt t) • v)) σ
          -- Bound the absolute value by `2 * ‖(-β*√t)•v‖`.
          have habs :
              |(fderiv ℝ (fun H : EnergySpace M => SpinGlass.gibbs_pmf M H σ)
                    ((-β) • (H_arith + (Real.sqrt t) • z)))
                  ((-β * Real.sqrt t) • v)| ≤
                2 * ‖(-β * Real.sqrt t) • v‖ := by
            -- rewrite using `hpmf`
            -- and use `0 ≤ gibbs_pmf ≤ 1` plus the triangle inequality.
            have h0 :
                0 ≤ SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) σ :=
              SpinGlass.gibbs_pmf_nonneg (N := M) (H := (-β) • (H_arith + (Real.sqrt t) • z)) σ
            have h1 :
                SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) σ ≤ 1 :=
              SpinGlass.gibbs_pmf_le_one (N := M) (H := (-β) • (H_arith + (Real.sqrt t) • z)) σ
            -- bound the bracket term
            have hsum_le :
                |∑ τ : Config M, SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) τ *
                      (( (-β * Real.sqrt t) • v) τ)|
                  ≤ ‖(-β * Real.sqrt t) • v‖ := by
              -- same argument as in `Calculus.hasModerateGrowth_free_energy_density`
              have hs1 :
                  (∑ τ : Config M, SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) τ) = 1 :=
                SpinGlass.sum_gibbs_pmf (N := M) (H := (-β) • (H_arith + (Real.sqrt t) • z))
              have h_abs_le :
                  |∑ τ : Config M,
                      SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) τ *
                        (( (-β * Real.sqrt t) • v) τ)|
                    ≤ ∑ τ : Config M,
                        |SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) τ *
                          (( (-β * Real.sqrt t) • v) τ)| := by
                    simpa using
                      (Finset.abs_sum_le_sum_abs
                        (f := fun τ : Config M =>
                          SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) τ *
                            (( (-β * Real.sqrt t) • v) τ))
                        (s := (Finset.univ : Finset (Config M))))
              have h_abs_term :
                  (∑ τ : Config M,
                      |SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) τ *
                        (( (-β * Real.sqrt t) • v) τ)|)
                    = ∑ τ : Config M,
                        (SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) τ) *
                          |(( (-β * Real.sqrt t) • v) τ)| := by
                    refine Finset.sum_congr rfl (fun τ _ => ?_)
                    have hg :
                        0 ≤ SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) τ :=
                      SpinGlass.gibbs_pmf_nonneg (N := M) (H := (-β) • (H_arith + (Real.sqrt t) • z)) τ
                    -- Use rewriting (not `simp`) to avoid cancellation lemmas producing disjunction goals.
                    rw [abs_mul, abs_of_nonneg hg]
              have hterm : ∀ τ : Config M,
                  (SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) τ) *
                    |(( (-β * Real.sqrt t) • v) τ)|
                    ≤ (SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) τ) *
                      ‖(-β * Real.sqrt t) • v‖ := by
                    intro τ
                    have hτ : |(( (-β * Real.sqrt t) • v) τ)| ≤ ‖(-β * Real.sqrt t) • v‖ :=
                      (SpinGlass.abs_apply_le_norm (N := M) ((-β * Real.sqrt t) • v) τ)
                    exact mul_le_mul_of_nonneg_left hτ
                      (SpinGlass.gibbs_pmf_nonneg (N := M) (H := (-β) • (H_arith + (Real.sqrt t) • z)) τ)
              have hsum' :=
                (Finset.sum_le_sum (s := (Finset.univ : Finset (Config M))) (fun τ _ => hterm τ))
              have hfactor :
                  (∑ τ : Config M,
                        (SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) τ) *
                          ‖(-β * Real.sqrt t) • v‖)
                    = (∑ τ : Config M, SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) τ) *
                        ‖(-β * Real.sqrt t) • v‖ := by
                    simpa using
                      (Finset.sum_mul (s := (Finset.univ : Finset (Config M)))
                        (f := fun τ : Config M =>
                          SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) τ)
                        (a := ‖(-β * Real.sqrt t) • v‖)).symm
              calc
                |∑ τ : Config M,
                    SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) τ *
                      (( (-β * Real.sqrt t) • v) τ)|
                    ≤ ∑ τ : Config M,
                        |SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) τ *
                          (( (-β * Real.sqrt t) • v) τ)| := h_abs_le
                _ = ∑ τ : Config M,
                        (SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) τ) *
                          |(( (-β * Real.sqrt t) • v) τ)| := h_abs_term
                _ ≤ (∑ τ : Config M, SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) τ) *
                        ‖(-β * Real.sqrt t) • v‖ := by
                      -- Avoid `simp` rewriting the Hamiltonian/scalars; just rewrite the RHS using `hfactor`.
                      exact le_trans hsum' (le_of_eq hfactor)
                _ = ‖(-β * Real.sqrt t) • v‖ := by
                      -- The goal has `-(β • H_arith) + -(β • √t • z)` which equals `(-β) • (H_arith + √t • z)`.
                      -- Also `‖(β * √t) • v‖ = ‖(-β * √t) • v‖` since norm ignores sign.
                      have heq : (∑ x, SpinGlass.gibbs_pmf M (-(β • H_arith) + -(β • (Real.sqrt t) • z)) x) = 1 := by
                        have : -(β • H_arith) + -(β • (Real.sqrt t) • z) = (-β) • (H_arith + (Real.sqrt t) • z) := by
                          ring_nf
                          simp only [neg_smul, smul_add]
                        rw [this]
                        exact hs1-- SpinGlass.gibbs_pmf_sum_eq_one M ((-β) • (H_arith + (Real.sqrt t) • z))
                      have hnorm_eq : ‖(β * Real.sqrt t) • v‖ = ‖(-β * Real.sqrt t) • v‖ := by
                        rw [norm_smul, norm_smul]
                        congr 1
                        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_neg]
                      rw [hs1, one_mul]
            have hvσ :
                |(( (-β * Real.sqrt t) • v) σ)| ≤ ‖(-β * Real.sqrt t) • v‖ :=
              SpinGlass.abs_apply_le_norm (N := M) ((-β * Real.sqrt t) • v) σ
            have hbr :
                |(∑ τ : Config M, SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) τ *
                      (( (-β * Real.sqrt t) • v) τ)) - (( (-β * Real.sqrt t) • v) σ)|
                  ≤ 2 * ‖(-β * Real.sqrt t) • v‖ := by
              calc
                |(∑ τ : Config M, SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) τ *
                      (( (-β * Real.sqrt t) • v) τ)) - (( (-β * Real.sqrt t) • v) σ)|
                    ≤ |∑ τ : Config M, SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) τ *
                          (( (-β * Real.sqrt t) • v) τ)| + |(( (-β * Real.sqrt t) • v) σ)| :=
                        abs_sub (∑ τ, gibbs_pmf M (-β • (H_arith + √t • z)) τ *
                          ((-β * √t) • v) τ) (((-β * √t) • v) σ)
                _ ≤ ‖(-β * Real.sqrt t) • v‖ + ‖(-β * Real.sqrt t) • v‖ := by gcongr
                _ ≤ 2 * ‖(-β * Real.sqrt t) • v‖ := by
                      simp [two_mul]
            -- assemble with `0 ≤ μσ ≤ 1`
            -- `|(μσ) * bracket| ≤ |bracket| ≤ 2‖(-β√t)•v‖`.
            have hμ :
                |(fderiv ℝ (fun H : EnergySpace M => SpinGlass.gibbs_pmf M H σ)
                      ((-β) • (H_arith + (Real.sqrt t) • z)))
                    ((-β * Real.sqrt t) • v)|
                  ≤ 2 * ‖(-β * Real.sqrt t) • v‖ := by
              -- rewrite with the explicit derivative formula `hpmf`
              rw [hpmf]
              -- turn `|μσ * bracket|` into `μσ * |bracket|`
              rw [abs_mul, abs_of_nonneg h0]
              -- use `μσ ≤ 1` and then `hbr`
              have hstep₁ :
                  SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) σ *
                      |(∑ τ : Config M, SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) τ *
                            (( (-β * Real.sqrt t) • v) τ)) - (( (-β * Real.sqrt t) • v) σ)|
                    ≤ 1 *
                      |(∑ τ : Config M, SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) τ *
                            (( (-β * Real.sqrt t) • v) τ)) - (( (-β * Real.sqrt t) • v) σ)| :=
                mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
              have hstep₂ :
                  1 *
                      |(∑ τ : Config M, SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • z)) τ *
                            (( (-β * Real.sqrt t) • v) τ)) - (( (-β * Real.sqrt t) • v) σ)|
                    ≤ 2 * ‖(-β * Real.sqrt t) • v‖ := by
                simpa [one_mul] using hbr
              exact le_trans hstep₁ hstep₂
            -- finish
            simpa using hμ
          -- convert to norm bound on `fderiv Fσ z v`
          have habs' : |(fderiv ℝ Fσ z) v| ≤ 2 * ‖(-β * Real.sqrt t) • v‖ := by
            -- Rewrite the LHS using the chain-rule identity `hchain`.
            -- We avoid `simp` here to prevent rewriting `L (c • v)` into `c * L v`.
            rw [hchain]
            exact habs
          have habs'' : |(fderiv ℝ Fσ z) v| ≤ (2 * |β| * Real.sqrt t) * ‖v‖ := by
            -- Rewrite `‖(-β*√t)•v‖` using `norm_smul` and `√t ≥ 0`.
            simpa [norm_smul, abs_of_nonneg (Real.sqrt_nonneg t), mul_assoc, mul_left_comm, mul_comm] using habs'
          -- Turn the codomain norm into an absolute value (`ℝ`).
          simpa [Real.norm_eq_abs, mul_assoc] using habs''
        -- finish by adding slack to reach `C`
        have : 2 * |β| * Real.sqrt t ≤ (2 * |β| * Real.sqrt t + 2) := by linarith
        simpa [C, pow_zero] using le_trans hderiv this
    -- Apply IBP.
    have hIBP :=
      PhysLean.Probability.GaussianIBP.gaussian_integration_by_parts_hilbert_cov_op
        (g := G) (hg := hG) (h := SpinGlass.std_basis M σ) (F := Fσ)
        (hF_diff := hFσ_diff) (hF_growth := hFσ_growth)
    -- Unfold the expectation notation used by the lemma.
    -- In our file, `𝔼[...]` is `∫ ω, ... ∂ℙ`.
    -- Rewrite both sides and simplify `⟪G ω, std_basis σ⟫ = G ω σ`.
    -- Finally, rewrite the derivative of `Fσ` using `SpinGlass.fderiv_gibbs_pmf_apply`.
    -- The result is the advertised covariance expression.
    -- Introduce the covariance row `Cov(σ, ·)` for notational convenience.
    let Cov : Config M → ℝ := fun τ =>
      inner ℝ (covOp hG (SpinGlass.std_basis M σ)) (SpinGlass.std_basis M τ)
    have hIBP' :
        (∫ ω, (μt ω σ) * (G ω σ) ∂ℙ) =
          ∫ ω,
              (fderiv ℝ Fσ (G ω))
                ((covOp (g := G) hG) (SpinGlass.std_basis M σ)) ∂ℙ := by
      -- `hIBP` is the IBP identity with `⟪G, eσ⟫ * Fσ(G)` on the LHS.
      -- Rewrite `⟪G ω, eσ⟫` as `G ω σ` and `Fσ (G ω)` as `μt ω σ`.
      have hinner : ∀ ω : Ω, inner ℝ (G ω) (std_basis M σ) = G ω σ := by
        intro ω
        calc
          inner ℝ (G ω) (std_basis M σ) = inner ℝ (std_basis M σ) (G ω) := by
            simp [real_inner_comm]
          _ = G ω σ := by
            simpa using (SpinGlass.inner_std_basis_apply (N := M) σ (G ω))
      simpa [μt, Fσ, Ht, hinner, mul_assoc, mul_left_comm, mul_comm] using hIBP
    -- Compute the derivative term pointwise using the explicit formula for `fderiv gibbs_pmf`.
    have hderiv_pointwise :
        ∀ ω,
          (fderiv ℝ Fσ (G ω)) ((covOp (g := G) hG) (SpinGlass.std_basis M σ)) =
            (β * Real.sqrt t) *
              ((μt ω σ) * (Cov σ - ∑ τ : Config M, (μt ω τ) * (Cov τ))) := by
      intro ω
      -- Chain rule: differentiate `Fσ = (gibbs_pmf … σ) ∘ (affine map)`.
      have hchain :
          (fderiv ℝ Fσ (G ω)) ((covOp (g := G) hG) (SpinGlass.std_basis M σ)) =
            (fderiv ℝ (fun H : EnergySpace M => SpinGlass.gibbs_pmf M H σ)
                  ((-β) • (H_arith + (Real.sqrt t) • G ω)))
              ((-β * Real.sqrt t) • ((covOp (g := G) hG) (SpinGlass.std_basis M σ))) := by
        -- Use `fderiv_comp` for the composition.
        have hpmf_diff :
            DifferentiableAt ℝ (fun H : EnergySpace M => SpinGlass.gibbs_pmf M H σ)
              ((-β) • (H_arith + (Real.sqrt t) • G ω)) :=
          SpinGlass.differentiableAt_gibbs_pmf (N := M)
            (H := (-β) • (H_arith + (Real.sqrt t) • G ω)) σ
        -- Differentiability of the affine map `G_vec ↦ (-β) • (H_arith + √t • G_vec)`.
        have haff :
            HasFDerivAt (fun G_vec : EnergySpace M => (-β) • (H_arith + (Real.sqrt t) • G_vec))
              ((Real.sqrt t * (-β)) • (1 : EnergySpace M →L[ℝ] EnergySpace M)) (G ω) := by
          -- Same computation as above: linear map + constant + scalar.
          have hlin :
              HasFDerivAt (fun G_vec : EnergySpace M => (Real.sqrt t) • G_vec)
                ((Real.sqrt t) • (1 : EnergySpace M →L[ℝ] EnergySpace M)) (G ω) := by
            simpa using ((Real.sqrt t) • (1 : EnergySpace M →L[ℝ] EnergySpace M)).hasFDerivAt
          have hadd :
              HasFDerivAt (fun G_vec : EnergySpace M => H_arith + (Real.sqrt t) • G_vec)
                ((Real.sqrt t) • (1 : EnergySpace M →L[ℝ] EnergySpace M)) (G ω) := by
            simpa using hlin.const_add H_arith
          have hsmul :
              HasFDerivAt (fun G_vec : EnergySpace M => (-β) • (H_arith + (Real.sqrt t) • G_vec))
                ((-β) • ((Real.sqrt t) • (1 : EnergySpace M →L[ℝ] EnergySpace M))) (G ω) :=
            hadd.const_smul (-β)
          simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using hsmul
        have haff_diff :
            DifferentiableAt ℝ (fun G_vec : EnergySpace M => (-β) • (H_arith + (Real.sqrt t) • G_vec))
              (G ω) :=
          haff.differentiableAt
        -- Expand `fderiv` of a composition and apply to the chosen direction.
        -- The derivative of the affine map is `v ↦ (-β*√t) • v`.
        have hfderiv_aff :
            fderiv ℝ (fun G_vec : EnergySpace M => (-β) • (H_arith + (Real.sqrt t) • G_vec)) (G ω) =
              ((Real.sqrt t * (-β)) • (1 : EnergySpace M →L[ℝ] EnergySpace M)) :=
          haff.fderiv
        -- Now use `fderiv_comp` and evaluate the resulting linear map on `covOp …`.
        have hcomp :
            fderiv ℝ Fσ (G ω) =
              (fderiv ℝ (fun H : EnergySpace M => SpinGlass.gibbs_pmf M H σ)
                    ((-β) • (H_arith + (Real.sqrt t) • G ω))).comp
                (fderiv ℝ (fun G_vec : EnergySpace M => (-β) • (H_arith + (Real.sqrt t) • G_vec)) (G ω)) := by
          simpa [Fσ] using
            (fderiv_comp (x := G ω) hpmf_diff haff_diff)
        -- Evaluate at the chosen direction.
        -- Do *not* rewrite the scalar action coordinatewise (that would unfold the covariance operator).
        have hcomp_apply :=
          congrArg
            (fun L : EnergySpace M →L[ℝ] ℝ =>
              L ((covOp (g := G) hG) (SpinGlass.std_basis M σ)))
            hcomp
        -- The `fderiv` of the linear map `y ↦ (β*√t) • y` is the constant linear map `(β*√t) • 1`.
        have hfderiv_smul :
            fderiv ℝ (fun y : EnergySpace M => (β * Real.sqrt t) • y) (G ω) =
              ((β * Real.sqrt t) • (1 : EnergySpace M →L[ℝ] EnergySpace M)) := by
          have hlin :
              HasFDerivAt (fun y : EnergySpace M => (β * Real.sqrt t) • y)
                ((β * Real.sqrt t) • (1 : EnergySpace M →L[ℝ] EnergySpace M)) (G ω) := by
            simpa using
              (((β * Real.sqrt t) • (1 : EnergySpace M →L[ℝ] EnergySpace M))).hasFDerivAt
          exact hlin.fderiv
        -- `((L.comp A) v) = L (A v)` and `A v = (√t * (-β)) • v`.
        -- `hcomp_apply` produces a sum with the scalar factors inside; rewrite the goal's RHS
        -- using `Finset.mul_sum` so the expressions match.
        simpa [ContinuousLinearMap.comp_apply, hfderiv_aff, hfderiv_smul, Finset.mul_sum,
          smul_smul, mul_assoc, mul_left_comm, mul_comm] using
          hcomp_apply
      -- Now use the explicit directional derivative formula for `gibbs_pmf`.
      have hpmf :=
        SpinGlass.fderiv_gibbs_pmf_apply (N := M)
          (H := (-β) • (H_arith + (Real.sqrt t) • G ω))
          (h := (-β * Real.sqrt t) • ((covOp (g := G) hG) (SpinGlass.std_basis M σ))) σ
      -- Rewrite `Cov` in terms of coordinates of `covOp …`.
      have hCov_eq : ∀ τ : Config M,
          Cov τ = ((covOp (g := G) hG) (SpinGlass.std_basis M σ)) τ := by
        intro τ
        -- `Cov τ = ⟪Σ eσ, eτ⟫ = ⟪eτ, Σ eσ⟫ = (Σ eσ) τ`.
        simpa [Cov, real_inner_comm] using
          (SpinGlass.inner_std_basis_apply (N := M) (σ := τ)
            (H := (covOp (g := G) hG) (SpinGlass.std_basis M σ)))
      -- Finish by simplification and algebra.
      -- Expand `hchain` using `hpmf`, then rewrite coordinates via `hCov_eq`.
      -- `simp` handles the pointwise `smul` on `PiLp` and reduces to ring arithmetic.
      have : (fderiv ℝ Fσ (G ω)) ((covOp (g := G) hG) (SpinGlass.std_basis M σ)) =
          (β * Real.sqrt t) *
            ((SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • G ω)) σ) *
              (((covOp (g := G) hG) (SpinGlass.std_basis M σ)) σ -
                ∑ τ : Config M,
                  SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • G ω)) τ *
                    ((covOp (g := G) hG) (SpinGlass.std_basis M σ)) τ)) := by
        -- Start from the chain-rule expression and plug in the `gibbs_pmf` derivative.
        -- Then rearrange to the `β*√t * μσ * (vσ - ∑ μτ vτ)` form.
        -- `simp` uses the explicit `fderiv_gibbs_pmf_apply`.
        -- Avoid a huge `simp` call: do the algebra explicitly.
        classical
        -- Abbreviate the covariance vector `v`.
        set v : EnergySpace M := (covOp (g := G) hG) (SpinGlass.std_basis M σ) with hv
        -- Rewrite `fderiv Fσ` via the chain rule and the explicit `fderiv gibbs_pmf` formula.
        have h0 :
            (fderiv ℝ Fσ (G ω)) v =
              (SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • G ω)) σ) *
                ((∑ τ : Config M,
                      SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • G ω)) τ *
                        ((-β * Real.sqrt t) • v) τ) -
                  ((-β * Real.sqrt t) • v) σ) := by
          -- `hchain` already reduces the derivative of `Fσ` to the derivative of `gibbs_pmf`
          -- evaluated at the direction `(-β*√t)•v`, and `hpmf` gives this derivative explicitly.
          have hchain_v :
              (fderiv ℝ Fσ (G ω)) v =
                (fderiv ℝ (fun H : EnergySpace M => SpinGlass.gibbs_pmf M H σ)
                      ((-β) • (H_arith + (Real.sqrt t) • G ω)))
                  ((-β * Real.sqrt t) • v) := by
            simpa [hv] using hchain
          -- Now rewrite by `hchain_v` and apply the explicit derivative formula `hpmf`.
          rw [hchain_v]
          simpa [hv] using hpmf
        -- Rewrite the scalar action on `v` pointwise.
        have hsmul_apply : ∀ τ : Config M, ((-β * Real.sqrt t) • v) τ = (-β * Real.sqrt t) * v τ := by
          intro τ
          simp [PiLp.smul_apply, smul_eq_mul]
        -- Pull the constant `(-β*√t)` out of the finite sum.
        have hsum :
            (∑ τ : Config M,
                SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • G ω)) τ *
                  ((-β * Real.sqrt t) • v) τ)
              =
              (-β * Real.sqrt t) *
                (∑ τ : Config M,
                  SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • G ω)) τ * v τ) := by
          -- termwise rewrite `((a • v) τ)` and then use `Finset.mul_sum`.
          -- (Sums over `Config M` are `Finset.univ` sums.)
          simp_rw [hsmul_apply, Finset.mul_sum, mul_assoc, mul_left_comm]
        -- Finish: rewrite `h0` using `hsum` and rearrange.
        -- The desired RHS is `(β*√t) * (μσ * (vσ - ∑ μτ vτ))`.
        -- From `h0` we get `μσ * ((a * ∑ μτ vτ) - (a * vσ))` with `a = -β*√t`,
        -- then factor `a` and flip the subtraction.
        have : (fderiv ℝ Fσ (G ω)) v =
            (β * Real.sqrt t) *
              (SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • G ω)) σ *
                (v σ - ∑ τ : Config M,
                  SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • G ω)) τ * v τ)) := by
          -- start from `h0`
          rw [h0]
          -- rewrite the sum and the `σ` term
          have hσ : ((-β * Real.sqrt t) • v) σ = (-β * Real.sqrt t) * v σ := hsmul_apply σ
          -- substitute
          rw [hsum, hσ]
          -- now just commutative-semiring algebra in `ℝ`
          -- `a*(S) - a*(vσ) = a*(S - vσ) = (-a)*(vσ - S)`
          -- and `-β*√t = -(β*√t)`
          ring_nf
        -- Put back `v = covOp …`; no need for any algebraic rewriting here.
        simpa [hv] using this
      -- Replace `μt` and `Cov` back into the final shape.
      -- (`μt ω τ = gibbs_pmf … τ` by definition.)
      -- Also rewrite the coordinates of `covOp` using `hCov_eq`.
      -- Rewrite the goal from `Cov` back to coordinates, then close with `this`.
      dsimp [μt, Ht]
      -- Replace `Cov σ` by the corresponding coordinate.
      rw [hCov_eq σ]
      -- Replace `Cov τ` inside the sum, termwise.
      have hsumCov :
          (∑ τ : Config M,
              SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • G ω)) τ * Cov τ)
            =
            ∑ τ : Config M,
              SpinGlass.gibbs_pmf M ((-β) • (H_arith + (Real.sqrt t) • G ω)) τ *
                ((covOp (g := G) hG) (SpinGlass.std_basis M σ)) τ := by
        classical
        refine Fintype.sum_congr _ _ (fun τ => ?_)
        rw [hCov_eq τ]
      rw [hsumCov]
      exact this
    -- Integrate the pointwise identity and pull out the constant factor.
    calc
      (∫ ω, (μt ω σ) * (G ω σ) ∂ℙ)
          = ∫ ω, (fderiv ℝ Fσ (G ω)) ((covOp (g := G) hG) (SpinGlass.std_basis M σ)) ∂ℙ := hIBP'
      _ = ∫ ω,
            (β * Real.sqrt t) *
              ((μt ω σ) * (Cov σ - ∑ τ : Config M, (μt ω τ) * (Cov τ))) ∂ℙ := by
            refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
            exact hderiv_pointwise ω
      _ = (β * Real.sqrt t) *
            ∫ ω, (μt ω σ) * (Cov σ - ∑ τ : Config M, (μt ω τ) * (Cov τ)) ∂ℙ := by
            -- Pull the constant `(β*√t)` out of the integral.
            simpa [mul_assoc] using
              (MeasureTheory.integral_const_mul (μ := (ℙ : Measure Ω)) (β * Real.sqrt t)
                (fun ω => (μt ω σ) * (Cov σ - ∑ τ : Config M, (μt ω τ) * (Cov τ))))
    -- The `calc` above already matches the statement (same `Cov` definition).

  -- Finish: assemble the dominated-differentiation result and simplify the derivative integral
  -- using `hIBP_coord` and finite-sum algebra.
  -- Use the dominated differentiation result.
  -- `hMain` gives the derivative as `∫ ω, F' t ω`.
  -- Rewrite `F' t ω` explicitly, then apply `hIBP_coord` and rearrange the finite sums.
  have hphi_deriv :
      HasDerivAt (phi (M := M) (β := β) H_arith G)
        (∫ ω, F' t ω ∂ℙ) t := by
    -- `phi = ∫ ω, F t ω`.
    simpa [phi, F] using hMain
  -- Now rewrite the derivative value.
  -- First expand `F' t ω` using `hF'_explicit`.
  have hderiv_value :
      (∫ ω, F' t ω ∂ℙ)
        =
          (β / (2 * (M : ℝ) * Real.sqrt t)) *
            ∑ σ : Config M, (∫ ω, (μt ω σ) * (G ω σ) ∂ℙ) := by
    -- Move the constant factor and the finite sum out of the integral.
    -- `hF'_explicit` gives the pointwise formula for `F' t`.
    have : (fun ω => F' t ω) =
        fun ω => (β / (2 * (M : ℝ) * Real.sqrt t)) * (∑ σ : Config M, (μt ω σ) * (G ω σ)) := by
      funext ω
      simpa using (hF'_explicit ω)
    -- Replace `F' t` by this expression and use linearity of the integral over finite sums.
    classical
    -- Pull out the constant factor, then swap the integral with the finite sum.
    -- (`MeasureTheory.integral_finset_sum` needs an `∑ i ∈ s` form, so we use `s = univ`.)
    have hsum :
        (∫ ω, ∑ σ ∈ (Finset.univ : Finset (Config M)),
            (μt ω σ) * (G ω σ) ∂ℙ)
          =
          ∑ σ ∈ (Finset.univ : Finset (Config M)), (∫ ω, (μt ω σ) * (G ω σ) ∂ℙ) := by
      -- Each summand is integrable: it is bounded by `‖G ω‖` and `‖G‖` is integrable for a Gaussian.
      have hGnorm : Integrable (fun ω => ‖G ω‖) (ℙ : Measure Ω) :=
        (PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian (g := G) hG)
      have hInt_each : ∀ σ : Config M, Integrable (fun ω => (μt ω σ) * (G ω σ)) (ℙ : Measure Ω) := by
        intro σ
        -- `|(μt ω σ) * (G ω σ)| ≤ ‖G ω‖` since `0 ≤ μt ≤ 1` and `|G ω σ| ≤ ‖G ω‖`.
        have hmeas : AEStronglyMeasurable (fun ω => (μt ω σ) * (G ω σ)) (ℙ : Measure Ω) := by
          -- Measurability: `μt ω σ` is continuous in `Ht t ω`, and `G ω σ` is a coordinate of `G ω`.
          have hG_meas : Measurable G := hG.repr_measurable
          have hHt_meas : Measurable fun ω => Ht t ω := by
            -- Keep the affine expression in the same normal form Lean uses for `Ht t ω`.
            have hG' : Measurable fun ω => -((β * Real.sqrt t) • G ω) :=
              (hG_meas.const_smul (β * Real.sqrt t)).neg
            have hsum : Measurable fun ω => (-(β • H_arith)) + -((β * Real.sqrt t) • G ω) :=
              measurable_const.add hG'
            -- This is definitionally equal to `Ht t ω`.
            simpa [Ht, smul_add, smul_smul, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm,
              add_comm] using hsum
          have hμ_meas : Measurable fun ω => μt ω σ := by
            -- unfold and use continuity of `gibbs_pmf` in the Hamiltonian
            have hcont :
                Continuous fun H : EnergySpace M => SpinGlass.gibbs_pmf M H σ :=
              (SpinGlass.contDiff_gibbs_pmf (N := M) (σ := σ)).continuous
            simpa [μt] using hcont.measurable.comp hHt_meas
          have hGcoord_meas : Measurable fun ω => G ω σ := by
            have :
                Measurable fun ω =>
                  (SpinGlass.evalCLM (N := M) σ) (G ω) :=
              (SpinGlass.evalCLM (N := M) σ).measurable.comp hG_meas
            simpa [SpinGlass.evalCLM] using this
          exact (hμ_meas.mul hGcoord_meas).aestronglyMeasurable
        refine MeasureTheory.Integrable.mono' (μ := (ℙ : Measure Ω)) hGnorm hmeas ?_
        refine ae_of_all _ (fun ω => ?_)
        -- pointwise bound
        have hμ_le : |μt ω σ| ≤ 1 := by
          have h0 : 0 ≤ μt ω σ := by
            -- `μt ω σ = gibbs_pmf … σ`
            simpa [μt] using
              SpinGlass.gibbs_pmf_nonneg (N := M) (H := Ht t ω) σ
          have h1 : μt ω σ ≤ 1 := by
            simpa [μt] using
              SpinGlass.gibbs_pmf_le_one (N := M) (H := Ht t ω) σ
          simpa [abs_of_nonneg h0] using h1
        have hcoord_le : |G ω σ| ≤ ‖G ω‖ := by
          simpa using (SpinGlass.abs_apply_le_norm (N := M) (σ := σ) (H := G ω))
        calc
          ‖(μt ω σ) * (G ω σ)‖ = |(μt ω σ) * (G ω σ)| := by simp [Real.norm_eq_abs]
          _ = |μt ω σ| * |G ω σ| := by simp [abs_mul]
          _ ≤ 1 * ‖G ω‖ := by
                have : |μt ω σ| * |G ω σ| ≤ 1 * ‖G ω‖ := by
                  exact mul_le_mul hμ_le hcoord_le (by positivity) (by positivity)
                simpa [mul_assoc] using this
          _ = ‖G ω‖ := by simp
      -- Apply the finite-sum integral lemma on `Finset.univ`.
      simpa using
        (MeasureTheory.integral_finset_sum (μ := (ℙ : Measure Ω))
          (s := (Finset.univ : Finset (Config M)))
          (f := fun σ ω => (μt ω σ) * (G ω σ))
          (by intro σ hσ; simpa using hInt_each σ))
    -- Now do the constant factor and convert between `∑ σ` and `∑ σ ∈ univ`.
    calc
      (∫ ω, F' t ω ∂ℙ)
          = ∫ ω, (β / (2 * (M : ℝ) * Real.sqrt t)) * (∑ σ : Config M, (μt ω σ) * (G ω σ)) ∂ℙ := by
              simp [this]
      _ = (β / (2 * (M : ℝ) * Real.sqrt t)) *
            ∫ ω, (∑ σ : Config M, (μt ω σ) * (G ω σ)) ∂ℙ := by
              simpa using
                (MeasureTheory.integral_const_mul (μ := (ℙ : Measure Ω))
                  (β / (2 * (M : ℝ) * Real.sqrt t))
                  (fun ω => ∑ σ : Config M, (μt ω σ) * (G ω σ)))
      _ = (β / (2 * (M : ℝ) * Real.sqrt t)) *
            ∑ σ : Config M, (∫ ω, (μt ω σ) * (G ω σ) ∂ℙ) := by
              -- rewrite the `Fintype` sum as a `Finset.univ` sum and use `hsum`
              simpa using congrArg (fun x => (β / (2 * (M : ℝ) * Real.sqrt t)) * x) (by
                -- `∑ σ` is `∑ σ ∈ univ`
                simpa using hsum)
  -- Apply the coordinate IBP formula to each summand, then simplify constants.
  have hsum_after_IBP :
      (∫ ω, F' t ω ∂ℙ)
        =
          (β^2 / (2 * (M : ℝ))) *
            ∫ ω,
              let H := (-β) • (H_arith + (Real.sqrt t) • G ω)
              let μ : Config M → ℝ := fun σ => SpinGlass.gibbs_pmf M H σ
              let Cov : Config M → Config M → ℝ :=
                fun σ τ => inner ℝ (covOp hG (SpinGlass.std_basis M σ)) (SpinGlass.std_basis M τ)
              (∑ σ, μ σ * Cov σ σ) - (∑ σ, ∑ τ, μ σ * μ τ * Cov σ τ)
            ∂ℙ := by
    -- Start from `hderiv_value` and substitute `hIBP_coord`.
    -- Then reorganize sums inside the integral.
    -- Key identity: `(β/(2*M*√t))*(β*√t) = β^2/(2*M)`.
    have ht_ne : Real.sqrt t ≠ 0 := by
      have : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
      exact ne_of_gt this
    -- Replace each `∫ ω, μt ω σ * G ω σ` using `hIBP_coord σ`.
    -- Then swap the finite sum with the integral.
    -- Finally expand `∑ σ μσ*(Cov σ - ∑ τ μτ*Cov τ)`.
    -- We do this inside a single `simp`/`ring` block.
    classical
    -- Use the expression from `hderiv_value`.
    -- `simp` will turn the sum of integrals into an integral of a sum.
    -- We keep the `let`-bindings from the statement to match the target exactly.
    calc
      (∫ ω, F' t ω ∂ℙ)
          = (β / (2 * (M : ℝ) * Real.sqrt t)) *
              ∑ σ : Config M, (∫ ω, (μt ω σ) * (G ω σ) ∂ℙ) := hderiv_value
      _ = (β / (2 * (M : ℝ) * Real.sqrt t)) *
            ∑ σ : Config M,
              (β * Real.sqrt t) *
                ∫ ω,
                  let Covσ : Config M → ℝ := fun τ =>
                    inner ℝ (covOp hG (SpinGlass.std_basis M σ)) (SpinGlass.std_basis M τ)
                  (μt ω σ) * (Covσ σ - ∑ τ : Config M, (μt ω τ) * (Covσ τ)) ∂ℙ := by
            refine congrArg (fun r => (β / (2 * (M : ℝ) * Real.sqrt t)) * r) ?_
            -- Apply `hIBP_coord` termwise.
            refine Finset.sum_congr rfl (fun σ _ => ?_)
            simpa using (hIBP_coord σ)
      _ = (β^2 / (2 * (M : ℝ))) *
            ∫ ω,
              let H := (-β) • (H_arith + (Real.sqrt t) • G ω)
              let μ : Config M → ℝ := fun σ => SpinGlass.gibbs_pmf M H σ
              let Cov : Config M → Config M → ℝ :=
                fun σ τ => inner ℝ (covOp hG (SpinGlass.std_basis M σ)) (SpinGlass.std_basis M τ)
              (∑ σ, μ σ * Cov σ σ) - (∑ σ, ∑ τ, μ σ * μ τ * Cov σ τ)
            ∂ℙ := by
            -- Pull constants through, swap `∑` with `∫`, and expand the algebra.
            -- First simplify constants.
            have hconst' :
                (β / (2 * (M : ℝ) * Real.sqrt t)) * (β * Real.sqrt t) = β^2 / (2 * (M : ℝ)) := by
              field_simp [ht_ne]
            classical
            -- Work with the same `Cov` as in the statement (no unfolding of `covOp`).
            let Cov : Config M → Config M → ℝ :=
              fun σ τ => inner ℝ (covOp hG (SpinGlass.std_basis M σ)) (SpinGlass.std_basis M τ)
            -- The integrand coming from `hIBP_coord`.
            let f : Config M → Ω → ℝ := fun σ ω =>
              (μt ω σ) * (Cov σ σ - ∑ τ : Config M, (μt ω τ) * (Cov σ τ))

            -- Swap the finite sum with the integral: `∑ σ ∫ fσ = ∫ ∑ σ fσ`.
            have hswap :
                (∑ σ : Config M, (∫ ω, f σ ω ∂ℙ))
                  =
                  ∫ ω, (∑ σ : Config M, f σ ω) ∂ℙ := by
              -- `integral_finset_sum` is stated for `∑ i ∈ s`; use `s = univ`.
              have hf_int : ∀ σ : Config M, Integrable (f σ) (ℙ : Measure Ω) := by
                intro σ
                -- `f σ` is bounded by a constant (finite sum of constants with `0 ≤ μt ≤ 1`).
                -- First, measurability of each `μt ω σ`.
                have hG_meas : Measurable G := hG.repr_measurable
                have hHt_meas : Measurable fun ω => Ht t ω := by
                  have hG' : Measurable fun ω => -((β * Real.sqrt t) • G ω) :=
                    (hG_meas.const_smul (β * Real.sqrt t)).neg
                  have hsum : Measurable fun ω => (-(β • H_arith)) + -((β * Real.sqrt t) • G ω) :=
                    measurable_const.add hG'
                  simpa [Ht, smul_add, smul_smul, mul_assoc, mul_left_comm, mul_comm,
                    add_assoc, add_left_comm, add_comm] using hsum
                have hμ_meas : ∀ σ : Config M, Measurable fun ω => μt ω σ := by
                  intro σ
                  have hcont :
                      Continuous fun H : EnergySpace M => SpinGlass.gibbs_pmf M H σ :=
                    (SpinGlass.contDiff_gibbs_pmf (N := M) (σ := σ)).continuous
                  simpa [μt] using hcont.measurable.comp hHt_meas
                have hf_meas : AEStronglyMeasurable (f σ) (ℙ : Measure Ω) := by
                  -- `f σ` is built from measurable pieces via `*`, `-`, and a finite sum.
                  have hsum_meas :
                      Measurable fun ω =>
                        ∑ τ : Config M, (μt ω τ) * (Cov σ τ) := by
                    refine Finset.measurable_sum (s := (Finset.univ : Finset (Config M))) ?_
                    intro τ _hτ
                    exact (hμ_meas τ).mul measurable_const
                  have hdiff_meas :
                      Measurable fun ω => (Cov σ σ - ∑ τ : Config M, (μt ω τ) * (Cov σ τ)) := by
                    exact measurable_const.sub hsum_meas
                  exact ((hμ_meas σ).mul hdiff_meas).aestronglyMeasurable
                -- Bound `‖f σ ω‖` by a constant `Cσ`.
                let Cσ : ℝ := |Cov σ σ| + ∑ τ : Config M, |Cov σ τ|
                have hCσ : Integrable (fun _ω : Ω => Cσ) (ℙ : Measure Ω) := by
                  simp
                refine MeasureTheory.Integrable.mono' (μ := (ℙ : Measure Ω)) hCσ hf_meas ?_
                refine ae_of_all _ (fun ω => ?_)
                -- `|μ| ≤ 1`
                have hμ_le_one : ∀ ρ : Config M, |μt ω ρ| ≤ 1 := by
                  intro ρ
                  have h0 : 0 ≤ μt ω ρ := by
                    simpa [μt] using
                      SpinGlass.gibbs_pmf_nonneg (N := M) (H := Ht t ω) ρ
                  have h1 : μt ω ρ ≤ 1 := by
                    simpa [μt] using
                      SpinGlass.gibbs_pmf_le_one (N := M) (H := Ht t ω) ρ
                  simpa [abs_of_nonneg h0] using h1
                -- Bound the inner sum by `∑ |Cov σ τ|`.
                have hsum_abs :
                    |∑ τ : Config M, (μt ω τ) * (Cov σ τ)|
                      ≤ ∑ τ : Config M, |Cov σ τ| := by
                  classical
                  have h1 :
                      |∑ τ : Config M, (μt ω τ) * (Cov σ τ)|
                        ≤ ∑ τ : Config M, |(μt ω τ) * (Cov σ τ)| := by
                    simpa using
                      (Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset (Config M)))
                        (f := fun τ => (μt ω τ) * (Cov σ τ)))
                  have h2 :
                      (∑ τ : Config M, |(μt ω τ) * (Cov σ τ)|)
                        ≤ ∑ τ : Config M, |Cov σ τ| := by
                    refine Finset.sum_le_sum (fun τ _hτ => ?_)
                    -- `|μ| ≤ 1`
                    have : |μt ω τ| * |Cov σ τ| ≤ 1 * |Cov σ τ| :=
                      mul_le_mul_of_nonneg_right (hμ_le_one τ) (abs_nonneg (Cov σ τ))
                    simpa [abs_mul, mul_assoc] using this
                  exact le_trans h1 h2
                -- Now the final bound.
                have habs :
                    |(μt ω σ) * (Cov σ σ - ∑ τ : Config M, (μt ω τ) * (Cov σ τ))|
                      ≤ Cσ := by
                  have hsub :
                      |Cov σ σ - ∑ τ : Config M, (μt ω τ) * (Cov σ τ)|
                        ≤ |Cov σ σ| + |∑ τ : Config M, (μt ω τ) * (Cov σ τ)| :=
                    abs_sub (Cov σ σ) (∑ τ : Config M, (μt ω τ) * (Cov σ τ))
                  have hsub' :
                      |Cov σ σ - ∑ τ : Config M, (μt ω τ) * (Cov σ τ)|
                        ≤ |Cov σ σ| + ∑ τ : Config M, |Cov σ τ| := by
                    exact le_trans hsub (add_le_add_left hsum_abs _)
                  have hmul :
                      |(μt ω σ) * (Cov σ σ - ∑ τ : Config M, (μt ω τ) * (Cov σ τ))|
                        = |μt ω σ| * |Cov σ σ - ∑ τ : Config M, (μt ω τ) * (Cov σ τ)| := by
                    simp [abs_mul]
                  -- use `|μ| ≤ 1`
                  have hμσ : |μt ω σ| ≤ 1 := hμ_le_one σ
                  calc
                    |(μt ω σ) * (Cov σ σ - ∑ τ : Config M, (μt ω τ) * (Cov σ τ))|
                        = |μt ω σ| *
                            |Cov σ σ - ∑ τ : Config M, (μt ω τ) * (Cov σ τ)| := hmul
                    _ ≤ 1 * (|Cov σ σ| + ∑ τ : Config M, |Cov σ τ|) := by
                          -- first bound the second factor, then the first
                          have hA :
                              |Cov σ σ - ∑ τ : Config M, (μt ω τ) * (Cov σ τ)|
                                ≤ |Cov σ σ| + ∑ τ : Config M, |Cov σ τ| := hsub'
                          have := mul_le_mul hμσ hA (by positivity)
                            (by positivity)
                          simpa [mul_assoc, add_assoc, add_left_comm, add_comm] using this
                    _ = Cσ := by simp [Cσ]
                -- Convert `‖·‖` to `|·|` for `ℝ` and unfold `f`.
                simpa [Real.norm_eq_abs, f] using habs
              -- Apply the `Finset` lemma on `univ` and rewrite back to `∑ σ`.
              have hf : ∀ σ ∈ (Finset.univ : Finset (Config M)), Integrable (f σ) (ℙ : Measure Ω) := by
                intro σ _hσ
                simpa using hf_int σ
              have h0 :=
                (MeasureTheory.integral_finset_sum (μ := (ℙ : Measure Ω))
                  (s := (Finset.univ : Finset (Config M)))
                  (f := fun σ ω => f σ ω) hf)
              -- `simp` rewrites `∑ σ ∈ univ` to `∑ σ`.
              simpa using h0.symm

            -- Expand the sum inside the integral to match the statement.
            have hsum_expand : ∀ ω : Ω,
                (∑ σ : Config M, f σ ω)
                  =
                  (∑ σ : Config M, (μt ω σ) * (Cov σ σ))
                    - (∑ σ : Config M, ∑ τ : Config M, (μt ω σ) * (μt ω τ) * (Cov σ τ)) := by
              intro ω
              classical
              -- Expand `f`, split the subtraction, then expand the inner sum.
              -- (We do this explicitly to avoid `simp` unfolding unrelated definitions.)
              have hsplit :
                  (∑ σ : Config M,
                      (μt ω σ) * (Cov σ σ - ∑ τ : Config M, (μt ω τ) * (Cov σ τ)))
                    =
                    (∑ σ : Config M, (μt ω σ) * (Cov σ σ))
                      - ∑ σ : Config M, (μt ω σ) * (∑ τ : Config M, (μt ω τ) * (Cov σ τ)) := by
                -- Use `mul_sub` inside the sum and then `sum_sub_distrib` on `univ`.
                -- (Rewrite `∑ σ` as `∑ σ ∈ univ` to apply the `Finset` lemma.)
                simp [mul_sub]
              have hdouble :
                  (∑ σ : Config M, (μt ω σ) * (∑ τ : Config M, (μt ω τ) * (Cov σ τ)))
                    =
                    ∑ σ : Config M, ∑ τ : Config M, (μt ω σ) * (μt ω τ) * (Cov σ τ) := by
                -- Expand `μσ * (∑τ ...)` into a double sum.
                classical
                -- First expand as `∑ σ, ∑ τ, μσ * ((μτ) * Covστ)`.
                have hdouble' :
                    (∑ σ : Config M, (μt ω σ) * (∑ τ : Config M, (μt ω τ) * (Cov σ τ)))
                      =
                      ∑ σ : Config M, ∑ τ : Config M, (μt ω σ) * ((μt ω τ) * (Cov σ τ)) := by
                  -- Expand the inner sum for each `σ`.
                  refine Finset.sum_congr rfl (fun σ _hσ => ?_)
                  -- `∑ τ` is over `univ`, so `Finset.mul_sum` applies.
                  simp [Finset.mul_sum]
                -- Reassociate multiplications.
                simpa [mul_assoc] using hdouble'
              -- Now put everything together and unfold `f`.
              dsimp [f]
              -- Replace the split-off term using `hdouble`.
              rw [hsplit, hdouble]

            -- Now assemble: constants + sum/integral swap + algebraic expansion.
            -- Start from the current expression and rewrite to the target form.
            -- (`simp` will unfold the `let`-bindings on the RHS of the goal.)
            have :
                (β / (2 * (M : ℝ) * Real.sqrt t)) *
                    ∑ σ : Config M,
                      (β * Real.sqrt t) * (∫ ω, f σ ω ∂ℙ)
                  =
                  (β^2 / (2 * (M : ℝ))) *
                    ∫ ω,
                      ((∑ σ : Config M, (μt ω σ) * (Cov σ σ)) -
                        (∑ σ : Config M, ∑ τ : Config M, (μt ω σ) * (μt ω τ) * (Cov σ τ))) ∂ℙ := by
              -- Pull `(β*√t)` out of the sum.
              have hsum_factor :
                  (∑ σ : Config M, (β * Real.sqrt t) * (∫ ω, f σ ω ∂ℙ))
                    = (β * Real.sqrt t) * (∑ σ : Config M, (∫ ω, f σ ω ∂ℙ)) := by
                classical
                simpa using
                  (Finset.mul_sum (s := (Finset.univ : Finset (Config M)))
                    (f := fun σ => (∫ ω, f σ ω ∂ℙ)) (β * Real.sqrt t)).symm
              -- Use `hconst'` to simplify the constant product, then swap sum/integral.
              calc
                (β / (2 * (M : ℝ) * Real.sqrt t)) *
                    ∑ σ : Config M, (β * Real.sqrt t) * (∫ ω, f σ ω ∂ℙ)
                    = (β / (2 * (M : ℝ) * Real.sqrt t)) *
                        ((β * Real.sqrt t) * (∑ σ : Config M, (∫ ω, f σ ω ∂ℙ))) := by
                          -- Just rewrite the inner sum; avoid `simp` turning `a*b = a*c` into disjunctions.
                          rw [hsum_factor]
                _ = (β^2 / (2 * (M : ℝ))) * (∑ σ : Config M, (∫ ω, f σ ω ∂ℙ)) := by
                      -- Associate and apply `hconst'`.
                      calc
                        (β / (2 * (M : ℝ) * Real.sqrt t)) *
                            ((β * Real.sqrt t) * (∑ σ : Config M, (∫ ω, f σ ω ∂ℙ)))
                            =
                            ((β / (2 * (M : ℝ) * Real.sqrt t)) * (β * Real.sqrt t)) *
                              (∑ σ : Config M, (∫ ω, f σ ω ∂ℙ)) := by
                              simp [mul_assoc, mul_left_comm, mul_comm]
                        _ = (β^2 / (2 * (M : ℝ))) * (∑ σ : Config M, (∫ ω, f σ ω ∂ℙ)) := by
                              simp [mul_assoc]; grind
                _ = (β^2 / (2 * (M : ℝ))) * (∫ ω, (∑ σ : Config M, f σ ω) ∂ℙ) := by
                      simp [hswap]
                _ = (β^2 / (2 * (M : ℝ))) *
                      ∫ ω,
                        ((∑ σ : Config M, (μt ω σ) * (Cov σ σ)) -
                          (∑ σ : Config M, ∑ τ : Config M, (μt ω σ) * (μt ω τ) * (Cov σ τ))) ∂ℙ := by
                      refine congrArg (fun r => (β^2 / (2 * (M : ℝ))) * r) ?_
                      refine MeasureTheory.integral_congr_ae (ae_of_all _ (fun ω => ?_))
                      simpa using (hsum_expand ω)

            -- Finish by unfolding `f`/`Cov` and the `let`-bindings from the statement.
            simpa [f, Cov, μt, Ht, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using this
  -- Conclude by rewriting the derivative value in `hphi_deriv`.
  -- The derivative in the statement is exactly `hsum_after_IBP`.
  -- We just replace the derivative value and finish.
  have : HasDerivAt (phi (M := M) (β := β) H_arith G)
      ((β^2 / (2 * (M : ℝ))) * ∫ ω,
        let H := (-β) • (H_arith + (Real.sqrt t) • G ω)
        let μ : Config M → ℝ := fun σ => SpinGlass.gibbs_pmf M H σ
        let Cov : Config M → Config M → ℝ :=
          fun σ τ => inner ℝ (covOp hG (SpinGlass.std_basis M σ)) (SpinGlass.std_basis M τ)
        (∑ σ, μ σ * Cov σ σ) - (∑ σ, ∑ τ, μ σ * μ τ * Cov σ τ)
      ∂ℙ) t := by
    -- `hphi_deriv` gives the derivative as `∫ ω, F' t ω`; rewrite using `hsum_after_IBP`.
    simpa [hsum_after_IBP, mul_assoc] using hphi_deriv
  exact this

end ArithmeticSpinGlass
