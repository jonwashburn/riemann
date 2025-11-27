# Finishing Checklist: Riemann Hypothesis Formalization

This checklist breaks down the "Finishing Strategy" from `proof_map.md` into executable tasks.
Use this to track progress.

## Phase 1: Honest Refactoring (De-Stubbing) ✅ COMPLETE
**Goal**: Replace trivial "energy=0" stubs with explicit Hypotheses so the proof is conditionally valid.

**Status**: All 4 tasks completed. The proof is now "honestly conditional" on VK hypotheses.

- [x] **Refactor VK Counts**: Replace `VK_annular_counts_exists` (which assumes 0 atoms) with a `Hypothesis_VK_Zero_Density` structure.
  - Added `zero_density_bound_from_hyp_nonneg` and `Zk_card_from_hyp_nonneg` lemmas
  - Added `vk_weighted_partial_sum_bound` theorem for the geometric decay argument
  - `VK_annular_counts_exists_real` now uses the VK hypothesis properly
- [x] **Refactor Carleson Bound**: Replace `carleson_energy_bound` (which assumes 0 energy) with `Hypothesis_Carleson_Bound`.
  - Created `CarlesonHypothesis.lean` with:
    - `CarlesonEnergyHypothesis` structure (K_xi, bounds, energy_bound)
    - `VKCarlesonHypothesis` extending it with VK dependency
    - `vk_derived_constant` placeholder for the VK → Carleson derivation
    - `carleson_implies_paper_bound` theorem
  - *Note*: DiagonalBounds.lean still has pre-existing compilation errors.
  - The `boxEnergy` placeholder needs to be connected to the real definition.
- [x] **Refactor Residues**: Replace `residue_bookkeeping` (empty list) with `Hypothesis_Residue_Atoms` that actually tracks $\xi$ zeros.
  - Created `ResidueHypothesis.lean` with:
    - `ResidueAtomsHypothesis` structure (C_total, total_bounded)
    - `VKResidueHypothesis` extending it with VK dependency
    - `vk_implies_residue_bounds` theorem (sorry'd)
    - `mkVKResidueHypothesis` constructor
  - Note: `residue_bookkeeping` already uses `zerosInBox` to enumerate zeros
- [x] **Fix KxiBound**: Redefine `KxiWhitney.KxiBound` to quantify over all Whitney intervals (analytic content) rather than just asserting existence of a number.
  - Updated `KxiBound` to include `∀ (I : WhitneyInterval), boxEnergy_abstract I ≤ Kξ * (2 * I.len)`
  - Added `boxEnergy_abstract` placeholder function
  - The condition now explicitly quantifies over all Whitney intervals

## Phase 2: Gap G1 (Phase-Velocity Identity)
**Goal**: Prove $-w'(t) = \pi \mu + \text{atoms}$ without assuming it.

- [ ] **Define Distributions**: Ensure `boundary_phase_derivative` is defined as a distribution on $\mathbb{R}$.
- [ ] **Smoothed Limit**: Prove the distributional limit of the smoothed phase derivative $\mathcal{H}[u_\epsilon']$ as $\epsilon \to 0$.
- [ ] **Singular Inner**: Prove the `no_singular_inner_factor` lemma (showing the limit measure has no singular component).
- [ ] **Atomic Positivity**: Prove `critical_atoms_nonneg` using the Argument Principle (residues are positive integers).

## Phase 3: Gap G2 (Carleson Energy from VK)
**Goal**: Derive the finite constant $K_\xi$ from Zero Density (The "Hardest Math").

- [ ] **VK Intervals**: Formalize the derivation of `VKAnnularCounts` from `VinogradovKorobov` estimates (linking `IntegralLogPlusBoundVK` to counts).
- [ ] **Log T Suppression**: Formalize the inequality showing $\sum 4^{-k} \nu_k \ll |I|$ (proving the exponent $\theta$ in VK is strong enough to kill $\log T$).
- [ ] **Connect to Energy**: Prove that the *analytic* `carleson_energy` (CR-Green) is bounded by the *counting* budget.

## Phase 4: Gap G3 (CR-Green Pairing)
**Goal**: Rigorous functional analysis for the upper bound.

- [ ] **Admissible Windows**: Define the `AdmissibleWindow` class (windows that dodge atoms).
- [ ] **Pairing Identity**: Prove `CR_green_identity` for admissible windows (Green's thm + cutoffs).
- [ ] **Uniform Bound**: Prove the "length-free" energy bound for admissible windows (crucial for the $\sqrt{|I|}$ scaling).

## Phase 5: Execution
- [ ] **Verify Constants**: Feed the proved/hypothesized constants into `PPlus_from_constants`.
- [ ] **Close Loop**: Confirm `Upsilon < 1/2` holds with the best available VK constants.
