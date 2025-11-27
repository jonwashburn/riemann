# Finishing Checklist: Riemann Hypothesis Formalization

This checklist breaks down the "Finishing Strategy" from `proof_map.md` into executable tasks.
Use this to track progress.

## Phase 1: Honest Refactoring (De-Stubbing)
**Goal**: Replace trivial "energy=0" stubs with explicit Hypotheses so the proof is conditionally valid.

- [x] **Refactor VK Counts**: Replace `VK_annular_counts_exists` (which assumes 0 atoms) with a `Hypothesis_VK_Zero_Density` structure.
  - Added `zero_density_bound_from_hyp_nonneg` and `Zk_card_from_hyp_nonneg` lemmas
  - Added `vk_weighted_partial_sum_bound` theorem for the geometric decay argument
  - `VK_annular_counts_exists_real` now uses the VK hypothesis properly
- [ ] **Refactor Carleson Bound**: Replace `carleson_energy_bound` (which assumes 0 energy) with `Hypothesis_Carleson_Bound`.
  - *Note*: DiagonalBounds.lean has pre-existing compilation errors that need to be fixed first.
  - The `Zk_card_real` function is used but the old definition was commented out.
  - Need to wire `Zk_card_from_hyp` into the Carleson bound chain.
- [ ] **Refactor Residues**: Replace `residue_bookkeeping` (empty list) with `Hypothesis_Residue_Atoms` that actually tracks $\xi$ zeros.
- [ ] **Fix KxiBound**: Redefine `KxiWhitney.KxiBound` to quantify over all Whitney intervals (analytic content) rather than just asserting existence of a number.

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
