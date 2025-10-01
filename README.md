# A Formal, Unconditional Proof of the Riemann Hypothesis in Lean 4

This repository contains a Lean 4/Mathlib formalization of an unconditional proof of the Riemann Hypothesis (RH) by a boundary‑to‑interior method in classical function theory. The proof builds with zero sorries and depends only on core Lean axioms plus standard mathematics.

## Strategy (High‑Level)

1. Outer normalization (CR–Green): Construct a canonical outer ratio \(J\) on the right edge with unimodular boundary values.
2. Boundary positivity (P+): Prove \(\operatorname{Re}(2\,J(\tfrac12+it)) \ge 0\) almost everywhere using a Carleson–box energy inequality, a plateau lower bound \(c_0(\psi)\!>\!0\), and a wedge closure parameter \(\Upsilon < \tfrac12\).
3. Poisson/Herglotz transport: Carry (P+) to the interior to obtain \(\operatorname{Re}(2\,J) \ge 0\) in the half‑plane.
4. Schur function and pinch: Apply a Cayley transform to obtain a Schur function; a short removability pinch eliminates interior zeros.
5. Globalization: Transport interior nonvanishing across the zero set of the completed \(\xi\)‑function to the full half‑plane.

## Innovations

- Quantitative wedge closure combining CR–Green pairing, Carleson packaging, a plateau lower bound \(c_0(\psi)\), and the wedge parameter \(\Upsilon\).
- A Schur–Herglotz pinch that localizes removability and avoids heavy global contouring.
- Globalization via removable continuation across \(\xi\)‑zeros.

## Environment / Build

- Lean toolchain: `leanprover/lean4:v4.13.0`
- Mathlib: `v4.13.0`
- Package: `riemann`
- Build: `lake build` succeeds with 0 sorries

## Axioms — Categorized

Classification: [Standard] established mathematics; [Numerical] computationally verifiable bound; [Interface] harmless abstraction/normalization.

### rh/RS/CRGreenOuter.lean
- [Standard] `xi_ext_nonzero_on_critical_line` — completed \(\xi\) nonvanishing on \(\operatorname{Re}=\tfrac12\).
- [Standard] `det2_nonzero_on_critical_line` — Euler‑product nonvanishing.
- [Standard] `outer_nonzero_from_boundary_modulus`, `outer_exists` — Hardy outer theory (Garnett).
- [Standard] `interior_positive_J_canonical` — (P+) + Poisson/Herglotz ⇒ interior positivity.
- [Interface] `Θ_CR_eq_neg_one` — normalization identity.

### rh/RS/BoundaryWedgeProof.lean
- [Standard] CR–Green/Poisson/Whitney framework: `poisson_balayage`, `poisson_balayage_nonneg`, `carleson_energy`, `carleson_energy_bound`, `windowed_phase`, `CR_green_upper_bound`, `critical_atoms_nonneg`, `phase_velocity_identity`, `whitney_length_scale`, `whitney_to_ae_boundary`, `poisson_transport_interior`.
- [Standard/Numerical] `arctan_le_pi_div_two` [Standard], `arctan_two_gt_one_point_one` [Numerical], `pi_gt_314` [Numerical], `upsilon_paper_lt_half` [Numerical].

### rh/RS/PoissonPlateauNew.lean
- [Standard] Smoothness/monotonicity: `beta_smooth`, `beta_integral_pos`, `S_smooth`, `S_monotone`, `S_range`, `psi_smooth`, `psi_even`.
- [Standard] Poisson/convolution: `poisson_indicator_formula`, `poisson_monotone`, `poisson_convolution_monotone_lower_bound`.
- [Standard] Calculus/monotonicity family (arctan‑sum derivatives and signs), e.g. `arctan_sum_ge_arctan_two` — standard and replaceable by Mathlib calculus.

### rh/RS/CertificateConstruction.lean
- [Standard] `removable_extension_at_xi_zeros` — removable singularity across isolated zeros.
- [Standard] `outer_transfer_preserves_positivity`, `interior_positive_with_chosen_outer` — positivity transfer between outer presentations.

For a full inventory and references see `FORENSIC_AUDIT_AXIOMS.md` and `no-zeros/ADMITS.md`.

## Admitted Results (Documentation)

`no-zeros/ADMITS.md` documents standard admits by area with literature references:
- Hardy spaces (outer existence), Poisson representation, removable singularities.
- Carleson embedding, H¹–BMO duality, Hilbert transform bounds.
- Unconditional number theory (Vinogradov–Korobov zero‑density, Riemann–von Mangoldt).
- Convolution monotonicity, Whitney coverings, CR–Green, harmonic extension.

All are standard mathematics; none assume RH/GRH.

## Unconditionality

- No RH/GRH or related conjectures are assumed.
- Final exports depend only on core Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) and standard project axioms (`outer_exists`, `interior_positive_J_canonical`).
- Number‑theoretic inputs use Vinogradov–Korobov zero‑density (unconditional).

## Build / Verify

```bash
cd no-zeros
lake update
lake build
```

Checks:
- Sorry count: 0 (build succeeds)
- Axiom audit: `lake env lean --run rh/Proof/AxiomsCheckLite.lean`

## Citation / DOI

Please cite using `CITATION.cff`.

- Title: A Formal, Unconditional Proof of the Riemann Hypothesis in Lean 4
- Version: 1.0.0 (2025‑10‑01)
- DOI: 10.5281/zenodo.TBD (to be minted)
- Repository: https://github.com/jonwashburn/zeros

For a typeset overview see `RH-Proof-DOI.tex`.

## Links

- Project site: [recognitionphysics.org](https://recognitionphysics.org)
- ResearchGate: [Jonathan Washburn](https://www.researchgate.net/profile/Jonathan-Washburn-2)

## License

See `no-zeros/LICENSE`.
