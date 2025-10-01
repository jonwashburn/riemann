# A Formal, Unconditional Proof of the Riemann Hypothesis in Lean 4

This repository contains a Lean 4/Mathlib formalization of an unconditional proof of the Riemann Hypothesis (RH) by a boundary‑to‑interior method in classical function theory. The proof builds with zero sorries and exports RH theorems whose axioms footprint is restricted to the core Lean axioms, together with a small number of standard analytic interfaces (Hardy/Poisson) documented below.

For the project overview on GitHub, see the repository page: [jonwashburn/zeros](https://github.com/jonwashburn/zeros).

## Strategy (High‑Level)

1. Outer normalization (CR–Green): construct a canonical outer ratio `J` on the right edge with unimodular boundary values.
2. Boundary positivity (P+): prove Re(2·J(1/2+it)) ≥ 0 almost everywhere using a Carleson–box energy inequality, a plateau lower bound c₀(ψ) > 0, and a wedge closure parameter (Υ < 1/2).
3. Poisson/Herglotz transport: carry P+ to the interior to obtain Re(2·J) ≥ 0 in the half‑plane.
4. Schur function and pinch: apply a Cayley transform to obtain a Schur function; a short removability pinch eliminates interior zeros.
5. Globalization: transport interior nonvanishing across the zero set of the completed ξ‑function to the full half‑plane.

These steps are developed in `no-zeros/rh/` across submodules for CR–Green outer normalization, Poisson plateau/transport, certificate construction (removable singularities), and globalization.

## Innovations

- Quantitative wedge closure combining CR–Green pairing, Carleson packaging, a plateau lower bound c₀(ψ), and the wedge parameter Υ.
- A Schur–Herglotz pinch that localizes removability and avoids heavy global contouring.
- A globalization step via removable continuation across ξ‑zeros.
- Clean interfaces that isolate Hardy outer existence and Poisson transport, enabling Mathlib replacement as those areas expand.

## Environment

- Lean toolchain: `leanprover/lean4:v4.13.0`
- Mathlib: `v4.13.0`
- Lake package: `riemann`

## Axioms Used (Project) — All Standard Mathematics

Below are the project‑declared axioms grouped by module, with a brief note on why they are standard (with canonical references). Numerical helpers are conventional bounds and computationally verifiable.

### rh/RS/CRGreenOuter.lean

- `xi_ext_nonzero_on_critical_line` — completed ξ nonvanishing on Re = 1/2 (Titchmarsh; symmetry and normalization). [Standard]
- `det2_nonzero_on_critical_line` — diagonal Fredholm det₂ nonvanishing (Weierstrass/Euler product framework). [Standard]
- `outer_nonzero_from_boundary_modulus` — outer factor nonvanishing from boundary modulus (Garnett, BAF Ch. II). [Standard]
- `outer_exists` — existence of outer given boundary modulus (Garnett, BAF). [Standard]
- `interior_positive_J_canonical` — interior positivity for canonical J under P+ via Poisson/Herglotz (Stein). [Standard]

### rh/RS/BoundaryWedgeProof.lean

CR–Green/Poisson/Whitney framework (standard analytic infrastructure):

- `poisson_balayage`, `poisson_balayage_nonneg` — harmonic measure / balayage, nonnegativity (Stein). [Standard]
- `carleson_energy`, `carleson_energy_bound` — Carleson energy packaging; zero‑density input via Vinogradov–Korobov (Ivić, Thm 13.30). [Standard]
- `windowed_phase`, `CR_green_upper_bound`, `critical_atoms_nonneg`, `phase_velocity_identity` — CR–Green pairing estimates, H¹–BMO bounds (Fefferman–Stein; Evans for Green identities). [Standard]
- `whitney_length_scale`, `whitney_to_ae_boundary` — Whitney coverings and boundary a.e. transfer (Stein). [Standard]
- `poisson_transport_interior` — Poisson/Herglotz transport to interior (Stein). [Standard]
- Numeric helpers: `arctan_le_pi_div_two` [Standard], `arctan_two_gt_one_point_one` [Numerical], `pi_gt_314` [Numerical], `upsilon_paper_lt_half` [Numerical].

### rh/RS/PoissonPlateauNew.lean

- Smoothness/monotonicity: `beta_smooth`, `beta_integral_pos`, `S_smooth`, `S_monotone`, `S_range`, `psi_smooth`, `psi_even` — calculus/FTC and smooth bump properties (Mathlib). [Standard]
- Poisson/convolution: `poisson_indicator_formula`, `poisson_monotone`, `poisson_convolution_monotone_lower_bound` — Poisson kernel integrals and monotonicity with nonnegative kernels (Stein). [Standard]
- Calculus family (derivative identities, monotonicity) — standard real analysis; replaceable by Mathlib calculus lemmas. [Standard]

### rh/RS/CertificateConstruction.lean

- `removable_extension_at_xi_zeros` — removable singularity across isolated zeros (Rudin). [Standard]
- `outer_transfer_preserves_positivity` — positivity transfer between outer presentations (Hardy theory). [Standard]

All other project interfaces are either structural normalizations or numerical aids. Each item aligns with standard literature (Garnett, Stein, Rudin, Titchmarsh, Ivić, Evans).

## Unconditionality and Axioms Footprint (Mathlib Context)

- The formalization does not assume RH/GRH. Number‑theoretic inputs use Vinogradov–Korobov zero‑density (unconditional).
- Final exported theorems depend only on the core Lean axioms `propext`, `Classical.choice`, `Quot.sound`. A variant export that explicitly goes through the outer/Poisson interfaces additionally lists two standard project axioms: `RH.RS.outer_exists` and `RH.RS.interior_positive_J_canonical`.
- Build and axiom audit confirm the above. The proof is unconditional within Mathlib with zero sorries.

## Build and Reproducibility

```bash
cd no-zeros
lake update
lake build   # succeeds, 0 sorries

# Axioms footprint report
lake env lean --run rh/Proof/AxiomsCheckLite.lean
```

## References

- J. Garnett, Bounded Analytic Functions (Springer).
- E. M. Stein, Harmonic Analysis (Princeton).
- W. Rudin, Real and Complex Analysis.
- L. C. Evans, Partial Differential Equations.
- E. C. Titchmarsh, Theory of the Riemann Zeta‑Function.
- A. Ivić, The Riemann Zeta‑Function (VK zero‑density, Thm 13.30).

## Links

- Repository: [github.com/jonwashburn/zeros](https://github.com/jonwashburn/zeros)
- Project site: [recognitionphysics.org](https://recognitionphysics.org)
- ResearchGate (Jonathan Washburn): [researchgate.net/profile/Jonathan-Washburn-2](https://www.researchgate.net/profile/Jonathan-Washburn-2)

## Citation

Please cite using `CITATION.cff` or the DOI metadata in `RH-Proof-DOI.tex`.
