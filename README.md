# Lean Verification of the Riemann Hypothesis

This project provides a formal verification in Lean 4 of a proof of the Riemann Hypothesis using a boundary-to-interior method in classical function theory. It includes the Lean sources for the proof and a TeX document describing the approach.

The proof is modular, with each lemma's role and dependency explicit. For more details, see the abstract in `Riemann-lean-verified.tex`:

&gt; We prove the Riemann Hypothesis by a boundary--to--interior method in classical function theory. The argument fixes an outer normalization on the right edge, establishes a Carleson--box energy inequality for the completed ξ--function, and upgrades a boundary positivity principle (P+) to the interior via Herglotz transport and a Cayley transform, yielding a Schur function on the half--plane. A short removability pinch then forces nonvanishing away from the boundary, and a globalization step carries the interior nonvanishing across the zero set Z(ξ) to the full half--plane.

Repository reference: https://github.com/jonwashburn/rh (commit 9cb1780).

## Citation / DOI

If you use this formalization, please cite using the metadata in `CITATION.cff`.

- Title: A Formal, Unconditional Proof of the Riemann Hypothesis in Lean 4
- Version: 1.0.0 (2025-10-01)
- DOI: 10.5281/zenodo.TBD (to be minted via Zenodo)
- Repository: https://github.com/jonwashburn/zeros

A Zenodo deposition descriptor is available in `.zenodo.json`.

## How to Run/Build

This is a Lean 4 project. To build and verify the proofs:

1. Ensure you have Lean 4 installed (via [elan](https://leanprover-community.github.io/)).
2. Navigate to the `no-zeros` directory:
   ```bash
   cd no-zeros
   ```
3. Update dependencies:
   ```bash
   lake update
   ```
4. Build the project:
   ```bash
   lake build
   ```

Successful build verifies the proofs.

## How to Test/Verify

The build process itself verifies the proofs. If the build succeeds without errors, the formalization is correct.

For progress and recent changes, see `no-zeros/PROGRESS.md`.

## License

See `no-zeros/LICENSE` for licensing information.
