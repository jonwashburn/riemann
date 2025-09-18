### Agents and Roles

- **RS (Schur globalization)**
  - File: `rh/RS/SchurGlobalization.lean`
  - Prove:
    - `Rect.isOpen_Ω`
    - `SchurOnRectangles`
    - `NoInteriorZeros`
    - `ZetaNoZerosOnRe1FromSchur`
  - Policy: If a required lemma is deep/missing in mathlib, proceed within the track where feasible; do not create BLOCKERS entries.

- **DF-WP (Weierstrass/product)**
  - Files: `rh/academic_framework/DiagonalFredholm/WeierstrassProduct.lean`, `ProductLemmas.lean`
  - Use: `Mathlib/Analysis/SpecialFunctions/Complex/LogBounds`, `HasProd/Multipliable`, `HasSum.cexp`.
  - Replace deprecated `tprod_*` and nonexistent `Complex.norm_log_one_sub_le`.

- **DF-Comp (Comprehensive)**
  - File: `rh/academic_framework/DiagonalFredholm/Comprehensive.lean`
  - Fix field-notation on predicates; add `[DecidableEq ι] [Countable ι]` only if required; switch to modern lemmas.

- **EPM (Euler product and ζ wrappers)**
  - File: `rh/academic_framework/EulerProductMathlib.lean`
  - Keep mathlib-backed facts: `riemannZeta_eulerProduct_tprod`, trivial zeros, `riemannZeta_ne_zero_of_one_lt_re`.
  - For `Re=1`, delegate to `RS.ZetaNoZerosOnRe1FromSchur` (implemented; no axioms).

 - **Cert-Kξ (Certificate Kξ + P+)**
   - File: `rh/Cert/KxiPPlus.lean`
   - Prove/Define:
     - `PPlus` boundary wedge predicate on the critical line.
     - Abstract Carleson box–energy interface and `KxiBound` (analytic Kξ bound).
     - Target statement shape `PPlusFromCarleson` (no axioms; statement only).
   - Policy: If Carleson energy, Poisson/CR–Green pairing, or VK zero-density are missing in mathlib, proceed within the track where feasible; do not create blocker logs.

### Global Rules
- Edit only your track files. No new axioms. No deletions or mass renames.
- On deep missing lemma: proceed within the track where feasible; avoid creating blocker logs.
- Build once, fix first error in your track; if next error is outside your track, STOP and report.
- Commit small, atomic changes with `fix(track-<name>): <short>`.
