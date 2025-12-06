[6 tools called]

### Available Poisson–kernel Infrastructure

**Core Mathlib**

- Everything we use ultimately sits on standard Mathlib analytic and measure‐theoretic APIs:
  - `Mathlib/Analysis/Complex/Basic`, `.../Analytic/Basic`, `.../Topology/ContinuousOn`, `.../MeasureTheory/Integral/CircleAverage`.
    These provide `AnalyticAt/AnalyticOn`, `IsROrC`, `intervalIntegral`, `circleAverage`, dominated convergence, etc.
  - There is no built‑in Poisson kernel/representation in upstream Mathlib yet; all kernel definitions in this project live in the `Riemann` namespace.

**Riemann project**

- `Riemann/Mathlib/Analysis/Complex/HardySpace.lean`
  ```260:330:Riemann/Mathlib/Analysis/Complex/HardySpace.lean
  def poissonKernel (r θ φ) := ...
  lemma poissonKernel_integral ...
  lemma poissonKernel_continuous ...
  lemma poissonKernel_approximate_identity ...
  ```
  - Disk Poisson kernel `poissonKernel r θ φ`, positivity/bounds, normalization, approximate identity.
  - Placeholders (`sorry`s) for Fatou’s theorem (`radialLimit_exists`, `boundaryValue_measurable`, `canonical_factorization`). These mark exactly the deep pieces still missing.

- `Riemann/Mathlib/Analysis/Complex/DeBranges/Nevanlinna/CanonicalRepresentation'.lean`
  ```610:990:.../CanonicalRepresentation'.lean
  def schwarzKernel ...
  lemma schwarzKernel_re_eq_poissonKernel ...
  def schwarzIntegral ...
  def analyticPoissonPart ...
  lemma analyticPoissonPart_hasDiskPoissonRepresentation ...
  ```
  - Identifies the classical Schwarz kernel with the disk Poisson kernel, proves analyticity of the Schwarz integral, and packages the Poisson representation for “analytic Poisson part”.

- `Riemann/Mathlib/Analysis/Complex/DeBranges/Nevanlinna/Space.lean`
  - Uses the Poisson kernel indirectly through `kernel_Cauchy` and differentiates integrals; provides admissibility/vanishing statements needed for de Branges spaces.

- `Riemann/academic_framework/DiskHardy.lean`
  - Alternate disk Poisson kernel `poissonKernel (z : 𝔻) θ` normalized by `1/(2π)` plus integrability facts along the boundary circle (`IntegrableOn … * poissonKernel z θ`).

- `Riemann/RS/PoissonPlateau.lean`, `RS/TentShadow.md`
  - Upper half–plane Poisson kernel `poissonKernelPlateau b u = (1/π) * b/(u²+b²)` with positivity, integrability on strips. Useful when transferring results through the Cayley transform (`DeBranges/Nevanlinna/Cayley.lean` has the `UpperHalfPlane ↔ 𝔻` bridge).

- `Riemann/Mathlib/Analysis/Complex/DeBranges/Nevanlinna/Cayley.lean`
  - Relates the upper half–plane Poisson kernel to the unit disc one via the Cayley map, so disk statements can be lifted to the half–plane setting required for Nevanlinna theory.

**PrimeNumberTheoremAnd / StrongPNT**

- Both libraries already prove integrability of the classical (real‐line) Poisson kernel used in explicit formula work:
  ```1640:1650:PrimeNumberTheoremAnd/MediumPNT.lean
  theorem poisson_kernel_integrable (x : ℝ) (hx : x ≠ 0) : ...
  ```
  - Same theorem duplicated in `StrongPNT/PNT5_Strong.lean`. These lemmas show the kernel is integrable against functions on `ℝ`, but they do not build the full harmonic Poisson representation.

### What’s ready vs. still missing

| Layer | Ready APIs | Missing pieces |
| --- | --- | --- |
| Disk kernel algebra | explicit formulas, bounds, integrability (`HardySpace`, `DiskHardy`, `CanonicalRepresentation'`) | none |
| Analytic Poisson part | `schwarzIntegral`, `analyticPoissonPart`, Poisson representation lemma | done |
| Hardy H^∞ boundary theory | definitions of `boundaryValue`, kernel approximations, setup for Fatou & canonical factorization | **Fatou’s theorem**, measurable boundary values, Blaschke factorization still `sorry` |
| Upper half–plane transfer | `Cayley`, `Space.lean` using admissibility, kernel differentiation | done except the remaining high-level reflection steps |
| External libraries | `PrimeNumberTheoremAnd` / `StrongPNT` Poisson integrability lemmas | do not yet offer general harmonic representation |

### Suggested next steps for a full SOTA Poisson–kernel formalization

1. **Fill the Hardy-space level gaps**
   - Prove `IsInHInfty.radialLimit_exists` using the kernel approximate identity plus Montel/normal family machinery.
   - Deduce `boundaryValue_measurable` from the specific sequences we already set up.
   - Finish `IsInHInfty.canonical_factorization` (Blaschke × outer factor). This unlocks the Szegő/outer integrability used later.

2. **Promote disk results to the upper half–plane**
   - Use `DeBranges/Nevanlinna/Cayley.lean` to rewrite the disk Poisson kernel results for the upper half-plane (needed for Nevanlinna/Poisson–Jensen).
   - Reuse `poissonKernelPlateau` lemmas from `RS/PoissonPlateau.lean` for vertical lines.

3. **Leverage existing integrability lemmas**
   - The integrability statements already proven in `PrimeNumberTheoremAnd` and `StrongPNT` show that the “real line” Poisson kernel behaves as expected; we can refactor them into a shared module (or re-export under `Riemann.Mathlib`) to avoid duplication.

4. **Connect to de Branges/Nevanlinna goals**
   - With Fatou + canonical factorization, the remaining `sorry`s in `CanonicalRepresentation'` and `Space.lean` become straightforward applications (boundary values exist, integrable log|f|, etc.).
   - The uniqueness lemma in `Space.lean` then follows by feeding the boundary zero info through the Hardy-space machinery rather than invoking placeholder arguments.

5. **Documentation and API consolidation**
   - Once the above results are in place, promote the key lemmas (`poissonKernel_integral`, `poissonKernel_approximate_identity`, `analyticPoissonPart_hasDiskPoissonRepresentation`) into a common namespace (e.g. `Riemann.Mathlib.Analysis.Complex.PoissonKernel`) so future files can import a single module.

With these ingredients, the project already contains all the low-level analytical tools needed; what remains is formalizing the deep classical theorems (Fatou, Szegő, Blaschke). Once those are in place, the Poisson kernel representation will follow directly from the existing `schwarzIntegral`/`analyticPoissonPart` APIs.
