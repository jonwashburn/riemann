### Scope of this review

This note reviews the current Lean formalization in this repo that is (explicitly or implicitly) meant to support the Arguin(-Bourgade-Radziwiłł)/Arguin–Tai “zeta as a spin glass” program, and compares it to the attached source TeX files in:

- `Notes/Papers/Arguin/arXiv-1706.08462v4/RZF-1RSB_oct23_2018.tex` (Arguin–Tai, *Is the Riemann zeta function in a short interval a 1-RSB spin glass?*)
- `Notes/Papers/Arguin/arXiv-2007.00988v2/ZetaMax_october9_2020.tex` (Arguin–Bourgade–Radziwiłł, FHK Conjecture I)
- `Notes/Papers/Arguin/arXiv-2307.00982v1/LB_FHK_July1_2023.tex` (Arguin–Bourgade–Radziwiłł, FHK Conjecture II)

### What is currently formalized (high-level map)

- **Approximate complex IBP lemma (Arguin–Tai `lem: by parts`)**
  - **Paper**: `RZF-1RSB_oct23_2018.tex`, Lemma `\ref{lem: by parts}`.
  - **Lean**: `Riemann/PhysLean/SpinGlass/ComplexIBP.lean`, theorem `approx_integral_by_parts_complex`.
  - **Status**: implemented and compiles.

- **Random phase model primitives (uniform phases, basic trig/covariance integrals)**
  - **Lean**: `Notes/Papers/CW/RandomPhaseMoments.lean`, `Notes/Papers/CW/RandomPhaseModelMoments.lean`.
  - **Status**: substantial “input lemmas” are present (uniform measure on `[0,2π]`, cosine identities, pushforward transfer, independence factorization).

- **Block decomposition / random prime-phase model scaffolding**
  - **Lean**: `Notes/Papers/CW/ZetaSpinGlassDefs.lean`.
  - **Status**: definitions exist for prime blocks `P_k`, arithmetic and random block increments, Gaussian surrogates, covariance matrices.
  - **Note**: these are “Notes/” files (research scaffolding), not the main library.

- **Lindeberg replacement (scalar)**
  - **Lean**: `Notes/Papers/CW/LindebergStep.lean`, `Notes/Papers/CW/LindebergBlockwise.lean`, `Notes/Papers/CW/Lindenberg.lean`.
  - **Status**: a full, reusable blockwise replacement theorem is present (stated on expectations of a `C^3` test function, controlled by third moments).

- **Spin glass finite-volume infrastructure + Guerra/Talagrand interpolation**
  - **Lean (library)**: `Riemann/PhysLean/SpinGlass/Defs.lean`, `Replicas.lean`, `GuerraBound.lean`, `SKModel.lean`, `Calculus.lean`, `Algebra.lean`.
  - **Lean (notes integration)**: `Notes/Papers/CW/ZetaSpinGlass.lean` (builds a Guerra derivative statement for a “zeta kernel” by assuming a Gaussian field with matching covariance).
  - **Status**: substantial general machinery exists; the zeta-specific piece currently assumes covariance matching rather than proving it from number theory.

### Paper-to-Lean alignment notes (most important)

#### 1) Arguin–Tai Lemma `lem: by parts`: statement mismatch is intentional and justified

- **Paper hypothesis** (as written) bounds only pure Wirtinger second derivatives:
  - `||∂_z^2 F||_∞ < M` and `||∂_{z̄}^2 F||_∞ < M`.
- **Lean hypothesis** uses a *correct* global control:
  - `FDerivLipschitz F M` = “real Fréchet derivative is globally Lipschitz with constant `M`”.
- **Why**: controlling only `∂_z^2` and `∂_{z̄}^2` does *not* control the mixed second-order directions; the Taylor remainder can be quadratic even when those two pure Wirtinger second derivatives vanish (e.g. `F(z)=|z|^2`). The Lean file documents this point.

#### 2) Constants / norms

- **Paper** hides constants with `≪`; Lean makes a (conservative) explicit constant:
  - Lean concludes `≤ (4 * M) * 𝔼[‖ξ‖^3]`.
- Lean uses `‖·‖` (norm) and Bochner expectations; paper uses `|·|` and scalar expectations.
  - For `ℂ`, these coincide, but the Lean formulation is more general/robust for later reuse.

#### 3) “Continuum vs finite configuration space”

- The Arguin zeta papers often define Gibbs measures on a **continuum** index set (e.g. `h ∈ [0,1]`).
- The core `Riemann/PhysLean/SpinGlass/*` library is primarily built around **finite** configuration spaces (`Config N := Fin N → Bool`).
- The zeta notes (`Notes/Papers/CW/ZetaSpinGlass.lean`) explicitly attach real “positions” `h(σ)` to finite configs, which is best viewed as a **discretization layer** (useful, but not literally the paper’s continuum Gibbs measure).

### Biggest gaps vs the papers (actionable checklist)

- **Arguin–Tai (1706.08462)**
  - [ ] Formalize the paper’s application `F_p(z, z̄)` and prove a usable `FDerivLipschitz` bound `M = O(p^{-3/2})` for that specific `F_p`.
  - [ ] Define/instantiate `ξ = U_p` (Steinhaus variable) and prove `𝔼[ξ]=0`, `𝔼[ξ^2]=0`, `𝔼[‖ξ‖^3]=1`.
  - [ ] Derive Proposition `\ref{prop: carmona-hu}` from `approx_integral_by_parts_complex`.
  - [ ] Formalize the chain from that proposition to `\ref{prop: overlap free}` (currently not in Lean).

- **FHK I/II (2007.00988, 2307.00982)**
  - [ ] The heavy number theory appendix tools (mean-value theorem for Dirichlet polynomials, splitting, moment bounds, discretization) are not formalized.
  - [ ] The “random model ↔ Dirichlet polynomial” transfer step is not formalized (currently only modeled abstractly in notes).
  - [ ] The barrier/ballot components used in the proofs are not formalized.

### API recommendations (Lean-side)

- **Factor out general-purpose complex calculus**:
  - `deriv_z`, `deriv_zbar`, and reconstruction lemma are broadly useful; consider a dedicated module (and/or upstreaming pieces).
- **Bridge lemma for usability**:
  - Add a lemma “bounded (real) Hessian ⇒ `FDerivLipschitz`” and a lemma that expresses this in Wirtinger terms, so the hypotheses look closer to the paper.
- **Decide what is “library” vs “notes”**:
  - If `Notes/Papers/CW/ZetaSpinGlassDefs.lean` et al. are intended to be stable, consider migrating them under `Riemann/PhysLean/ZetaSpinGlass/…` and cleaning the “diamond oracle” workaround comments.
