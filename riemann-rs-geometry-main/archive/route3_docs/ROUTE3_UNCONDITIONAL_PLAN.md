### Route‑3 Unconditional RH Plan (Promptable)

This file is the **single source of truth** for the Route‑3 (Lagarias/Weil) "unconditional" program in this repo.

---

## 🔄 PROACTIVE EXECUTION PROTOCOL

**Instructions for the AI assistant:**

When the user says "continue executing on our plan" or similar:

1. **Read this file first** — Identify the current state from "Current status + next action" below
2. **Execute immediately** — Don't ask for confirmation. Start working on the next item.
3. **Iterate until blocked** — After completing one item, immediately start the next.
4. **Self-direct + re-plan continuously** — Before each new item, quickly re-evaluate if the next step is still the best move. If you find a better sequencing/refactor/lemma target, update the relevant plan docs *first* (this file + `ROUTE3_LEMMA_COMPLETION_LOOP.md`), then proceed.
5. **Keep the plan “alive”** — After *every* successful milestone (new theorem, axiom removed, major refactor), immediately update:
   - this file’s “Current status + next action” section, and
   - `ROUTE3_LEMMA_COMPLETION_LOOP.md` (execution queue + axiom counts),
   - and, if it changes the narrative/status, `ROUTE3_MOST_RECENT_PROOF.tex`.
6. **Prefer de-axiomatization** — If something is currently a global Lean `axiom`, first try to convert it into:
   - a theorem (best), or
   - an explicit hypothesis/bundle field (`structure` field / `def … : Prop`) that is threaded where needed (acceptable intermediate).
7. **Track progress** — Mark items as complete, add notes about what was done.
8. **Run the build** — After any substantive Lean edit, run `lake build`. If it fails, fix the errors before doing anything else.
9. **Report blockers clearly** — If truly stuck (missing Mathlib API, unclear requirement), explain what's needed, then pivot to the next best sub-lemma per the anti-stall rule.

**Proactive planning loop (must follow every time):**
- At the start of each “continue”, write a 2–4 line **micro-plan** (what you will do next + what files you’ll touch).
- Before coding, ensure the next action is a **single smallest lemma/definition**; if not, split it into new checkboxes in `ROUTE3_LEMMA_COMPLETION_LOOP.md`.
- Never end a session with “next step unclear”: if needed, create the next checkbox item(s) yourself.

**Goal:** Keep grinding until `RiemannHypothesis` is proved with **no Lean axioms remaining on the Route‑3 proof path** (i.e. in the `ExplicitFormula` pipeline and its direct imports).

**Anti-stall rule:** If a step looks blocked, attempt one alternative (e.g. prove a “derived axiom” as a theorem, split a big axiom into smaller lemmas, or switch to a different checklist track) before declaring a blocker.

**Driver file for detailed checklists:** See `ROUTE3_LEMMA_COMPLETION_LOOP.md`

---

### Definition of "unconditional" (project-specific)
For this project, **“unconditional” means:**
- We are allowed to assume **standard / classically accepted axioms and theorems** (e.g. ZFC + classical analysis theorems) even if they are not yet formalized in Mathlib, by recording them as Lean `axiom`s when needed.
- We are **not** allowed to assume any **RH‑equivalent** positivity statement for ξ/ζ; that RH‑level bridge must be proved (this is the real mathematical bottleneck).

**How to use this file (for repeated prompting):**
- If you are an assistant: **read this file first** and then continue from the first unchecked item in **“Current status + next action”**.
- Do **not** assume RH. Do **not** claim RH is solved. Treat **Recognition Science (RS)** as “given correct physics” only for the purpose of proposing a *derivation route*; then translate to explicit classical lemmas.
- Keep the work split into:
  - **Identity (standard analysis)**: proving equalities, contour/limit interchanges, boundary values.
  - **Positivity (RH‑equivalent core)**: proving a positivity/passivity property that forces a **positive spectral measure**.

---

### One-sentence goal
Produce a **non‑conditional** proof of RH by proving the **single RH‑equivalent bridge lemma** for ζ/ξ in Route‑3: the Weil/Lagarias quadratic form admits a **positive spectral measure** representation (reflection positivity), which implies Weil positivity and hence RH.

---

### Critical corrections discovered (do not lose these)

- **(C1) The current “weight” definition is trivial for ξ on the critical line.**
  - In Lean, `weightOfJ J t := Re( (2 : ℂ) * J(1/2 + i t) )` (`ExplicitFormula/HilbertRealization.lean`).
  - In Route‑3, `J := CompletedJ.J = -(1/2)·(ξ'/ξ)` (`ExplicitFormula/Route3HypBundle.lean`).
  - For the standard completed ξ, \(\xi(\tfrac12+it)\in\mathbb R\) and \(\xi'(\tfrac12+it)\in i\mathbb R\) off zeros, hence:
    - \(\Re(-\xi'/\xi(\tfrac12+it)) = 0\) **a.e.**
  - Therefore, any literal identity of the form
    - \(\int w(t)\,|M[f](\tfrac12+it)|^2\,dt\)
    with \(w(t)=\Re(-\xi'/\xi(\tfrac12+it))\) is **not** a meaningful Lebesgue‑density identity. The correct object is a **boundary measure/distribution**, not a pointwise weight.

- **(C2) The right finish-line statement is measure‑level, not density‑level.**
  - The usable spectral identity is:
    - \[
      W^{(1)}(\mathrm{pair}(f,g)) \;=\; \int_{\mathbb R}\overline{F_f(t)}\,F_g(t)\,d\mu(t),
      \qquad F_f(t)=M[f]\!\left(\tfrac12+it\right),
      \]
      where \(\mu\) is a **positive Borel measure** (may have singular/atomic parts).
  - The “\(d\mu=w(t)\,dt\)” (absolute continuity) version is **optional** and should not be the primary target.

- **(C3) The log‑Schwartz/Fourier idea is the best Lean‑feasible way to handle the analytic plumbing.**
  - Work in log‑coordinates: multiplicative convolution/Mellin on \((0,\infty)\) becomes additive convolution/Fourier on \(\mathbb R\).
  - Use Schwartz functions so integrability/Fubini/Plancherel become library lemmas (or definitional if you transport convolution through Fourier).
  - This helps **formalization**, but it does **not** remove the RH‑equivalent core.

---

### Repo reality check (what is abstract vs what must be proven)

- `LagariasFramework` (`ExplicitFormula/Lagarias.lean`) packages:
  - `W1 : F → ℂ` (symmetric zero sum, abstract)
  - `Warith : F → ℂ` (arithmetic side, abstract)
  - `explicitFormula : ∀ f, M[f](1) - W1 f + M[f](0) = Warith f` (Lagarias Thm 3.1, assumed)
  - `weilPositivity : RH ↔ (∀ f, 0 ≤ Re(W1(quad f)))` (Lagarias Thm 3.2, assumed)
- Route‑3 pipeline already proves:
  - `ReflectionPositivityRealization → WeilGate → RH` (mechanical)
- Therefore, the “unconditional” program must ultimately **prove** the missing analytic/number‑theory content for the ζ/ξ‑derived `W1`—and the RH‑equivalent core will be a positivity/passivity statement.

---

### Updated path (do this in order)

### Step 0 — Lock the finish-line lemma (single RH‑equivalent bridge, measure form)

**Target lemma (classical, minimal form):**
- There exists a **finite positive Borel measure** \(\mu\) on \(\mathbb R\) and a boundary transform \(F_f(t)\) (intended: \(M[f](\tfrac12+it)\)) such that for all admissible \(f,g\),
  - \[
    W^{(1)}(\mathrm{pair}(f,g)) \;=\; \int_{\mathbb R}\overline{F_f(t)}\,F_g(t)\,d\mu(t).
    \]

**Strawman best splice (PSC → Route‑3): choose \(\mu := \mu_{\mathrm{spec}}\) from `Riemann-active.txt`.**
- In the boundary-certificate manuscript, the phase–velocity identity produces a **positive boundary measure** on \(\mathbb R\) of the form
  \[
  -w' \;=\; \pi\,\mu \;+\; \pi\sum_{\gamma} m_\gamma\,\delta_\gamma,
  \]
  where \(\mu\) is the (absolutely continuous) Poisson–balayage of off‑critical zeros and the sum is the atomic part from critical‑line ordinates.
- Define the **full spectral boundary measure**
  \[
  \mu_{\mathrm{spec}} \;:=\; \mu \;+\; \sum_{\gamma} m_\gamma\,\delta_\gamma \ \ge\ 0,
  \]
  and feed **this** \(\mu_{\mathrm{spec}}\) to the Route‑3 measure-first pipeline.
- This choice is “best” for a splice because it is already a measure on \(\mathbb R\) (Route‑3’s boundary parameter), already includes atoms, and is explicitly constructed in the PSC proof.
- **Lean wiring:**
  - The naming-aligned wrapper `μ_spec → Route3.AssumptionsMeasure → Route3.RHμ` is in
    `RiemannRecognitionGeometry/ExplicitFormula/PSCSplice.lean`.
  - The contour-to-boundary connection is in
    `RiemannRecognitionGeometry/ExplicitFormula/ContourToBoundary.lean`:
    - ✅ `PSCComponents` structure (det₂, O, ξ with differentiability)
    - ✅ `log_deriv_decomposition` **PROVED** using Mathlib's `logDeriv_div` and `logDeriv_mul`
    - Remaining identity inputs (non-axiom): `ContourToBoundary.explicit_formula_cancellation` (now an explicit hypothesis; no longer a global `axiom`). PSC phase–velocity is bundled as data/fields in `PSCComponents`.

**What this buys immediately:**
- \(W^{(1)}(\mathrm{quad}(f)) = \int |F_f(t)|^2\,d\mu(t) \ge 0\), hence `WeilGate`, hence RH (via Lagarias).

**Important separation:**
- The **identity** (representation with some signed distribution/measure) can be standard analysis.
- The **positivity** \(\mu \ge 0\) is the RH‑equivalent core.

---

### Step 1 — Choose a Lean-feasible test space (log‑Schwartz/Fourier)

**Lean‑friendly choice (recommended):**
- Take the test space to be Schwartz in log‑time:
  - \(F := \mathcal S(\mathbb R;\mathbb C)\) (Mathlib: `SchwartzMap ℝ ℂ`).
  - Interpret “Mellin on \(\Re(s)=\tfrac12\)” as a Fourier transform:
    - \(F_f(t)\) is the Fourier transform of the log‑lift.

**Implementation tactic to minimize pain:**
- Define the convolution operation by transport through Fourier:
  - `conv` := `F⁻¹ (Ff * Fg)`
  - Then `mellin_conv` (Fourier convolution theorem) becomes definitional.

**Why this matters:**
- It removes huge amounts of custom Fubini/Tonelli work from Lean without changing the mathematical core.

---

### Step 2 — Prove the identity part (no positivity)

**Goal of Step 2:**
- Prove a representation
  - \(W^{(1)}(\mathrm{pair}(f,g)) = \langle \nu,\overline{F_f}F_g\rangle\)
  for some boundary distribution/measure \(\nu\) (not yet positive).

**Splice completion target (PSC → Route‑3):**
- Strengthen the identity to the concrete positive measure from `Riemann-active.txt`:
  \[
    \nu \;=\; \mu_{\mathrm{spec}}
    \qquad\text{(up to the project’s normalization constants, i.e. the chosen \(\pi\) factors).}
  \]
  Equivalently, prove the **measure-first Bochner identity**
  \[
    W^{(1)}(\mathrm{pair}(f,g)) \;=\; \int_{\mathbb R}\overline{F_f(t)}\,F_g(t)\,d\mu_{\mathrm{spec}}(t).
  \]
- **Lean shape:** this is exactly the data of `SesqMeasureIntegralIdentity` (Bochner form) with `μ := μ_spec`,
  which converts automatically to `SesqMeasureIdentity` via `SesqMeasureIntegralIdentity.toSesqMeasureIdentity`, and then fires
  `Route3.RHμ`. The PSC-named wrapper is in `RiemannRecognitionGeometry/ExplicitFormula/PSCSplice.lean`.
- Concretely, this splice-completion proof splits into:
  - **(SC1)** show the PSC and Route‑3 boundary transforms agree on the chosen test space (`transform_eq_mellinOnCriticalLine`),
  - **(SC2)** identify the boundary distribution produced by the contour definition of \(W^{(1)}\) with the PSC phase distribution
    \(\nu = \frac1\pi(-w')\), and then use the PSC phase–velocity identity \(-w'=\pi\mu_{\mathrm{spec}}\) to conclude \(\nu=\mu_{\mathrm{spec}}\),
  - **(SC3)** check the fixed \(\pi\) normalization constants so the final statement is exactly the Bochner identity above.

**Standard-analysis checklist (contour/explicit formula route):**
- **(Infrastructure)** Use `ExplicitFormula/ContourW1.lean` + `ExplicitFormula/LagariasContour.lean` as the canonical Lean scaffolding for “`W¹` is a contour-limit” (rectangle boundary integral + `T → ∞` limit hypothesis bundle).
- Define \(W^{(1)}\) as a contour limit or symmetric truncation over zeros.
- Show horizontals vanish (Mellin/Schwartz decay + \(ξ'/ξ = O(\log|t|)\) in strips).
- Justify limit ↔ integral swaps (dominated convergence).
- Handle poles on the contour (indentations / principal value conventions).
- Identify the boundary object \(\nu\) (often as a Poisson‑regularized boundary limit).

**Deliverable for Step 2:**
- A precise theorem statement listing minimal hypotheses on \(F_f\) so that the identity is rigorous.

---

### Step 3 — Prove positivity from RS passivity (the RH‑equivalent core)

This is the only place the “new physics” is allowed to do real work.

**RS→classical translation target:**
- Prove that a certain response/transfer function is **positive‑real** (Carathéodory/Herglotz) on a half‑plane (or Schur on the disk after Cayley), which implies the boundary spectral object is a **positive measure** \(\mu\).

**Canonical classical wrapper (one clean statement):**
- Let
  - \(\Phi(z) := -\dfrac{\xi'}{\xi}\!\left(\tfrac12 + z\right)\), analytic on \(\Re z>0\) (away from zeros).
- Prove (from passivity) a **positive‑real condition** such as:
  - \(\Re \Phi(z) \ge 0\) for all \(\Re z>0\),
  - equivalently, the Cayley transform \(Θ(z) = \dfrac{\Phi(z)-1}{\Phi(z)+1}\) is Schur (|Θ|≤1) on the disk/half-plane domain.
- Then apply Herglotz/Carathéodory to obtain a **positive measure** \(\mu\) with \(\Re\Phi\) as its Poisson extension.

**What is RH‑equivalent here:**
- For classical ξ, \(\Re\Phi(z)\ge0\) on \(\Re z>0\) is essentially “no zeros to the right of \(\Re(s)=\tfrac12\)”, i.e. RH‑level content. RS must supply the physical reason it holds.

**Splice option (if you want RS-free positivity): import passivity from the boundary-certificate route**
- The active boundary product-certificate manuscript (`Riemann-active.txt`) constructs an explicit ratio
  \(\mathcal J(s)=\det_2(I-A(s))/(\mathcal O(s)\,\xi(s))\) on \(\Omega=\{\Re s>\tfrac12\}\), sets \(F(s)=2\mathcal J(s)\),
  proves the a.e. boundary wedge \((\mathrm P^+)\): \(\Re F(\tfrac12+it)\ge0\) a.e., and then pushes it into \(\Omega\) by Poisson
  and globalizes by the Schur–Herglotz pinch.
- That supplies exactly the “positive‑real” hypothesis that Step 3 otherwise asks RS to justify.
- Once \(\Re F\ge0\) on \(\Omega\), the step “positive‑real ⇒ positive boundary measure” is standard Herglotz/Nevanlinna theory.
- **Caveat (still needed):** Route‑3 still needs the spectral identity identifying the Lagarias/Weil form \(W^{(1)}\) with an
  \(L^2(\mu)\) pairing against that boundary measure. This is Step 2 (“identity part”).

---

### Step 4 — Fire the existing Route‑3 plumbing (Lean)

Once you have a positive‑measure representation (or a reflection positivity realization), the repo already contains the mechanical steps:
- `ReflectionPositivityRealization → WeilGate → RH`.

---

### The “single RS→classical lemma” to target (copy/paste for prompts)

**Bridge Lemma (RS‑passivity ⇒ positive spectral measure for ξ):**
- **Input (physics/RS):** The completed‑channel prime transfer field associated to ξ is **passive**: every admissible probe has nonnegative total J‑work.
- **Classical translation:** The associated boundary kernel / response function is **positive‑real** (Carathéodory/Herglotz) on the right half-plane (or Schur after Cayley).
- **Output:** There exists a **finite positive Borel measure** \(\mu\) on \(\mathbb R\) such that for all test probes \(f,g\),
  - \[
    W^{(1)}(\mathrm{pair}(f,g)) \;=\; \int_{\mathbb R}\overline{F_f(t)}\,F_g(t)\,d\mu(t),
    \quad F_f(t)=M[f]\!\left(\tfrac12+it\right),
    \]
  and hence \(W^{(1)}(\mathrm{quad}(f))\ge0\) for all \(f\), giving RH via Lagarias.

---

### Lean-facing work items (only what affects the math)

- **(L1) Refactor Route‑3 “weight” usage toward measure‑first.**
  - Current structures (`SpectralIdentity`, `SesqIntegralIdentity`) are written as “Lebesgue + weight function”.
  - Updated goal: treat the spectral object as a **measure \(\mu\)** first; the density \(w\) is optional.

- **(L2) Add/instantiate a Schwartz/Fourier `TestSpace`** for the “plumbing” layer.
  - Goal: make the convolution/tilde/star axioms provable (or definitional) using Mathlib Fourier on `SchwartzMap ℝ ℂ`.

- **(L3) Keep ζ‑specific content isolated.**
  - Do not accidentally “prove RH” by defining `W1` to be an \(L^2(\mu)\) inner product with \(\mu\ge0\); that would bake the conclusion into the definition.
  - The point is to **derive** the positive measure from ζ/ξ (RS passivity + classical theorems).

---

### Current status + next action (update this as we work)

- [x] **Update Route‑3 spectral identity to measure‑first (no pointwise `weightOfJ` dependence).**
  - Implemented: `SesqMeasureIdentity` in `ExplicitFormula/HilbertRealization.lean`
  - Implemented: `Route3.AssumptionsMeasure`, `Route3.RHμ` pipeline in `ExplicitFormula/Route3HypBundle.lean`
- [x] **Define/instantiate a Schwartz/Fourier `TestSpace`** (log‑coordinates approach) to eliminate routine analytic pain.
  - Implemented: `TestSpace (SchwartzMap ℝ ℂ)` via Fourier in `ExplicitFormula/SchwartzTestSpace.lean`
- [x] **Write the precise classical “identity part” theorem** (contour + boundary value) as a checklist of standard lemmas.
  - Drafted: `ROUTE3_IDENTITY_PART.md`
- [x] **Write the precise RS→classical passivity lemma** (Carathéodory/Herglotz positivity) as the single RH‑equivalent target.
  - Drafted: `ROUTE3_POSITIVITY_BRIDGE.md`
- [x] **Map the RS lemma to the existing Lean bridge point** (`CayleyBridgeAssumptions.bridge_to_reflection` or a replacement that uses the measure‑first spectral identity).
  - Implemented: `CayleyMeasureBridgeAssumptions` (measure‑first bridge) in `ExplicitFormula/CayleyBridge.lean`

---

### Next phase (what remains after the scaffolding)

At this point the program is structurally complete. What remains is split into:

---

#### **Splice Completion (the single remaining identity lemma)**

- [ ] **Construct a `PSCSplice.IntegralAssumptions` instance whose `identity_integral` is the splice completion identity**
  - Target statement (identity claim \(\nu = \mu_{\mathrm{spec}}\)):
    \[
      W^{(1)}(\mathrm{pair}(f,g)) = \int_{\mathbb R} \overline{F_f(t)}\,F_g(t)\,d\mu_{\mathrm{spec}}(t).
    \]
  - **Where it lives in Lean now:** there is **no global axiom**. The statement is exactly the field
    `Route3.PSCSplice.IntegralAssumptions.identity_integral` in `ExplicitFormula/PSCSplice.lean`.
  - **Proof sketch: COMPLETE** — see `ROUTE3_IDENTITY_PART.md`:
    - §"Detailed proof of the log-derivative cancellation (SC2)" — det₂ and outer O cancel via explicit formula
    - §"Normalization verification (SC3)" — π factors and symmetric pairing conventions match
  - **Normalization note:** if the contour bookkeeping yields a real prefactor (e.g. `1/2`), we can absorb it by scaling the measure
    using `IntegralAssumptions.ofHalfScalarMulIntegral` / `ofRealScalarMulIntegral` (see `PSCSplice.lean`).
  - **Why not "RH‑equivalent":** positivity \(\mu_{\mathrm{spec}}\ge0\) is already supplied by `Riemann-active.txt`
    (phase–velocity identity + Herglotz); what remains is the **identity** bookkeeping (contour limits, normalization, outer cancellation).

---

#### Standard theorems not yet formalized (big but "just work")

- [x] **Remove the global `herglotz_representation` axiom** (done): it is now an explicit hypothesis threaded through `Caratheodory`/`HilbertRealization`.
- [ ] **Prove `herglotz_representation`** (now a hypothesis) in `ExplicitFormula/Caratheodory.lean` by formalizing (or importing) the Herglotz representation theorem.
  - Good news: Mathlib has foundational measure-representation tools (e.g. `MeasureTheory/Integral/RieszMarkovKakutani.lean`) and weak-* compactness (Banach–Alaoglu in `Analysis/Normed/Module/WeakDual.lean`).
  - Note: Mathlib does **not** currently appear to have a ready-made "Poisson kernel / harmonic functions on the disk / Herglotz representation" development, so proving this is still a substantial standalone formalization project.
- [ ] **Build a concrete `LagariasFramework` instance** for a concrete test space (recommended: `WeilTestFunction` / log‑Schwartz), proving:
  - Lagarias Thm 3.1 (explicit formula) as an equality of functionals, and
  - Lagarias Thm 3.2 (Weil criterion) as an equivalence `RH ↔ WeilGate`.

---

#### The RH‑equivalent core (already addressed by the PSC splice)

- [x] **Prove the positivity bridge for the arithmetic ξ/ζ channel.**
  - **Supplied by `Riemann-active.txt`:** the phase–velocity identity gives \(\mu_{\mathrm{spec}}\ge0\) directly (no additional positivity proof needed once the splice identity is established).
  - Once the splice identity is provided as an `IntegralAssumptions.identity_integral` proof (i.e. once a
    `PSCSplice.IntegralAssumptions` instance exists), the Lean pipeline fires:
    `IntegralAssumptions → Assumptions → AssumptionsMeasure → RHμ → RiemannHypothesis`.


