# Route 3 Parallel Work Tracks

This document defines three parallel tracks for completing the Route 3 Riemann Hypothesis formalization.

**Instructions for the User:**
To start a session on a specific track:
1. Open a new chat window.
2. Paste this entire document (or just the "Universal Context" and the specific "Track" section you are assigning).
3. Add the prompt: **"I am assigning you to Track [X]. Please read the instructions below, analyze the current state of the listed files, and propose the first step."**

---

## Universal Context (Read this first)

We are formalizing a proof of the Riemann Hypothesis using the **Route 3 (Lagarias/Weil/Li)** strategy.
The codebase is currently a **compiling implication skeleton**.
- We have proved `Assumptions → RiemannHypothesis`.
- The "Assumptions" are currently packaged as Lean structures or axioms.
- **Your goal is to discharge these assumptions (turn axioms/sorry into proofs) without breaking the build.**

**Global Constraints:**
1. **Do not break downstream compilation.** If you modify a definition, ensure `lake build` still passes for the whole project.
2. **Prefer Mathlib.** Use existing Mathlib theorems whenever possible. If a major theorem is missing, isolate it as a clean lemma rather than mixing it into the main logic.
3. **Keep changes localized.** Work only within the files listed for your track unless absolutely necessary.

---

## Track 1: Analytic Closure of Test Functions

**Goal:** Provide proofs for the algebraic and analytic closure properties of the `WeilTestFunction` space. Currently, `WeilTestFunction.lean` contains `axiom` declarations for convolution, reflection, and their Mellin transform identities.

**Target File:**
- `RiemannRecognitionGeometry/ExplicitFormula/WeilTestFunction.lean`

**Key Tasks:**
1. **Convolution Closure:** Prove that the multiplicative convolution of two Schwartz functions with exponential decay also has exponential decay.
2. **Reflection/Conjugation:** Prove closure under $f(x) \mapsto f(-x)$ and conjugation (trivial but needs formal proofs).
3. **Transform Identities:** Prove the "Convolution Theorem" for the `weilTransform` (Mellin transform):
   $$ \mathcal{M}(f \star g)(s) = \mathcal{M}(f)(s) \cdot \mathcal{M}(g)(s) $$
   This requires justifying Fubini's theorem using the decay bounds.

**Resources/Hints:**
- Use `Mathlib.Analysis.Distribution.SchwartzSpace`.
- Use `Mathlib.Analysis.MellinTransform`.
- The decay condition is `‖f(x)‖ ≤ C * exp(-(1/2 + ε)|x|)`.

**Constraint:**
- You must replace the `axiom` declarations in `WeilTestFunction.lean` with `def` (for data) and `theorem` (for props).

---

## Track 2: The Spectral Identity & Interchanges

**Goal:** Instantiate the `Route3.Assumptions` structure with the concrete Arithmetic `J` function. This involves proving the "Spectral Identity" (Plancherel for the explicit formula) and justifying all integral/sum interchanges.

**Target Files:**
- `RiemannRecognitionGeometry/ExplicitFormula/Route3HypBundle.lean` (Main wiring)
- `RiemannRecognitionGeometry/ExplicitFormula/Route3FubiniTonelliLemmas.lean` (Specific interchange lemmas)
- `RiemannRecognitionGeometry/ExplicitFormula/ArithmeticJ.lean` (Definition of `J`)

**Key Tasks:**
1. **Normalization Match:** Prove that the explicit formula sum $\sum_\rho$ equals the contour integral over the critical line for our specific $J(s) = -\zeta'(s)/\zeta(s)$.
2. **Fubini/Tonelli:** Prove the `integrable_*` and `summable_*` fields in `Route3FubiniTonelliObligations`. This requires establishing bounds on $\zeta'/\zeta$ on vertical lines (e.g., $\ll \log|t|$).
3. **Boundary Limits:** Handle the shift from $\sigma > 1$ to $\sigma = 1/2$.

**Resources/Hints:**
- `ArithmeticJ.lean` defines `J`.
- You will need heavy analytic number theory estimates (standard zero-density or log-derivative bounds).
- If a bound is missing in Mathlib, declare it as a focused Lemma in a new file (e.g., `ZetaBounds.lean`) and use it.

**Constraint:**
- The structure `Route3.Assumptions` in `Route3HypBundle.lean` is the "final boss". Instantiating this without sorry completes the proof.

---

## Track 3: Carathéodory / Herglotz Representation

**Goal:** Eliminate the `caratheodory_positive_definite` axiom in `HilbertRealization.lean`.

**Target File:**
- `RiemannRecognitionGeometry/ExplicitFormula/HilbertRealization.lean`

**Key Tasks:**
1. **Formalize Carathéodory's Theorem:**
   "If $F(z)$ is analytic in the unit disk with $\text{Re}(F(z)) \ge 0$, then the kernel $K(z,w) = \frac{F(z) + \overline{F(w)}}{1 - z\overline{w}}$ is positive definite."
2. **Or Formalize Herglotz Representation:**
   "If $F$ has positive real part, it can be represented as an integral against a positive measure." (This implies the kernel property).

**Resources/Hints:**
- This is purely Complex Analysis (no Number Theory).
- Look for "Herglotz representation theorem" or "Positive functions on the disk".
- Mathlib has `Analysis.Complex.Basic` and some reproducing kernel Hilbert space machinery, but this specific theorem might need to be built.

**Constraint:**
- You can move this theorem to a separate file (e.g., `Mathlib/Analysis/Complex/Caratheodory.lean` inside the project) if it grows large, but it must be called by `HilbertRealization.lean`.
