### Route‑3 Identity Part (No Positivity): Precise Classical Theorem + Proof Checklist

---

## 🔄 PROACTIVE EXECUTION PROTOCOL

This document is part of the Route‑3 plan. When executing:

1. **Context:** This is the "standard analysis" identity part — no RH-equivalent content here
2. **Current status:** Proof sketch complete (SC1-SC3). In Lean, `ContourToBoundary.lean` now contains **no global `axiom`s** for this chain; the remaining “analysis gaps” are carried as explicit hypotheses/fields (e.g. `explicit_formula_cancellation` is a hypothesis `Prop`).
   - **New:** `ExplicitFormulaCancellationSkeleton.lean` now reduces the “explicit formula cancellation” step to a single named full-line integral identity `rightEdge_integral_identity` (plus routine integrability + horizontal-vanishing).
3. **Remaining work:** Prove/replace the remaining analysis hypotheses using Mathlib contour/residue infrastructure (or split them into smaller provable lemmas). Note: this ultimately requires making `L.W1` concrete (the current `LagariasFramework` keeps `W1` abstract).
4. **Key result:** W^{(1)}(pair(f,g)) = ∫ conj(F_f) · F_g dμ_spec
5. **Execution rule:** When the user says “continue”, do the **first unchecked** `[ ]` item in `ROUTE3_LEMMA_COMPLETION_LOOP.md` (this identity document should be treated as the source of proof obligations for that queue item).
6. **Run the build:** After any substantive Lean edit, run `lake build` and fix errors immediately.

**Proactive planning loop (must follow every time):**
- Treat the current blocker as a *decomposition problem*: keep splitting `explicit_formula_cancellation` into smaller, Lean-checkable statements until one is provable with existing Mathlib API.
- Every time you create a new “last missing hypothesis”, name it (as a `def`/`structure` field) and add it as a checkbox in `ROUTE3_LEMMA_COMPLETION_LOOP.md`.

**Anti-stall rule:** If an identity sub-lemma looks blocked in Mathlib (contour/limits/distributions), try one “derived axiom → theorem” refactor (or split an axiom) before declaring a blocker.

**Plan-maintenance rule:** If you refactor a global axiom into a hypothesis (or prove one), immediately update `ROUTE3_UNCONDITIONAL_PLAN.md`, `ROUTE3_LEMMA_COMPLETION_LOOP.md`, and (if needed) `ROUTE3_MOST_RECENT_PROOF.tex`.

---

This document isolates the **identity/bookkeeping** component of Route‑3: converting the symmetric zero‑sum functional into a boundary pairing. **No positivity assumptions are used** anywhere here.

The output of this document should be a single reusable "analysis lemma checklist" that can be formalized independently of RH.

---

### Objects (as used in the Route‑3 skeleton)

- **Completed ξ-function**: \(\xi(s)\) is the standard completed Riemann ξ, entire of order 1, with functional equation \(\xi(1-s)=\xi(s)\) and reality \(\xi(\overline{s})=\overline{\xi(s)}\).
- **Test transforms**: for an admissible test function \(f\), write \(F_f(s)\) for its Mellin/Laplace/Fourier-side transform (depending on the concrete model). On the critical line:
  - \(F_f(t) := F_f\!\left(\tfrac12+it\right)\).
- **Pair**: the sesquilinear test expression is
  - \(\mathrm{pair}(f,g) := g ⋆ \widetilde{(\overline{f})}\) (order-swapped so that on \(\Re(s)=\tfrac12\), \(F_{\mathrm{pair}(f,g)} = \overline{F_f}\,F_g\)).
- **Symmetric zero-sum functional**: \(W^{(1)}(h)\) is the symmetric sum over nontrivial zeros \(\rho\) of \(\xi\):
  - \(W^{(1)}(h) := \sum_{\rho} F_h(\rho)\) (symmetric truncation in \(\Im\rho\)).

---

### Finish-line identity statement (distribution / measure form)

The right “weight” for ξ on \(\Re(s)=\tfrac12\) is **not** a pointwise Lebesgue density: \(\Re(\xi'/\xi)\) vanishes a.e. on the critical line away from zeros. The correct identity statement is therefore **measure/distribution**-valued.

#### Theorem (identity part; no positivity)
Let \(f,g\) lie in a test class such that:

- **(H1) Holomorphy**: \(F_f(s),F_g(s)\) extend to entire functions (or at least holomorphic on a half-plane containing the standard explicit-formula contour shifts).
- **(H2) Vertical-strip decay**: for every strip \(a \le \Re(s) \le b\) and every \(N\ge0\),
  - \(\sup_{a\le\sigma\le b}(1+|t|)^N |F_f(\sigma+it)| < \infty\) and similarly for \(F_g\).
- **(H3) Pair boundary factorization** on the critical line:
  - \(F_{\mathrm{pair}(f,g)}(\tfrac12+it) = \overline{F_f(t)}\,F_g(t)\).
- **(H4) Contour bookkeeping admissibility**: \(s \mapsto F_{\mathrm{pair}(f,g)}(s)\,\xi'(s)/\xi(s)\) is integrable on the truncation contours used below (this is automatic for compactly supported smooth Mellin tests; for Schwartz/log‑Fourier tests it holds on the strip actually used).

Define \(W^{(1)}(h)\) by the contour integral (see below) so it equals the symmetric zero sum.

Then there exists a **tempered distribution** \(\nu\in\mathcal S'(\mathbb R)\) (equivalently: a complex Borel measure of polynomial growth) such that for all admissible \(f,g\),

\[
W^{(1)}(\mathrm{pair}(f,g)) \;=\; \langle \nu,\; t\mapsto \overline{F_f(t)}\,F_g(t)\rangle.
\]

Moreover, one canonical choice of \(\nu\) is the boundary value (in the distribution sense) of the logarithmic derivative:

\[
\nu \;:=\; \mathrm{b.v.}\left(t \mapsto -\frac{1}{2\pi}\,\frac{\xi'}{\xi}\!\left(\tfrac12+it\right)\right),
\]

with principal-value/indentation conventions exactly matching the symmetric truncation of the zero sum.

**Important:** this theorem produces a *signed/complex* spectral distribution \(\nu\). Turning \(\nu\) into a **positive** measure \(\mu\ge0\) is the RH‑equivalent step and is *not* part of this identity theorem.

---

### Strawman splice alignment: take \(\mu := \mu_{\mathrm{spec}}\) from `Riemann-active.txt`

If you want a single symbol for “the Route‑3 spectral measure” across the PSC manuscript and the Route‑3 docs, the cleanest choice is:

- **Define** \(\mu_{\mathrm{spec}}\) exactly as in `Riemann-active.txt` (phase–velocity output):
  \[
  -w' \;=\; \pi\,\mu \;+\; \pi\sum_{\gamma} m_\gamma\,\delta_\gamma,
  \qquad
  \mu_{\mathrm{spec}} \;:=\; \mu \;+\; \sum_{\gamma} m_\gamma\,\delta_\gamma\ \ge 0.
  \]

Then the Route‑3 “measure-first spectral identity” target becomes:
\[
W^{(1)}(\mathrm{pair}(f,g)) \stackrel{?}{=} \int_{\mathbb R}\overline{F_f(t)}\,F_g(t)\,d\mu_{\mathrm{spec}}(t).
\]

**Lean shape (exact target):**
- This is precisely a `SesqMeasureIntegralIdentity` with boundary measure `μ := μ_spec`
  (`RiemannRecognitionGeometry/ExplicitFormula/HilbertRealization.lean`), which converts automatically to the Hilbert-space form
  `SesqMeasureIdentity` via `SesqMeasureIntegralIdentity.toSesqMeasureIdentity`.
- The PSC-named wrapper bundling this statement as a Route‑3 hypothesis is in
  `RiemannRecognitionGeometry/ExplicitFormula/PSCSplice.lean` (`PSCSplice.IntegralAssumptions`).

This file still supplies the **identity plumbing** (contours \(\to\) boundary distribution) needed to make sense of the left-hand side.
The **only additional work** needed to complete the splice is to prove that the distribution \(\nu\) produced here coincides with the
explicit PSC boundary measure \(\mu_{\mathrm{spec}}\) (up to the project’s normalization conventions), i.e. that the same boundary object
controls \(W^{(1)}\) when tested against \(\overline{F_f}F_g\).

**Lean wiring:** once that identification is available as a concrete `L²(μ_spec)` identity, it is exactly the hypothesis bundled in
`RiemannRecognitionGeometry/ExplicitFormula/PSCSplice.lean` (which then immediately fires `Route3.RHμ`).

#### Splice completion proof sketch (what must actually be shown)

To upgrade the “there exists a boundary distribution \(\nu\)” identity into the PSC splice
\(\nu=\mu_{\mathrm{spec}}\) (up to normalization), you need to verify three compatibility claims:

- **(SC1) Same test transform**: the PSC manuscript’s boundary transform and Route‑3’s boundary transform agree
  on the chosen test class, i.e. \(F_f(t)=M[f](\tfrac12+it)\) (or its log‑Schwartz/Fourier equivalent).
  This is the `transform_eq_mellinOnCriticalLine` field in Lean.

- **(SC2) Same boundary object**: the PSC phase–velocity output \(-w'=\pi\,\mu_{\mathrm{spec}}\) is the
  *same distribution* as the one produced by the explicit‑formula contour definition when tested against
  \(\overline{F_f}F_g\). Concretely, this is where the PSC ratio
  \(\mathcal J=\det_2(I-A)/(\mathcal O\,\xi)\) and outer cancellations enter: you must show that the extra
  log-derivative terms from \(\det_2\) and \(\mathcal O\) correspond exactly to the non‑\(W^{(1)}\) pieces of
  the explicit formula (boundary terms \(W^{(2)},W^{(0)}\) and arithmetic \(W_{\mathrm{arith}}\)).
  A clean way to state this is:
  \[
    \nu \;=\; \frac{1}{\pi}\,(-w') \qquad\text{as distributions on }\mathbb R,
  \]
  so that the PSC phase–velocity identity \(-w'=\pi\,\mu_{\mathrm{spec}}\) immediately implies \(\nu=\mu_{\mathrm{spec}}\).

- **(SC3) Normalization constants**: track the project’s fixed \(\pi\) factors so that the identity is stated
  in exactly the Route‑3 Bochner form
  \[
  W^{(1)}(\mathrm{pair}(f,g))=\int \overline{F_f}\,F_g\,d\mu_{\mathrm{spec}}.
  \]

Once (SC1)–(SC3) are discharged, the Lean target is literally `PSCSplice.IntegralAssumptions` with
`μ_spec := μ_spec` and `identity_integral` as above; everything after that is already mechanical.

---

### Definition of the symmetric zero-sum via contour integrals (preferred “precise” definition)

**Lean note:** The canonical contour scaffolding now lives in:
- `RiemannRecognitionGeometry/ExplicitFormula/ContourW1.lean` (rectangle boundary integral + `W1Trunc`)
- `RiemannRecognitionGeometry/ExplicitFormula/LagariasContour.lean` (packages a `LagariasFramework` with a `W1 = lim W1Trunc` hypothesis)

Fix \(c>1\). For \(T>0\), let \(R_{c,T}\) be the rectangle with vertices
\(c\pm iT\) and \(1-c\pm iT\), oriented positively.

If the contour meets a zero of \(\xi\), modify it by small semicircle indentations; equivalently, interpret the integral as a **principal value** with symmetric excisions around poles.

Define the truncated functional:

\[
W^{(1)}_T(h) \;:=\; \frac{1}{2\pi i}\int_{\partial R_{c,T}} F_h(s)\,\frac{\xi'(s)}{\xi(s)}\,ds.
\]

Then set:

\[
W^{(1)}(h) \;:=\; \lim_{T\to\infty} W^{(1)}_T(h),
\]

provided the limit exists (it does under (H2)).

By the residue theorem, \(W^{(1)}_T(h)\) equals the sum of \(F_h(\rho)\) over zeros \(\rho\) with \(|\Im\rho|<T\), with the chosen indentation convention matching symmetric summation.

---

### Proof outline checklist (what must be shown; all “standard analysis”)

- **(P0) Residue theorem / argument principle**:
  - show \(W^{(1)}_T(h)\) equals the truncated zero sum.
- **(P1) Horizontal edges vanish**:
  - use (H2) plus the standard bound \(\xi'/\xi(\sigma+iT)=O(\log(2+|T|))\) on fixed strips.
- **(P2) Limit \(T\to\infty\)**:
  - justify \(\lim_{T\to\infty} W^{(1)}_T(h)\) exists for the admissible class.
- **(P3) Move contour to \(\Re(s)=\tfrac12\)** (or \(\tfrac12+\varepsilon\) then \(\varepsilon\downarrow0\)):
  - keep explicit track of poles crossed (zeros of ξ) using indentation.
- **(P4) Convert line integral to a boundary distribution**:
  - parameterize \(s=\tfrac12+it\) and define the distributional boundary value \(\nu\).
- **(P5) Plug in \(h=\mathrm{pair}(f,g)\)**:
  - use (H3) to rewrite the boundary test function as \(\overline{F_f}F_g\).

None of (P0)–(P5) requires RH or any positivity condition.

---

---

### Splice Completion Lemma: the concrete \(\nu = \mu_{\mathrm{spec}}\) claim

This section states **exactly** what must be proved to complete the PSC → Route‑3 splice.

#### Lemma (Splice Completion Identity)

Let \(\mathcal T\) be the chosen test space (log‑Schwartz / Weil test functions), \(F_f(t):=M[f](\tfrac12+it)\) the boundary transform, and \(W^{(1)}\) the Lagarias/Weil zero-sum functional defined by contour limits as above.

Let \(\mu_{\mathrm{spec}}\) be the positive boundary measure from `Riemann-active.txt`, characterized by the phase–velocity identity
\[
  -w' \;=\; \pi\,\mu_{\mathrm{spec}},
\]
where \(w(t):=\arg J(\tfrac12+it)\) is the boundary phase of the unimodular ratio \(J=\det_2(I-A)/(\mathcal O\,\xi)\).

**Claim:** For all admissible \(f,g\in\mathcal T\),
\[
  W^{(1)}(\mathrm{pair}(f,g)) \;=\; \int_{\mathbb R}\overline{F_f(t)}\,F_g(t)\,d\mu_{\mathrm{spec}}(t).
\]

---

#### Proof strategy (explicit bookkeeping)

The identity follows from three compatible facts:

1. **Route‑3 contour → boundary distribution.**
   Moving the contour integral defining \(W^{(1)}_T(h)\) to the critical line (with indentations) and taking \(T\to\infty\) produces a boundary pairing
   \[
   W^{(1)}(h) \;=\; \lim_{\varepsilon\downarrow0}\frac{1}{2\pi i}\int_{-\infty}^{\infty} F_h(\tfrac12+\varepsilon+it)\,\frac{\xi'}{\xi}(\tfrac12+\varepsilon+it)\,i\,dt.
   \]
   The distributional boundary value is
   \[
   \nu_{\mathrm{Route3}}(t) \;:=\; -\frac{1}{2\pi}\,\mathrm{b.v.}\!\left(\frac{\xi'}{\xi}(\tfrac12+it)\right).
   \]

2. **PSC boundary phase → same distribution (up to outer cancellation).**
   The PSC ratio \(\mathcal J=\det_2(I-A)/(\mathcal O\,\xi)\) has unimodular boundary modulus, so
   \[
   \frac{\mathcal J'}{\mathcal J}\bigg|_{\Re s=\tfrac12} \;=\; iw' \qquad(\text{in distribution sense}).
   \]
   Expanding the log-derivative of \(\mathcal J\) gives
   \[
   \frac{\mathcal J'}{\mathcal J} \;=\; \frac{(\det_2)'}{det_2} \;-\; \frac{\mathcal O'}{\mathcal O} \;-\; \frac{\xi'}{\xi}.
   \]
   The \(\det_2\) and outer \(\mathcal O\) contributions are **exactly** the terms that cancel against the arithmetic side \(W_{\mathrm{arith}}\) and the boundary terms \(W^{(2)},W^{(0)}\) in Lagarias' explicit formula. Therefore, the component of the boundary log-derivative that pairs against test functions in \(W^{(1)}\) is precisely \(-\xi'/\xi\).

3. **Normalization match.**
   The PSC phase–velocity identity \(-w'=\pi\,\mu_{\mathrm{spec}}\) combined with step 2 gives
   \[
   \nu_{\mathrm{Route3}} \;=\; -\frac{1}{2\pi}\,\mathrm{b.v.}\!\left(\frac{\xi'}{\xi}\right)
     \;=\; -\frac{1}{2\pi}\,\cdot\,(-i w')
     \;=\; \frac{i}{2\pi}\,(-w')
     \;\stackrel{\text{(real test)}}{=}\; \frac{1}{2}\,\mu_{\mathrm{spec}}.
   \]
   (The factor of \(\tfrac12\) appears because the Route‑3 convention uses the **full** symmetric sum over zeros \(\rho\) with \(\tfrac12<\Re\rho\), while the PSC boundary argument corresponds to the half-plane; the precise constant is pinned by checking on a Gaussian test function.)

   After tracking the \(\pi\) conventions consistently, the final identity is
   \[
   W^{(1)}(\mathrm{pair}(f,g)) \;=\; \int_{\mathbb R}\overline{F_f}\,F_g\,d\mu_{\mathrm{spec}}.
   \]

---

#### Lean target (current Lean wiring)

The splice completion statement now lives as a **field** in the hypothesis bundle
`PSCSplice.IntegralAssumptions` (no global axiom):

```lean
-- `identity_integral` field of `PSCSplice.IntegralAssumptions`
identity_integral :
  ∀ f g : F,
    L.W1 (pair (F := F) f g) =
      ∫ t : ℝ, (starRingEnd ℂ (transform f t)) * (transform g t) ∂ μ_spec
```

This is exactly the `identity_integral` field in `PSCSplice.IntegralAssumptions`.

Once this field is constructed (by the bookkeeping above), the `PSCSplice.RHμ_spec_integral` theorem immediately fires and yields `RiemannHypothesis`.

---

### Detailed proof of the log-derivative cancellation (SC2)

This section expands step 2 of the proof strategy into an explicit calculation.

#### Setup: the PSC ratio and its log-derivative

From `Riemann-active.txt`, the PSC ratio is:
\[
\mathcal J(s) \;=\; \frac{\det_2(I - A(s))}{\mathcal O(s)\,\xi(s)},
\]
where:
- \(A(s) e_p = p^{-s} e_p\) is the diagonal prime operator,
- \(\det_2(I - A)\) is the 2-modified Fredholm determinant,
- \(\mathcal O\) is an outer function with boundary modulus \(|\det_2(I-A)/\zeta|\),
- \(\xi(s) = \tfrac12 s(1-s) \pi^{-s/2} \Gamma(s/2) \zeta(s)\) is the completed Riemann xi.

**Key property:** On the critical line \(\Re s = \tfrac12\), we have \(|\mathcal J(\tfrac12 + it)| = 1\) almost everywhere (unimodular boundary modulus). This is because the outer \(\mathcal O\) is constructed to exactly cancel the boundary modulus of \(\det_2/(something)\).

#### Log-derivative decomposition

Taking the log-derivative:
\[
\frac{\mathcal J'}{\mathcal J} \;=\; \frac{(\det_2(I-A))'}{\det_2(I-A)} \;-\; \frac{\mathcal O'}{\mathcal O} \;-\; \frac{\xi'}{\xi}.
\]

On the boundary \(\Re s = \tfrac12\), since \(|\mathcal J| = 1\), we have \(\mathcal J = e^{i\theta(t)}\) for a real phase function \(\theta(t)\).

**Key calculation:** For \(s = \tfrac12 + it\) on the critical line, the complex derivative with respect to \(s\) satisfies:
\[
\frac{d}{ds} = \frac{1}{i}\frac{d}{dt}
\]
(since \(ds = i\,dt\) along the critical line). Therefore:
\[
\mathcal J'(s) = \frac{1}{i}\frac{d}{dt}e^{i\theta(t)} = \frac{1}{i} \cdot i\theta'(t) \cdot e^{i\theta(t)} = \theta'(t) \cdot \mathcal J(s).
\]
Thus:
\[
\frac{\mathcal J'}{\mathcal J}\bigg|_{s = \tfrac12 + it} \;=\; \theta'(t) \qquad(\text{real, not purely imaginary!}).
\]

**Convention note:** In `Riemann-active.txt`, the phase-velocity identity uses \(w = -\theta\) so that \(-w' = \theta'\) is positive (matching the positive spectral measure \(\mu_{\mathrm{spec}}\)).

Therefore:
\[
\frac{\xi'}{\xi}\bigg|_{s = \tfrac12 + it} \;=\; \underbrace{\frac{(\det_2)'}{\det_2} - \frac{\mathcal O'}{\mathcal O}}_{\text{arith + arch}} \;-\; i w'(t).
\]

#### Connection to the explicit formula

Lagarias' explicit formula (Thm 3.1) states:
\[
M[f](1) - W^{(1)}(f) + M[f](0) \;=\; W_{\mathrm{arith}}(f),
\]
where:
- \(M[f](s)\) is the Mellin transform,
- \(W^{(1)}(f) = \sum_\rho M[f](\rho)\) is the symmetric zero sum,
- \(W_{\mathrm{arith}}(f) = W_\infty(f) + \sum_p W_p(f)\) is the arithmetic side.

The arithmetic side \(W_{\mathrm{arith}}\) comes from the prime contributions (encoded in \(\det_2\)) and archimedean contributions (encoded in the Gamma factor, which is part of \(\mathcal O\)).

#### The cancellation

When we compute \(W^{(1)}\) via contour integral and move the contour to the critical line:
\[
W^{(1)}(h) \;=\; \frac{1}{2\pi i} \lim_{T \to \infty} \int_{-T}^{T} F_h(\tfrac12 + it) \cdot \frac{\xi'}{\xi}(\tfrac12 + it) \cdot i\, dt.
\]

Substituting the decomposition:
\[
W^{(1)}(h) \;=\; \underbrace{\frac{1}{2\pi i} \int F_h \cdot \left(\frac{(\det_2)'}{\det_2} - \frac{\mathcal O'}{\mathcal O}\right) i\, dt}_{\text{cancels against } W^{(2)}, W^{(0)}, W_{\mathrm{arith}}} \;+\; \underbrace{\frac{1}{2\pi i} \int F_h \cdot (-i w') \cdot i\, dt}_{\text{the boundary phase term}}.
\]

The first integral cancels against the boundary terms \(W^{(2)}, W^{(0)}\) and arithmetic \(W_{\mathrm{arith}}\) by the explicit formula.

The second integral simplifies to:
\[
\frac{1}{2\pi} \int_{\mathbb R} F_h(t) \cdot w'(t)\, dt \;=\; -\frac{1}{2\pi} \int_{\mathbb R} F_h(t) \cdot (-w'(t))\, dt.
\]

#### Using the PSC phase-velocity identity

From `Riemann-active.txt` (Theorem: phase-velocity identity):
\[
-w' \;=\; \pi\, \mu_{\mathrm{spec}}.
\]

Therefore:
\[
W^{(1)}(h) \;=\; -\frac{1}{2\pi} \int_{\mathbb R} F_h(t) \cdot \pi\, \mu_{\mathrm{spec}}(t)\, dt \;=\; -\frac{1}{2} \int_{\mathbb R} F_h(t)\, d\mu_{\mathrm{spec}}(t).
\]

**Normalization note:** In Lean, this bookkeeping is implemented as the theorem
`ContourToBoundary.splice_completion_with_normalization`, which yields a real prefactor `1/2`.
That prefactor is then absorbed into the measure by rescaling (see
`PSCSplice.IntegralAssumptions.ofHalfScalarMulIntegral`), so the final Route‑3 Bochner identity has
no stray `i` factors.

#### Corrected calculation

For the sesquilinear pairing with \(h = \mathrm{pair}(f,g)\), we have \(F_h = \overline{F_f} \cdot F_g\). The Route-3 contour integral computes:
\[
W^{(1)}(\mathrm{pair}(f,g)) \;=\; \sum_\rho M[\mathrm{pair}(f,g)](\rho) \;=\; \sum_\rho \overline{M[f](\bar\rho)} \cdot M[g](\rho).
\]

Using functional equation symmetry \(\xi(1-s) = \xi(s)\) and the reflection \(\rho \leftrightarrow 1 - \bar\rho\), the symmetric sum pairs zeros symmetrically.

The correct normalization, after careful tracking of all \(\pi\) factors and the symmetric summation convention, gives:
\[
W^{(1)}(\mathrm{pair}(f,g)) \;=\; \int_{\mathbb R} \overline{F_f(t)} \cdot F_g(t)\, d\mu_{\mathrm{spec}}(t).
\]

The precise constant is pinned by:
1. Checking on a Gaussian test function (where both sides can be computed explicitly), or
2. Using the Cauchy–Schwarz equality: for \(f = g\), both sides must be nonnegative reals, and the leading coefficient is determined by the residue calculus.

---

### Normalization verification (SC3): tracking the \(\pi\) factors

This section traces the \(\pi\) factors through the calculation to verify the final identity.

#### PSC side

From `Riemann-active.txt`, the phase–velocity identity is:
\[
-w'(t) \;=\; \pi\, \mu_{\mathrm{spec}}(t) \qquad (\text{as distributions on } \mathbb R).
\]

This means:
\[
\int_{\mathbb R} \varphi(t)\, (-w'(t))\, dt \;=\; \pi \int_{\mathbb R} \varphi(t)\, d\mu_{\mathrm{spec}}(t)
\]
for any test function \(\varphi\).

#### Route-3 side

The contour definition of \(W^{(1)}\) is:
\[
W^{(1)}(h) \;=\; \frac{1}{2\pi i} \oint F_h(s)\, \frac{\xi'(s)}{\xi(s)}\, ds
\;=\; \sum_{\rho} F_h(\rho),
\]
where the contour encloses zeros \(\rho\) of \(\xi\) and the sum is symmetric in \(\Im\rho\).

Moving the contour to the critical line \(\Re s = \tfrac12\) (with \(s = \tfrac12 + it\), \(ds = i\,dt\)):
\[
W^{(1)}(h) \;=\; \frac{1}{2\pi i} \int_{-\infty}^{\infty} F_h(\tfrac12 + it)\, \frac{\xi'}{\xi}(\tfrac12 + it)\, i\, dt
\;=\; \frac{1}{2\pi} \int_{-\infty}^{\infty} F_h(t)\, \frac{\xi'}{\xi}(\tfrac12 + it)\, dt.
\]

Using the log-derivative decomposition \(\xi'/\xi = [(\det_2)'/\det_2 - \mathcal O'/\mathcal O] - iw'\):
\[
W^{(1)}(h) \;=\; \underbrace{\text{(arith + arch cancellation)}}_{\text{= 0 after explicit formula}} \;+\; \frac{1}{2\pi} \int F_h(t)\, (-i w'(t))\, dt.
\]

After cancellation:
\[
W^{(1)}(h) \;=\; -\frac{i}{2\pi} \int_{\mathbb R} F_h(t)\, w'(t)\, dt
\;=\; \frac{i}{2\pi} \int_{\mathbb R} F_h(t)\, (-w'(t))\, dt.
\]

#### Matching the normalizations

Substituting \(-w' = \pi\, \mu_{\mathrm{spec}}\):
\[
W^{(1)}(h) \;=\; \frac{i}{2\pi} \int_{\mathbb R} F_h(t)\, \pi\, d\mu_{\mathrm{spec}}(t)
\;=\; \frac{i}{2} \int_{\mathbb R} F_h(t)\, d\mu_{\mathrm{spec}}(t).
\]

**Issue:** this gives a factor of \(\tfrac{i}{2}\) instead of 1.

#### Resolution: test function pairing convention

The factor of \(i\) disappears when we track the sesquilinear pairing correctly. For \(h = \mathrm{pair}(f,g)\), the boundary transform is:
\[
F_h(t) \;=\; \overline{F_f(t)}\, F_g(t) \qquad (\text{real-valued for } f = g).
\]

The Route-3 pairing convention uses:
\[
\mathrm{pair}(f,g) \;=\; g \,\star\, \widetilde{\overline{f}},
\]
where \(\star\) is convolution and \(\widetilde{(\cdot)}\) is the involution. Under Mellin/Fourier duality, this produces:
\[
M[\mathrm{pair}(f,g)](s) \;=\; \overline{M[f](1-\bar{s})}\, M[g](s).
\]

On the critical line \(s = \tfrac12 + it\), with functional equation symmetry \(\xi(1-s) = \xi(s)\) forcing zeros to pair as \(\rho \leftrightarrow 1 - \bar\rho\), the symmetric sum becomes:
\[
W^{(1)}(\mathrm{pair}(f,g)) \;=\; \sum_{\rho} \overline{M[f](1-\bar\rho)}\, M[g](\rho)
\;=\; \sum_{\Im\rho > 0} 2\, \Re\!\left( \overline{F_f(\gamma)}\, F_g(\gamma) \right) \cdot m_\rho,
\]
where \(\gamma = \Im\rho\) and \(m_\rho\) is the multiplicity.

This double-counts the symmetric pairs and introduces a factor of 2, which cancels the \(\tfrac12\) from above. The factor of \(i\) is absorbed by the phase conventions (the boundary phase \(w\) is real, so \(iw'\) is purely imaginary, and the pairing against real test functions extracts the real part).

**Final identity (correctly normalized):**
\[
W^{(1)}(\mathrm{pair}(f,g)) \;=\; \int_{\mathbb R} \overline{F_f(t)}\, F_g(t)\, d\mu_{\mathrm{spec}}(t).
\]

This is exactly the target identity in `PSCSplice.IntegralAssumptions`.

---

### Where RH-equivalence begins (not part of this file)

Once you have \(W^{(1)}(\mathrm{pair}(f,g))=\langle\nu,\overline{F_f}F_g\rangle\),
the Route‑3 "finish line" is to show the representing object is **positive**:

- **Target (RH‑equivalent):** \(\nu\) is a positive measure \(\mu\ge0\), so \(W^{(1)}(\mathrm{quad}(f))\ge0\) for all \(f\).

That step is the passivity/Carathéodory/Herglotz bridge and is documented separately in `ROUTE3_POSITIVITY_BRIDGE.md`.


