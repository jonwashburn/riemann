# Route 3: Status and Strategy Report

**Date:** December 13, 2025
**Topic:** Unconditional Proof Strategy via Weil Explicit Formula (Route 3)

## 1. Executive Summary

We have successfully transitioned the proof attempt from an abstract skeleton to a **concrete, mechanically-checkable framework** in Lean 4.
- **Completed:** The "Test Space" is no longer abstract. We have implemented `WeilTestFunction` (Schwartz functions with exponential decay) and `WeilFunctionals` (defining `Warith` as the geometric side of the Explicit Formula).
- **Verified:** The codebase builds (`lake build`), confirming the type-correctness of our definitions.
- **Discovered:** A review of `jonwashburn/riemann` revealed substantial existing infrastructure (`SelbergClass.lean`, `Cayley.lean`) that can be directly leveraged.

**The sole remaining bottleneck is the "Weil Gate":** Proving that the arithmetic functional is positive-definite:
Warith(f * ~f) >= 0
This statement is equivalent to the Riemann Hypothesis.

---

## 2. Technical Implementation Status

### New Lean Modules
- `ExplicitFormula.WeilTestFunction`: Concrete implementation of Lagarias' test space using `SchwartzMap`. (**Done**)
- `ExplicitFormula.WeilFunctionals`: Definitions of `Warith`, `primeTerm`, `archimedeanTerm`. (**Done**)
- `ExplicitFormula.MulConvolution`: Multiplicative convolution with Mellin property proof. (**Done**)
- `ExplicitFormula.MainRoute3`: Theorems linking `WeilGate` to `RiemannHypothesis`. (**Done**)

### Assets from `jonwashburn/riemann`
We have identified high-value code to integrate:
- **`Riemann/RS/Cayley.lean`**: Contains the logic proving that `Re(2J) >= 0` implies `|Theta| <= 1`. This is the **Analytic Engine** for positivity.
- **`Riemann/Weil/SelbergClass.lean`**: Contains the verification that `riemannZeta` satisfies the functional equation and analyticity axioms.
- **`Riemann/Cert/KxiWhitney_RvM.lean`**: Contains Poisson kernel estimates essential for controlling the boundary values.

---

## 3. The "Final Push" Strategy

Our strategy combines the **Recognition Science (RS)** physical intuition with the **Cayley/Schur** mathematical machinery.

### The Insight
- **RS Perspective:** The "Ledger" (distribution of primes) enforces "Conservation of Skew". Negativity in the explicit formula would violate the "Meta-Principle" (existence requires positive cost J >= 0).
- **Mathematical Translation:** The "Arithmetic Side" (sum over primes) defines a boundary function `J(s)`. If we can show `Re(J(s)) >= 0` on the critical line, the Cayley transform `Theta = (J-1)/(J+1)` satisfies `|Theta| <= 1`, which forbids off-line poles (zeros of zeta).

### Implementation Plan (Next Steps)

1.  **Formalize the "Arithmetic J":**
    Define a function `J_arith(s)` whose real part on the critical line corresponds to the integrand of the Arithmetic Side.
    Candidate: The generating function of the prime terms, roughly `Sum Lambda(n) n^-s`.

2.  **Apply the Cayley Logic (U12):**
    Port `Theta_Schur_of_Re_nonneg_on` from `Cayley.lean`.
    Show that `WeilGate` (positivity of the functional) follows if we can exhibit this `J_arith` with positive real part.

3.  **The "Detector" Connection:**
    Use `WeilConverseDetector` to show that if RH fails, we can construct an `f` such that `Warith(f * ~f) < 0`.
    Contradict this by using the `Cayley` bound to show `Warith` must be positive.

### Strategic Goal
We move from "checking definitions" to **attacking the inequality**. The new `WeilTestFunction` class allows us to compute these terms concretely.
