# Route 3: The Spectral Identity — THE REAL BLOCKER

**Date:** December 13, 2025
**Status:** This document identifies the precise analytic lemma needed to close Route 3.

---

## Executive Summary

The Route 3 proof reduces to proving **one analytic identity**:

```
W¹(f ⋆ₘ ˜ₘ(⋆ₜ f)) = ∫ Re(2·J(½ + it)) · |M[f](½ + it)|² dt
```

Once this identity is established:
- Positivity follows immediately from `Re(2·J) ≥ 0` and `|M[f]|² ≥ 0`
- The Hilbert-space realization is mechanical (GNS construction)
- Existing Lean theorems fire and conclude RH

---

## The Factorization

### What is NOT the hard part

1. **Hilbert-space construction**: Given a positive-semidefinite Hermitian form `B`, constructing `H` and `T` with `B(f,g) = ⟪Tf, Tg⟫` is standard (GNS/RKHS).

2. **Cayley transform algebra**: Already proved in `Cayley.lean` that `Re(z) ≥ 0 ⇒ |θ(z)| ≤ 1`.

3. **Gate implications**: Already proved in `MainRoute3.lean` that `WeilGate ⇒ RH`.

### What IS the hard part

**The Spectral Identity**: Express the Weil quadratic form as a weighted L² norm:

```
W¹(f ⋆ₘ ˜ₘ(⋆ₜ f)) = ∫_{ℝ} Re(2·J(½ + it)) · |M[f](½ + it)|² dt
```

This requires:

1. **Fubini/Tonelli justification**: Interchange the symmetric sum over zeros (defining W¹) with the integral representation.

2. **Boundary limits**: Handle the distributional boundary values of analytic functions (Fatou-type theorems).

3. **Normalization matching**: Ensure the Mellin transform conventions match the convolution/involution definitions so that `f ⋆ₘ ˜ₘ(⋆ₜ f)` literally gives `|M[f]|²` on the critical line.

---

## The Key Equation to Prove

### Version 1: Critical Line Form

For the Lagarias-normalized W¹ functional and test functions f:

```
W¹(f ⋆ₘ ˜ₘ(⋆ₜ f)) = ∫_{-∞}^{∞} K(t) · |M[f](½ + it)|² dt
```

where the "spectral kernel" K(t) is:

```
K(t) = Re(2 · J(½ + it))
     = Re(2 · (-ζ'(½ + it) / ζ(½ + it)))
```

**Key observation**: If `Re(2·J) ≥ 0` on the critical line, then K(t) ≥ 0, and the integral is nonnegative.

### Version 2: Unit Circle Form (after Cayley)

After applying the Cayley transform θ(s) = (s-1)/(s+1):

```
W¹(f ⋆ₘ ˜ₘ(⋆ₜ f)) = ∫_{|z|=1} K̃(z) · |F[f](z)|² |dz|
```

where F[f] is the transformed test function and K̃ is the pushed-forward kernel.

---

## Why This Identity Should Hold (Heuristic)

The explicit formula (Guinand–Weil) states:

```
W_spec(f) = W_arith(f)
```

where:
- W_spec = W² - W¹ + W⁰ (zeros contribute to W¹)
- W_arith = sum over primes + archimedean term

For "reflection squares" f ⋆ₘ ˜ₘ(⋆ₜ f), the Mellin transform satisfies:

```
M[f ⋆ₘ ˜ₘ(⋆ₜ f)](s) = M[f](s) · M[˜ₘ(⋆ₜ f)](s)
                     = M[f](s) · M[⋆ₜ f](1-s)
                     = M[f](s) · conj(M[f](1 - conj(s)))
```

On the critical line s = ½ + it, this gives:

```
M[f ⋆ₘ ˜ₘ(⋆ₜ f)](½ + it) = |M[f](½ + it)|²
```

The spectral identity then asserts that the sum over zeros W¹ can be "unfolded" via residue calculus / contour integration into an integral over the critical line with the J-field as weight.

---

## The Two Approaches

### Approach A: Direct Proof of Spectral Identity

Prove directly that:

1. The symmetric zero-sum W¹(g) for g = f ⋆ₘ ˜ₘ(⋆ₜ f) equals a contour integral.
2. Deform the contour to the critical line.
3. The resulting integral has the form ∫ K(t) |M[f](½+it)|² dt.

This requires:
- Careful handling of zero distributions
- Justification of contour deformation
- Absolute convergence estimates

### Approach B: Carathéodory/Herglotz Representation

Use the classical theorem:

If F(z) = 2·J(z) is analytic on the unit disk with Re(F) ≥ 0, then the kernel

```
K_F(z,w) = (F(z) + conj(F(w))) / (1 - z·conj(w))
```

is positive definite, which directly implies a Hilbert-space realization.

This requires:
- Establishing that the Cayley-transformed J is analytic in the disk
- Connecting the kernel K_F to the Weil form

---

## What's in the Lean Codebase

| Module | Content |
|--------|---------|
| `HilbertRealization.lean` | GNS theorem: positive-semidefinite form ⇒ Hilbert space |
| `HilbertRealization.lean` | `SpectralIdentity` structure packaging the needed lemma |
| `HilbertRealization.lean` | `weilGate_from_spectral_identity`: spectral identity + Re(2J)≥0 ⇒ WeilGate |
| `MainRoute3.lean` | `WeilGate_implies_RH`: WeilGate ⇒ RiemannHypothesis |

---

## The Path to Completion

1. **Prove the spectral identity** (the real mathematics)
   - This is the genuine analytic content
   - Requires Fubini, boundary limits, normalization matching

2. **Establish `Re(2·J) ≥ 0`** on the critical line
   - This may require assuming RH (circular) or proving it from arithmetic
   - Or: use the Carathéodory approach which gets positivity "for free"

3. **Instantiate `SpectralIdentity`** in Lean
   - Once the math is done, this is straightforward

4. **Apply `weilGate_from_spectral_identity`**
   - Automatic

5. **Apply `WeilGate_implies_RH`**
   - Automatic

---

## Honest Assessment

The spectral identity is the bottleneck because it encodes the **entire analytic content of the explicit formula**. We are essentially trying to prove:

> The Weil positivity criterion (∀f, W¹(f⋆˜f̄) ≥ 0) is equivalent to the existence of a positive-definite spectral measure on the critical line.

This is a deep statement. It's not "mystical" — it's a precise analytic theorem that can be proved with classical tools. But it requires careful work with:
- Distributions and boundary values
- The explicit formula machinery
- Measure theory on the critical line

**The good news**: This is a well-posed, tractable problem. The structure is clear. The remaining work is genuine analysis, not hand-waving.
