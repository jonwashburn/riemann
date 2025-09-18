/-
Copyright: Recognition Physics Institute

Module: rh/RS/CRGreenOuter.lean
Status: BLOCKED on one analytic L² inequality (see `BLOCKER:` below)

This module is intentionally *algebraic-only*: it states and documents the single
annular balayage L² estimate needed by the Kξ Whitney–Carleson bound. The
estimate is formulated in a way that can be proved with mathlib’s measure theory
and basic calculus once one auxiliary inequality on Poisson tails is added.

No axioms, no `sorry`. This file compiles as documentation until the `TODO`
lemmas are implemented.

## Notation and setup
- Let `I := [T - L, T + L] ⊂ ℝ`, `|I| = 2L`, with `L = c / log ⟨T⟩` and
  `⟨T⟩ := √(1 + T^2)`.
- For a height parameter `σ > 0` and horizontal variable `t ∈ ℝ`, the Poisson
  kernel is `Kσ(x) := σ / (x^2 + σ^2)`.
- The Whitney box is `Q(α, I) := { (σ, t) : 0 < σ ≤ α L, t ∈ I }`.
- Zeros are partitioned into Whitney annuli
  `A_k := { ρ = β + iγ : 2^k L < |γ - T| ≤ 2^{k+1} L }`, with counts `ν_k := #A_k`.
- After neutralizing zeros in a fixed dilate by a half‑plane Blaschke product,
  the gradient component of the ξ–potential contributes (up to harmless smooth
  terms) the Poisson balayage of the counting measure on `A_k`.

## Goal of this module
Provide the quantitative “annular L² balayage” bound that isolates the 4^{-k}
Whitney decay and is **linear in ν_k**:

```
annular_balayage_L2 :
  ∀ {α c T L k} (Ak : Finset ℝ),
    (∀ γ ∈ Ak, 2^k*L < |γ - T| ∧ |γ - T| ≤ 2^(k+1)*L) →
    ∬_{(σ,t) ∈ Q(α,I)} (∑ γ∈Ak, Kσ(t-γ))^2 σ dt dσ
      ≤ C_α * |I| * 4^{-k} * (Ak.card)
```

with a constant `C_α` depending only on `α` (and harmless absolute constants).

### Why this is nontrivial
A direct Cauchy–Schwarz gives a factor `Ak.card` **twice** and loses linearity.
The proof uses the standard “balayage almost-orthogonality” on Whitney boxes:
one subtracts a center Poisson tail to kill the rank‑one part (“outer
cancellation”), then uses pointwise dyadic off‑support decay to bound the
result by a Carleson norm times `Ak.card`.

## Minimal auxiliary inequality (what’s actually missing)

BLOCKER: `poisson_square_whitney_offsupport`
> For any interval `I = [T-L, T+L]`, any `0 < σ ≤ αL`, and any `x` with
> `|x - T| ≥ 2^{k-1} L`, we need the elementary bound
> ```
> ∫_{t∈I} Kσ(t - x)^2 dt ≤ |I| * (σ^2 / ((2^{k-1}L)^2 + σ^2)^2).
> ```
> Equivalently (integrating also in `σ` with the Carleson weight),
> ```
> ∫_{0}^{αL} ∫_{t∈I} Kσ(t - x)^2 σ dt dσ
>     ≤ |I| * ( (αL)^4 / (4 * (2^{k-1}L)^4) ) = |I| * (α^4 / 4) * 4^{-k}.
> ```
> The second line uses the trivial inequality `( (2^{k-1}L)^2 + σ^2 )^2 ≥ (2^{k-1}L)^4`
> and the elementary integral `∫_0^{αL} σ^3 dσ = (αL)^4 / 4`. Both are available (or
> easy) in mathlib.

With this in hand, the *centered* balayage
`Kσ(t-γ) - Kσ(t-T)` gains almost‑orthogonality on `Q(α,I)`, and the sum of the
cross terms is absorbed into the diagonal at cost `≲ 4^{-k}`. This yields the
linear `ν_k` dependence required by the Whitney–Carleson argument.

## Deliverable lemma (to be proven here)

Once `poisson_square_whitney_offsupport` is in place, we can prove:

```
lemma annular_balayage_L2
  (α c T L : ℝ) (k : ℕ) (Ak : Finset ℝ)
  (hWL : ∀ γ ∈ Ak, 2^k*L < |γ - T| ∧ |γ - T| ≤ 2^(k+1)*L)
  : ∬_{(σ,t) ∈ Q(α,I)} (∑ γ∈Ak, Kσ(t-γ))^2 σ dt dσ
      ≤ C_α * |I| * 4^{-k} * (Ak.card)
```

with `C_α := α^4/2` acceptable (any explicit `C_α ≲ α^4` is fine).

*Proof sketch (implementable in mathlib):*
1. Set `d := 2^{k-1} L` and write `S(σ,t) := ∑_{γ∈Ak} (Kσ(t-γ) - Kσ(t-T))`.
   The outer cancellation yields
   `∬ (∑ Kσ(t-γ))^2 σ ≤ 2 ∬ S(σ,t)^2 σ + 2 ν_k ∬ Kσ(t-T)^2 σ`.
   The second term is absorbed into the first (identical bound with `x := T`).
2. On `Q(α,I)`, each `x ∈ {γ} ∪ {T}` satisfies `|x - T| ≥ d`. Apply
   `poisson_square_whitney_offsupport` to each term of `S` and sum:
   `∬ S^2 σ ≤ Ak.card * C_α * |I| * 4^{-k}`.
3. Track constants to finish.

This is the exact quantitative statement consumed by the Cert step.

## Where to put the auxiliary lemma
File: this file (`rh/RS/CRGreenOuter.lean`), section “Whitney Poisson L² tails”.

Once this blocker is discharged, `rh/Cert/KxiWhitney_RvM.lean` can import this
module and finish the proof of the quantitative Kξ Whitney–Carleson bound.
-/
