# Standalone Analytic Tasks (Problems 1–4)

These are self-contained and repo-agnostic. Solve independently; later we’ll port to Lean.

- Problem 1: Complex log bounds (Weierstrass)
  - Prove: for all z with |z| ≤ 1/2, |log(1−z)| ≤ 2|z| and |log(1−z)+z| ≤ |z|^2/(1−|z|).
  - Also justify −log(1−z)=∑_{n≥1} z^n/n for |z|<1.

- Problem 2: Infinite product criterion and non-vanishing
  - If ∑|a_i|<∞ and |a_i|≤1/2 eventually, then ∏(1−a_i) converges absolutely and ≠0.
  - Moreover, ∏(1−a_i)=0 ⇔ ∃i, a_i=1. Include ∏_S exp(a_i) = exp(∑_S a_i) for finite S.

- Problem 3: Eventually small from summability
  - If ∑‖e_i‖<∞ then e_i→0 (cofinite), hence eventually ‖e_i‖<1/2.

- Problem 4: Trivial zeros on Re(s) ≤ 0
  - If Re(z)≤0 and ζ(z)=0, then ∃n≥1, z=−2n; also ζ(−2(n+1))=0.
  - Use the functional equation, sin(πs/2) zeros, Γ nonvanishing, ζ(0)=−1/2.

Notes
- Problem 5 (non-vanishing on Re=1) is handled via RS/Schur globalization instead.
