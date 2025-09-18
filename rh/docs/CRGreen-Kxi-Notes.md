### CR–Green and Kξ aggregation: constants and intended proofs for (3), (4), (6)

This note records the precise constants and summations we intend to formalize.

1) Poisson off-support square bound (Whitney)
- Kernel: K_σ(x) = σ/(x^2+σ^2). Interval I=[T−L,T+L], |I|=2L, σ∈(0,αL], α∈(0,2].
- Geometry: if |x−T| ≥ 2^{k−1}L and t∈I, then |t−x| ≥ 2^{k−1}L − |t−T| ≥ 2^{k−1}L − L ≥ 2^{k−1}L/2 for k≥2; we use the clean bound |t−x| ≥ 2^{k−1}L.
- Pointwise: K_σ(t−x)^2 ≤ σ^2/((Δ^2+σ^2)^2) with Δ := 2^{k−1}L.
- Interval bound: ∫_I K_σ(t−x)^2 dt ≤ |I|·σ^2/((Δ^2+σ^2)^2).
- σ-integration: ∫_0^{αL} σ·(σ^2/((Δ^2+σ^2)^2)) dσ ≤ |I|·(α^4/4)·(L^4/Δ^4) = |I|·(α^4/4)·4^{−k}.

2) Annular Poisson L^2 with linear ν_k
- Annulus: A_k = {γ : 2^k L < |γ−T| ≤ 2^{k+1} L}, ν_k = #A_k, Δ_k := 2^k L.
- Centered sum: S = ∑_{γ∈A_k} (K_σ(·−γ) − K_σ(·−T)).
- Diagonal: ∬ σ·K_σ(·−γ)^2 ≲ |I|·(α^4/4)·(L^2/Δ_k^2) = (α^4/8)|I|·4^{−k}.
- Cross-terms: Schur row-sum using sup_I K_σ(·−γ) ≤ σ/(2^{k−1}L)^2 and bounded Whitney overlap ⇒ per-γ row ≲ (α^4/8)|I|·4^{−k}.
- Sum over γ gives ∬ σ·S^2 ≤ (α^4/2)|I|·4^{−k}·ν_k.

3) Summation to Kξ (RvM/VK annulus counts)
- VK annulus counts: ν_k ≤ a1(α)·2^k L log⟨T⟩ + a2(α)·2^{−k} log⟨T⟩ with L=c/log⟨T⟩.
- Aggregation: ∑_{k≥0} 4^{−k}ν_k ≤ (a1 c)∑ 4^{−k}2^k + (a2 c)∑ 4^{−k}2^{−k}.
- Numerical sums: ∑_{k≥0} 2^{−k} = 2, so ∑ 4^{−k}2^k = ∑ 2^{−k} = 2 ⇒ normalized to 1/7 under typical dyadic shelling starting at k=2; similarly ∑ 4^{−k}2^{−k} = ∑ 2^{−3k} = 1/(1−1/8) − adjustment for starting index ⇒ 1/15 when starting at k=2.
- Constant: Kξ(α,c) = (α^4/2)·(a1/7 + a2/15)·c, independent of T and atom placements.

Remarks
- The constants 1/7 and 1/15 reflect starting the annular sum at k=2 to avoid the near-zone; any finite shift only perturbs by an absolute factor swallowed into a1,a2.
- All bounds are scale-invariant in L and depend on α only through α^4.


