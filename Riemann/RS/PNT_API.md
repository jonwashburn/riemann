[17 tools called]

### High‑level answer

Here’s a compact “shopping list” of API from `PrimeNumberTheoremAnd` and `StrongPNT` that looks directly reusable in your RH / `J_canonical` / `G_U` development in `Riemann`.

---

### 1. ℝ–ℂ differentiability bridge (already useful, you’re using it)

From `PrimeNumberTheoremAnd/Auxiliary.lean`:

- **Real→complex coercion derivatives**
  - `Complex.hasDerivAt_ofReal`
  - `Complex.differentiableAt_ofReal`
  - `Complex.differentiable_ofReal`
- **Composing complex functions with real arguments**
  - `DifferentiableAt.comp_ofReal`, `deriv.comp_ofReal`
  - `Differentiable.comp_ofReal`
- **Equivalences for real vs. coerced‑to‑ℂ functions**
  - `DifferentiableAt.ofReal_comp_iff`, `Differentiable.ofReal_comp_iff`
  - `deriv.ofReal_comp`

These are exactly what you want whenever you parameterize complex curves by real variables (e.g. `t ↦ z + t`, `t ↦ z + t·I`) and want to switch smoothly between `ℝ`‑ and `ℂ`‑Fréchet derivatives, as in your `secondDeriv_along_line`, `uxx_as_iteratedFDeriv`, `uyy_as_iteratedFDeriv`.

---

### 2. General complex‑analysis / zero‑set API

From `StrongPNT/PNT1_ComplexAnalysis.lean`:

- **Zero sets in disks and compactness:**
  - `zerosetKfR` (closed‑ball zero set of `f`)
  - `lemKinDR`, `lemKRinK1` (various inclusions of zeros into balls)
  - `lem_bolzano_weierstrass`, `lem_zeros_have_limit_point` (accumulation point of infinite zero sets in compact sets)

- **Identity theorem in a ready‑to‑use form:**
  - `lem_identity_theorem` (analytic on a ball, zero set with accumulation ⇒ f ≡ 0 on ball)
  - `lem_identity_theoremR`, `lem_identity_theoremKR`, `lem_identity_infiniteKR`
  - `lem_Contra_finiteKR`: “if f is nonzero somewhere, then the zeros in a compact disk are finite”

- **Analytic order / multiplicity at zeros:**
  - `lem_frho_zero` (value zero at a zero in `zerosetKfR`)
  - `lem_m_rho_is_nat` (analytic order at a zero is finite ⇒ not `⊤`)
  - `analyticOrderAt_ge_one_of_zero` (order ≥ 1 at a zero)
  - `lem_m_rho_ge_1` (order ≥ 1 for zeros in a region, with global assumptions)

These are **generic holomorphic‑function tools**. For RH‑style arguments about zeros of `riemannXi_ext`, `J_canonical`, etc., you can reuse this whole identity‑theorem / analytic‑order setup almost verbatim (with different domains / radii).

---

### 3. Local behaviour of ζ and its log‑derivative

From `PrimeNumberTheoremAnd/ZetaBounds.lean` and `StrongPNT/Z0.lean`:

- **Residue‑style control near a simple pole:**
  - `ResidueOfTendsTo`: if `(s-p) f s → A`, then `f(s) = A/(s-p) + O(1)` near `p`.
- **Log‑derivative of ζ near `s = 1`:**
  - `riemannZetaLogDerivResidueBigO` (used in `Z0.lean`)
  - `Z0bound_aux`, `Z0bound`: `-(ζ'/ζ)(1+δ) − 1/δ = O(1)` as `δ → 0⁺`.

This is **exactly the pattern you need** for: “log derivative has simple pole with bounded remainder”, which feeds directly into potential‑theoretic or Green‑function representations of `log J_canonical` / `G_U`.

---

### 4. Global Euler‑product and product‑manipulation API for ζ

From `StrongPNT/PNT3_RiemannZeta.lean`:

- **Euler product and absolute values:**
  - `p_s_abs_1` (|p^{-s}| < 1 for Re(s)>1)
  - `zetaEulerprod` (Euler product for ζ for Re(s)>1)
  - `abs_zeta_prod`, `abs_zeta_prod_prime`, `abs_P_prod`
- **Ratios and product identities:**
  - `zeta_ratio_prod` (ζ(2s)/ζ(s) as a ratio of Euler products)
  - General product API over units:
    - `tprod_commutes_with_inclusion_infinite`, `inclusion_commutes_with_division`
    - `lift_multipliable_of_nonzero`, `prod_of_ratios_simplified`, `prod_of_ratios`, `simplify_prod_ratio`

These are helpful if your RH proof needs to **re‑express or bound ζ, ζ', Xi, or J_canonical through Euler products and prime factors**, or to manipulate infinite products in a provably legal way.

---

### 5. Analytic / asymptotic tools more specific to PNT, but still re‑usable

From `PrimeNumberTheoremAnd/ZetaBounds.lean`, `Consequences.lean`, and related files:

- Many lemmas about:
  - `IsBigO` / `IsTheta` estimates,
  - integrability and asymptotics of prime sums (`th`, Chebyshev θ‑function),
  - derivative and continuity of smoothing kernels (`deriv_smoothingFn`, `extracted_1`, `extracted_2` in `Consequences.lean`),
  - Abel summation and prime‑counting bounds.

These are **less directly RH‑structural**, but useful if you later want to connect your RH‑side analytic arguments to explicit prime‑counting statements or inverse transforms.

---

### 6. Summary of what is “immediately useful” in `Riemann`

For your current RH‑oriented work in `Riemann` (especially the CR/Green and Laplacian arguments):

- **Definitely use/import:**
  - `PrimeNumberTheoremAnd.Auxiliary` for all the ℝ↔ℂ differentiability lemmas.
  - `StrongPNT.PNT1_ComplexAnalysis` for identity‑theorem, analytic order, and finiteness of zero sets in disks.
  - `PrimeNumberTheoremAnd.ZetaBounds` + `StrongPNT.Z0` for residue/big‑O structure of ζ and its log derivative near `s = 1`.
- **Likely useful later:**
  - `StrongPNT.PNT3_RiemannZeta` for Euler product manipulations and absolute value/product estimates.
- **Possibly useful at later “number‑theoretic consequences” stage:**
  - PNT/prime‑counting material in `Consequences.lean`, `MediumPNT.lean`, `StrongPNT.PNT2_LogDerivative`, `PNT4_ZeroFreeRegion`, etc.

If you’d like, I can next propose a concrete set of `import` lines and minimal wrapper lemmas (e.g. specialized identity theorems for `J_canonical` / `G_U`) tailored to exactly what `DiagonalBounds.lean` and your half‑plane Green proofs currently need.
