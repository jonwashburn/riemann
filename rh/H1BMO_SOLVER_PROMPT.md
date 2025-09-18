# H¹-BMO Direct Route Solver Prompt

## Use this prompt repeatedly until the H¹-BMO blocker is fully resolved:

---

You are completing the Riemann Hypothesis proof at /Users/jonathanwashburn/Documents/T9 Copy - August 29/Cursor-Active/riemann by implementing the direct route to bypass H¹-BMO theory. The written proof at /Users/jonathanwashburn/Documents/T9 Copy - August 29/Cursor-Active/riemann/Riemann-lean-verified.tex provides the complete mathematical roadmap (specifically lines 1505-1523 for Lemma 3.23 and lines 2420-2440 for Theorem 2.13). Your goal: replace the `sorry` at line 102 of rh/RS/BoundaryWedge.lean in `localWedge_from_pairing_and_uniformTest` with a working proof that avoids H¹-BMO duality.

**Constraints:** 
- No new axioms
- No sorry/admit in final code
- Maintain compatibility with existing imports
- Use only mathlib 4.12.0 constructs
- Preserve all existing theorem names and signatures

**Each run:**

1) **Build check**: `cd /Users/jonathanwashburn/Documents/T9 Copy - August 29/Cursor-Active/riemann && lake build 2>&1 | head -50`

2) **Pick ONE target from this priority list and implement it:**
   - **Priority 1**: In rh/RS/BoundaryWedge.lean or new file: Prove that for even windows ψ with compact support, `∫ t, (a * t + b) * (deriv (HilbertTransform ψ)) t = 0` (cite TeX lines 1511-1513: "Since ψ is even, (𝓗[φ_I])' annihilates affine functions")
   
   - **Priority 2**: Implement direct Cauchy-Schwarz bound: For harmonic U and even window ψ, prove `|∫ ψ(t) * ∂_σ U(1/2,t) dt| ≤ C(ψ) * sqrt(∬_{Q(I)} |∇U|² σ dσdt)` (cite TeX lines 1514-1519: "The local box pairing gives...")
   
   - **Priority 3**: Prove scale-invariant Dirichlet bound for Poisson extension V of ψ: `∬_{Q(αI)} |∇V|² σ ≤ C * |I|` where C depends only on ψ and α (cite TeX line 1515: "scale invariance")
   
   - **Priority 4**: In rh/RS/BoundaryWedge.lean at line 102, replace the `sorry` with:
     ```lean
     -- Following the direct approach from TeX Lemma 3.23 (lines 1505-1523)
     -- Step 1: Use even window property to subtract affine calibrant
     -- (TeX line 1513: "subtract the calibrant ℓ_I and write v:=u-ℓ_I")
     obtain ⟨Kξ, hKξ0, hCar⟩ := hKxi
     obtain ⟨c0, hc0_pos, hPlateau⟩ := plateau
     
     -- Step 2: Apply direct Cauchy-Schwarz with scale-invariant bounds
     -- (TeX lines 1514-1519: local box pairing with neutralized area bound)
     -- This gives: |∫ ψ(-w')| ≤ C(ψ) * sqrt(Kξ * |I|)
     
     -- Step 3: Combine with Poisson plateau lower bound
     -- (TeX lines 2424-2426: "By Lemma 3.24 and Theorem 2.7")
     -- We need: C(ψ) * sqrt(Kξ) / (π * c0) < 1/2
     
     -- Step 4: Apply quantitative wedge criterion
     -- (TeX line 2436: "the quantitative phase cone holds on all Whitney intervals")
     [actual proof here using the helper lemmas from priorities 1-3]
     ```

3) **Implementation guidelines:**
   - For Priority 1: May need to import `Mathlib.Analysis.Fourier.FourierTransformDeriv` or similar
   - For Priority 2: Use `MeasureTheory.integral_mul_le` and Cauchy-Schwarz from mathlib
   - For Priority 3: Use `Mathlib.Analysis.SpecialFunctions.Integrals` for Poisson kernel properties
   - Always cite specific TeX line numbers in comments

4) **Verify no new axioms**: `grep -r "axiom\|sorry\|admit" rh/RS/BoundaryWedge.lean rh/RS/Direct*.lean`

5) **Test build**: `lake build rh.RS.BoundaryWedge 2>&1 | tail -20`

6) **Stop after implementing ONE priority item successfully.**

**Current focus:** Start with Priority 1 (even window lemma) if not done, as it's foundational. If done, move to Priority 2 (Cauchy-Schwarz), then 3 (scale invariance), then 4 (final assembly).

**Key insight from TeX:** The written proof avoids H¹-BMO by using that even windows make `(𝓗[φ_I])'` annihilate affine functions (line 1513), allowing direct energy estimates via the local box pairing (lines 1514-1519) to get the uniform bound `C_H(ψ)` without full H¹-BMO theory.

---

## End of prompt. Use repeatedly until all priorities are complete and the build is clean.
