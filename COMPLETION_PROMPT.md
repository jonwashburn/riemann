# RH Proof Completion Prompt

Use this prompt to instruct an AI assistant to complete the Riemann Hypothesis proof formalization.

---

## THE PROMPT

```
I need you to complete the Riemann Hypothesis proof formalization in this Lean 4 project. 

CONTEXT:
- Location: /Users/jonathanwashburn/Projects/zeros/no-zeros/
- Current status: 42% complete, ~32 sorries remaining
- Architecture: Complete and sound - only computational/analytic gaps remain
- Goal: Eliminate all sorries and produce a concrete RiemannHypothesis theorem

PLAN:
Read and follow FINISH_PLAN.md exactly. Work through the three phases:

PHASE 1 (3-4 days): Complete computational sorries
- Fix PoissonPlateauNew.lean (13 sorries)
- Fix CRGreenOuter.lean domain details (4 sorries)
- Either prove simple calculus/algebra or admit with proper citations

PHASE 2 (0.5 days): Document standard admits
- CRGreenOuter.lean boundary nonvanishing (2 sorries) → admit with FE/Euler citations
- CertificateConstruction.lean outer uniqueness (1 sorry) → admit with Hardy space citation

PHASE 3 (5-7 days): Complete main theorem
- Phase velocity identity (c₀ minimization) - MUST PROVE
- Main wedge theorem (line 371) - MUST PROVE
- Numerical bounds

CRITICAL RULES:
1. READ FILES THOROUGHLY before editing - understand the full context
2. The proof architecture is CORRECT - don't restructure, just fill gaps
3. For standard math results, use well-documented axioms/admits with literature citations
4. For novel proof-specific results (phase velocity, wedge assembly), you MUST prove them
5. Test with `lake build` after each significant change
6. Track progress by updating sorry counts

PROCESS:
1. Start by reading FINISH_PLAN.md completely
2. Execute Phase 1, Task 1.1 (Poisson computations in PoissonPlateauNew.lean)
3. After each task, run `lake build` and count remaining sorries
4. Document each admit with proper citations in comments
5. Continue through all phases systematically
6. Final verification: build succeeds, axiom check clean, concrete certificate exists

OUTPUT EXPECTATIONS:
- Work incrementally, one file at a time
- Show diffs for all changes
- Explain your reasoning for each fix
- Flag if you need to admit something (with justification)
- Report progress after each task

BEGIN with: "I've read the FINISH_PLAN.md. Starting Phase 1, Task 1.1..."
```

---

## Quick Start

Simply paste the prompt above into a conversation with an AI assistant that has access to this codebase.

## Alternative: Direct Task Assignment

If you want to tackle specific tasks yourself, refer to the "File-by-File Action Items" in FINISH_PLAN.md.

## Verification After Completion

```bash
cd /Users/jonathanwashburn/Projects/zeros/no-zeros

# Should pass with no errors
lake build

# Should return 0
grep -rn "sorry" rh/ --include="*.lean" | grep -v "^\s*--" | wc -l

# Should show only Mathlib axioms
lake env lean --run rh/Proof/AxiomsCheckLite.lean
```

---

**Created**: 2025-10-01
