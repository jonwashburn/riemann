# Roadmap to Zero Sorries and ArXiv-Ready Proof
Jonathan Washburn – June 2025

This document breaks the remaining work into atomic tasks, provides the key mathematics required, and lists the Lean artefacts that must be produced.  Each subsection ends with a **deliverable checklist** that can be ticked off in future PRs.

---
## 1 Concrete Diagonal-Operator Framework on ℓ²

### 1.1 Mathematical definition
Let `I` be a countable index set and `μ : I → ℂ` a bounded function.  Define
\[
  D_{μ}
  :  \ell^{2}(I) \;\longrightarrow\; \ell^{2}(I),\qquad
  (D_{μ}x)(i) := μ(i)\,x(i).
\]

Key facts (to be proven in Lean):
1. **Boundedness.**  If \(\|μ\|_{\infty}=\sup_{i}|μ(i)|<\infty\) then
   \(\|D_{μ}\|=\|μ\|_{\infty}.\)
2. **Adjoint.**  \(D_{μ}^{\*}=D_{\bar μ}.\)
3. **Hilbert–Schmidt criterion.**  \(D_{μ}\) is Hilbert–Schmidt iff
   \(\sum_{i}|μ(i)|^{2}<\infty.\)
4. **Trace class.**  If \(\sum_{i}|μ(i)|<\infty\) then `TraceClass D_μ` and
   \(\operatorname{tr}(D_{μ})=\sum_{i} μ(i).\)

### 1.2 Lean API
```lean
namespace DiagOp
  variable {I : Type*} [DecidableEq I] [Countable I]

  /-- Diagonal operator with eigenvalues `μ`. -/
  def mk (μ : I → ℂ) (h : BddAbove (Set.range fun i ↦ ‖μ i‖)) :
      ℓ₂ I →L[ℂ] ℓ₂ I :=
    {
      toLinearMap :=
        { toFun := fun x i ↦ μ i * x i,
          map_add' := by simp [mul_add],
          map_smulₛₗ' := by simp [smul_eq_mul, mul_comm] },
      cont := by
        obtain ⟨C, hC⟩ := h
        refine ⟨C,?_⟩; intro x;
        have : ‖μ _‖ ≤ C := by
          apply hC; exact ⟨_,rfl⟩
        simp [lp.norm_mul_le _ this] }

  theorem opNorm_eq_supr (μ) (h) :
      ‖mk μ h‖ = ⨆ i, ‖μ i‖ := by
    -- proof uses `norm_mul_le` and standard `ciSup` facts
  ···
end DiagOp
```

**Deliverables**
- [ ] New file `DiagonalFredholm/DiagOp.lean` with the above.
- [ ] Replace axioms in `DiagonalTools.lean`, `Operator.lean`, `OperatorView.lean`.
- [ ] All existing lemmas (`DiagonalOperator_apply`, `adjoint`, `norm`) now reference `DiagOp.mk`.

---
## 2 Bridge File Cleanup

### 2.1 Functional Equation Admit
Mathlib lemma:
```lean
open Complex
lemma completedZeta_symm (s : ℂ) :
  completedRiemannZeta s = completedRiemannZeta (1 - s) :=
by simpa using completedRiemannZeta_one_sub s
```
Insert in `RSInfrastructure.lean`:
```lean
have hξ : completedRiemannZeta s = completedRiemannZeta (1 - s) :=
  completedZeta_symm s
```
Use that \(ξ(s)=0⟺ζ(s)=0\) off the trivial zeros.

### 2.2 Hilbert–Schmidt Lemma
We need to show Λ_s is Hilbert–Schmidt for `Re s > 1/2`.

Observation: eigenvalues are \(p^{-s}\).  Their squares have absolute value
\(p^{-2\Re s}\).  Since \(\Re s>1/2\) we have \(\sum_{p}p^{-(1+ε)}<\infty\),
so the square-norm sum converges.

Lean sketch:
```lean
open DiagOp
lemma euler_hilbertSchmidt (hs : (1/2 : ℝ) < s.re) :
  HilbertSchmidt ℂ ℓ₂Prime (euler_operator s hs') := by
  -- use `HilbertSchmidt.of_summable_norm` from mathlib
  have h_sum : Summable (fun p : PrimeIndex ↦ ‖(p.val : ℂ)^(-s)‖^2) :=
    primeNormSummable (by linarith : 1 < (2* s.re))
  simpa using HilbertSchmidt.of_summable_norm _ h_sum
```

**Deliverables**
- [ ] Remove the two `admit`s; proofs < 40 lines.

---
## 3 Fredholm Infrastructure Fixes
Replace uses of axiomatized `fredholm_det2` with mathlib's
`Trace.fredholmDet` where possible.  If not available, keep a thin wrapper
but prove continuity and positivity in operator norm using `Determinant`
from linear algebra.

**Deliverables**
- [ ] `FredholmInfrastructure.lean` compiles with real operators.

---
## 4 DiagonalOperatorAnalysis & Long-Running Proofs
Many time-outs come from large `simp`/`linarith` calls.  Strategy:
1. Split monster lemmas into helper lemmas with explicit `have` steps.
2. Add `set_option maxHeartbeats 80000` locally rather than globally.
3. Use `ring` / `field_simp` instead of `linarith` when algebraic.

**Deliverables**
- [ ] File compiles within default heartbeat.
- [ ] No remaining `norm_cpow_of_ne_zero` (use `abs_cpow_eq_rpow_re_of_pos`).

---
## 5 CI & Documentation
- Add `lake build` GitHub workflow (matrix = linux, macOS).
- Update `RH_Mathematical_Proof.tex` to cite Lean lemma names.
- Final pass with `lake fmt` and `lake lint`.

---
## Milestone Schedule
| Week | Target |
|------|--------|
| 1 | Diagonal-operator framework merged, Bridge admits closed |
| 2 | FredholmInfrastructure + DiagonalOperatorAnalysis compile |
| 3 | Zero sorries across academic framework |
| 4 | CI green; draft arXiv paper ready for internal review |

Let's proceed with **Step 1** (DiagOp core).  Once that lands we'll iterate through dependent files. 