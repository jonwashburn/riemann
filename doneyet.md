# Finishing Plan: Unconditional RH

## 1. Eliminate Analytic Placeholders in `CRGreenReal.lean`
- The theorem `CRGreen_window_bound_real` currently ends in a `sorry`.
- **Goal**: Replace this `sorry` with a rigorous derivation using `CRCalculus.lean`.
- **Steps**:
  - Instantiate the CR-Green identity for the windowed phase.
  - Use the finite Carleson energy `Kxi_finite_real` (proven unconditional).
  - Apply the window decay properties from `WindowClass.lean`.
  - Verify the constant `C_psi_H1` bounds the integral.

## 2. Connect `KxiFinite` to `ConcreteHalfPlaneCarleson`
- In `HardySchurIntegration.lean`, the step packaging `Kxi_finite_real` into `ConcreteHalfPlaneCarleson` is stubbed.
- **Goal**: Implement the instance derivation.
- **Steps**:
  - `ConcreteHalfPlaneCarleson` expects a bound on *every* Whitney box.
  - `Kxi_finite_real` provides this bound for any `I`.
  - Need to ensure the constant `Kxi_paper` matches the certificate requirements.

## 3. Prove the Wedge Closure Implication
- `HardySchurIntegration.lean` contains a `sorry` for the implication `PPlusFromCarleson`.
- **Goal**: This is the core "pinch" logic: if energy is small, the wedge closes.
- **Steps**:
  - Link `WedgeVerify.lean` (which proves Υ < 1/2) to the `PPlus` predicate.
  - Show that Υ < 1/2 implies `Re F > 0` on the boundary (or equivalent distributional condition).
  - This likely involves `BoundaryAiDistribution.lean` (phase velocity identity).

## 4. Finalize Boundary Distribution Logic
- `BoundaryAiDistribution.lean` has been cleaned of axioms but relies on `weak_star_limit_is_measure`.
- **Goal**: Ensure the "no singular inner factor" deduction is fully rigorous.
- **Steps**:
  - Verify the Poisson balayage logic.
  - Ensure the de-smoothing limit is connected to the `PPlus` condition.

## 5. De Branges Track (Parallel/Optional)
- The De Branges track has its own `axiom XiGenerator_is_HB_axiom`.
- This route is separate but should be kept building.
- **Status**: `DBEmbedding.lean` and `ReproducingKernel/Basic.lean` contain sorries/axioms.

## Summary of Critical Gaps (Hardy/Schur)
1. **CR-Green Integration**: Linking energy to phase integral (`CRGreenReal.lean`).
2. **Carleson Packaging**: Formalizing the witness (`HardySchurIntegration.lean`).
3. **Wedge Logic**: Connecting numerical verification to the `PPlus` predicate (`HardySchurIntegration.lean`).

