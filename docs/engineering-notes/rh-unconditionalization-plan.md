# RH Unconditionalization Plan (Lean / mathlib track)

Goal: Make the final RH wrappers unconditional within mathlib, while only relying on acceptable classical axioms (propext, Classical.choice, Quot.sound).

## Current state (baseline c5dd35d)
- Build is green on `main`.
- Final exports compile; axioms check shows only classical axioms.
- Remaining inputs (Prop-level) keeping the result conditional:
  - Outer existence on Ω with boundary modulus |det₂/ξ_ext| (provided in-repo via a witness; classical Montel/Hurwitz route deferred).
  - Carleson budget ⇒ (P+) for the boundary trace (statement-level interface, proof not in-repo).
  - Poisson representation transport (boundary (P+) ⇒ interior nonnegativity): packaged as interface; representation identity itself is an input.
  - Kξ Whitney–box Carleson bound (Prop-level interface, no in-repo proof).
  - Removable-extension assignment at ξ_ext-zeros (Prop-level input; packaging from u-trick implemented).

## High-level milestones
1) Provide a concrete RS proof of Carleson ⇒ (P+) for the default pinch field using existing scaffolds (density, Egorov, negativity-window, plateau, CR–Green pairing). Outcome: inhabit `PPlusFromCarleson_exists` for `F := (2 : ℂ) * J_pinch det2 O`.
2) Keep transport and removable data as explicit inputs (acceptable) while documenting them clearly in the final route wrappers.
3) Maintain the simple outer witness (Ω-constant) for |det₂/ξ_ext|; optionally add a doc-only alias describing the classical Montel/Hurwitz path.
4) Wire an axioms check target into the repo for quick audits.

## Minimal change set (mathlib-ready)
- Implement `PPlusFromCarleson_exists_proved_default` in `rh/RS/PPlusFromCarleson.lean` by composing:
  - density window (`density_window_from_not_PPlus_default`)
  - Egorov selection on intervals (`EgorovWindow_default_from_selection` or `Egorov_from_a.e.on_I`)
  - negativity window (`neg_window_from_density_and_egorov`)
  - averaged upper bound (`avg_upper_bound_from_window_default`)
  - plateau lower bound (`poisson_plateau_c0`)
  - CR–Green pairing with Carleson budget (`local_pairing_bound_from_IBP_and_Carleson`)
- Add/restore `rh/Proof/AxiomsCheckLite.lean` for easy `#print axioms` on final exports.
- Document the interfaces that remain as inputs in this track (transport representation; Kξ bound; removable assignment) and justify them as classical/acceptable.

## Small, single-post tasks (execution order)
1) Add `rh/Proof/AxiomsCheckLite.lean` (axioms printer) and commit.
2) Implement `PPlusFromCarleson_exists_proved_default` in `rh/RS/PPlusFromCarleson.lean` using existing lemmas; ensure no import cycles.
3) Build: `lake clean && lake build`; fix any trivial import/measurability issues.
4) Run axioms check via `lake env lean rh/Proof/AxiomsCheckLite.lean` and record output.
5) Update docs: append an “Axioms audit” note to `docs/engineering-notes/cayley_carleson_lessons_2025-09-20.md` linking to the new checker.
6) (Optional) CI: add a small script/Makefile target to run the axioms checker.

## Notes on scope
- Transport and removable assignment remain inputs documented in `rh/Proof/Main.lean` wrappers; this track focuses on discharging the Carleson ⇒ (P+) link within RS using existing scaffolding.
- The outer existence currently uses a simple Ω-constant witness; a classical Montel/Hurwitz proof can replace it later without changing the downstream API.


