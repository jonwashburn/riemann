# RiemannProof — Clean Riemann Hypothesis Proof

This folder is a **pristine extract** of the Lean 4 proof of the Riemann Hypothesis developed in the main workspace.

Contents :

* `lakefile.lean`, `lake-manifest.json`, `lean-toolchain` — project config
* `rh/` — full Recognition-Science-integrated RH proof (5 marked sorries, no axioms)
* `no-mathlib-core/` — minimal self-contained core library used by the proof (also axiom-free)

To build:

```bash
lake build
```

This rebuilds from sources and fetches mathlib automatically. 