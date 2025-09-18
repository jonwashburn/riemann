# Riemann Hypothesis (RS route)

This repository contains the RS Schur–globalization route and supporting analytic/certification infrastructure. See `rh/README.md` for module-level details.

- Key RS exports: `no_offcritical_zeros_from_schur`, `ZetaNoZerosOnRe1FromSchur`.
- Wedge step update: the boundary (P+) now wires a proven AI-based negativity selection (Poisson approximate identity on the boundary) via `whitney_carleson_coercivity_aepos_AI`. The non-AI variant remains available.

Build:

```
lake build
```

