/-
Phase 0 audit of unresolved assumptions in the boundary-wedge pipeline.

Summary:
* `CR_green_upper_bound`, `whitney_phase_upper_bound` (file:
  `rh/RS/sealed/BoundaryWedgeProofCore`) are axioms that currently use a
  zero integrand placeholder.  Action: reprove the Green identity for the
  analytic reciprocal `G := (O · ξ_ext) / det₂`, tracking disks around zeros.
* `critical_atoms_nonneg`, `phase_velocity_identity`,
  `phase_velocity_lower_bound` (same file) rely on stub residue bookkeeping
  and ignore a possible singular inner factor.  Action: compute residues of `G`
  and either eliminate or explicitly carry any singular boundary measure.
* `boundary_realpart_ae_nonneg_on_interval_from_wedge`,
  `whitney_to_ae_boundary`, and the final `PPlus` theorems depend on “AF bridge”
  placeholders and an unspecified Whitney covering.  Action: supply the
  Poisson/Cayley change of variables, prove measurability, and implement the
  covering argument.
* All Schur/annular infrastructure in `mc-rh/rh/RS/BWP/*.lean` currently takes
  residue counts from an arbitrary list; the certificate
  `rh/Cert/KxiWhitney_RvM.lean` only states the desired RvM/VK bound.
  Action: connect these modules to genuine zero-density inputs (or record them
  explicitly as external hypotheses).

This audit defines the scope for Phase 1 (recasting everything in terms of `G`)
and Phase 2 (phase-velocity/factorization), before any downstream Schur or
Whitney arguments can be trusted.


\subsection{Phase 0 Audit of Analytic Placeholders}

\begin{tabular}{p{3cm}p{4cm}p{4cm}p{4cm}}
\toprule
Statement & Location & Current status & Required resolution \\
\midrule
$\mathsf{CR\_green\_upper\_bound}$ &
\texttt{rh/RS/sealed/BoundaryWedgeProofCore.lean} &
Assumed; proof replaced by “windowed phase = 0” placeholder. &
Prove the Green-identity/Cauchy–Schwarz estimate for $U_G$ on Whitney tents minus $\{\Xi=0\}$; track boundary discs. \\
\addlinespace
$\mathsf{whitney\_phase\_upper\_bound}$ &
same file &
Immediate corollary of the previous placeholder. &
Derive from the proven CR–Green estimate plus a genuine Carleson bound. \\
\addlinespace
$\mathsf{critical\_atoms\_nonneg}$ &
same file &
Axiomatized via dummy residue bookkeeping. &
Compute residues of $G$ explicitly; show nonnegativity (or carry their sign into later steps). \\
\addlinespace
$\mathsf{phase\_velocity\_identity}$ &
same file &
Axiom; ignores singular inner factor. &
Rephrase for $G=(O\Xi)/\det_2$ including any singular boundary measure; either show it vanishes or keep it in estimates. \\
\addlinespace
$\mathsf{phase\_velocity\_lower\_bound}$ &
same file &
Depends on the previous axioms. &
Reprove once the phase-velocity identity is established. \\
\addlinespace
$\mathsf{boundary\_realpart\_ae\_nonneg\_on\_interval\_from\_wedge}$ &
same file &
Delegated to an “AF bridge” lemma that is currently an axiom. &
Supply the Poisson/Cayley change-of-variable proof linking boundary integrals to $\Re(2J)$. \\
\addlinespace
$\mathsf{whitney\_to\_ae\_boundary}$ &
same file &
Axiom relying on an unspecified Whitney cover. &
Construct the cover, prove measurability, and run the measure-theoretic argument. \\
\addlinespace
$\mathsf{PPlus\_from\_constants}$ and $\mathsf{PPlus\_from\_Carleson}$ &
same file &
Declared theorems, but both hinge on all placeholders above. &
Becomes a corollary only after CR–Green, Carleson, and Whitney-to-a.e. are rigorous. \\
\addlinespace
Dyadic row bounds, annular splits (\texttt{BWP/DiagonalBounds.lean}) &
\texttt{mc-rh/rh/RS/BWP/*.lean} &
Definitions + statements; witnesses provided by trivial bookkeeping. &
Replace dummy inputs with data extracted from zeros (or from certified inequalities). \\
\addlinespace
$\mathsf{rvM\_short\_interval\_bound}$ certificates &
\texttt{rh/Cert/KxiWhitney\_RvM.lean} &
Pure specification; no link to actual zero counts. &
Either import the needed RvM/VK estimates or label them as external hypotheses. \\
\bottomrule
\end{tabular}

\paragraph{Outstanding structural issues.}
(1) All CR–Green objects reference $J=\det_2/(O\Xi)$, which is meromorphic when $\Xi$ vanishes; they must be rewritten for $G=(O\Xi)/\det_2$.
(2) The singular inner factor of $G$ is never controlled.
(3) Every Carleson/Schur bound ultimately depends on abstract residue bookkeeping; no arithmetic input is wired in yet.
-/
