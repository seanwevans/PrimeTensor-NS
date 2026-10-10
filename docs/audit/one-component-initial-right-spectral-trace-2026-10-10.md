# One-sided initial physical H³ trace and the one-component full-time criterion

Parent commit: `b378015a` — derive full-time H3/2 from initial strong spectral path.

The previous audit assumed an ambient whole-line H³ spectral velocity path
continuous at time zero and agreeing with every physical velocity coordinate.
For a one-component continuation condition this is stronger than needed.

`OneComponentInitialRightSpectralTrace.lean` defines the actual selected
velocity component's canonical H³-weighted Fourier snapshot on `(0,T)`, with a
zero extension elsewhere. The new predicate
`H3AuditInitialRightComplementH3SpectralTrace` requires convergence of that
specific physical component in H³ Fourier L² as `t ↓ 0` (a one-sided
`𝓝[>] 0` limit). This is a *physical-state* trace, not an unrelated curve.

An H³-valued right limit bounds its component norm on `(0,b)` by a finite
constant. That bound combines with the existing continuous interior-time
homogeneous Fourier density and the already-proved terminal strong H³ endpoint
integral to produce `L²(0,T; Ḣ^(3/2))` for the intrinsic physical seminorm.
The two-component result takes the two corresponding right traces and one
common physical endpoint. The one-component theorem needs just one trace.

**Open obligations:** The existence of the right trace from the actual initial
H³ datum/local mild solution remains unproved. Also pending are a precise
local-strong-solution eligibility theorem, the external Liu–Zhang Sobolev
space comparison, and the continuation/real-restart implication. This patch
makes no unconditional Navier–Stokes regularity claim.

The theorem
`h3Audit_initialStrongSpectralPath_implies_rightComplementTrace` proves that
the stronger previously postulated whole-line initial spectral path entails
each selected one-sided trace when `0<T`. The new full-time conclusions
therefore remain compatible with the preceding audit's solution interface.

## Lean typecheck fix (2026-10-10)

- Convert `t ∈ Ioi 0` into `0 < t` before invoking `abs_of_pos`, so
  `dist t 0 < min δ T` simplifies to the expected real inequality.
- Rewrite `dist` to its norm identity explicitly rather than use the
  unspecialized `dist_eq_norm` lemma as a term.
- All statements and hypotheses are unchanged. The local Lean typecheck
  is delegated to the Rocky Linux/Lake workflow.
