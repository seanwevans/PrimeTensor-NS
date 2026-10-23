# Physical projected FTC: approximate momentum residual stability

Baseline: `9bc43588` (`master`).

## Why an approximate equation matters

The existing consistent-mollification interface requires exact `V′(t)=W(t)` for a velocity approximant `V` and projected-source approximant `W`. Temporal or spatial smoothing of the actual preterminal Navier–Stokes PDE may instead produce a commutator/consistency defect `E`, such that `V′=W+E`.

This module separates three physical Hilbert-space approximation errors on strict time intervals:

- `εU`: `sup ‖U−V‖L²`
- `εR`: `sup ‖R−W‖L²`
- `η`: `sup ‖E‖L²`

By absorbing `E` into the source approximant `W+E`, the existing exact-smooth FTC stability theorem proves

`‖U(b)−U(a)−∫ₐᵇ R(s)ds‖L² ≤ (2+b−a) max(εU, εR+η)`.

Therefore, if a sequence of approximate regularized momentum equations exists with all three errors tending to zero, every prefix of the actual physical Hilbert FTC defect vanishes. Compact divergence-free weak momentum follows. Conversely, a nonzero actual defect forces a positive approximation-error obstruction.

## Analytic scope

**No such approximating sequence is constructed in this module.** Continuity of the projected physical `L²` source and of the old physical velocity is already available but does not force `V′=W+E` with `‖E‖→0`. The known old-vs-canonical pressure-gradient defect may obstruct a direct Fubini/distributional argument, and must be treated rather than discarded. The precise remaining target is to establish small *physical* temporal/spatial regularization commutators from the classical preterminal momentum equation and the existing H³ path estimates, without postulating the desired evolution identity.

The module uses only the existing rigorously proved `ConsistentSmoothMomentumApprox` stability and the Leray-fixed weak-FTC bridge. It does not claim unconditional Navier–Stokes continuation.
