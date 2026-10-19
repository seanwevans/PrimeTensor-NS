# Full third Schwartz: split-jet closure of five physical observables

**Base:** `39f70048` — close signed full-third Schwartz observable approximation bridge.

## What closes

The previous five-observable bridge assumed convergence of the **entire** signed top-order Schwartz cubic. This module factors it into the 12-term-per-index gradient channel `G` and the signed 243-slot interpolation monomial `M`, using `T3 = G + 3 M`.

The established theorem `lowNormalRealSchwartz_firstMonomial_tendsto_of_strongJets244` already proves `M(f_n) -> M(g)` from actual third-derivative L2 and second-derivative L4 roots at each physical slot. Thus only gradient-channel convergence `G(f_n) -> G(g)` and the physical identification `G(g) + 3 M(g) = T3(u,t)` remain inputs for signed cubic convergence. There is no premise that `G(f_n)+3M(f_n)` itself converges.

The four separate energy limits `E0..E3` yield the normalized total energy by finite addition. The `E1..E3` plus fourth-order top-dissipation limit yield full physical viscosity using `thirdFullPhysicalDissipation_eq_lowerEnergies_add_top244`.

A split-jet structure packages these data and discharges `H3FullThirdSchwartzObservableApproximation244`; the already-proved nonextension witness and continuation criterion are reused without assuming exact Schwartz realization.

## What remains open

Prove true strong mixed-jet Schwartz approximation of arbitrary actual physical H3 slices, gradient-channel convergence from an appropriate 3-3-1 mixed Lebesgue graph (or a PDE-based identity), and identify the limiting full signed cubic with the actual top-order PDE pairing. A fixed Schwartz target `g` is currently part of the split-jet input: this is **not** a density theorem for general non-Schwartz H3 data.

No unconditional continuation or singularity claim is asserted. Local Lean compilation is required before accepting the patch as checked.
