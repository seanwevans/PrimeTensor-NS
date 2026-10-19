# Full-third Schwartz scalar-observable closure (244)

**Base:** `c5119d98` — transfer kinetic-absorbed signed top obstruction to Schwartz H3 slices.

## Actual mathematical advance

The preceding theorem `h3Path_noExtension_realSchwartzTopAdverse_onEverySubtail244` required an EXACT real-Schwartz realization of every selected physical velocity slice.

This module replaces that requirement with a clearly specified approximation of five **scalar** observables at the same physical time:

1. canonical normalized full H3 energy, `E`;
2. complete third derivative energy, `E3`;
3. physical top fourth derivative dissipation, `D4`;
4. physical complete dissipation, `D`;
5. the **entire** physical signed third-order transport, `T3`, approximated by the full real-Schwartz cubic `fullSchwartzThirdCommutator244` (gradient plus three signed interpolation monomials).

The fifth item is crucial. Existing convergence of the signed 243-slot first monomial does NOT by itself imply convergence of the full cubic without handling the gradient-transport part. Here full-cubic convergence is explicitly hypothesized. Mere L2 density does not discharge it.

## Closedness of signed envelopes

If a Schwartz approximating sequence has `-T3(f_n) <= B E(f_n) + D(f_n)` eventually, then its limiting physical velocity satisfies

`-T3(u,t) <= B E(u,t) + D(u,t)`.

The same argument, using continuity of `sqrt`, transfers a spectral dominance inequality

`4398 C1 sqrt(E(f_n)) E3(f_n) <= D4(f_n)`

to the physical top dissipation and third-order energy. Both yield conditional continuation under the prior physical theorems.

## Necessary nonextension witness with approximants

Fix a strict kinetic anchor `b`, a later tail `d`, and any `M>=0`. If a preterminal H3 path cannot extend, the **previously proved physical theorem** supplies some `t in (d,T)` with

`M E(u,t) + D(u,t) < -T3(u,t)`.

Whenever this actual slice possesses the five-observable converging family, at least ONE approximating real-Schwartz field `f_n` also satisfies

`M E(f_n) + D(f_n) < -fullSchwartzThirdCommutator244(f_n)`.

Otherwise every member would satisfy the reverse weak inequality, and continuity would contradict the strict physical witness. This argument does not assert that the approximant is itself a Navier--Stokes time slice.

## Remaining obstruction

Prove all five scalar-observable limits for actual admissible positive-time H3 slices. This is strictly weaker than demanding exact real-Schwartz realization, but the signed cubic is sensitive to triple-product convergence; ordinary L2 density alone is insufficient. Existing strong Schwartz 2-4-4 jet continuity for the signed first monomial is one useful component; matching the full gradient transport and the complete dissipative H4 graph needs further analysis.

**Claims excluded:** no general H3 continuation theorem, no unconditional Navier--Stokes singularity theorem, no coercive bound disproved on actual solution paths, and no assumption that the static solenoidal Schwartz obstruction is attained by an actual solution.
