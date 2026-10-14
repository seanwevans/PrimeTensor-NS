# Quarter-packet Point3 cubic/quadratic scaling

Checkpoint: `c488b413`, real Schwartz velocity reversal and both signs.

`FirstMonomialTriadLowQuarterPoint3AmplitudeScaling.lean` isolates exact
amplitude homogeneity of the complete 243-slot physical first-monomial
functional (degree three) and of the four-spatial-derivative squared
Schwartz mass associated with top-order H3 dissipation (degree two).

The positive real Schwartz witness from velocity reversal therefore
violates every proposed universal linear absorption inequality
`M(f) ≤ C D4(f)` after sufficiently large positive scalar multiplication.
The result is an algebraic obstruction to that *bare* absorption
inequality, not a Navier–Stokes blowup theorem or a claim about the full
energy balance.

**Build hygiene:** After registering the new Lean module, run
`python3 proof/generate_index.py`, `--check`, and
`python3 proof/check_fragment.py --all` **before Lake compilation**.
Commit the updated `proof/order.txt`; otherwise the audit baseline
(and CI) rejects the stale source index even when Lean succeeds.

This patch has not been typechecked using the pinned Lean/mathlib toolchain;
the repository's Rocky Linux build is the required compiler gate.
