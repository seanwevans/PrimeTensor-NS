# First-crossing physical outer annular cutoffs

Base commit: `55d74d14`.

## Why canonical cutoff selection matters

The earlier conditional outer-cutoff growth theorem chooses an outer
Fourier cutoff existentially. Such a cutoff can be inflated by selecting
a much larger radius: a lower bound on that *chosen* radius alone does
not establish that the PDE truly requires a broad annular range.

This module repairs the selection interface. Given an actual high-radial
cubic snapshot at inner index `n` and time `t`, choose the **least**
integer `N` such that

`3*(n+1)^3/4 < lowDiss(N+1,t)-lowDiss(n+1,t)`.

For every `m` with `n <= m < N`, the same annular dissipation stays at
or below that strict three-quarter-cubic threshold. Existence is proved
by the existing spectral high-tail partition theorem, and minimality
by well-ordering (`Nat.find` and `Nat.find_min`). This does not assume
continuity or monotonicity in the integer radius beyond existing facts.

## Transfer through the physical clocks

The local quadratic-sharp exact persistence clock is reconstructed using
that particular least cutoff. The source ceiling and initial weighted
spectral-state norm are selected afterwards, so the clock and annular
persistence estimate refer to the **same actual minimal annulus**.

The no-terminal-strong-L2-trace cofinal sequence is rebuilt with this
minimal outer cutoff on each index, and the finite-H3-terminal-dissipation
hypothesis again supplies summable costs on a strict pairwise separated
subsequence. Thus the original three-scale alternative survives:

`R^3*(T-tau)/4 <= eps  OR  R^6 <= 16*eps*(Lambda+1)  OR`
`R^9 <= 16*eps^2*(Xi+1)`.

Crucially, the selected cutoff now has a true first-crossing property.
This should be used before transferring the previously proved
superlinear ninth-eighth outer-cutoff criterion onto these witnesses;
otherwise the forced cutoff growth can be an artefact of the existential
radius choice.

Finite terminal full H3 dissipation remains an **additional hypothesis**;
this module neither bounds the minimal outer cutoff from above nor
establishes terminal regularity.

## Validation

The ZIP is statically checked, but the packaging environment lacks Lean.
Compile the module in the user's repository, run the audit, regenerate
and check proof/order.txt, and then build the whole project.
