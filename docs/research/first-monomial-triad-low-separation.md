# Quantitative separation of the six sharp low-normal frequency centers

Base checkpoint: `1ed6ebef` — classify exact resonances of six sharp low-normal frequency centers.

The preceding theorem proves that every zero-sum ordered triple among the six
sharp low-normal centers is a permutation of `(p,q,r)` or `(-p,-q,-r)`.
The present module establishes a **numerical coordinate margin** for all
204 excluded triples, not merely a qualitative nonzero-sum statement.

For an integer lattice sum `(A,B)` the physical frequency embedding is

    L_t(A,B) = (A + t B, t B, 0).

For an excluded triple, `(A,B) != (0,0)`.
If `B != 0`, the second coordinate has magnitude `|t B| >= |t|`.
If `B = 0`, then `A != 0` and the first coordinate has magnitude
`|A| >= 1`.  Thus there is always some coordinate whose sum has magnitude
at least `min(1,|t|)`.

For `t != 0` let `delta(t) = min(1,|t|)/4`.  This radius is positive.
If three frequency vectors lie within strict coordinatewise distance
`delta(t)` from labeled centers and sum to zero, their center triple must
be coherent: all positive centers once each, or all reflected centers once
each. Indeed, every coordinate of the difference between their zero sum and
the center sum has magnitude less than `3 delta(t) < min(1,|t|)`.

The radius shrinks with `t`; no uniform-in-`t` positive separation is claimed.
The result does not yet construct Schwartz Fourier bumps, establish their
reality/divergence symmetries, or control the sign of the integrated
six-order kernel.
