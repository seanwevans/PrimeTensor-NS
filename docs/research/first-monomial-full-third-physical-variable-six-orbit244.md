# Moving-germ five-index physical orbit and its negative tube

Base checkpoint: `2769baa3`.

The existing proofs identify the genuine complete five-index H3 physical
ordered sharp core with twice the corrected physical symbol. This file
transfers the contraction to the *arbitrary-frequency* sector physical core,
not just the six center values. In that formula, the three solenoidal germs
are evaluated at the actual three momenta `p`, `q=-p-r`, and `r`, and the
original gradient coefficient 2 and interpolation coefficient 6 are kept.

The six-permutation orbit constructed from the genuine ordered five-index
cores is proved exactly equal to `thirdFullProjectedHermitianKernel244`.
Existing continuity and strict-local-negativity theorems for that kernel
therefore give a positive-radius neighborhood in which the **sum** of the
six physical ordered cores is strictly negative. The six terms need not
be pointwise negative individually.

## Open analytic bridge

This is a strict sign for the unwindowed, simultaneously permuted *orbit*
on a common momentum-pair domain. It is not a sign of the actual Schwartz
six-sector integral. To establish the latter, one must change variables in
the six genuine positive-sector integrals, check the momentum-dependent
Schwartz cutoff product transforms to a common nonnegative weight, account
for the volume Jacobian and boundaries, handle points with zero spectral
triple mass, and then integrate the negative common orbit. No such change
of variables is asserted by this module.
