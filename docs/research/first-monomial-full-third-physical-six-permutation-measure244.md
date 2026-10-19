# Physical H³ six-permutation Fourier-pair measure bridge

**Base:** `5e5942f9` (moving physical six-orbit identified with the projected Hermitian kernel).

This module defines the six changes of the independent physical Fourier pair
`(p,r)` under the genuine conservation rule `q=-(p+r)`:

| Sector | Ordered independent pair | Generator word |
|---|---|---|
| 0 | `(p,r)` | identity |
| 1 | `(r,p)` | swap |
| 2 | `(q,r)` | swap; middle; swap |
| 3 | `(r,q)` | swap; middle |
| 4 | `(q,p)` | middle; swap |
| 5 | `(p,q)` | middle |

Existing theorem `h3TriadPermutation_preserving` in
`FirstMonomialTriadSixIntegral.lean` already gives six genuine measurable
product-volume preserving equivalences. This patch does not reprove the
Jacobian. It identifies the older permutation indices `0,5,2,4,3,1`
with the actual positive coherent sector order, proves this reindexing
is involutive, identifies the two six-term orbit sums exactly, and transports arbitrary signed sector integrals accordingly.

The results include unconditional full-domain integral equalities, transfer
of integrability, exact measurable-domain preimage transport, and finite-sum
reindexing of six arbitrary integrable signed sector functions onto a single
momentum-pair carrier.

**Important gap:** These equalities do *not* automatically turn the actual
label-specific scalar Schwartz window products into a common factor; their
transformation under each permutation still needs a theorem. Nor do they
handle zero triple-mass points or imply strict negativity of the integral.
The previously proved negative six-orbit tube is for the *unwindowed* physical
core, not six separately windowed sector integrals.

The final theorem `thirdFullPositiveSixBallIntegral_permutation_reindex244`
instantiates the generic six-integral result for the **actual real Schwartz
H³ third-order unphased kernel**, its six honest Hilbert-space sector balls,
and the pre-existing global kernel integrability result. It introduces no
new integrability hypothesis and preserves all indicator/window functions.
