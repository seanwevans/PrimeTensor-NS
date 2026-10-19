# Sharp real interpolation center audit — `879f0790`

This module isolates the **actual** `3+2+2` physical coefficient (with the overall factor six kept outside) from the full-third six-sector Fourier polynomial, and determines its ordered sharp-center values. The sharp physical momenta are `p=(1,0,0)`, `q=(1,1,0)`, `r=(-2,-1,0)`; their solenoidal real polarizations are `A=(0,1,0)`, `B=(1,-1,0)`, `C=(1,-2,0)`.

The ordered coefficient is `(p·r)(p·q)^2(r·B)(A·C)`. In the six positive ordered frequency triples (`pqr`, `rqp`, `qpr`, `rpq`, `qrp`, `prq`), the coefficient evaluates exactly to **-4, 36, 9, -36, -9, 4**, summing to zero. This is an **ordered interpolation cancellation at the sharp centers**, not a statement about the complete physical kernel, the four `3+3+1` patterns, or integrals over nonconstant Schwartz packets. In particular, individual positive-sector interpolation contributions need not have a common sign.

The Lean module separately proves that every normalized polynomial transverse germ agrees with its original polarization at a transverse nonzero frequency center, and supplies a sharp-center bridge for the actual *cutoff-free interpolation core*. It also proves the six positive center pairs obey exactly the missing-middle momentum equation, so the comparison does not silently assume that the middle momentum is centered.

What remains: instantiate the center bridge with the three canonical solenoidal polarizations and physically embedded center pairs; reduce the five-index gradient core to its corrected ordered symbol; then combine its six center values and prove a uniform negative neighborhood in the real phase-free physical kernel before any global integral sign claim.

No axioms, placeholders, global sign or Navier–Stokes regularity claims are added.
