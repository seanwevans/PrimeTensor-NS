# Six sharp values of the actual full H³ physical core

**Base checkpoint:** `0c0a39f2`.

This module exploits the audited full five-index coordinate contraction
`thirdFullSharpPhysicalOrderedCore_eq_twice_corrected244` together with the
already-certified six corrected ordered values. These are not new model
coefficients: each physical sharp ordered term is the actual sharp gradient
five-index polynomial plus six times its sharp interpolation coefficient,
transported into the Hilbert Fourier carrier with `WithLp.toLp 2`.

The order of the six **positive coherent sectors** is
`(p,q,r), (r,q,p), (q,p,r), (r,p,q), (q,r,p), (p,r,q)`, with respective
full physical coefficients `-32, 0, 66, -120, -162, 56`. The total is
`-192` and is proved from these actual physical sharp-core terms.

This does **not** imply pointwise negativity on each sector, nor sign of the
actual windowed Schwartz integrals. Several sharp sectors are positive.
A subsequent theorem must match the sector-by-sector geometry and the
nonnegative window product, and integrate while preserving permutation
measures and variable transverse germs.

Run the new register script and audit before committing. No proof placeholders.
