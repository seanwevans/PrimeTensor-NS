# First pointwise shell estimate

Base: 7831e4e5, physical Schwartz interpolation identified with shell integral.

Write q=-(p+r), P=||p||, R=||r|| and Q=||q||, all Euclidean norms.
The new module proves

    |R²-P²| = |<p-r,q>| <= (P+R)Q.

It also proves the localized consequence |R²-P²| <= 2NL when P,R<=N
and Q<=L, including zero frequencies without division.

For the exact shell kernel already appearing in the physical identity, set
B=|p·U(q)| and C=|sum_j U_j(p)U_j(r)|. The new bound is

    |S(p,r)| <= P R B Q³ (P+R) C.

The proof retains the shell difference until after the exact exchange
cancellation. It uses Euclidean Cauchy-Schwarz on p·r, not the sup norm
of the coordinate function type. Polarization contractions B and C remain
explicit. The estimate holds for the shell expression without a divergence
hypothesis; divergence remains essential for the physical shell identity.

## Meaning and remaining work

For P and R comparable to N and Q comparable to L much smaller than N,
the shell-gap estimate is O(NL), instead of the elementary O(N²) bound.
This supplies a relative L/N gain. It gives no improvement when all three
frequencies are comparable and does not give a favorable sign.

Next: bound the mixed and bilinear complex polarization contractions in
Euclidean l², with incompressibility allowing min(P,R) in the mixed factor.
Then split frequency interactions and estimate their integrals in the
physical norms needed by the H3 continuation argument. The present
pointwise result does not supply that integrated estimate, absorption,
or extension beyond the explicit Schwartz realization.

## Checks

Source indexing, fragment checks and whitespace checks are run when packaging.
Lean compilation and the audit are pending the user's pinned local toolchain.
No new axioms, sorry declarations, or weakened existing statements are introduced.
