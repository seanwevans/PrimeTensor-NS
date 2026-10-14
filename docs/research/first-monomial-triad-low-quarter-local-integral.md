# The quarter-scale localized signed integral

Checkpoint: `275bd2b1` — local sign persistence for the sharp Schwartz triad.

The Fourier field is the actual fixed, divergence-free, conjugate-symmetric
vector-valued Schwartz map `lowNormalQuarterSchwartz`.  On the momentum
hyperplane q=-p-r, the *symbolic* signed real kernel is

    F(p,r) = Re( i C_6(p,-p-r,r; U(p),U(-p-r),U(r)) ).

`FirstMonomialTriadLowQuarterLocalSign` proves F(p₀,r₀)=9/64>0 and continuity
at the resonant pair.  This module selects a closed ball of positive radius
inside that strict positivity neighborhood.  It proves a strictly positive
integral of F over that closed ball with product volume, using compact-ball
integrability and positive measure of an inner open ball.

The entire six-center field is not asserted to have a nonzero full-space
integral.  The 12 coherent resonances, including the reflected family, must
be accounted for.  The physical seven-derivative Fourier phase is **minus**
(2π)^7 i; the localized F sign by itself is not a physical H³ energy sign.

Next: group the coherent packet sectors, exploit Hermitian reflection and
cyclic symmetries to control the complement and prove or refute global
noncancellation for the specific fixed bump profiles.  Also bridge the Fin 3
frequency carrier to the project's actual H³ Fourier carrier before making
physical PDE claims.
