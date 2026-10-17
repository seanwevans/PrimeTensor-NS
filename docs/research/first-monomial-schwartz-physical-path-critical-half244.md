# Realized-Schwartz critical-half estimate on a canonical H³ path

Base: `89ff14cc` — derive homogeneous critical half bound from Schwartz Holder 244.

The previously proved **unconditional-for-Schwartz** estimate is

    |M(f)| <= K (E0(f) E1(f))^(1/4) D(f),
    K^4 = 16 * 3^9 * S^6.

The existing `h3PathCanonicalFirstMonomialAggregate_eq_complexSchwartz`
and `lowNormalRealSchwartzPoint3Monomial_eq_complex` identities both retain
the physical factor **two**, and identify the path aggregate `A0(u,t)` with
`M(f)` when a *real Schwartz realization* of the logged velocity is provided.
The separately proved signed three-monomial cyclic identity gives

    I3(u,t) = 3 A0(u,t) = 3 M(f).

Thus `|I3| <= 3 K (E0(f) E1(f))^(1/4) D(f)`. Using the established gradient
commutator bound yields the complete top transport comparison

    |T3(u,t)| <= 24 C1 sqrt(E(u,t)) E3(u,t)
                   + 3 K (E0(f) E1(f))^(1/4) D(f).

The mathematical frontier is **not** another factor of three: it is to
relate Schwartz energies to the physical path energies and, separately,
to justify a Schwartz realization/approximation for general H³ slices with
bounds stable under approximation. This module does not assume the
realization holds at every time and makes no global smoothness claim.

Validation: Lean check and full build must run in the user's repository.
