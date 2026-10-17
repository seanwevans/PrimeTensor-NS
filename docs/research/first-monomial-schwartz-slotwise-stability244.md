# Signed 243-slot stability and physical H³ approximation criterion

Base commit: `755aa61f` (`close Schwartz critical half bound under physical H3 approximation`).

## Exact algebra

For signed real triples, the telescoping identity

    abc - a'b'c' = (a-a')bc + a'(b-b')c + a'b'(c-c')

leads, by the triangle inequality, to a coefficient-one bound for each
factor perturbation. The sum over an arbitrary finite index set retains
coefficient one. This part requires neither PDE hypotheses nor spatial
integrability, and handles zero and negative values without division.

## Physical 243-slot convergence

The new `H3SchwartzSlotwiseCriticalHalfApproximable244` predicate specifies
actual physical slot limits of

    2 * lowNormalRealSchwartz_firstMonomialSlotIntegral (f n) i k l r j

for all five physical indices `(j,r,i,k,l)`, together with strong scalar
convergence of E0, E1, and the full 243-slot top dissipation. The factor 2
is the exact `spatialEnergyPairing` normalization. A generic finite-sum
limit theorem, applied five times, proves convergence of the complete signed
monomial; finite reindexing matches the canonical physical aggregate.

This yields `H3SchwartzCriticalHalfApproximable244`, so the established
physical top-transport critical-half estimate follows without an exact
Schwartz realization.

## Honest remaining frontier

The slotwise limits are explicit premises, not automatic consequences of
L² density. To remove them, prove strong L² convergence of third-order
jets, strong L⁴ convergence of the two second-order jets, and continuity
of the associated triple integrals using spatial 2-4-4 Hölder. For the
energy premises, establish strong convergence in the fourth-order Sobolev
graph norm on the canonical physical carrier. This module does not claim
that every canonical H³ slice has such approximants or that a continuation
theorem has been obtained.
