# Point3 transport of the physical first-monomial aggregate

Base: 2f2b0107, derive triad incompressibility from physical Schwartz divergence.

## Result

The new module works with real Schwartz functions f on H3FourierPoint3.
Their Point3 realization is the scalar field

    x ↦ f(h3Point3ToFourierCLM x).

It proves that this pullback commutes with the project's actual spatial3.d:

    spatial3.d i (pullback f) = pullback (∂_{e_i} f).

The chain rule uses the already-defined continuous linear identification of
the carriers. Repeated use supplies every second and third derivative in the
first monomial. There are no derivative matching hypotheses.

Separately, volume preservation proves equality of the Point3 and Euclidean
integrals under the same coordinate map. Thus spatialEnergyPairing transports
with its exact factor two.

## Connection to the existing physical aggregate

Assume, at a fixed time t, that each loggedVelocityComponent u t j is the
Point3 realization of a real Schwartz function f_j. The new theorem identifies
the existing h3PathCanonicalInterpolationMonomialPairing with the corresponding
real Schwartz derivative triple integral.

Summing gives an identity for the existing
h3PathCanonicalFirstMonomialAggregateAt, retaining its original index order
j,v,i,k,l and its factor two. This is a theorem about the existing physical
aggregate, not a newly defined replacement aggregate.

## Remaining boundary

The realization hypothesis concerns only the velocity components themselves.
It is an actual regularity restriction: an arbitrary preterminal H3 path has
not been proved to possess Schwartz components.

The new right-hand side is a real Schwartz sum. The next algebraic bridge is
to complexify those real Schwartz functions, commute that operation with
derivatives and integrals, and reindex the sum into the complex aggregate
already used by the shell theorem. Physical incompressibility must be carried
through those identifications as well.

After the Schwartz physical shell formula is assembled, extending it to the
needed solution class and proving a useful critical shell estimate remain
separate analytic tasks. No continuation conclusion is asserted here.

## Validation

The patch updates audit statements and axiom reports and regenerates the
source index. Source-index, fragment, and whitespace checks are run during
preparation. Lean compilation remains pending on the pinned toolchain.
