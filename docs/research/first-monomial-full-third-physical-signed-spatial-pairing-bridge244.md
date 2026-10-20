# Old physical 243-slot spatial pairing = integrable jet aggregate

Parent: `943f58b4` (`prove physical H3 signed 243-slot Holder integrability and canonical representative invariance`).

## What is proved

Every old concrete `velocityH3L2JetAt` derivative is almost everywhere identical to the physical spatial derivative it represents. The `h3ToFourierRealL2` map is defined using `Lp.compMeasurePreserving` along `WithLp.ofLp`. We compose the existing a.e. identification with this measure-preserving map and use the exact volume transport to identify actual signed 3–2–2 Euclidean integrals with the original `Point3` physical integrals. Crucially, the exact physical pairing factor `2` and all ordered axes `(j,r,i,k,l)` are retained.

This proves:

1. General old-physical jet a.e. identity on the Euclidean carrier.
2. A.e. identity of each signed triple product with its old physical derivative product.
3. Equality of each Euclidean and `Point3` triple integral.
4. `h3PathCanonicalInterpolationMonomialPairing ... 0 = 2 * h3ActualSignedFirstMonomialSlotIntegral244`.
5. `h3PathCanonicalFirstMonomialAggregateAt = h3ActualSignedFirstMonomialAggregate244`.
6. Under Fourier compatibility, equality with `h3CanonicalSignedFirstMonomialAggregate244` (which replaces the two second-order derivatives by canonical L⁴ representatives).

No new regularity or Schwartz-realization hypothesis is used in these equalities. `H3` snapshot integrability and measurability are the original hypotheses; Fourier compatibility is required only for the final canonical representative equality.

## Remaining frontier

The canonical-representative aggregate from the new module is **not** yet shown equal to `weightedH3CanonicalSignedFirstMonomial244`, the independently defined Schwartz-limit observable. That requires convergence of the full triple product, using strong L² third and L⁴ second jet convergence (2–4–4) and exact matching of the Schwartz monomial index convention. The separate full-third 3–3–1 gradient pairing is also still open.

## Validation

This overlay is statically checked and needs `lake env lean` and full `lake build` in the user’s pinned Lean/mathlib environment. No `sorry` or `admit` is allowed.
