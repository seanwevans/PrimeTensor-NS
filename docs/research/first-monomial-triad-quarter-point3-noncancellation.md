# Real Schwartz Point3 first-monomial noncancellation

Base: `d46da08c` — transport signed six-order integral to canonical H3 carrier.

This checkpoint makes the previous frequency-space conclusion into a real
spatial one. It defines the entire 243-slot first monomial using the **actual**
`Point3` derivatives `spatial3.d` and `spatialEnergyPairing` of the specific
real Schwartz packet pulled back from `H3FourierPoint3`.

The existing physical Schwarz monomial pairing theorem identifies each of
these physical slots with its Euclidean Schwartz triple-product integral.
The complexification theorem, finite axis-sum reindexing, Fourier shell
identity, and cyclic six-order identity then prove the exact relation

```
3 * physicalPoint3FirstMonomial
  = integral (re ((2*pi*i)^7 * sixOrderFourierCoefficient))
```

for the **same** real, divergence-free Schwartz velocity. The canonical-axis
phase integral was already proved negative, so the spatial physical
first-monomial is strictly negative for some explicit positive packet width.

The result rules out a universal signed cancellation of this complete
monomial, but does not establish a Navier--Stokes solution with this snapshot.
A corollary for the existing `h3PathCanonicalFirstMonomialAggregateAt` is
conditional on logged-velocity snapshot realization. No PDE existence or
extension premise is inferred from the static Schwartz construction.

The Lean source and this note were prepared without a local Lean compiler.
Build and axiom-audit success must be checked in the user repository.
