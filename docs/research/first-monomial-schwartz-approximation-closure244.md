# Schwartz 2-4-4 critical-half: sequential closure to physical H3 paths

Base: `dcbfb694` (`fix physical H3 dissipation bound assembly`).

This module transfers the exact 243-slot fourth-root estimate to physical
path slices that are limits of real Schwartz vector fields in **four specific
scalar observables**: the signed complete first monomial, zeroth energy,
first energy, and 243-slot top dissipation. It is not enough to have only
L2 convergence of the velocity or only weak H3 convergence.

For approximating Schwartz vectors `f_n`, assume:

* `M(f_n) -> h3PathCanonicalFirstMonomialAggregateAt u t`;
* `E0(f_n) -> velocityH3Energy0At u t`;
* `E1(f_n) -> velocityH3Energy1At u t`;
* `D4(f_n) -> velocityH3Dissipation3At u t`.

The existing unconditional Schwartz theorem and continuity of the real
absolute value, product, and nested square roots prove

`|A0(u,t)| <= K (E0(u,t)*E1(u,t))^(1/4) D3(u,t)`.

The already-proved exact signed identity `I3 = 3*A0` gives an interpolation
bound with coefficient `3*K`. The gradient estimate completes the full
transport bound with the original `24*C1*sqrt(E)*E3` allowance. Finally
`D3 <= D` yields a full physical dissipation version.

The predicate is genuinely weaker than an exact Schwartz realization;
a constant sequence proves that realization implies approximability.

**Open analytic requirement:** produce such approximation sequences for
all required genuine H3 slices. A useful sufficient route is strong L2
convergence through fourth derivatives plus suitable `L2 x L4 x L4`
Hölder continuity of all signed triple products. No such density or
nonlinear convergence theorem is claimed in this module. Merely invoking
Schwartz L2 density would be insufficient.
