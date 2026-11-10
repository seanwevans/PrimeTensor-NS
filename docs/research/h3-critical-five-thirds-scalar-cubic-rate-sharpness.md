# Cubic-rate scalar sharpness at the critical H3 terminal weight

Base commit: `945899bc20a20224489ba1a6d404756ae5151bf3`.

## Goal

Establish that `5/3` is **the exact largest terminal weight exponent supported
by the rate alone** in the preceding physical continuation theorem. This is
not a counterexample to Navier--Stokes regularity, merely a scalar
counterexample to extrapolating the existing cubic inequality.

The real positive-distance profile

    D(d) = d^(-8/3),   d > 0

saturates the accepted nonextension inequality with coefficient one:

    d^8 D(d)^3 = d^8 d^(-8) = 1.

For a general terminal weight exponent `beta`,

    d^beta D(d) = d^(beta - 8/3).

The exact real-power integrability criterion at zero is

    ∫_0^L d^(beta - 8/3) dd < ∞  iff  beta - 8/3 > -1,

or `beta > 5/3`. At `beta = 5/3`, the integrand is `1/d` and
nonintegrable. Thus the scalar cubic rate, without additional analytic
information, cannot imply supercritical-weight nonintegrability.

## Hard-math implication

To go beyond the already accepted `5/3` conditional continuation criterion,
one must prove a genuinely stronger PDE statement: e.g. a stricter lower
blow-up rate, a quantitative dyadic shell charge exceeding the harmonic
baseline, or a time-occupation/transport obstruction for the exact scalar
profile. Algebraic normalization of the cubic rate will not suffice.

## Lean declarations

- `thirdFullKinetic_cubicRateSaturatingProfile244` (definition)
- `thirdFullKinetic_cubicRateSaturatingProfile_nonneg244`
- `thirdFullKinetic_cubicRateSaturatingProfile_exactCubic244`
- `thirdFullKinetic_cubicRateSaturatingProfile_weight244`
- `thirdFullKinetic_cubicRateSaturatingProfile_criticalNonintegrable244`
- `thirdFullKinetic_cubicRateSaturatingProfile_supercriticalIntegrable244`
- `thirdFullKinetic_cubicRate_supercriticalWeight_hasCounterprofile244`

No axioms or sorry/admit are introduced. Kernel compilation must be run on
the user's Lean 4.34/mathlib environment; local static checks cannot
establish Lean proof acceptance.
