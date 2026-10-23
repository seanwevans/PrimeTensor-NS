# Physical weak FTC yields a genuine regular temporal distribution

Base: `37ec076b` (`recover physical weak FTC from outer primitive distributions`).

## Analytic result

On a strict physical interval `0 < a < b < T`, a scalar momentum path `M`
continuous on `[a,b]` with derivative `R` at each interior time, where `R`
is continuous on `[a,b]`, satisfies the compactly supported test identity

    -∫ M(t) θ'(t) dt = ∫ R(t) θ(t) dt.

The proof is direct: scalar continuity on `[a,b]` implies local integrability
on `(a,b)`; the test and its time derivative are compactly supported there;
their products with `M` and `R` are globally integrable. The proven
`integral_mul_deriv_eq_deriv_mul_of_integrable` method gives integration by
parts and hence equality of genuine regular distributions.

The existing theorem `h3Path_pointwiseWeakMomentum_of_solenoidalWeakFTC244`
identifies the interior derivative of each physically tested old velocity
with the already identified Leray-projected source whenever physical weak FTC
holds. Applying the scalar distribution theorem proves

    physical solenoidal weak FTC ==> distributional momentum equation

and hence the explicit temporal test identity.

## What is still open

Neither the pointwise old PDE by itself nor continuity of `U` and `R`
establishes physical weak FTC. The *other* direction needs:

1. PDE -> genuine time-tested distributional equation, justified by the
   spatial/time derivative interchange or an appropriate weak space-time
   identity.
2. Zero distributional derivative -> constant distribution on a connected
   open interval. One route is an explicit compactly supported smooth
   antiderivative for every zero-mean time test, followed by an appropriate
   normalization and continuous-representative injectivity.

No new endpoint boundedness or continuation conclusion is introduced.

## Validation

Run `python3 tools/audit/register_first_monomial_physical_top_time_distribution_from_weakftc244.py`,
`python3 proof/generate_index.py`, targeted `lake build` (to emit the `.olean`),
then `lake env lean tools/audit/FirstMonomialTriad.lean` and `lake build`.

This patch was authored without a local Lean toolchain: only downstream Lake
compilation establishes its correctness.
