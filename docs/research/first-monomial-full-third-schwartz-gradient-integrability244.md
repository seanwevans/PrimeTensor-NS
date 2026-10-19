# Complete full-third gradient integrability from real Schwartz realization

Baseline: `5c57d9ac` — identify full third Schwartz gradient with physical H3 path transport.

## Actual analytic issue

The established `thirdFullRealSchwartz_pathGradientTotal_eq244` used the
explicit predicate `H3RealSchwartzGradientAxesIntegrable244 u t` to justify
splitting the physical three-axis energy pairing as a sum of integrals.

The new file proves this predicate from the existing componentwise real
Schwartz slice realization, without a new PDE assumption or sign constraint.

For each fixed `j i k l r`, the physical integrand is exactly the pullback
along `h3Point3ToFourierCLM` of the sum of four genuine Schwartz products:

`F (G₁ H₁ + G₂ H₂ + G₃ H₃ + G₄ H₄)`.

Each triple belongs to L¹ since Schwartz functions are closed under
pointwise multiplication and integrable. The finite sum is integrable.
`PiLp.volume_preserving_toLp` transports integrability from the canonical
`H3FourierPoint3` carrier back to genuine `Point3` volume, preserving the
precise Fourier/physical normalization already established.

## Results

* `thirdFullRealSchwartz_gradientAxisDensity_integrable244`
* `thirdFullRealSchwartz_gradientAxesIntegrable_of_realization244`
* `thirdFullRealSchwartz_pathGradientTotal_eq_of_realization244`
* `h3Path_fullThirdTransport_eq_realSchwartz_of_realization244`

The final theorem identifies the full top-order transport with the complete
`G₃+3M` Schwartz functional without an extra axis-integrability hypothesis.

## Scope

A Schwartz **realization of an actual time slice** remains an explicit
hypothesis. This spatial result does not construct a global NS solution from
arbitrary static data, impose an initial-condition matching theorem, or
bound the full transport including lower orders. It does not prove blowup.

No `sorry`, `admit`, or additional axioms are introduced.
