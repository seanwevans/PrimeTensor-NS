# The high-radial remainder is exactly complementary Fourier H³ mass

**Base commit:** `3747a0a8` — derive high radial spectral escape from physical kinetic anchor.

The prior theorem proves that, for actual H³ spectral velocity `G(t)` and a fixed
radial cutoff `rho`, the algebraic remainder

`High(rho,G) = SpectralSquareEnergy(G) - LowRadialSquareMass(rho,G)`

is cofinally unbounded whenever a strong physical terminal kinetic L² trace
fails and the canonical terminal kinetic energy is positive. The physical
kinetic monotonicity and exact Plancherel relation supply the previously
required raw Fourier mass ceiling on every fixed later subtail.

## Measure-theoretic normalization

The density of the state is

`A_G(xi) = |G_0(xi)|² + |G_1(xi)|² + |G_2(xi)|²`.

It belongs to `L¹` by the scalar `L²` component estimates, and

`SpectralSquareEnergy(G) = integral A_G over all Fourier space`.

The low-radial square-defect construction, evaluated against the zero state,
is exactly `integral A_G over {|D(xi)| < rho}`. The measurable-set integral
complement formula now identifies

`High(rho,G) = integral_{|D(xi)| >= rho} A_G(xi) dxi >= 0`.

Here `D` is the repository Fourier-gradient symbol and includes the relevant
`2*pi` normalization. No point evaluation functional or frequency-domain
compactness is postulated.

## Consequence and limitation

The preceding actual kinetic anchor bound yields cofinal unbounded integrated
weighted H³ mass on the complement of *every fixed radial ball* if the strong
physical kinetic L² terminal trace does not exist. For zero terminal kinetic
mass the prior dichotomy already gives the physical strong trace. Thus the
updated alternative is exact-mass physical kinetic trace or genuinely
integrated high-radial weighted spectral escape.

This is **not** a Navier–Stokes smooth-continuation theorem: in particular,
nonextension is not identified with failure of the physical kinetic L² trace.
Nor is pointwise spectral blowup at a bounded frequency being used to infer
integrated mass blowup. The remaining analytic work is a mechanism to control
or exclude the normalized high-frequency alternative under the actual PDE.
