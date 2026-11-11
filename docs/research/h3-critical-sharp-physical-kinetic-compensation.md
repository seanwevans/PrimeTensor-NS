# Sharp physical kinetic compensation: actual cutoff and quantitative near-saturation obstruction

Pinned accepted HEAD: `5a4f00bee1806fa3b7183588277e6b304466ca4b`.

## Why this mathematical increment matters

The preceding physical low/high kinetic compensation theorem still demanded
four abstract decomposition/cross-orthogonality certificates. This package
builds the *actual* physical sharp radial projector from the already accepted
Hermitian-preserving real Fourier cutoff, component by component. The existing
real Plancherel pairing transports the complex L2 disjoint-indicator
orthogonality to the physical real scalar L2 pairing. Summing the three
physical coordinates gives both exact cross-orthogonality certificates, and
Pythagoras proves the vector operator is contractive.

## Physical kinetic anchor and genuine source bound

For every strict time `b<t<T` and Fourier gradient radius `rho>=0`:

    ||P_rho U(t)|| <= sqrt(E0(b))
    ||P_rho R(t)|| <= 3*Ckin(rho,E0(b))

where `U(t)` is the actual three-component physical velocity, `R(t)` its
actual projected Navier--Stokes momentum source, and `Ckin` is the
previously proved coordinatewise kinetic-only Bernstein ceiling.

The first bound uses *actual order-zero kinetic energy monotonicity*, not
an assumed full H3 ceiling. The second uses the accepted three-coordinate
Hilbert norm bound and the actual projected source lowpass theorem.

## Exact low/high compensation at an actual physical time

Write `Uhi=(I-P_rho)U`, `Rhi=(I-P_rho)R`. If, for a scalar rate and epsilon,

    ||Rhi-rate*Uhi|| <= eps*||Uhi||,

then the accepted exact physical kinetic identity and sharp cutoff geometry
force the quantitative inequality

    (rate-eps)*||Uhi||^2 <= 3*sqrt(E0(b))*Ckin(rho,E0(b)).

The contrapositive theorem states that a sufficiently large *actual*
highpass kinetic carrier necessarily fails this relative anti-heat
alignment condition. This removes abstract decomposition assumptions and
tracks the full physical source without a fictitious spectral state.

## The obstruction not yet removed

The RHS grows with the cutoff radius. The highpass Young-gap remainder
contains a `q^3` frequency weight and a frequency-dependent anti-heat
coefficient `q(xi)`, whereas this is an unweighted physical L2 gate against
a *constant* rate. An annular multiplier-variation estimate (and the correct
frequency-weighted normalization) is still necessary to translate small
Young-gap mass into small relative unweighted source error on moving shells.
That conversion is **not** claimed here. No endpoint H3 estimate, terminal
trace, or Clay continuation follows from this package.

No axiom, sorry, admit, or added physical regularity hypothesis is introduced.
Actual Lean compilation must be verified with the pinned repository toolchain.
