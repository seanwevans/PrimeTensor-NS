# Intrinsic physical homogeneous H3/2 Fourier-Sobolev domain (2026-10-10)

Parent checkpoint: `7ef2f8e3`, *realize homogeneous H3/2 fractional derivative in real L2*.

## What this adds

`OneComponentPhysicalHomogeneousSobolev.lean` defines an actual
physical-field Fourier-Sobolev criterion for `f : H3ScalarL2` independently
of the project's weighted H3 spectral solver states.

The predicate `H3AuditPhysicalHomogeneousThreeHalvesDerivativeSpec f D`
asserts that a **real** Euclidean physical `L²` field `D` has complex
Fourier transform equal almost everywhere to

    ((2π)^2 |ξ|²)^(3/4) * 𝓕(f)(ξ).

Equivalently the multiplier is
`sqrt (sqrt (h3FourierGradientSquare ξ ^ 3))` in the project's existing
`exp(-2π i x·ξ)` normalization.

`H3AuditPhysicalHomogeneousThreeHalvesSobolev f` is existence of such a
derivative. The derivative is **unique** by Fourier injectivity and the
real-projection inverse to complexification.

For every strict H3 preterminal physical time the actual zeroth-order
velocity component has this physical Fourier-Sobolev property. Its unique
derivative is the real physical `L²` fractional derivative constructed at
`7ef2f8e3`. One physical curl-component endpoint plus the existing H3 energy
class still gives the terminal `L²_t` estimates for both transverse
real derivatives on a common interval.

## Remaining boundary

This is a complete definition and verification of the *Fourier-multiplier*
homogeneous derivative relation for the actual project physical scalar `L²`
fields, not an equivalence proof for a separately defined homogeneous
Sobolev space of distributions or for every normalization used in an
external article. The Liu--Zhang local-strong-solution eligibility,
time interval from zero, and published continuation conclusion are
still unformalized. No unconditional Navier--Stokes continuation is claimed.
