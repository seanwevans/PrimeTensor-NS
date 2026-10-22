# Exact physical second-order energy vs eighth Fourier moment escape

Base checkpoint: `49231f56` — inverse-Bessel raw Fourier `L¹` reduction to
order-two Fourier `L²` representatives.

## The physical multiplier

The Fourier multiplier in the second derivative energy is
`q(ξ) = (2π)² |ξ|²`. Consequently `q² = (2π)^4 |ξ|⁴`, and the exact
physical second-order energy is

    E₂(t) = ∑_{j=0}² ∫ q(ξ)² |û_j(t,ξ)|² dξ.

For any `G₂,j` representing `|ξ|² û_j` in Fourier `L²`, the established
Fourier-compatible physical trace implies

    (2π)^4 ‖G₂,j‖₂² ≤ E₂(t),
    ‖G₂,j‖₂ ≤ sqrt(E₂(t))/(2π)².

The proof uses the already formalized exact physical E₂/radial Fourier
identity, not an abstract spectral-state norm ceiling.

## Combining kinetic, inverse-Bessel, and E₂

For every terminal-tail anchor `s` and `t ≥ s`, the kinetic identity gives

    ‖û_j(t)‖₂ ≤ sqrt(E₀(s)).

The inverse-Bessel estimate therefore yields

    ‖û_j(t)‖₁ ≤ C_B [sqrt(E₀(s)) + sqrt(E₂(t))/(2π)²].

Thus a **physical E₂(t) ceiling** replaces the independently assumed
uniform second-radial Fourier norm ceiling from the previous checkpoint.
Under the retained strict-time eighth-moment integrability and the existence
of the order-two Fourier representatives, unbounded physical top dissipation
forces cofinally unbounded eighth-order velocity Fourier moments whenever
E₂ remains bounded.

Without an E₂ ceiling, the result is the precise necessary alternative

    (unbounded E₂ on the initial terminal tail)
         OR
    (eighth raw Fourier moment unbounded on every later subtail).

The second branch is cofinal; the first is initially stated as unboundedness
on the full selected strict tail. The existence of order-two Fourier `L²`
representatives is an explicit separate premise. Deriving it from the physical
second Fourier jet is the next regularity bridge. No unconditional Navier–Stokes
continuation or singularity exclusion is claimed.

Finally, the existing exact physical identity `velocityH3Dissipation1At =
velocityH3Energy2At` rewrites the first branch as growth of the **first
physical dissipation block**, without any spectral normalization convention.
