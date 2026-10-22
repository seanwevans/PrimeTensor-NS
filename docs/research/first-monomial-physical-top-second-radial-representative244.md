# Actual second-radial Fourier representative from physical H³ jets

Base: `66c2d3d6` (physical lower-dissipation / eighth-moment terminal alternative).

## Closing the representation premise

The prior theorem bounded an arbitrary `G₂ ∈ L²` representing `|ξ|² û_j` by the
actual second-order physical energy `E₂(t)`, but required the representative's
existence separately. On a strict physical H³ slice, Fourier compatibility
already establishes

    Integrable (q(ξ)^2 · ‖û_j(t,ξ)‖²),   q(ξ)=(2π)²|ξ|².

Using `q²=(2π)^4|ξ|^4`, positivity of the constant, and the a.e. identification
of the terminal raw spectral velocity with the physical Fourier velocity, we
obtain integrability of

    ‖|ξ|² û_j(t,ξ)‖².

Strong measurability follows from the continuous radial weight and the already
proved raw Fourier `MemLp 2`. Therefore `MemLp.toLp` constructs a canonical
`G₂` with the exact requested a.e. representative. No new analytic premise is
necessary for this order-two construction.

## Sharpened endpoint necessary alternative

Under physical top D3 escape and the **remaining explicit strict-time order-8
raw Fourier moment integrability** used by the nonlinear convolution Young
estimate, either physical first-order dissipation `D₁(t)=E₂(t)` is unbounded
on the selected terminal tail, or genuine eighth-order velocity moments
become arbitrarily large on every later terminal subtail.

The Fourier-representative existence hypothesis has been removed entirely.
The order-eight integrability premise has **not** been removed. This is a
necessary blowup alternative, not a proof that blowup is impossible.
