# Full-third real interpolation reflection and signed density

Base commit: `8c64a0e7` — exact Hermitian reflection of the 3+3+1 physical gradient slots.

This patch completes the matching **pointwise frequency-reflection identity** for
`thirdFullAxisRealInterpolationKernel244`, the existing 3+2+2 Schwartz Fourier
triad kernel of the same actual real, divergence-free velocity. Its proof uses
the project's `amplitudeKernel`, `complexCoefficient`, `mixedDot`, and
`amplitudeDot` without replacing the physical multiplier by a surrogate.

Under `(-p, -r)` and Hermitian Fourier reflection, both kernels satisfy

`K(-p,-r) = -conj(K(p,r))`.

The phase `(2 π i)^7` is purely imaginary. Consequently the signed real
contributions of both the gradient and interpolation channels are **even**
under simultaneous momentum reflection. The assembled density
`thirdFullAxisRealThirdSignedDensity244` includes all four gradient slots,
all five axis-index sums, their coefficient `2`, and the interpolation
coefficient `6`. It is pointwise even and vanishes off the existing common
12-sector tube when `0 < ρ ≤ min(δ, separationRadius)`.

## Remaining sign frontier

This patch does **not** claim the integral of the assembled density has one
sign. It also does not yet prove the integral of the newly assembled *real*
density is equal to the physical commutator, although the previously committed
complex Fourier integral identity contains the corresponding terms. That
integral assembly, followed by positive-sector control and an exact
signed noncancellation proof, is the next frontier.

Static Schwartz calculations do not imply Navier–Stokes global regularity.
