# Solenoidal weak momentum residual and pressure-neutralization (base `d3b3db20`)

The earlier approximate residual theorem assumes a *strong* Hilbert derivative
`HasDerivAt V (W t + E t) t`. This patch changes the input to the physical
weak momentum identity against compact divergence-free tests, for projected
regularized velocity `V` and source `W + E` that belong to the Leray-fixed
Hilbert subspace. Existing solenoidal weak-to-strong uniqueness then produces
that Hilbert derivative without a pressure gradient in `L²`.

For every strict physical time interval `[a,b]`, the resulting physical FTC
error obeys

`‖D(a,b)‖ ≤ (2+b-a) max(ε_U, ε_R + η)`.

A generic scalar pressure-neutralization lemma allows an extra pressure-test
term whose value vanishes at every sampled physical time against a solenoidal
compact test. Its time integral vanishes pointwise, without separately bounding
the pressure gradient in the physical Hilbert norm.

## Exact frontier

This module DOES NOT construct the weak approximate solution from the old
classical PDE. In particular, the old-versus-canonical pressure gradient
is known to cancel against divergence-free tests snapshotwise, but it is not
proved here that the time-integrated physical velocity increments obey the
weak test equation. Proving that distributional-time equation remains the
missing analytic step, and no unconditional eighth moments, NSE continuation,
or resolution of 3D regularity is asserted.
