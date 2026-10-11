# Initial canonical overlap from actual physical compact weak-test comparison

Checkpoint: `61b78d11` (`identify initial physical L2 from compact weak subsequences`).

## New implication

Rather than assuming that the actual old three-component weighted Fourier H³
velocity **equals** the selected mild solution on an initial interval, assume
that at each strictly positive time their **real physical L² pairings** agree
against every compact smooth scalar weak test. The selected restart is anchored
at the actual encoded initial datum

`U₀ = velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0`.

The module proves:

1. Physical compact smooth test density identifies the old and selected
   decoded real L² velocity at each time.
2. Exact inverse physical-carrier transport identifies the real Fourier
   decoders. The old encoder is realizable, and the selected mild solution
   from a genuine real initial state remains realizable.
3. Real decoder injectivity on realizable spectral states identifies the
   complete old and selected weighted Fourier H³ state.
4. Existing initial canonical-overlap machinery gives actual right H³ trace.
   Because the selected datum is the genuine initial H³ encoding, physical L²
   convergence and H³ energy right continuity follow without a separate weak
   initial subsequence or time derivative hypothesis.

## Boundary

The compact weak-test **old/selected comparison at all positive times remains
an explicit unproved PDE-side uniqueness condition**. This patch makes that
condition precise and connects it to canonical overlap; it does not derive it
from the Navier–Stokes equations. The independent terminal actual-vorticity
strong H³ endpoint is still required for the full-time 3/2 Sobolev statement.

No new axioms, sorry, or admit are used. Lean compilation must be checked on
the repository's pinned Lean/mathlib toolchain.
