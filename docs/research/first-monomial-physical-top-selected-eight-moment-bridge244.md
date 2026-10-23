# Physical order-eight Fourier moments from positive-time selected slabs

Baseline: `49249529` (physical second-radial Fourier representatives).

## Verified input

The previously formalized theorem
`h3PreterminalSelectedUnitSpectralStateOnSlab_natMoment_integrable`
proves arbitrary finite-order raw Fourier moments at a selected positive-time
mild velocity snapshot, including `p = 8`.

## The remaining identification seam

The physical convolution estimate needs order-eight integrability of the
**actual** `h3TerminalVelocitySpectralStateAt`, not merely of a chosen
Schwartz approximation or selected restart solution.

The new predicate `h3PathVelocitySelectedSlabRealizedAt244` supplies a witness
`(t₀,E,Q,s)` with a genuine positive terminal-half-slab time, the physical
time relation `t=t₀+s`, and exact equality of the *full* weighted H³ velocity
states. Given this equality, the selected moment theorem applies to each
physical velocity coordinate. Covering every strict physical time eliminates
the explicit eighth-moment assumption in the already-closed alternative:

    top D₃ escape + selected-spectral coverage
      => D₁ unbounded on the tail OR raw velocity M₈ cofinally unbounded.

No independent second-radial Fourier-L² representative assumption survives;
that was eliminated at the previous checkpoint.

## What is not shown

The new spectral coverage premise is **not** derived from the original H³
path hypotheses. Existence of a selected mild slab at a positive time and
independent spectral equality with the actual physical velocity are different
claims. Pointwise physical smoothness at positive time also does not, by
itself, yield finite order-eight Fourier L¹ moments on all of R³. The next
hard-math step is proving the selected/old/physical equality and sufficient
covering geometry from the already existing overlap and restart uniqueness
results, without assuming their conclusion.
