# Incompressible polarization reconstruction

Base checkpoint: `71580ece` (orthogonal covariance).

## Mathematical increment

For p=(x,y,0), x²+y²≠0, and a complex amplitude a satisfying
x a₀+y a₁=0, define

    α = (x a₁-y a₀)/(x²+y²), A = a₂.

Then a=(-y α,x α,A). This is an exact algebraic reconstruction, not an
estimate. The first two coordinate identities follow by multiplying the
divergence equation by -x and -y respectively. The third is definitional.

The complexification of a real orthogonal map has inverse given by the
complexification of its inverse. Consequently an arbitrary amplitude
perpendicular to O(x,y,0) can first be pulled back, reconstructed, and
pushed forward. No amplitude parameterization is assumed at the interface.

For three nonzero frequencies in the supplied plane, momentum fixes the
third frequency to (-x-z,-y-w,0). If all three pulled-back amplitudes have
zero normal component and satisfy incompressibility, the complete six-order
coefficient vanishes. This now follows for arbitrary amplitudes from their
reconstruction and the previously proved polynomial identity.

## Roadmap and limits

1. Completed in earlier checkpoints: shell identity, weighted moment bounds,
   sign audit, planar/normal polynomial identity, orthogonal covariance.
2. This patch: completeness of the planar/normal parameterization at nonzero
   frequencies, and cancellation for arbitrary amplitudes in a supplied frame.
3. Next: construct a common orthogonal frame from a momentum-conserving triad;
   separate noncollinear, collinear, and zero-frequency cases.
4. Then: translate the two-normal-amplitude remainder into intrinsic geometric
   quantities and prove estimates without artificial inverse-frequency loss.
5. Finally: justify six-order symmetrization of the field integral and assess
   whether the surviving geometric factor improves the comparable-frequency
   regime. Symbol cancellation alone does not establish an integral bound.

The coefficient α uses an unnormalized tangent direction and can grow near
zero frequency. This patch asserts no uniform bound on α, no measurable
choice of frequency-dependent frames, and no new PDE continuation result.
The existing positive/negative symbol examples remain consistent with planar
cancellation: mixed planar and normal amplitudes can survive.

## Validation

The audit file checks the reconstruction and cancellation declarations and
prints their axioms. Generated proof-index consistency, prose-fragment
validation, and whitespace checks are run before packaging. Lean compilation
must be performed with the repository's pinned toolchain on the user's machine;
no Lean executable is available in the patch-preparation environment.
