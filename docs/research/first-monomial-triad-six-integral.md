# Six-order integral symmetrization and the physical interpolation

Base checkpoint: `367c102d` (low-frequency sharpness audit).

## Six measure-preserving changes

Use free variables (p,r), with q=-(p+r). Let

    M(p,r)=(p,q), S(p,r)=(r,p).

Both are measurable volume-preserving equivalences. The six changes

    id, M, M then S then M, M then S, S then M, S

give the ordered triads pqr, prq, qpr, qrp, rpq, rqp respectively.
The patch proves preservation for every map and proves integrability of
all six compositions from integrability of the original ordered kernel.

For any integrable complex kernel K, the integral of its six-term orbit
sum is exactly six times the integral of K. This is a Bochner integral
identity justified by integrability and measure-preserving equivalences.

## Actual Schwartz coefficient

`h3SchwartzTriadSixKernel` evaluates the existing complete six-order
coefficient on the three Fourier amplitudes of one Schwartz vector field.
The pointwise orbit identity proves that this is exactly the six-term orbit
sum of the ordered Schwartz kernel. No incompressibility is needed for
that identification, integrability, or the factor-six integral identity.

Under Fourier incompressibility, the previous shell identity gives

    integral C6 = 6 integral ordered = 3 integral shell.

## Physical normalization

For a real Schwartz realization of the logged velocity, with physical
divergence zero and the existing H3 path/class hypotheses, the patch obtains

    thirdOrderInterpolationTransportSum = (2*pi)^7 Im(integral C6).

The interpolation multiplicity three is exactly accounted for by the
three shell channels. There is no remaining factor 1/3 or 1/6 in this
physical interpolation formula. The assumptions are the same physical
Schwartz realization and path hypotheses used by the prior shell theorem;
the patch does not assert that arbitrary H3 snapshots are Schwartz.

## Research consequence

The geometric and sharpness analyses now concern a complete coefficient
whose integral is explicitly connected to the physical interpolation.
This provides the analytic starting point for studying cancellation across
frequency regions instead of seeking an impossible unconditional quadratic
pointwise bound.

No new norm estimate is claimed. The integral construction uses only
frequency permutations and no chosen normal field, so it does not require
a measurable choice of orthogonal frames. Inserting the normal-amplitude
representation inside an integral would still require an appropriate
intrinsic formulation or measurable-selection justification.

## Roadmap

- Established: complete pointwise geometry, separated estimates, and the
  failure of an unconditional quadratic low-frequency symbol bound.
- This patch: six-order integrability, exact symmetrization, and the physical
  interpolation identity with the full coefficient.
- Next: examine integrated frequency partitions and any relations among
  amplitudes of the same Fourier field that were absent from the symbol audit.
- A stronger integrated estimate and critical H3 continuation control remain
  to be established.

## Validation

The changes reuse the compiled middle-frequency equivalence and product-swap
preservation theorem. The audit checks the new declarations and prints their
axioms. Source-index consistency, prose-fragment validation, and whitespace
checks are run before packaging. Lean compilation is pending on the user's
pinned toolchain; no Lean executable is installed in this environment.
