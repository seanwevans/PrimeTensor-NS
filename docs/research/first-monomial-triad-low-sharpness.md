# Sharpness of the low-frequency normal term

Base checkpoint: `b611fb06` (complete low-frequency geometric bound).

## Explicit family

For t>0, take

    p=(1,0,0), q=(t,t,0), r=(-1-t,-t,0),
    a=(0,1,0), b=(0,0,1), c=(0,0,i).

Momentum and incompressibility hold. All three complex Euclidean amplitude
norms equal one. Relative to the frequency plane, the low-frequency amplitude
b is purely normal. The squared radii are

    P²=1, Q²=2t², R²=1+2t+2t².

The complete six-order coefficient is exactly

    C6(t) = -i t²(1+2t)².

For 0≤t≤1, its norm is at least t². The opposite-frequency partner with
conjugated amplitudes has the same coefficient: a,b are real and c is purely
imaginary. This verifies that adding just the reality partner does not cancel
this example. No actual Fourier field is constructed here.

## Failure of an unconditional quadratic bound

On this family, Q≤2t min(P,R). With epsilon=2t, let

    D(t)=epsilon² P³R³Q |a||b||c|.

The patch proves D(t)≤216t³ for 0≤t≤1. For every K≥0 it then constructs

    t = 1/[432(K+1)]

with 0<t≤1 and the stated low-middle condition, for which

    K D(t) < |C6(t)|.

Thus no uniform constant can give the quadratic-separation estimate for
arbitrary incompressible symbol data. The earlier conditional result is
consistent with this: the low amplitude has full normal fraction, not an
extra epsilon-small normal fraction.

In terms of the baseline energy/moment weight P³R³Q, the example's normalized
coefficient has linear order in t. The audit supplies the explicit polynomial
and the failure of the stronger quadratic bound; it does not assert an optimal
numerical constant for the existing linear estimate.

## Consequence for the research direction

The linear low-outer contribution cannot be eliminated solely by momentum,
incompressibility, six-order algebra, or the opposite-frequency reality pair.
Further improvement must use additional structure or a different estimate.
Potential sources to investigate are quantitative relations between nearby
high-frequency amplitudes, PDE-derived polarization restrictions, or
cancellation across a larger integrated frequency set.

This does not show that every integrated bound must lose linearly. Nor is it
a counterexample to a Schwartz estimate, a Navier-Stokes solution, or global
regularity. Those would require constructing fields and checking the relevant
analytic or dynamical hypotheses.

## Roadmap

- Completed: intrinsic geometry, full three-channel frequency bound, and the
  sufficient low-normal-smallness condition for quadratic gain.
- This patch: explicit audit showing that the additional condition cannot
  simply be dropped from the pointwise quadratic claim.
- Next: move toward justified six-order integral symmetrization and identify
  what information about the actual Fourier field could improve the integral.
- Comparable-frequency control and the physical H3 continuation estimate
  remain unresolved by this symbol audit.

## Validation

The coefficient formulas are direct polynomial proofs, independent of the
normal-shell decomposition. The audit checks the declarations and prints their
axioms. Source-index consistency, prose-fragment validation, and whitespace
checks are run before packaging. Lean compilation is pending on the user's
pinned toolchain; this environment has no Lean executable.
