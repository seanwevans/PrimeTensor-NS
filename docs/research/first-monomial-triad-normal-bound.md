# Quantitative tangential-normal triad geometry

Base checkpoint: `3f1f275b` (intrinsic normal-shell decomposition).

## Projection and exact energy split

For a real unit normal n and a complex polarization a, set

    a_tan = a - (n·a)n.

The amplitude norm is the complex Euclidean l2 norm. The patch establishes

    |a_tan|² + |n·a|² = |a|².

For a real frequency p perpendicular to n, p·a=p·a_tan. Cauchy-Schwarz then
gives |p·a| ≤ |p| |a_tan|. In particular, the contracting amplitude in a
shell channel contributes only its tangential part.

## Complete coefficient bound

Define the exact scalar weight

    W(p,q,r) = |p·r| |p| |q·q| |r·r-p·p|.

The intrinsic normal-shell identity and the triangle inequality give

    |C6| ≤ W(p,q,r) |b_tan| |n·a| |n·c|
         + W(p,r,q) |c_tan| |n·a| |n·b|
         + W(q,p,r) |a_tan| |n·b| |n·c|.

The patch proves existence of a real unit common normal for which this bound
holds for every incompressible momentum triad, including zero frequencies.
The new weight retains the actual dot product and squared-radius difference;
it uses |p| for the mixed contraction. It does not yet incorporate the earlier
smaller-outer-radius or middle-frequency estimates.

## Explicit quadratic gain

If each normal amplitude satisfies

    |n·a| ≤ ε|a|, |n·b| ≤ ε|b|, |n·c| ≤ ε|c|, ε ≥ 0,

then the displayed majorant is at most

    ε² [W(p,q,r)+W(p,r,q)+W(q,p,r)] |a| |b| |c|.

This is a conditional gain relative to the displayed three-weight envelope.
Incompressibility alone does not supply those normal-smallness hypotheses.
The exact Pythagorean identity also captures the opposite limit: a purely
normal amplitude has zero tangential component, so its contracting channel
vanishes.

## Roadmap

- Established: intrinsic exact remainder with two normal amplitudes per channel.
- This patch: exact projection energy split, tangential contraction estimate,
  complete pointwise geometric bound, and conditional quadratic gain.
- Next: combine the geometric bound with frequency separation/angle estimates
  without discarding the paired normal amplitudes.
- Analytic question: determine whether the actual PDE supplies suitable
  geometric control, or whether integration supplies cancellation that a
  pointwise norm bound cannot capture.
- Integral work: justify six-order symmetrization and compare with the existing
  third-energy/first-moment bound. No stronger integral bound is claimed here.

No measurable normal selection, unconditional small parameter, sign theorem,
or continuation result is asserted.

## Validation

The Pythagorean API was checked in pinned Mathlib's InnerProductSpace/Basic.lean.
The audit checks the new projection and quantitative declarations and prints
their axioms. Source-index, prose-fragment, and whitespace checks are run before
packaging. Lean compilation is pending on the user's pinned toolchain; there
is no Lean executable in this environment.
