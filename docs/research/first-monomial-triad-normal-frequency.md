# Combining frequency separation with normal-amplitude geometry

Base checkpoint: `9f04d20f` (tangential and paired-normal bounds).

## Smaller outer radius and shell gap

For p+q+r=0 and q·b=0, momentum gives p·b=-r·b. If the real common
normal n is perpendicular to p and r, both contractions see only b_tan.
Consequently, writing P=|p|, Q=|q|, R=|r|,

    |p·b| ≤ min(P,R) |b_tan|.

The existing shell-gap argument works in every real inner product space and
has now been connected to the generic coordinate-frequency API:

    ||r|²-|p|²| ≤ (P+R)Q.

Together with |p·r|≤PR, this bounds the complex shell coefficient by

    Wsep(p,q,r) |b_tan|,
    Wsep(p,q,r)=PR min(P,R)(P+R)Q³.

No nonzero-frequency or division assumption is needed.

## Complete coefficient envelope

The intrinsic decomposition gives a unit common normal and the bound

    |C6| ≤ Wsep(p,q,r)|b_tan||n·a||n·c|
         + Wsep(p,r,q)|c_tan||n·a||n·b|
         + Wsep(q,p,r)|a_tan||n·b||n·c|.

This combines the frequency structure from the earlier shell analysis with
the newer tangential/normal structure. It does not discard the two normal
amplitudes in any channel. The earlier exact-dot-product majorant remains
useful: replacing dot products and shell gaps by radial bounds need not make
an estimate numerically smaller for every triad.

## Low-middle channel

If Q≤ε min(P,R), ε≥0, then

    Wsep(p,q,r) ≤ 2 ε² P³R³Q.

The proof uses min(P,R)(P+R)≤2PR and the previously established scalar
low-middle inequality. A channel theorem keeps the geometric factors:

    |S(p,q,r;b)(n·a)(n·c)|
      ≤ 2 ε² P³R³Q |b_tan| |n·a| |n·c|.

This gain concerns the displayed channel. In the other two channels the
middle frequency is different. Small Q alone does not justify assigning the
same low-middle gain to all three terms of the complete coefficient.

## Roadmap

- Established before this patch: intrinsic decomposition, exact projection
  energy split, geometric norm bound, and conditional normal-fraction gain.
- This patch: smaller-outer-radius tangential bound, radial shell-gap factor,
  combined complete envelope, and a low-middle geometric channel estimate.
- Next: reconcile all three channel weights on a common frequency partition,
  particularly the low-outer roles created by permuting one low frequency.
- Analytic work: justify six-order integral symmetrization and determine
  whether PDE geometry or integrated cancellation yields a useful gain in
  the comparable-frequency regime.

No new integrated estimate, measurable frame selection, unconditional
polarization smallness, or continuation result is asserted.

## Validation

The proof reuses the existing compiled generic shell-gap and scalar low-middle
lemmas. The audit checks the new declarations and prints their axioms.
Source-index consistency, prose-fragment validation, and whitespace checks
are run before packaging. Lean compilation is pending on the user's pinned
toolchain; no Lean executable is installed in this environment.
