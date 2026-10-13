# A common low-frequency bound for the complete triad

Base checkpoint: `d8636454` (frequency separation and normal geometry).

## Three roles of one low frequency

Write P=|p|, Q=|q|, R=|r| and suppose Q≤ε min(P,R), ε≥0.
Let Ta,Tb,Tc denote tangential polarization norms and Na,Nb,Nc the absolute
normal amplitudes for the unit common normal furnished by the intrinsic
identity. The complete coefficient is bounded by

    |C6| ≤ 2 P³R³Q [ε² Tb Na Nc + ε Nb (Tc Na + Ta Nc)].

The first shell channel has q as its middle frequency and gains ε².
In the other two channels, q is an outer frequency and yields linear ε gain.
Both of those channels contain the normal amplitude Nb of the polarization
at q. This is why the linear part has the common factor Nb.

The scalar weight estimates require no momentum or divergence hypotheses;
those enter when connecting the weights to the complete coefficient.
All estimates include zero frequencies and require no division. The bound
is valid for every ε≥0; its interpretation as a small gain requires small ε.

## A targeted sufficient condition

If the low-frequency polarization satisfies

    Nb ≤ ε |b|,

then the whole coefficient has the quadratic bound

    |C6| ≤ 6 ε² P³R³Q |a| |b| |c|.

The proof uses the existing Pythagorean projection identity to bound each
tangential or normal amplitude by its full Euclidean norm. There is no
smallness assumption on the normal fractions of the two high-frequency
polarizations a and c.

If Nb=0 exactly, both linear channels disappear from the geometric envelope,
leaving the sharper expression 2 ε² P³R³Q Tb Na Nc. This is an algebraic
consequence of the envelope and does not require the high amplitudes to be
planar.

The final existence theorem provides a common unit normal, the complete
three-channel bound, and the conditional quadratic consequence for that same
normal. It does not assume or prove that the extra normal-smallness condition
holds for a Navier-Stokes solution.

## Roadmap

- Established: common frame, intrinsic normal-shell identity, projection energy
  split, and frequency/polarization estimates for individual channels.
- This patch: reconcile all three channels on one low-q region and identify
  the low-frequency normal amplitude as the linear-loss factor.
- Next analytic question: can the PDE, spectral geometry, or integration control
  that specific low-mode normal component, or exploit cancellation between
  the two linear channels before taking absolute values?
- Integral work remains: justify six-order symmetrization and compare the
  resulting complete bound with the established energy/moment estimate.
- Comparable-frequency interactions still have no small separation parameter.

No unconditional quadratic gain, measurable frame choice, integrated bound,
or continuation result is asserted.

## Validation

The proof reuses the compiled separated geometric envelope and low-middle
weight theorem. The audit checks the new bounds and prints their axioms.
Source-index consistency, prose-fragment validation, and whitespace checks
are run before packaging. Lean compilation is pending on the user's pinned
toolchain; this environment has no Lean executable.
