# Reality and odd-derivative phase in the low-normal sharpness family

Base commit: `367c102d` (audit sharpness of low-frequency normal triad contribution).

This note refines the **finite-dimensional symbol** audit. The earlier family
has a six-order coefficient

    C6(t) = -i t^2 (1 + 2t)^2.

At the reflected frequencies with conjugated polarizations, the coefficient
is the same. Consequently the reality pair is

    C6(t) + C6^ref(t) = -2i t^2 (1 + 2t)^2.

Its real part vanishes. However the real part **after inserting one factor i** is

    Re[i (C6(t) + C6^ref(t))] = 2 t^2 (1 + 2t)^2.

The new Lean module proves this identity, its lower bound for nonnegative t,
and the failure of any uniform bound using the previously defined
quadratic-separation weight (of cubic order in t). In particular, merely
pairing opposite frequencies does not dispose of the symbol's magnitude once
an odd Fourier phase is relevant.

**Important scope restriction:** The module deliberately uses multiplication
by `Complex.I` as an *algebraic phase audit*. It does not prove that this is
the prefactor of the actual first H3 energy monomial. That requires a separate
Fourier-to-physical identification that accounts for the derivative indices,
normalization, conjugation conventions, the real pairing, and all physical
source terms. Nor does the single-triad example rule out cancellations after
integration over a frequency region, or show that actual Schwartz Fourier
transforms realize the example in a way that preserves a lower bound.

Next analytical steps: (1) establish the physical Fourier phase explicitly;
(2) establish the six-order integral under an invertible change of variables
and sufficient integrability hypotheses; (3) test whether localization near
the sharp family survives the integrated kernel with reality and divergence
constraints. Avoid enlarging a pointwise symbol statement into a global
Navier–Stokes claim.
