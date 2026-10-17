# Canonical weighted H³ signed monomial: quartic energy control

Base checkpoint: `9db83b17` (canonical functional).

## Goal

Carry the unconditional physical real-Schwartz 243-slot inequality

`|M(f)|^4 ≤ K^4 E2(f) E3(f)^5`

into the **canonical** weighted spectral H³ functional without a new
approximation hypothesis or any control of fourth derivatives. Define

* `Q2(U) = Σ_{27 slots} ‖real physical second Fourier jet(U)‖_L²²`
* `Q3(U) = Σ_{81 slots} ‖real physical third Fourier jet(U)‖_L²²`.

Both are continuous, nonnegative functions on the native H³ weighted state.
Exact derivative matching means an arbitrary matched Schwartz witness at
index n has E2=Q2(Vn) and E3=Q3(Vn); its signed monomial converges to the
canonical choice-independent M(U). Taking the limit proves the original
constant without coefficient inflation:

`|M(U)|^4 ≤ K^4 Q2(U) Q3(U)^5`.

The cubic-jet norm estimate gives Q3(0)=0, hence M(0)=0. The quartic
bound and continuity of Q2 and Q3 prove continuity of M at the origin.

## Delimitations

This is not a full continuity theorem away from zero (which calls for a
cross-field quantitative modulus), does not give divergence-free Schwartz
approximants, and does not identify M(U) with the original physical
Navier–Stokes nonlinear H³ transport integral. Those are separate frontier
items. No fourth-order spectral control or Schwartz representation of the
physical velocity is assumed.

The Lean patch is uncompiled in the assistant environment; the user's
local Lean 4 + mathlib build is the correctness check.
