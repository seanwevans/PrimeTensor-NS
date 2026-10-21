# Physical differential identity for normalized Fourier moment variance

Base checkpoint: `c81972b6` — normalized physical H³ Fourier moment rigidity.

## The new PDE-linked identity

The scalar normalized Cauchy variance is

    R(t) = (E0(t) D3(t) - E2(t)^2)/(E0(t) D3(t))
         = 1 - E2(t)^2/(E0(t) D3(t)).

Unlike the preceding concentration inequalities, its time derivative can be
computed from *already established differentiability theorems* for the actual
physical energy states. The order-zero and order-two energy derivatives are
`velocityH3FormalDerivative0At` and `velocityH3FormalDerivative2At`.
The fourth-radial physical Hilbert path used in the terminal derivative program
has `D3'` equal to a sum of three genuine real Hilbert pairings.

Define `A = E0*D3`, `A' = E0'*D3 + E0*D3'`. Then on each strict physical
energy-class interval where `E0,D3>0`:

    R' = [ E2² A' - 2 E2 E2' A ] / A².

In particular,

    R' < 0  ==>  2 E2 E2' A > E2² A'.

This gives the *signed source orientation* that a dynamically collapsing
variance must satisfy. The theorem connects the Fourier rigidity program to
the actual time-dependent Navier–Stokes states via preexisting H³ derivative
closures, with no new assumptions of spectral spreading or moment smoothness.

## Formalization scope

The module defines the normalized variance on the existing physical
fourth-radial Hilbert path, proves equality with the earlier physical
normalized Fourier variance at every strict time, then proves its exact
`HasDerivAt` and ordinary `deriv` formula. The necessary strict signed-excess
criterion is deduced by positivity of the physical kinetic/top-dissipation
product. The time derivative is not asserted to have a sign; the remaining
hard problem is to estimate the signed middle-moment growth relative to
kinetic and fourth-radial dissipation evolution, particularly along a
hypothetical terminal sequence.

## Audit

Register the module in `PrimeTensor.lean` and central audit; record `#check`
and `#print axioms` for all definitions and theorems, regenerate proof index,
check fragments, compile module, run full build and baseline audit.
