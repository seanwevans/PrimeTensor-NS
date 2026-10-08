# Full-dissipation absorption threshold

Base: `f8936b5b`. New source:
[Control/DissipationFloor.lean](../../PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/DissipationFloor.lean).

Let E be the normalized H³ energy, D its dissipation, and C₁ the existing
spectral derivative-evaluation coefficient. The established PDE inequality is

    E' + 2D ≤ 4422 E + 4422 C₁ sqrt(E) E.

The new pointwise estimate retains both copies of dissipation. Under

    4422 C₁ sqrt(E) E ≤ 2D + c(t) E,

it yields

    E' ≤ (4422 + c(t)) E.

If c is integrable on one terminal energy-class tail, the constant 4422 is
also integrable there, and the existing linear-majorant continuation theorem
applies. No separate nonnegativity assumption on c is needed.

The zero-deficit specialization has the explicit sufficient threshold

    D ≥ 2211 C₁ sqrt(E) E.

All statements retain the admissible H³ path and energy-class tail hypotheses.
The public conclusions use the existing `SmoothContinuationExtension` package;
the reused scalar-majorant proof passes through terminal H³ control and the
already closed restart. The patch adds three theorems, no new universal
frontier proposition, and no modifications to existing library proofs.

## Scope and remaining estimate

This is an algebraic consequence of the established dissipative estimate,
with a sharper sufficient condition than simply discarding D. It does not
improve the underlying transport bound or establish the floor for arbitrary
solutions. It assumes neither integrability of sqrt(E) nor an independent
vorticity envelope, but it explicitly requires the displayed deficit bound
and integrability of c (or the stronger zero-deficit floor).

The next substantive question is whether spatial estimates can bound this
nonlinear deficit by an independently integrable coefficient. Defining c to
be the normalized positive deficit without proving its integrability would
not close that question. The threshold is sufficient, not asserted optimal.

Static import coverage and index checks are available locally. Lean compilation
and the new theorem axiom reports await the user's baseline run.
