# Integrated annular gain and off-shell decomposition of physical H³ flux

**Base commit:** `15dc58599d48006a13111d4436953e5798ad767a`

## Core mathematical step

The existing real, solenoidal Schwartz recovery gives a pure complex sixth-power
Fourier flux for the old third-order Navier–Stokes energy transport.  The prior
module estimates each triad pointwise by a squared-radius spread.  This module
passes the factor into a *genuine restricted Bochner integral*.

For a complex Schwartz velocity `v`, let `F_v(p,r)` be the exact three-transfer
sixth-power flux and let `B_v(p,r)` be the sum of norms of its three complex
polarization-frequency contractions. For any measurable subset `s` of the
six-dimensional momentum-conserving carrier, suppose all three squared radii
are in `[lo,hi]` on `s`. Then, **provided** the exact budget is integrable on
`s`,

    ‖ ∫_s F_v ‖ <= 3 hi² (hi-lo) ∫_s B_v.

All phases are retained inside the original flux and the complex norm is taken
only afterward.  No division by frequency, zero-exclusion, or sign hypothesis.
The `hBudget : IntegrableOn B_v s` premise is deliberately visible: proving
uniform control of this quantity from physical H³ data is a separate task.

For physical solenoidal data, the full flux is integrable unconditionally by
its already proved ordered-kernel integrability. Consequently,

    ∫_{R6} F_v = ∫_s F_v + ∫_{sᶜ} F_v.

Combining both identities gives

    ‖∫_{R6} F_v‖ <= 3 hi² (hi-lo) ∫_s B_v + ‖∫_{sᶜ} F_v‖.

If the total flux exceeds the annular budget by `M`, the complementary
integral necessarily has norm greater than `M`. This is an explicit
**off-shell obstruction**, not an upper bound for off-shell mass.

## Physical PDE transfer

`exists_thirdFullPhysicalSnapshot_solenoidalAnnularFluxSplit244` chooses the
same previously constructed real divergence-free Schwartz approximants. For
any sequence of measurable triad sectors `s_n` (they may move with `n`), the
sum of the annular and off-shell complex integrals, multiplied by the true
`(2π)^7/3` imaginary-part normalization, converges to the actual old physical
`velocityH3TransportDerivative3At u t`. Both approximation energies converge
to the original `velocityH3Energy2At` and `velocityH3Energy3At` exactly.

**Neither term of the split is asserted to converge separately.** Nor is the
annular budget automatically controlled uniformly in `n`. The next hard
analytical step is to prove such control, or a stronger radial-scale separation
estimate, from the genuine physical Fourier state and dissipation.

## Validation

Run the registrar `--apply` and `--check`, regenerate the proof index, compile
the single Lean module, build the module and then the repository, and run the
fragment and axiom audits. Static source checks alone do not establish Lean
compilation or mathematical continuation.
