# Critical H3 dyadic source peaks and the nine-pair velocity-convolution frontier

Base: `353f89c2704954f20890babdf50370e37b29532a`.

## New physical localization

The accepted critical dyadic source-peak alternative says that, on a
last-half interval `[s,t]` with `T-s=2(T-t)`, when the later cubic rate holds
and the earlier critical anchor is below a specified threshold, there exists
`r in (s,t)` with the *actual third-radial Leray forcing* bound

    K D3(r) < (2*pi)^6 * sum_{j=0}^2 ||F3_j(r)||_2^2.

The preexisting physical order-four convolution corridor proves, component by
component, that each `||F3_j(r)||_2` is bounded by the same **nine ordered
velocity-product convolutions**:

    A4(r) = sum_{k=0}^2 2 * sum_{j=0}^2 (2*pi) *
              || |xi|^4 * (U_k * U_j)(xi) ||_2,

where the actual multiplication, Fourier conventions and Leray projector
are encapsulated in the kernel-checked library definition
`h3RawOrderFourVelocityConvolutionEnvelope244`. The expression above is
schematic; no new convolution normalization is postulated.

It follows that at a real strict physical time

    K D3(r) < 3*(2*pi)^6 * A4(r)^2.

Conversely, a uniform inequality

    3*(2*pi)^6 * A4(r)^2 <= K D3(r)

on `[s,t]` eliminates the large normalized cubic source branch and forces

    8 log 2 - 3 K (t-s) <= log B + 8 log(T-s) + 3 log D3(s).

This is a *velocity-only* source-peak frontier: the missing PDE estimate is
not a bound on an abstract forcing variable but a bound on actual solenoidal
quadratic velocity convolutions relative to top-third dissipation.

## The explicit regularity boundary

The preexisting order-four convolution estimate requires
`H3RawFourierMomentIntegrable (8 : Real)` for each velocity component.
This requirement is carried into each new physical theorem through
`hMom : forall t (ht : t in (a,T)), h3PathVelocityRawEightMomentsAt244 ...`.
**The H3 energy-class hypothesis alone does not supply these order-eight
raw Fourier moments.** We have not manufactured such an implication.
Proving a version with only the natural H3 / viscous available moments,
possibly via frequency truncation plus an explicit high-pass defect, is the
next genuine mathematical task. The stated results do not claim a PDE upper
bound on A4/D3 or an unconditional continuation theorem.

## New declarations

- `thirdFullPhysicalCriticalOrderFourEnvelopeAt244` (physical zero-extended definition)
- `thirdFullPhysical_thirdRadialForcing_le_orderFourEnvelope244`
- `thirdFullPhysical_thirdRadialForcingMass_le_orderFourEnvelopeSquare244`
- `thirdFullPhysical_nearCriticalAnchor_forces_orderFourVelocityConvolution244`
- `thirdFullPhysical_dyadicOrderFourConvolutionCeiling_forces_criticalAnchorExcess244`

Run the new audit registration and index regeneration before `lake env lean`
and `lake build PrimeTensor`. Static checks cannot establish Lean compilation.
