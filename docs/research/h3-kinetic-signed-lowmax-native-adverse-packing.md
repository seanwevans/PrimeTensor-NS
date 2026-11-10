# Native adverse signed sixth flux: choose actual physical annuli, then pack

**Base commit:** `aae5a30e8c86eea688bb67a632b4f642f3e27d5e`

## Genuine gap in the previous interface

The certified spectral packing and finite-frequency occupancy theorems assumed
an arbitrary activity predicate `active : ℕ → Prop` together with a supplied
`ThirdFullKineticSignedLowMaxGapPackingCertificate244` for every active index.
The earlier theorem `thirdFullPhysical_kineticGaps_signedLowMax_trueCertifiedEleventh244`
actually **constructs** such annuli on sufficiently late original kinetic gaps
from native signed-flux observations, tenth-power-residual exclusion, and
strictly low relative gap dissipation. This module combines them.

## Native activity

For user-selected sequences of physical inner cutoffs `R k` and observation
times `t k`, the predicate `ThirdFullKineticSignedLowMaxNativeAdverseGap244`
requires precisely:

1. `t k` lies in the original kinetic gap;
2. `eta < -velocityH3TransportDerivative3At u (t k)`;
3. the existing `ThirdFullKineticSignedLowMaxTenthPowerResidual244` does **not** hold;
4. `16 D_k < (y_k-x_k) h`, where `h` is the fixed positive capped height floor.

It does not mention any annular certificate, outer cutoff, or persistence
width. The residual exclusion already implies the needed physical energy cap
`velocityH3EnergyAt u (t k) ≤ E` by its explicit energy-excess branch.

## Constructed physical selection

The theorem `thirdFullPhysical_kineticGaps_signedLowMax_nativeAdverseCertifiedOccupancy244`
obtains a single cofinal threshold `k0` from the accepted certified-eleventh
physical theorem. For every `k ≥ k0` at which native activity holds, classical
choice selects `Q k` and `w k` **from that theorem**. The selected pair retains
all components of `ThirdFullKineticSignedLowMaxGapPackingCertificate244`:
physical annular H3 peak at time `t k`, actual `R k ≤ Q k`, exact positive
symmetric in-gap persistence width, and integrated full-H3 gap charge.

Outside active late gaps the chosen values are irrelevant; no assertion is
made about them. The proof then feeds these selected certificates to the
accepted `thirdFullPhysical_kineticGaps_signedLowMax_certifiedFrequencyOccupancy244`
theorem. The count is restricted to `k ≥ k0` and to *actual* adverse observations
with cutoff `Q k ≤ B`, and obeys

    count(B,m) * h² / (32 K(E0)) ≤ (B+1)^11 * integral_a^T D_H3.

The same selection works simultaneously for **every** finite prefix `m` and
frequency threshold `B`; there is no monotonicity premise on `Q`.

## Mathematical scope

This is a native derivation of the physical finite-frequency capacity law,
not a continuation theorem. It does **not** establish existence, recurrence,
positive density, or a bounded-growth law for adverse flux observations.
Those remain hard PDE obligations. The proof relies on the accepted finite
terminal H3 dissipation hypothesis and existing signed-flux/tenth-residual
interface, not an invented trace or axiom.

## Local verification

Use the guarded ZIP script to run the new module under the pinned Lean and
mathlib toolchain, regenerate the proof index, run the audit, and only then
commit and push. The patch was not Lean-kernel checked in its construction
environment.
