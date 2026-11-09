# First excluded kinetic band of the adaptive signed-sixth-flux gauge

**Pinned base:** `88a9e177438ee22e51d787f8b4e3c0b34f138479` — diagonalize signed sixth flux kinetic gauge against actual H3 gap dissipation.

## Actual physical budget and exact next-band increment

For a fixed signed margin `eta>0` and actual H3 energy cap `E>=0`, the previously verified physical floor is

`h = thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E > 0`.

Let `D(k) = ∫_[tau(v k)+delta(v k), tau(v (k+1))] velocityH3DissipationAt(u,r) dr`. The already-proved finite-gap integrability theorem yields `D(k) -> 0`.

At the EARLIER physical kinetic anchor `b`, define the precise finite-gauge rate

`C(G) = 1 + 2 * sum_{j=0}^G L(j)`, where

`L(j) = thirdFullPhysicalKineticLowBandDissipationRate244(j,velocityH3Energy0At(u,b))`.

`L(j) >= 0`; NO monotonicity in `j` is postulated. The previous adaptive selection is the largest natural `g(k) <= k` with `32*C(g(k))*D(k) < h^2` (fallback zero before this condition is available).

The new exact discrete identity is `C(g+1) = C(g) + 2*L(g+1)`.

## New proof: saturation at the FIRST excluded band

When `g(k)<k`, suppose the next band also met the strict affordability condition. `Nat.le_findGreatest` would imply `g(k)+1 <= g(k)`, a contradiction. Thus

`h^2 <= 32*C(g(k)+1)*D(k) = 32*C(g(k))*D(k) + 64*L(g(k)+1)*D(k)`.

The original selected gauge is strictly affordable on every sufficiently late gap, so subtracting gives the sharp shell deficit inequality:

`0 < h^2 - 32*C(g(k))*D(k) <= 64*L(g(k)+1)*D(k)`.

The right side is necessarily strictly positive: the first excluded single kinetic band incurs nonzero physical rate-times-dissipation. This is a genuine quantitative shell-specific constraint, rather than just `g(k) -> infinity`.

If `g(k)=k`, the index bound itself is saturated and no rate lower bound at `k+1` is claimed. Both possibilities are retained.

## Synchronization with the physical signed sixth flux

`thirdFullPhysical_kineticGaps_signedLowMax_tenthResidual_adaptiveShell244` intersects the new shell ledger with the already proved physical adverse-sample theorem on the SAME original separated kinetic gaps and SAME adaptive gauge. The cofinal index may depend on the prescribed signed margin, energy cap, and residual epsilon; it does not depend on the selected observation time or inner cutoff.

On every sufficiently late gap, the shell ledger holds, and for **every** adverse signed physical sample whose previous tenth-power residual is excluded:

`(gap length)*h <= 16*D(k)` **or** `exists Q >= R : g(k)<Q`.

The coupled theorem does not assert the existence of an adverse observation on every gap or rule out its tenth-power residual. It does not rule out positive average dissipation: merely integrable physical dissipation can have nonvanishing local averages on shrinking intervals. No Clay continuation conclusion is claimed.

## Formal declarations

- `thirdFullKinetic_signedLowMax_adaptiveNextGauge_unaffordable244`
- `thirdFullKinetic_signedLowMax_finiteGaugeRate_step244`
- `thirdFullKinetic_signedLowMax_oneShell_pays_deficit244`
- `thirdFullKinetic_signedLowMax_physicalAdaptive_shellSaturation244`
- `thirdFullPhysical_kineticGaps_signedLowMax_adaptiveShellLedger244`
- `ThirdFullKineticSignedLowMaxAdaptiveShellCost244`
- `thirdFullPhysical_kineticGaps_signedLowMax_tenthResidual_adaptiveShell244`

## Verification

The audit registrar checks every declaration and checks/prints its axioms in the usual audit module. Run `lake env lean` on this module, the targeted Lake build, the global project build, and `proof/check_fragment.py --all` in the pinned project checkout. Static archive checks do not certify Lean kernel verification.
