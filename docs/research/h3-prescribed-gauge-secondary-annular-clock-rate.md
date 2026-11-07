# Attained secondary H³ annular PDE clock: compression or rate amplification

**Base:** `e96595415bd6a68ea49f7ec4e6089ed3ff9fbba4` — committed genuine physical annular persistence charge.

## Hard analytical step and sharp constants

The previous physical theorem `thirdFullPhysical_secondaryHighRadialSpike_annularPDECharge244` turns a high-radial spike at the ACTUAL selected secondary time `x` into a finite-band PDE-certified positive persistence interval. With a fixed `σ >= 0`, height `M > 0`, outer cutoff `Q = N+1`, attained compact-half-tail spectral/source maxima and real physical dissipative tail `B=∫_m^T D`, its exact statements include

    Λ = h3PathFiniteAnnulusPDEVariationCoefficient244 σ Q K C,
    δ = min (((T-x)/2)/2) ((M/2)/(2*(Λ+1))),
    δ * (M/2) <= B.

Here `Λ >= 0` follows from the existing **physical PDE** nonnegativity theorem, not an external Lipschitz hypothesis. The second alternative is equivalent to

    δ = min ((T-x)/4) (M/(4*(Λ+1))).

If the first argument is minimal, the finite integral directly gives

    (T-x)*M <= 8 B.

If the rate-limited second argument is minimal, it gives

    M^2 <= 8*(Λ+1)*B.

The original secondary witnesses are inside `[s,s+(T-s)/2]`, so `T-x >= (T-s)/2`; the first inequality thus implies `(T-s)*M <= 16*B`. This quantitative **primary-clock-or-PDE-rate** fork has no uniform cutoff, bounded transport rate, or pointwise dissipation ceiling premise.

## Exact witness order and cofinal transfer

The extended retained ledger `ThirdFullLateRetainedPrimarySecondaryAnnularClockRateCofinalLedger244` preserves its predecessor (`ThirdFullLateRetainedPrimarySecondaryHighRadialCofinalLedger244`) as the FIRST conjunct. For the already activated two-slice rate, positive kinetic gap and `48 sqrt(R B) <= 1`, it selects the SAME `s,eta2,J2,zSource,zState` before radius `σ` and height `M`. If the deep-excess primary clock remains wide and the moving-cutoff demand exceeds the physical threshold with `L_σ + 2M`, one of `x = zState` or `x = zSource` carries the original real annular charge **and** the above clock-or-rate inequality.

Only the finite outer `N` and its maximizing source/spectral rate observations `qSource, qState` are chosen after `σ,M`; none of the original secondary observations is changed. The no-terminal-H³-trace cofinal theorem carries forward the same initial minimal crossings, the prior pairwise-disjoint viscous sum, high-frequency escape and vanishing `B`.

## No false summation; unresolved mathematical obstruction

The new intervals `[x,x+δ]` can overlap the preexisting primary interval or other secondary intervals, so their charges are each individually bounded by the **same** `B`, never added to the old disjoint sum. This patch does not claim summability across these additional intervals.

The remaining hard step is an actual nonlinear PDE constraint on the solution-dependent `Λ`, its selected outer radius `N` and the drift of the secondary cutoff `J2`. The inequality `M² <= 8*(Λ+1)B` is only a necessary amplification lower bound; it does not preclude `Λ` diverging sufficiently rapidly while `B -> 0`.

Proof verification must use the pinned Lean 4.34.0-rc1 and mathlib, `python3 proof/generate_index.py`, the target build and complete theorem audit. The build environment used to create this ZIP does not have Lean; the archive must not be treated as compiled before the user's checks pass.
