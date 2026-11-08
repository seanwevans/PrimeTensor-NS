# Tolerance-free instantaneous viscous gate for cofinal signed LowMax transport

**Pinned base:** `4a589befd53edf5f759336b2c188c15b870c065b`.

## Previously unresolved physical high-frequency alternative

The preceding theorem `thirdFullPhysical_kineticGaps_signedLowMax_radiusEnergyEscape244`
proves, on sufficiently late original separated kinetic gaps, a four-way alternative
for **every** natural cutoff `R`, positive Schwartz recovery tolerance `gamma`,
and adverse physical third-order observation `t` inside that same gap.
Its first arm was the quantitative, but still approximate, true high-H3 Fourier
carrier:

`eta/2 < A(t) * (||P_R U(t)|| + gamma)^2`

where `A(t) = ((2*pi)^7/3) * 1944 * C1 * (E3(t)+1)`.
The cutoff and adverse time are allowed to move with the gap. No terminal-
uniform H3 energy ceiling, fixed R, or two-time flux-jump assumption is made.

## Hard step: eliminate gamma *after* fixing the physical time

The other three branches (earlier physical cubic baseline, radius/physical-energy
threshold escape, and a strictly positive inside-gap annular dissipation charge)
are INDEPENDENT of `gamma`. For a fixed original gap, radius and physical
adverse time, if any of those three branches holds we are finished. If none
holds, the true physical tail inequality holds for **every gamma>0**.

The scalar lemma `thirdFull_scalar_signedLowMax_removePositiveTailTolerance244`
is a genuine limit argument using `gamma_n=1/(n+1)>0` and the standard
`tendsto_one_div_add_atTop_nhds_zero_nat` result. It yields

`eta/2 <= A(t)*||P_R U(t)||^2`.

Unlike a direct selection of a small `gamma`, there is **no constant loss**
or additional recovery hypothesis. The strict inequality necessarily becomes
nonstrict in the limit.

## Genuine instantaneous physical H3 dissipation

The already accepted coercivity theorem
`thirdFullPhysical_fullViscousCoercivity244` establishes at each strict
physical time

`(R+1)^2 * ||P_R U(t)||^2 <= velocityH3DissipationAt(u,t)`.

Multiplying the limiting signed-tail inequality by `(R+1)^2` and the radial
coercivity by the nonnegative actual energy factor `A(t)` yields the new,
strict-time, fully physical conclusion

`(R+1)^2 * (eta/2) <= A(t) * velocityH3DissipationAt(u,t)`.

This is a pointwise viscous-spike statement; it does **not** provide a lower
bound on how long the spike lasts. The separately certified inside-gap
viscous window retains its previous genuine positive but potentially
shrinking width.

## Four physical alternatives without Schwartz errors

`ThirdFullKineticSignedLowMaxGammaFreeViscousEscape244` contains exactly:

1. the exact instantaneous full-H3 viscous spike above;
2. the original cubic physical left-endpoint LowMax baseline;
3. either `J<R`, `E<E3(t)` or `E<E3(x)` for arbitrarily prescribed J and E;
4. a positive-width, forward- or backward-contained physical annular
   width-times-height charge less than any prescribed positive epsilon.

The theorem
`thirdFullPhysical_kineticGaps_signedLowMax_gammaFreeViscousEscape244`
retains the original uniform-in-cutoff cofinal index from the accepted source
and dissipation tail proofs. In particular, the index does NOT depend on
R, t or gamma, because gamma has been eliminated *inside* that uniform quantifier.

`thirdFullPhysical_kineticGaps_signedSurplus_gammaFreeViscousEscape244`
automatically selects the adverse time from the original actual signed
integrated surplus, when it exceeds its explicit physical lower-order budget.
The signed-surplus premise remains conditional on the individual gap.

## Remaining obstruction

The instantaneous H3 dissipation may have arbitrarily narrow temporal spikes,
so finite time-integrated H3 dissipation does not alone rule out this branch.
The original kinetic-height clock and moving-radius/energy bounds must still
be synchronized to obtain a nonvanishing temporal persistence width, while
the physical left-endpoint cubic baseline remains a genuine carrier.
No unconditional Navier--Stokes continuation theorem is asserted.

## Verification

Run registrar `--apply` and `--check`, `proof/generate_index.py` and its
`--check` mode, targeted Lean elaboration, targeted and full Lake builds,
and the complete proof-fragment audit on the pinned base. The archive is
statically verified; Lean kernel verification is to be performed locally.
