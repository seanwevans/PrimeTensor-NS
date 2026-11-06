# Secondary exact PDE clock from a two-slice late viscous obstruction

**Base commit:** `78acf3dc9cd08a8ea1d44e2ac6ab8e2c7b92049e`

## Physical input

On the prescribed-gauge last branch, the original witnesses give
`A² ≤ 96 C0 (J+2)^5 B (E0+3 D(sState))(E0+3 D(sSource))`,
where `B = ∫_m^T D`, `A=H(vk)^4/(2P)`, `E0=1+6 E_kin(b)`,
and `C0=3+C_L`. The times `sState,sSource` are actual attained maxima
inside the late half-terminal interval.

For any `h>0` with the *kinetic-only threshold test*

`96 C0 (J+2)^5 B (E0+3h)^2 < A²`,

at least one attained observation satisfies `h < D(s)`. This implication
uses nonnegative real products and NO L-infinity estimate on `D`.

## Second exact physical PDE clock

At that actual high-dissipation time `s`, the existing finite-radial
capture theorem supplies `J2` with `h < D_low,J2(s)`. Applied again to
the established projected-Navier--Stokes low-band variation theorem, this
gives attained late source/state maxima and an **exact** positive width

`η = min ((T-s)/4) ((h/2)/(2*(Λ(J2,K2,C2)+1)))`,

`h/2 < D_low,J2(q) ≤ D(q)` on `[s,s+η]`, and

`η h/2 ≤ ∫_m^T D(q) dq`.

The new time `s` is **one of the original selected late maxima**; the new
PDE clock is not a separate hypothetical source. The new interval can
overlap the first late PDE interval and other selected intervals, so its
integrated charge cannot be added independently to the old charges.
The new `J2`, source/state envelopes and exact width may grow/compress
without bound. This is a quantitative necessary condition, not an NS
regularity theorem or terminal-uniform coercive width.

## Lean declarations

- `thirdFull_scalar_twoSliceRate_forces_actualViscousObservation244`
- `ThirdFullLateSecondaryPDEClock244`
- `thirdFullPhysical_twoSelectedTimes_secondaryPDEClock244`
- `thirdFullPhysical_lateTwoSliceRate_forces_secondaryPDEClock244`
- `thirdFullPhysical_noH3Trace_prescribedGauge_lateSecondaryPDEClock244`

The registrar imports the new module in `PrimeTensor.lean`, adds the
first-monomial audit checks and prints axioms. Lean compilation and
full integration build must run in the pinned user toolchain.
