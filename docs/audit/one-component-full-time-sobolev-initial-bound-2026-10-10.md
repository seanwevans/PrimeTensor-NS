# Full-time physical homogeneous H3/2 criterion from early H3 bounds (2026-10-10)

Parent checkpoint: `71cca4f3` (`extend physical H3/2 Sobolev time L2 across positive tail`).

## Precise initial-time gap

The prior checkpoint proved the intrinsic *physical* homogeneous H3/2 seminorm
lies in `L²((a,T))` for both transverse components whenever there is one
physical-curl-component strong H3 terminal endpoint and a preterminal H3
energy class starting at `a > 0`.

This does **not** prove integrability on `(0,T)`: H3 energy continuity strictly
inside the lifespan does not imply finite H3 energy or finite homogeneous
Sobolev time integral near `t=0`.

## This patch

`OneComponentFullTimeSobolevInitialBound.lean` makes the missing hypothesis
explicit via `H3AuditInitialComplementSpectralBound`: one actual component's
weighted Fourier H3 norm is bounded by some finite `M` at all strict times
`t < a`. It then proves:

- `h3Audit_homogeneousThreeHalvesTimeDensity_integrableOn_initial_of_bound`:
  the actual Fourier homogeneous three-halves square density belongs to
  `L¹((0,a))`, by the already-proved Fourier domination, global Borel
  measurability, and finite measure of `(0,a)`;
- `h3Audit_homogeneousThreeHalvesTimeDensity_integrableOn_fullTime_of_split`:
  join independently available early and positive-tail integrability into
  `L¹((0,T))` using standard interval integrability;
- `h3Audit_complementEndpoint_intrinsicThreeHalves_fullTime_of_initialBound`:
  one actual physical velocity coordinate's intrinsic homogeneous 3/2
  seminorm is in `L²((0,T))` under its **explicit early bound** and its
  terminal H3 endpoint;
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialBounds`:
  both transverse components' physical seminorms lie in `L²((0,T))` when
  both individual early H3 bounds are furnished;
- a one-component corollary requiring only that component's early bound.

## Not proved

The early spectral H3 bounds do **not** follow from the current
`LoggedPreterminalH3PathAdmissible` assumptions, which only control the open
interval. They require an independent initial-data/local-strong-solution
regularity argument. The Liu–Zhang continuation theorem, compatibility of
its local-strong-solution class, and conversion of its continuation to the
project's `SmoothContinuationExtension` remain unformalized. In particular,
none of the results is an unconditional global Navier–Stokes theorem.
