# Kinetic closure of Fourier L² branches; L¹ or eighth moment escape

Baseline: `cf27f234` — reduce the physical six-factor escape to eighth velocity moments under explicit low Fourier ceilings.

## Genuine physical kinetic control

The repository already proves `sq_norm_h3TerminalVelocityRawFourierL2_le_energy0` for each actual velocity spectral coordinate. It also proves that `velocityH3Energy0At u` is antitone on the strict H³ energy-class interval. Therefore, for a fixed strict anchor `s` and any later time `t`,

    ||RawFourierL2(U_j(t))|| ≤ sqrt(velocityH3Energy0At u s).

The raw conjugate Fourier L² norm equals the unconjugated L² norm. Both raw L² primitive branches in the six-factor order-eight Young envelope therefore have a uniform **derived** bound. This does not require a uniform H³ spectral-state norm or a terminal bound on fourth dissipation.

## Remaining genuine two-way obstruction

Under the retained strict-time eighth-order raw-moment integrability premise and physical fourth-radial dissipation escape:

1. Either the genuine raw Fourier L¹ mass of some velocity coordinate exceeds every ceiling somewhere on the strict terminal tail; or
2. for every later terminal subtail and every threshold, some velocity coordinate has an order-eight raw Fourier moment above that threshold.

If all actual velocity raw Fourier L¹ masses admit a common ceiling after anchor s, the first branch is removed automatically, and eighth-moment escape is cofinal. The previously proved `h3SpectralScalarRawFourierL1Mass_le_norm` actually states `L1(U_j) ≤ h3RawFourierL1DeweightingCoefficient * ‖U_j‖`. Therefore a common spectral H³-state norm ceiling `B` supplies the L¹ ceiling `h3RawFourierL1DeweightingCoefficient * B`, using the nonnegativity of that coefficient. No uniform spectral ceiling is asserted from the Navier–Stokes PDE.

## Limits

This is a necessary consequence of a **conditional top-mass escape hypothesis** and the explicitly required order-eight moment integrability at strict times. It is not unconditional regularity. The first L¹ alternative is stated as unbounded on the initial strict tail; no uniform continuity theorem at T is used to strengthen it cofinally. The kinetic result itself is unconditional under the existing H³ path and energy-class assumptions.
