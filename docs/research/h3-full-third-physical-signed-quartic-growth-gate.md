# Physical signed H³ growth: quartic interpolation and terminal obstruction

Baseline: `c4263444` (`identify physical H3 jet energies and signed quartic transport barrier`).

## The actual physical energy residual

Write `E = velocityH3EnergyAt u t`, `D = velocityH3DissipationAt u t`,
`Ek = velocityH3EnergykAt u t`, and
`h = h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient * sqrt E`.
Let `I3 = thirdOrderInterpolationTransportSum u t` and `G3` denote the
third-order gradient transport. Existing physical identities establish

    E' + 2 D <= h(6 E1 + 18 E2) - G3 - I3,
    |G3| <= 24 h E3.

Thus, without spending any of the `2 D`, the physical signed residual

    R = E' + 2 D - [ h(6 E1 + 18 E2) + 24 h E3 ]

obeys `max(0,R) <= |I3|`. The previously proved *exact physical* signed
interpolation quartic bound yields

    max(0,R)^4 <= 3^4 K^4 E2 E3^5,

where `K = lowNormalRealSchwartz_holder244CriticalConstant`.
The result does not replace `E2` and `E3` by equivalent norms or posit
an unproved favorable sign. It also does not prove that this quartic
quantity is temporally integrable.

## Adverse top-transport alternative

At a time when the existing physical signed-transport analysis yields

    A := M E + D < 24 h E3 - I3,

there are two possible outcomes: either `A < 24 h E3`, or the nonnegative
excess `A - 24 h E3` obeys the same physical fourth-power inequality.
This is division-free, including when a physical energy coordinate
vanishes. The earlier nonextension theorem supplies such a time on every
strict terminal subtail, with the necessary Fourier compatibility
constructed from the genuine preterminal NS assumptions.

With the **additional explicit tail hypothesis** `24 h E3 <= D`, the
nonextension alternative forces, for each `M >= 0`, a time arbitrarily
close to the terminal point such that

    (M E)^4 <= 3^4 K^4 E2 E3^5.

This is a necessary obstruction under the gradient-absorption hypothesis,
not a proof of gradient absorption or global continuation. It does not
exclude either branch of the unconditional alternative.

## Audit

Module: `PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdPhysicalSignedQuarticGrowthGate`.
Five theorem declarations, one noncomputable residual definition. Twelve
`#check` / `#print axioms` entries; registrar and fragment checks required.
Lean compilation must be performed in the repository's toolchain.
