# Dynamic raw Fourier carrier on the genuine kinetic PDE-selected annular clocks

**Base HEAD:** `0bf2fd6a562bec52ba3f885d9da87db69938cdc1`.

This module transfers the already-compiled critical-eighth physical momentum
transport to a DIFFERENT collection of windows: the kinetic-only
`ThirdFullKineticNaturalAnnularLocalWitness244` clocks. Their widths and
outer Fourier frequencies are not resampled or shortened.

## Physical projected-source action

Assuming `LoggedPreterminalH3PathAdmissible`, `PreterminalH3EnergyClass`,
and ordinary `IntervalIntegrable (velocityH3DissipationAt u) volume a T`,
the accepted `h3Critical_projected_source_integrable_of_finite_dissipation`
shows the **actual physical projected momentum source** is Bochner-L1 near T.
The accepted `thirdFull_terminalSourceL1_on_cofinalWindows_tendsto_zero244`
then applies to each cofinal kinetic annular window:

    integral_{tau(vk)}^{tau(vk)+delta(vk)} ||source(r)|| dr -> 0.

An attained source maximum times width is NOT substituted for this integral.

## Physical Hilbert FTC gives UNIFORM moving raw annulus mass

The accepted real Fourier map and `thirdFullPhysical_rawBandMass_window_le_sourceL1244`
prove for every physical `s` in the selected interval:

    mu_k(s) <= 3 ( highpassRaw_k(tau(vk)) + ||FourierMap|| * sourceL1_k )^2.

The actual physical L2 terminal trace from finite ordinary H3 dissipation
makes the first highpass term vanish along moving inner frequency `v(k)`, and
source Bochner-L1 gives the second. Consequently:

    for every epsilon>0, eventually for every s in the SAME window,
       mu_[v(k)+1,N(vk)+1](s) < epsilon.

The *outer* cutoff is entirely unconstrained and may escape arbitrarily fast.
The estimate uses physical momentum FTC, not an assumed time derivative of
the weighted H3 Fourier state.

## Persistent positive H3 dissipation, despite vanishing raw carrier

The *original exact PDE* kinetic window certifies at EVERY time `s`

    M(vk)/4 < D_low,N(vk)+1(s) - D_low,vk+1(s)
               <= D_full(s).

The accepted physical radial Fourier-multiplier inequality now gives, also at
EVERY time in the SAME window,

    M(vk)/4 < 4 (N(vk)+2)^8 * mu_k(s).

Thus the kinetic height satisfies uniformly in window time

    M(vk)/(N(vk)+2)^8 <= 16 * mu_k(s) -> 0.

The final theorem uses the ORIGINAL no-H3-trace arbitrary-height cofinal
selector from the global extended budget module. It retains strict separation,
the original natural cutoffs and exact widths, the global extended H3
finite-window packing inequality, source absolute-L1 decay, uniform raw
carrier vanishing, and the persistent H3 floor, on one common sequence.

**What is NOT established:** H3 terminal trace, an upper bound on outer
frequency, a uniform positive persistence width, any sign of the full signed
H3 transport flux, or Navier--Stokes continuation. Ordinary finite-H3
interval integrability is an explicit premise, not deduced from an ENNReal
budget. This proof also does not use the mutually inconsistent pair of
`no physical L2 terminal trace` and finite H3 dissipation.

## Declarations

- `thirdFullPhysical_kineticWindows_sourceL1_tendsto_zero244`
- `thirdFullPhysical_kineticWindow_rawEighthThroughout244`
- `thirdFullPhysical_kineticWindows_uniformMovingRawMass244`
- `thirdFullPhysical_kineticWindows_uniformNormalizedHeight244`
- `thirdFullPhysical_noH3Trace_kineticDynamicRawWindowConcentration244`

No placeholders or new axioms. Run pinned Lean/mathlib compilation; static
source and audit registration tests do NOT establish Lean elaboration.
