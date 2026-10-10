# One-component endpoint: genuine strict-time continuity (2026-10-10)

Checkpoint `ae93a012`: the homogeneous Ḣ^(3/2) Fourier square mass is a continuous functional of the native weighted H³ state.

## No global terminal ceiling is assumed

A first draft accidentally used `CanonicalH3TailDataFrom u t T E`, which assumes a bounded H³ tail all the way to the potentially singular T. **This was corrected before delivery.** This module instead chooses an earlier local terminal time **S < T**, using `LoggedPreterminalH3PathAdmissible.exists_localCanonicalRestartWindowAt`, with local tail data only for `(t,S)`.

The proof uses these *existing* results:

- `LoggedPreterminalH3PathAdmissible.energy_continuousAt`, the scalar-energy continuity already in the path class;
- `h3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed_of_energyContinuousOnTail`, localization to elapsed time;
- `h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_physicalEnergy_pressureFree`, the previously closed weak-plus-norm pressure-free Navier–Stokes continuity theorem;
- `continuous_h3Audit_homogeneousThreeHalvesMass`, the Fourier multiplier functional from `ae93a012`.

The new module proves strong spectral continuity on the **local** canonical tail, identifies that state with the original physical component from the full preterminal path, and proves that every strict preterminal time lies in an interval where the **actual** homogeneous Ḣ^(3/2) square density is continuous and hence measurable.

## Remaining steps

1. Globalize the locally continuous time density to a Borel-measurable map on all real times (zero outside `(0,T)`).
2. Apply the previous late-time domination result to obtain **unconditional** terminal-integrability of both transverse components under `hPhysical`.
3. Verify the hypotheses and spatial/Fourier conventions of Liu–Zhang's published local-strong-solution criterion. No external mathematical theorem has been imported into Lean.

The universal terminal H³ bound and genuine Clay Form A remain unproved.
