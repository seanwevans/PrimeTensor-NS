# Initial canonical heat–Leray mild overlap → actual physical H³ right trace

Parent checkpoint: `c1dbd729` — `reduce initial H3 criterion to one-sided physical spectral trace`.

## Existing compiled ingredients

- `h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension` constructs the **actual Banach-selected** weighted Fourier H³ Navier–Stokes mild path at unit viscosity from initial spectral state `U₀` and energy ceiling `A`.
- `continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension` proves global physical-time continuity of that spectral path.
- `h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_zero` identifies its value at elapsed time zero **exactly with `U₀`**.
- `norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA` controls that path by the canonical Picard bound `2*A` at every real time.
- `OneComponentInitialRightSpectralTrace.lean` already derives the full-time physical `L²_t Ḣ^(3/2)_x` criterion from a right H³ Fourier trace of the actual velocity.

## New Lean interface and results

`OneComponentInitialCanonicalMildOverlap.lean` introduces:

- `H3AuditInitialCanonicalMildOverlapAt`: a **named, explicit** identification of the old actual physical velocity's weighted Fourier components with the specific selected Banach mild solution over a nonempty early interval `0<t<b`, with `b` at most the canonical Picard radius;
- `H3AuditInitialCanonicalMildOverlap`: the existential package containing actual proposed H³ initial Fourier datum, positive norm ceiling, and positive overlap width;
- `h3Audit_initialCanonicalMildOverlapAt_earlySpectralBound`: a **quantitative `2*A` bound** on the actual physical component H³ norm over a shortened early interval;
- `h3Audit_initialCanonicalMildOverlapAt_rightTrace_to_initialDatum`: the **exact** one-sided strong weighted Fourier H³ trace `U₀[j]` of the actual physical component;
- `h3Audit_initialCanonicalMildOverlap_rightComplementTrace`: discharge of the previous abstract right-trace condition;
- full-time one- and two-transverse-component intrinsic physical `L²_t Ḣ^(3/2)_x` results under one actual vorticity strong endpoint and the initial overlap.

## Remaining frontier

**The local initial overlap is still a premise.** The present old PDE path does not yet have a proved identification with the selected canonical Picard solution launched at time zero. Establishing this from actual finite H³ initial data requires a local strong-solution compatibility/uniqueness bridge. The published Liu–Zhang one-velocity-component continuation theorem is not imported or proved, and no global Navier–Stokes regularity claim follows here.

The proof does not take a mere finite initial H³ snapshot as a substitute for local strong-solution uniqueness. It also does not conflate the internal Fourier–Plancherel homogeneous Sobolev domain with an independently formalized distributional homogeneous Sobolev space.
