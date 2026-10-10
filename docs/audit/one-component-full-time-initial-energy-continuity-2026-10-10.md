# Full-time physical Ḣ³ᐟ² criterion from continuity of the genuine initial H³ energy

Parent: `84c7ba21` — `extend physical H3/2 time L2 under initial H3 bounds`.

The previous theorem assumed *two separately supplied* initial-time H³ spectral
component bounds, one for each transverse velocity component. This patch
replaces both with a single physical-space initial regularity interface:

`H3AuditInitialPhysicalH3EnergyContinuous u :=
  ContinuousAt (velocityH3EnergyAt u) 0`.

The canonical Fourier encoder already supplies the componentwise estimate
`‖U_j(t)‖ ≤ ‖U(t)‖ ≤ sqrt (velocityH3EnergyAt u t)`.
Continuity of the physical H³ energy at zero gives a common initial interval
`(0,b)` and a bound `M` for *all three* Fourier components there. This is not
uniform H³ control through the possibly singular terminal time `T`.

The result joins an initial integrable square density on `(0,b)` to the
previous terminal density on `(c,T)` by continuity of the actual Fourier
square density on every strict preterminal compact interval, including the
entire `(b,c)` middle region. This gives intrinsic physical Ḣ³ᐟ² seminorms
in `L²((0,T))` for both selected transverse coordinates under the *existing*
strong physical endpoint and the *new explicit* initial energy continuity.

### Important remaining boundaries

The existing `LoggedPreterminalH3PathAdmissible` assumes continuity of its H³
energy only at strictly positive times, not at `t=0`. The new hypothesis must
be derived from an appropriate initial-data/strong-solution theory; this
patch does not smuggle it into the existing path definition. The Liu–Zhang
local-strong-solution hypothesis, independent homogeneous Sobolev-space
normalization, and the published continuation conclusion remain separate
formal bridges. No unconditional Navier–Stokes regularity follows.
