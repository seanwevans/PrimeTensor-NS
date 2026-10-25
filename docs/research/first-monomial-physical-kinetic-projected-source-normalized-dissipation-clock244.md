# Moving radial dominance yields physical normalized H3 dissipation clocks

**Base:** `c531ad34`, after the source-coverage baseline repair.

## Exact implications

Let `G(t)` denote the actual weighted H³ Fourier velocity state,
`E_H3(t)=velocityH3EnergyAt u t`, `D_H3(t)=velocityH3DissipationAt u t`,
`L_R(t)` its integrated spectral H³ mass at gradient frequencies below `R`,
and `H_R(t)` the complementary integrated mass.

The previous committed moving-dominance theorem, under positive terminal
kinetic mass and failure of the strong physical kinetic-L² terminal trace,
provides one sequence `t_n -> T` with `R_n = n+1` and

    (R_n+1) H_Rn(t_n) > R_n (E_H3(t_n)-1),
    D_H3(t_n) >= R_n² H_Rn(t_n),
    D_H3(t_n) > R_n³.

The first two imply

    R_n³ (E_H3(t_n)-1) < (R_n+1) D_H3(t_n).

The third adds the missing constant one of the physical H³ energy:

    R_n³ E_H3(t_n) < (R_n+2) D_H3(t_n).

For `R_n >= 2`, the elementary inequality `R_n² >= R_n+2` gives

    D_H3(t_n) / E_H3(t_n) > R_n.

Thus the normalized full H³ dissipation diverges along the same terminal
witness, *without assuming failure of smooth continuation*. The new module
records both the cross-multiplied quantitative clock and its divergent ratio.

## Correct interpretation

This is a stronger **necessary condition** of failure of the physical
kinetic-L² endpoint trace. It does not prove the failure occurs, nor does it
exclude that branch or produce global regularity. Existing results in the
repository give full-left-neighborhood dissipation ratio divergence under
**nonextension**; these are separate hypotheses and should not be conflated.

The next genuinely dynamical task is to constrain normalized dissipation
by a signed transport balance on the same witness sequence, or to derive
sufficient physical kinetic-trace compactness that rules out the no-trace
branch. Neither is asserted here.
