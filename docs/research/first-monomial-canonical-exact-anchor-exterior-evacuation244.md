# Canonical physical H³ temporal cliffs require exterior spectral evacuation

Base `a2db481b` — prove canonical H3 physical dissipation temporal cliff alternative.

At a strictly physical preterminal time, let

- `D(t) = velocityH3DissipationAt u t` denote the **full** viscous H³ dissipation;
- `B_{R,Q}(t) = L_Q(t) - L_R(t)` denote the finite annulus's actual dissipation;
- `X_{R,Q}(t) = L_R(t) + H_Q(t)` denote the **physical exterior** low-`R` plus high-`Q` dissipation.

The actual radial partition proves the exact identity

    D(t) = B_{R,Q}(t) + X_{R,Q}(t).

For the *same* original exact-anchor canonical clocks, the established physical projected-momentum PDE modulus gives

    |B_{R,Q}(t) - B_{R,Q}(s)| <= Lambda_k (s-t) + Xi_k (s-t)^2

for `s` inside the canonical window, with coefficients

    Lambda_k = h3PathCubicAnnulusActualLinearRate244 N K C (v k)
    Xi_k = h3PathCubicAnnulusActualQuadraticRate244 N C (v k).

The exact spectral coefficient `K(v k)=‖U₃(t)‖`, attained canonical projected-source envelope `C(v k)`, and exact quadratic-sharp clock `δ(v k)` are all inherited from the original witness constructor. Since both PDE coefficients are nonnegative, the annular variation over any subwindow is bounded by `Lambda_k δ_k + Xi_k δ_k²`.

If the **full** physical dissipation at an actual time `s` within the window drops below `theta * D(t)`, simple subtraction yields

    (1-theta) D(t) - (Lambda_k δ_k + Xi_k δ_k²)
         < X_{R,Q}(t) - X_{R,Q}(s).

The new theorem transports this estimate through the original non-L²-terminal-trace, finite-full-dissipation canonical **disjoint** sequence. An *additional, explicit* eventual positive lower bound on the height-width product `δ_k D(t_k)` yields a relative physical cliff at a point of every sufficiently late original window, for each `0 < theta < 1`; the same point satisfies the exterior-evacuation inequality.

This does **not** prove that the right side is positive: the quantitative PDE annular variation budget may be as large as the anchor dissipation. To turn this into an absolute exterior evacuation lower bound one must independently control that budget. Nor does the existing mathematical framework establish the persistent positive height-width premise. The result is a necessary redistribution condition, not an unconditional exclusion or a 3D Navier–Stokes regularity proof.

## Formal declarations

1. `h3PathFiniteAnnulusPhysicalExterior244` (physical low + high exterior)
2. `h3Path_physicalFiniteAnnulus_exteriorPartition244`
3. `h3Path_scalar_cliff_forces_exteriorLoss244`
4. `h3Path_physicalPDE_cliff_forces_exteriorEvacuation244`
5. `h3Path_exactAnchorPDE_dip_forces_exteriorEvacuation244`
6. `h3Path_noL2Trace_exactAnchor_persistentCharge_exteriorEvacuation244`

The ZIP is checked for integrity and the registrar for idempotence. The Lean/mathlib build is to be run in the pinned project environment.
