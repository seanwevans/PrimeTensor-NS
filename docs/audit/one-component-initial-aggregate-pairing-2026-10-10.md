# Initial right H³ trace from total energy and a single aggregate correlation

Parent checkpoint: `4e0bc4e5` — derive initial strong H3 trace from total energy and pairings.

## Exact reduction

Instead of checking three separate weak correlations with the initial
weighted Fourier coordinates, it is enough to check their *sum*:

`Σ_j Re⟪U_j(t), U₀_j⟫ → Σ_j ‖U₀_j‖²`.

Coupled with `velocityH3EnergyAt u t → 1 + Σ_j ‖U₀_j‖²`, the precise
Hilbert polarization identity forces

`Σ_j ‖U_j(t) - U₀_j‖² → 0`.

All three actual H³ Fourier coordinates therefore converge strongly. The
previous right-trace-to-time-L² theorem then supplies full-time intrinsic
`L²_t Ḣ^(3/2)_x` for both transverse physical velocity components, under the
separate terminal vorticity endpoint hypothesis.

A separate theorem uses the existing initial physical H³ energy continuity
predicate plus the exact initial energy value to discharge the energy limit.

## Boundary and next task

The aggregate correlation is not inferred from the open-time PDE path. Proving
that limit from genuine weak initial data or the PDE's local mild formulation
remains the initial-data obligation. No unconditional Navier--Stokes
continuation, Liu--Zhang theorem, or regularity closure is claimed.

The aggregate condition replaces three scalar limits by one, but with the
energy limit present it is mathematically equivalent to the full strong H³
right trace, and hence entails the original three limits.
