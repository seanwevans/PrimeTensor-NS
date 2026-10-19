# Full-third unforced sign frontier

Base: `0b580777` — unconditional Schwartz static H3 obstruction.

## The new mathematical result

The unforced Navier–Stokes H3 energy balance has sign `E' + 2D = -T`, not `+T`. The previously proved complete Schwartz noncancellation and fixed-kinetic concentration can be reversed without modifying the kinetic anchor or the quadratic terms. The new theorem `thirdFullSchwartz_oneSeed_adverseUnforcedTransport244` constructs a **single fixed-kinetic solenoidal seed** such that, for each `C K : ℝ`, a physically solenoidal Schwartz profile with the same kinetic energy has

`C * D4(g) + K * E_H3(g) < -fullSchwartzThirdCommutator244(g)`.

The result prevents claiming a universal, static, energy-only pointwise coercivity estimate on all divergence-free Schwartz profiles in the physically adverse sign.

## Exact PDE bridge and what is missing

The established **unforced** PDE theorem says

`deriv E(t) + 2 * D(t) = - velocityH3TransportDerivativeAt u t`.

`h3Path_energySlope_pos_of_fullThird_adverseSlice244` proves a positive derivative if the full path transport equals the complete Schwartz top-order cubic plus an explicit remainder, and if this remainder together with the actual PDE dissipation is controlled by the Schwartz quadratic budget. Both compatibility assumptions are stated, not hidden.

The outstanding hard math remains: identify the full physical third-gradient Schwartz block with a realized path time-slice, control the lower-order transport and viscous remainder under the *unforced* PDE, and make the relevant local smooth solution and initial trace explicit. No finite-time singularity, universal positive energy derivative for all solutions, or invalidation of conditional dynamical estimates follows from the static obstruction.
