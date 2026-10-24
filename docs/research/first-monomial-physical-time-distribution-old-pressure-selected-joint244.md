# Old pressure on selected restart slabs (90346dac)

The old-pressure L1-in-time compact-test mass criterion is already sufficient for physical momentum distributions. This patch identifies a stronger, **automatic** regularity fact on strictly positive selected-restart slabs, via an existing independent curl-weak-FTC physical-evolution theorem.

1. `h3PreterminalTailPhysicalEvolutionOnRestartRadius_tailH3_curl` furnishes physical evolution on the canonical restart radius from the tail H3 datum.
2. `H3PreterminalTailCanonicalSelectedPressureForceJointlyContinuousOnAbsoluteSlab_of_le_restartRadius` supplies joint space-time continuity of the selected pressure force.
3. `H3PreterminalPressureFirstSpatialDerivativeJointlyContinuousOnAbsoluteSlab_of_selectedPressureForce` transfers this to the **old** pressure gradient, since pressure-force equality implies equality of the gradients.
4. A compact cylinder `[a,b] × tsupport(φᵢ)` strictly inside `(t,t+τ) × Point3` yields a finite bound by `IsCompact.exists_bound_of_continuousOn`. Multiplication by the fixed test coordinate then gives a uniform compact-test integrand bound, with no assumptions about global spatial decay or the additive pressure gauge.

The result is genuinely conditional only on the usual canonical H3 tail data, positive elapsed time, terminal bound, and restart-radius restriction. It does **not** assert old pressure gradient joint continuity on the entire `(0,T)` cylinder: the strict-slab geometry is important. A subsequent patch should use the existing local canonical restart coverage to rebase closed elapsed test intervals strictly inside those slabs, integrate the compact-test bound, and feed `h3PreterminalPressureWitnessL1MassOnElapsed244`, `h3PreterminalOldPressureL1MassOnElapsed244` and the resulting physical momentum distribution theorem.

The use of the previously proved curl physical evolution means this is a consistency/re-use of an already strong branch, not an independent new proof of Navier–Stokes regularity. No axioms or holes are added.
