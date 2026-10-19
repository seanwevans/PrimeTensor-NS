# Complete physical Schwartz dissipation and unforced H³ balance

Base: `021aa34c` — derive full third gradient integrability from Schwartz realization.

The already-proved `lowNormalRealSchwartz_pathTopDissipation_eq` identifies the
order-three viscous block with the actual 243-term fourth derivative square mass.
The remaining physical identities are purely finite-sum reindexings:

- `velocityH3Dissipation0At = velocityH3Energy1At` (definitional);
- `velocityH3Dissipation1At = velocityH3Energy2At` (two sums exchanged);
- `velocityH3Dissipation2At = velocityH3Energy3At` (three sums cyclically reindexed).

Neither step assumes commutation of distinct spatial derivatives. Summing
produces `D_total = E1 + E2 + E3 + D_top`, for every physical slice.

With an actual real Schwartz realization, the existing four energy and
top dissipation identifications yield exact equality with
`E1(f) + E2(f) + E3(f) + D4(f)`. Combined with the committed exact
unforced Navier–Stokes identity and the newly closed `T3 = G3(f) + 3M(f)`,
this gives the full signed H³ energy balance with lower transports
`T0 + T1 + T2` exposed.

The positive-slope consequence assumes an explicit adverse total budget
at an *actual* solution slice. Static concentration does not establish the
existence of such a slice and does not prove finite-time blowup.

All theorems use existing declarations and add no axioms, `sorry`, or `admit`.
Lean compilation must be checked in the target Rocky Linux/mathlib environment.
