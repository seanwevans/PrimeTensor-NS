# Physical momentum distributions from spatial equicontinuity

Base commit: `1a573567` (spatial Lipschitz sufficient condition).

## Improvement

A uniform spatial Lipschitz constant on every compact physical test support is
stronger than needed. Replace it by a genuine *spatial equicontinuity* condition:
for every desired spatial increment tolerance `eta > 0`, there is a small
spatial radius `delta > 0` and a time neighborhood about each elapsed time on
which all signed physical momentum snapshots satisfy

    dist(x,y) < delta  ==>  norm(F(t,x)-F(t,y)) <= eta

for x,y in the compact support of the chosen test coordinate. This modulus
need not be Lipschitz, Holder, or uniform among tests/observation times.

The PDE already makes `t ↦ F(t,x)` continuous at every fixed x. A finite
cover of the test support by delta-balls and time continuity at its finitely
many centers yields uniform temporal oscillation on the entire compact support.
The previous signed-oscillation bridge then produces the genuine distributional
momentum equation on strict physical windows.

## Critical distinction

Neither spatial equicontinuity uniform over a time neighborhood nor its
weaker integral replacement is proved from bare `LoggedPreterminalH3PathAdmissible`.
At each fixed time the spatial signed expression is C1, but the family of
spatial derivatives is not yet shown uniformly bounded across time; separate
continuity does not provide that estimate. The new implication is conditional
and does not assert unconditional Navier--Stokes continuation.

## Theorems

- `h3Path_compactUniformTimeOscillation_of_spatialEquicontinuity244`
- `h3Preterminal_signedOscillation_of_localSpatialEquicontinuity244`
- `h3Path_interiorSignedOscillation_of_spatialEquicontinuity244`
- `h3Path_distributionalMomentum_of_spatialEquicontinuity244`
- `h3Path_nonzeroPhysicalFTCDefect_forces_spatialEquicontinuityFailure244`
- `h3Preterminal_spatialEquicontinuity_of_spatialLipschitz244`

The testwise finite-cover proof uses no placeholders or new axioms.
