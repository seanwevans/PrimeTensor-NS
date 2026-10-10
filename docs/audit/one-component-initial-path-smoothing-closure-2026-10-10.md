# Initial-time C5/C4 smoothing closure from the existing H3 path

Checkpoint: `ca7a36d8` (`derive initial energy class cover from positive time smoothing`).

This addition removes the explicitly assumed positive-time C5 velocity / C4 pressure condition from the initial signed-transport trace proof. It does not add a regularity axiom.

The existing theorem `LoggedPreterminalH3PathAdmissible.exists_localCanonicalRestartWindowAt` constructs, for each strict time `s ∈ (0,T)`, an earlier anchor `t₀`, a later `S<T`, a finite local energy ceiling, and an elapsed time `q=s-t₀` strictly inside the selected restart radius. The old-velocity transfer theorem supplies the spatial C5 shape at `s`. The old-pressure witness transfer theorem supplies the C4 shape for the original global pressure witness even though the short-restart witness can differ by a pressure gauge.

New theorems:

- `h3Audit_h3Path_positiveVelocitySpatialC5`
- `h3Audit_h3Path_positivePressureSpatialC4`
- `h3Audit_h3Path_positiveHighOrderClassicalNS`
- `h3Audit_h3Path_positiveEnergyClassCover`
- `h3Audit_h3Path_initialOrderwiseEnergyDerivatives`
- `h3Audit_initialSignedTransportCore_implies_signedTransportData`
- `h3Audit_initialSignedTransportCore_implies_strongH3Trace`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialSignedTransportCore`

Remaining initial-value hypotheses: a genuine initial H3 state; initial endpoint strong physical L2 continuity and source bounds; initial scalar H3-energy continuity and rate integrability; a uniform upper bound on signed H3 transport near zero. These are **not** consequences of the open-time classical PDE predicate. The terminal physical vorticity endpoint remains a separate hypothesis for the full-time two-component consequence.

No uniform energy bound approaching the candidate singular terminal time `T` is inferred; the selected restart windows depend on their strict target times.
