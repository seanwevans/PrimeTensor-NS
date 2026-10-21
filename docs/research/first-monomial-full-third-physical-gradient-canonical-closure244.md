# Physical H³ 3–3–1 gradient completion: actual Point3 vs weighted Schwartz

Checkpoint: `a961596a` (identified each real Schwartz L²×L²×L∞ triple with the original physical Point3 integral). This overlay targets the remaining finite assembly and scalar limit uniqueness.

## Proof structure

For every ordered `(j,i,k,l,r)` axis tuple, the original `thirdTransportCommutatorAxisGradientBlock` consists of four distinct terms with first-jet/third-jet factors in their physical orientation. The integrability of each is already proved by `h3ActualPhysicalGradientTriple_integrable244`. The new `h3PhysicalGradientAxis_eq_fourTriples244` distributes its physical `spatialEnergyPairing` through their sum, retaining the energy factor 2.

`h3MatchedSchwartz_gradientAxis_tendsto_oldPhysical244` applies the preceding checkpoint's strong Schwartz-to-physical triple limit to all four orientations. The axis contraction is finite (`xAxis`, `yAxis`, `zAxis`) and distribution of the spatial integral uses individually integrable terms, not integrability of a sum as a surrogate for integrability of each summand.

`h3MatchedSchwartz_gradientTransport_tendsto_oldPhysical244` passes through exactly 243 ordered five-axis slots and identifies their sum with the OLD `thirdOrderGradientTransportSum`. The existing independent weighted H³ matched-gradient convergence has the same real scalar sequence, so `tendsto_nhds_unique` gives the physical/canonical gradient equality.

Finally, `h3PhysicalFullThird_eq_weightedCanonical244` combines this identification with the already proved signed-gap-zero theorem and the existing exact physical commutator split. This is a top-order H³ transport identity only. It does not prove global regularity or smooth continuation.

## Validation limits

The source contains no `sorry`/`admit`; registrar and shell syntax are checked. This environment does not have the project Lean toolchain or mathlib `.olean` cache. The compile and repository-wide audit must run on Rocky Linux before this is a verified Lean proof.
