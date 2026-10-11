# Initial canonical uniqueness under arbitrarily small integrated relative-energy errors

Base: `1933d259` (`derive initial uniqueness from integrated relative energy residuals`).

## What changes

This is a proof-interface improvement: the PDE can supply a **single approximation at each prescribed positive error tolerance** rather than a numbered family of approximations with a convergence theorem.

The signed real error density `R` must satisfy `IntervalIntegrable (fun s => |R s|) volume 0 b`, full-interval absolute mass `≤ ε`, and the approximate energy inequality for **every** `t ∈ [0,b]` with a coefficient `κ ≤ K`. The ceiling `K` does not depend on the error tolerance.

A direct order-theoretic epsilon argument bounds the forward absolute residual integral by its full-interval mass, raises the comparison coefficient to `K` using nonnegative energy, and lets `ε → 0` using `le_of_forall_pos_le_add`.

## Declarations

- `h3Audit_initialRelativeEnergy_exact_of_arbitrarySmallIntegratedResidual`
- `h3Audit_initialScalarEnergy_integralGronwall_of_arbitrarySmallIntegratedResidual`
- `H3AuditInitialCanonicalEpsilonResidualRelativeEnergyData`
- `h3Audit_initialEpsilonResidual_implies_scalarRelativeEnergyData`
- `h3Audit_initialIntegratedResidual_implies_epsilonResidualData`
- `h3Audit_initialEpsilonResidual_implies_compactWeakComparisonData`
- `h3Audit_initialEpsilonResidual_implies_physicalZeroJetAndEnergyUpper`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialEpsilonResidual`

## Remaining analytic frontier

The epsilon-dependent approximate inequality and integrated source estimates have **not** been derived from `LoggedPreterminalH3PathAdmissible`, nor has continuity of the physical squared difference at its artificially zero-valued initial time. The terminal physical-vorticity strong-H³ endpoint remains a separate assumption. No unconditional NS regularity is claimed.

This module has been packaged, but not independently elaborated with `lake env lean` in this environment.
