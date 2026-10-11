# Positive-time strong derivative discharges interior Bochner increments

Base checkpoint: `e472bbb8` — `derive strong initial L2 from weak trace and interior Bochner evolution`.

## Newly proved

- `h3Audit_initialIntervalIntegrable_of_globalBochner` restricts one interval-integrability proof on `0..b` to any `0..t`, `0<t<b`.
- `h3Audit_positiveUnorderedInterval_subset_initial` and `h3Audit_positiveUnorderedInterval_strict` handle either order of two interior time endpoints.
- `h3Audit_positiveStrongDerivative_implies_interiorBochnerIncrements` uses `intervalIntegral.integral_eq_sub_of_hasDerivAt` to derive the exact Bochner increment identity from an actual strong L² derivative and a single Bochner-integrable source.
- `h3Audit_initialPositiveStrongDerivative_implies_physicalL2RightTrace` combines the theorem with the previous weak-to-strong initial-trace result, without assuming any initial right-continuity or endpoint FTC.
- `H3AuditInitialPhysicalEnergyMildWeakStrongDerivativeData` packages the weaker interface: mild representation, initial H³ datum, one initial Bochner-L¹ temporal source, strict positive-time strong L² derivative, and weak initial L² convergence.
- Bridge the new interface to the previous Bochner-increment data, physical L² trace, genuine spectral zero datum, H³ energy right limit, and conditional two-component full-time intrinsic Sobolev criterion.

## Assumptions not discharged

The `HasDerivAt` statement for actual physical L² velocity and its `IntervalIntegrable` temporal derivative on `(0,b)` remain explicit. They are not inferred merely from the pointwise Navier–Stokes PDE. The actual old-velocity physical mild representation and the weak initial condition are also still conditional. The separate strong terminal vorticity endpoint is unchanged. No Navier–Stokes global regularity conclusion is made.

No sorry/admit/new axiom declarations. This ZIP is prepared against `e472bbb8` but Lean compilation must be performed in the user's Rocky Linux repository.
