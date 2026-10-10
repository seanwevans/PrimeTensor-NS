# Initial old/selected equality from canonical-radius Picard uniqueness

Parent checkpoint: `6a158079` — `derive initial physical H3 trace from canonical mild overlap`.

## Mathematical progress

`OneComponentInitialCanonicalMildOverlap.lean` postulated that the actual
physical velocity and the selected Banach fixed-point solution have equal
weighted H3 Fourier states on one initial interval. The present module
replaces that direct equality assumption with a named and checkable
**old-solution normalized mild contract**:

1. A normalized, bounded continuous spectral H3 path `V` represents the
   Fourier H3 states of the *actual* preterminal velocity on `(0,b)`.
2. `‖V‖ <= 2*A` in the canonical Picard ball.
3. `V` satisfies exactly the same signed heat-minus-Duhamel mild equation
   with initial datum `U₀` and the canonical unit-viscosity restart radius.

The previously proved
`h3SpectralFinHeatLerayMildSolutionAtRestartRadius_unique` then proves
`V = h3SpectralFinHeatLerayMildSolutionAtRestartRadius`. Therefore the old
velocity has the canonical initial overlap previously only hypothesized.
The initial physical right H3 trace and full-time intrinsic physical
`L²_t Ḣ^(3/2)_x` conclusions follow from the existing audit theorems.

## New Lean declarations

- `H3AuditInitialOldNormalizedMildDataAt`
- `h3Audit_initialOldNormalizedMildDataAt_implies_canonicalMildOverlap`
- `H3AuditInitialOldNormalizedMildData`
- `h3Audit_initialOldNormalizedMildData_implies_canonicalMildOverlap`
- `h3Audit_initialOldNormalizedMildData_rightComplementTrace`
- `h3Audit_onePhysicalEndpoint_oneIntrinsicThreeHalves_fullTime_of_initialOldNormalizedMildData`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialOldNormalizedMildData`

## Still open

The project does not yet derive the normalized old-solution Fourier-H3
mild equation, its Banach ball bound, or its initial-time continuous
realization from an arbitrary single H3 initial datum and the existing
pointwise Navier--Stokes admissibility class. Those are **explicit**
mathematical obligations in the contract, not facts inferred from the PDE.
The local-strong-solution compatibility and published Liu--Zhang continuation
theorem are still external/formalization frontiers. No unconditional regularity
is claimed.
