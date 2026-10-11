# Initial old mild H³ path: weak initial L² data are sufficient

Checkpoint: `1838af37` (`derive interior Bochner evolution from positive strong L2 derivatives`).

## Mathematical dependency reduction

A continuous, actual-old identified spectral H³ mild path on `[0,b]` yields
strong H³ spectral convergence to its mild datum `U₀`. This implies strong
physical L² convergence to the **decoded** physical datum via the real
inverse-Fourier decoder. The ordinary weak L² initial trace against the
original `u(0)` identifies the decoded limit with `u(0)` by uniqueness of
Hilbert weak limits, so the physical L² right trace is automatic.

The previous Bochner-family alternative required a global `L¹` temporal
source, genuine positive-time `HasDerivAt` equal to that source, and weak
initial traces. The new contract drops the temporal source and derivative
altogether, retaining only the actual old mild path, genuine H³ initial
snapshot/Fourier compatibility, and the weak initial L² trace.

## Proof inventory

- `h3Audit_actualPositivePhysicalZeroJet_eq_spectralRealDecode`: exact inverse-Fourier real-decoder equality for genuine old positive-time velocity jets.
- `h3Audit_initialStrongSpectralTrace_physicalDecodeRightLimit`: strong H³ spectral trace implies physical L² convergence to the decoded state.
- `h3Audit_initialHilbertStrongAndWeakLimit_identify`: a generic strong-and-weak Hilbert right-limit uniqueness result.
- `h3Audit_initialMildStrongTrace_and_weakInitial_implies_physicalL2Trace`: weak initial condition upgrades to the true physical L² initial trace under the spectral mild trace.
- `H3AuditInitialPhysicalEnergyMildWeakTraceData`: weakened initial-data interface, with no positive-time temporal-source hypothesis.
- `h3Audit_initialMildWeakTrace_implies_L2TraceData`: bridges to the old interface.
- `h3Audit_initialMildWeakTrace_identifies_initialSpectral`: identifies spectral datum with the actual old `u(0)` encoder.
- `h3Audit_initialMildWeakTrace_energyRightLimit`: exact right limit for the physical H³ energy.
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialMildWeakTrace`: retains the independent terminal endpoint.

## Remaining analytic obligations

- Establish an actual-old continuous H³ mild path with correct old-velocity equality, starting at physical time zero, from a suitable Navier–Stokes initial-value theorem. The pre-existing mild-data interface asserts this; it is not a consequence of open-time classical NS admissibility.
- Establish a weak physical L² initial trace to the prescribed `u(0)`.
- Prove the separate terminal strong H³ vorticity endpoint if the unconditional global criterion is sought.

This file makes **no** global smoothness claim. Lean compilation was not available in the artifact builder and must be checked in the target repository.
