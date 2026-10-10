# Initial physical H³ trace from one-sided energy/correlation inequalities

Parent: `25c1fde5` (`reduce initial H3 trace to aggregate spectral correlation`).

## Mathematical advance

Prior audit assumed **convergence** of (i) normalized physical H³ energy and (ii) its aggregate weighted Fourier H³ correlation with a proposed initial spectral velocity `U₀`.

`OneComponentInitialRightOneSidedEnergyPairing.lean` requires only:

* For every `ε > 0`, **eventually** physical H³ energy is less than `1 + Σ ‖U₀,j‖² + ε`.
* For every `ε > 0`, **eventually** the aggregate real spectral correlation is greater than `Σ ‖U₀,j‖² − ε`.

The exact polarization identity makes the nonnegative sum `Σ ‖U(t)_j − U₀,j‖²` smaller than any positive epsilon, so it tends to zero. Component right traces and conditional full-time `L²_t Ḣ^(3/2)_x` follow.

The physical-energy upper estimate follows from already-defined initial energy continuity with its correct value, leaving only the **one-sided aggregate lower correlation**. In PDE work this is a natural target for a weak initial trace plus high-frequency control. Neither initial premise follows from the open-time H³ admissibility class.

## New declarations

- `h3Audit_rightSpectralVelocity_tendsto_of_upperEnergy_lowerCorrelation`
- `H3AuditInitialRightEnergyUpperCorrelationLower`
- `h3Audit_initialRightEnergyUpperCorrelationLower_implies_strongVelocityTrace`
- `h3Audit_initialRightEnergyUpperCorrelationLower_rightComplementTrace`
- `h3Audit_initialEnergyContinuous_implies_rightUpperEnergy`
- `h3Audit_initialEnergyContinuous_and_rightLowerCorrelation_data`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialOneSidedEnergyPairing`

## Boundary

No initial weak convergence, physical initial-value mild identity, or Liu–Zhang continuation theorem has been supplied. No `sorry`, `admit`, or axioms are introduced. Local Lean compilation unavailable in the patch-authoring environment.
