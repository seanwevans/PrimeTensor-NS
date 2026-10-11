# Initial uniqueness from an integrated kinetic-energy budget

Base checkpoint: `985236d5` (`derive initial uniqueness from right kinetic energy trace`).

New module: `PrimeTensor/Fluid/Vorticity/Continuation/H3/Audit/OneComponentInitialIntegratedKineticBudgetRelativeEnergy.lean`.

## Mathematical improvement

The previous criterion uses `Tendsto (velocityH3Energy0At u) (𝓝[>] 0) (𝓝 L)` solely to obtain a bounded old physical velocity near the initial time. The new criterion does not require the old kinetic energy to have a right limit.

Instead, for the *actual old velocity*, assume a single integrable signed kinetic defect `r` on `(0,b)` and the initial-value kinetic budget

    E₀(t) ≤ E₀(0) + ∫₀ᵗ |r(s)| ds        (0 < t < b).

By monotonicity of integrals of nonnegative functions,

    E₀(t) ≤ E₀(0) + ∫₀ᵇ |r(s)| ds.

The previous exact old physical Hilbert identity gives `‖u_old(t)‖² = E₀(t)`, so the kinetic budget supplies the physical norm ceiling `sqrt(E₀(0) + ∫₀ᵇ |r|)`. Positive-time old Hilbert time measurability is already automatic from the H³ path class. The previous `H3AuditInitialCanonicalOldKineticCeilingRelativeEnergyData` and its uniqueness theorem then apply.

There is **no requirement for the kinetic defect mass to vanish**. Finite `L¹` mass is enough to obtain a norm bound; the *separate* approximation-dependent old/selected relative-energy residuals `R` must have arbitrarily small `L¹` mass to force uniqueness.

## New declarations

- `h3Audit_initialIntegratedKineticBudget_uniformUpper`
- `h3Audit_initialPhysicalKineticBudget_uniformCeiling`
- `h3Audit_initialOldPhysicalHilbert_norm_le_of_integratedKineticBudget`
- `H3AuditInitialCanonicalIntegratedKineticBudgetRelativeEnergyData`
- `h3Audit_initialIntegratedKineticBudget_implies_oldKineticData`
- `h3Audit_initialIntegratedKineticBudget_implies_compactWeakComparisonData`
- `h3Audit_initialIntegratedKineticBudget_implies_physicalZeroJetAndEnergyUpper`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialIntegratedKineticBudget`

## Open analytic obligations

The integrated kinetic-energy budget **is not derived automatically** from open-time `LoggedPreterminalH3PathAdmissible`; that class does not encode a weak initial kinetic-energy inequality or an initial boundary flux condition. The small-residual old/selected relative-energy inequality is also assumed, not derived from the PDE. Neither this patch nor its predecessors close the separate terminal strong-`H³` actual-vorticity endpoint. No unconditional Navier–Stokes continuation follows from this patch.

## Verification

The ZIP package contains only the new Lean module and this audit note. Lean compilation and the full repository audit must be run in the user's checkout; no Lean toolchain is present in the patch-generation environment.
