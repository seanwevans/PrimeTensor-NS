# Initial mild right H³ trace: physical zero-time compatibility

**Based on:** `9fbcc42e` — derive full initial H3 trace from actual physical mild path.

The prior theorem obtains `Tendsto` of the genuine positive-time Fourier H³
velocity to the datum of a continuous old mild spectral path. It does not
identify this datum with the original old field's specified time-zero value.

This module supplies an explicit equality between those two states, then:

1. applies continuity of spectral raw deweighting to transfer the weighted H³
   right limit to each coordinate's raw Fourier L² state;
2. uses the exact physical scalar Plancherel distance isometry to transfer
   each right limit into the actual physical velocity L² zero-jet;
3. transfers the mild spectral energy limit to the *actual* time-zero H³
   physical energy by exact encoder normalization; and
4. proves the compatible mild contract implies the earlier minimal physical
   `H3AuditInitialPhysicalZeroJetL2AndEnergyUpper` interface.

## Declarations

- `h3Audit_compatibleInitialSpectral_raw_eq_physicalZeroJet`
- `h3Audit_compatibleInitialStrongH3Trace_physicalL2RightTrace`
- `h3Audit_compatibleInitialPhysicalMild_energyRightLimit`
- `H3AuditInitialPhysicalEnergyMildZeroCompatibleData`
- `h3Audit_initialMildZeroCompatible_implies_physicalL2AndEnergyUpper`
- `h3Audit_initialMildZeroCompatible_strongH3Trace_via_physicalL2`

## Unresolved analysis

Old-solution initial mild representation and equality between the prescribed
old physical datum at zero and the mild initial spectral datum still need to
be supplied by an initial-value Navier–Stokes theorem. None of this derives
unconditional 3D global regularity. The terminal vorticity endpoint remains
independent. The bridge introduces no new axioms or sorry.

## Compilation fix 1

In `h3Audit_compatibleInitialStrongH3Trace_physicalL2RightTrace`,
Lean elaborates the continuous-map composition as
`h3SpectralScalarRawFourierL2 ∘ (fun t => F t j)`. A `change`
normalization makes the composition's lambda form explicit before the
existing initial-value rewrite. No theorem statement or hypothesis changed.
