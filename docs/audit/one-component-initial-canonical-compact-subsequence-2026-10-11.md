# Initial canonical overlap: compact weak cluster subsequences

Base checkpoint: `25346558` — derive initial scalar weak FTC from interior derivative and sequence.

The previous scalar-FTC route asks, for every physical component and compact smooth
scalar test, for an integrable scalar temporal source, a positive-time strong
scalar derivative, and one right-approaching initial-value sequence. The new
route eliminates BOTH the temporal source and the derivative completely when
the existing *canonical old/selected overlap* is assumed.

Why: `h3Audit_initialCanonicalOverlap_fullStrongH3Trace` gives an actual old
strong H³ spectral right limit `U₀`. Continuous inverse Fourier decoding
(`h3Audit_initialStrongSpectralTrace_physicalDecodeRightLimit`) gives a strong
physical L² right limit `L_j` for each velocity coordinate. This forces each
compact-test pairing to have the corresponding strong-decoder right limit.
If *some* positive-time sequence approaching zero has pairing limit equal to
the prescribed initial velocity pairing (a different sequence may be chosen
for each component and each test), uniqueness of scalar limits makes the
initial and decoder pairings equal. Project-proved density of compact smooth
scalar tests (`h3ScalarL2_eq_of_weakTest_inner_eq_orderOne`) implies
`L_j = u_j(0)` in physical `L²`.

This produces the complete original compact-weak trace contract, then the
correct physical zero-jet strong L² initial trace and H³ energy upper limit.
The terminal physical vorticity H³ endpoint remains an independent condition
for the full-time transverse homogeneous 3/2-Sobolev conclusions.

## New declarations

- `h3Audit_initialStrongL2Limit_identified_by_compactSubsequences`
- `h3Audit_initialStrongSpectralTrace_and_compactSubsequences_implies_physicalL2Trace`
- `H3AuditInitialCanonicalOverlapCompactSubsequenceData`
- `h3Audit_initialCanonicalCompactSubsequence_implies_compactInitialData`
- `h3Audit_initialCanonicalCompactSubsequence_implies_physicalZeroJetAndEnergyUpper`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialCanonicalCompactSubsequence`

## Explicit unclosed PDE obligations

The actual old/selected canonical mild overlap must still be proved from the
specific physical initial-value problem, and the prescribed distributional
initial-state cluster property must still be supplied. Open-time Navier--Stokes
admissibility does not on its own identify the specified field `u(0)`.

This is a logical reduction of sufficient initial hypotheses, not a proof of
regularity or of the old/selected overlap. No new axioms were introduced.
