# Initial diffusion-minus-Leray projected-RHS weak evolution

Base checkpoint: `88b8175e` — derive initial kinetic control from physical projected RHS weak FTC.

## Genuine new deductions

- Two interval-integrable physical Hilbert paths `D,N` yield an interval-integrable projected source `D-N`, with the quantitative triangle estimate `∫ ‖D-N‖ ≤ ∫ ‖D‖ + ∫ ‖N‖`.
- The common dual mass bound is constructed from the two source integrals. No separate numerical budget constant is requested.
- The strictly positive scalar `HasDerivAt` momentum identity against every Schwartz vector, together with the two source integrability hypotheses, yields the exact two-time weak momentum FTC via `intervalIntegral.integral_eq_sub_of_hasDerivAt`. Both time directions are covered; neither endpoint equals zero.
- Existing projected-RHS/Schwartz dual estimates then imply cofinal kinetic control and the existing conditional compact weak-test comparison, physical zero-jet trace, H3 upper trace, and transverse full-time Sobolev conclusions.

## Audit of remaining assumptions

The `D` and `N` paths are intended as the actual physical diffusion and Leray-projected transport. **This module does not itself identify them with pointwise PDE differential operators**. Their `L¹_t L²_x` integrability over `(0,b)` and the exact positive-time scalar derivative identity are new explicit inputs that still need verification from Navier–Stokes data. They may be stronger than the weak PDE alone.

The selected/old epsilon-vanishing relative-energy comparison is still assumed, and a strong-H3 actual-vorticity terminal endpoint is independently required for the full-time transverse conclusion. No 3D Navier–Stokes global regularity or unconditional continuation result is claimed.

## New declarations

- `h3Audit_initialDiffusionLeray_integrableProjectedRHS_and_mass`
- `h3Audit_initialDiffusionLeray_exists_projectedRHS_budget`
- `h3Audit_initialDiffusionLeray_scalarDerivative_implies_weakFTC`
- `h3Audit_initialDiffusionLeray_implies_schwartzDualL1`
- `H3AuditInitialCanonicalDiffusionLerayRelativeEnergyData`
- `h3Audit_initialDiffusionLeray_implies_projectedRHSData`
- `h3Audit_initialDiffusionLeray_implies_schwartzDualL1Data`
- `h3Audit_initialDiffusionLeray_implies_compactWeakComparisonData`
- `h3Audit_initialDiffusionLeray_implies_physicalZeroJetAndEnergyUpper`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialDiffusionLeray`

No sorry/admit declarations. Compilation is to be checked with local `lake env lean` and full `lake build`.
