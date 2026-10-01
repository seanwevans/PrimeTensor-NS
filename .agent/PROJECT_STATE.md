# PrimeTensor-NS Project State

Keep this concise and update it before each checkpoint.

## Last known clean checkpoint
`8a3b9cb7 extract actual frequency sequence from dissipation concentration`

Strict localized physical H3 dissipation mass now makes every shrinking high-radial bad-cone localization nonempty. An actual frequency sequence is therefore selected and the literal transverse aspect-ratio classification applies nonvacuously.

## Immediate intended checkpoint
Strengthen that selected sequence to points where the canonical single-time spectral dissipation density is strictly positive.

A previous manual draft of `...PhysicalDissipationPositiveDensityFrequencyAspectRatioLimit.lean` had the correct argument but failed on local measure/typeclass synthesis.

Intended repair: mirror compiled physical-dissipation files by installing local finite-axis and Point3 product-measure instances, and use an explicit `∂volume` localized lintegral.

Argument: if the nonnegative spectral dissipation density vanished at every point in the localization, `setLIntegral_eq_zero` would force localized mass zero, contradicting the strict lower bound. This proves a positive-density point, not positive atomic mass.

## Recent frontier
The hypothetical nonextension branch has been sharpened through:
- single-time physical H3 dissipation concentration on shrinking high-radial equatorial bad cones;
- transverse polarization and a fixed transverse channel;
- literal coordinate lower bounds;
- longitudinal/transverse ratio collapse;
- transverse share theta in [1/2,1];
- axial vs genuine two-channel regimes;
- squared and unsquared transverse aspect-ratio limits;
- actual nonvacuous frequency selection.

Earlier: infrared branch conditionally excluded using raw velocity Fourier L2 Cauchy; full physical H3 dissipation identified with radial Fourier moment.

## Strategic frontier after positive-density selection
Stop repackaging finite-dimensional geometry unless it closes a genuine gap.

The substantive analytical direction is to derive the physical angular vanishing continuation criterion from standard compactness/equiintegrability hypotheses:

1. uniform radial-tail tightness handles |xi| > R;
2. on rho <= |xi| <= R, shrinking cone volume tends to zero;
3. uniform integrability of physical H3 dissipation density converts small measure to small mass.

Mere uniform L1/dissipation boundedness is not uniform integrability.

## Scientific constraint
Remain neutral. These are necessary mechanisms under hypothetical nonextension and conditional continuation criteria; neither a singular solution nor global regularity has been proved.
