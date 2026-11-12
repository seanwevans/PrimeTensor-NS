# Actual annular deficit: exact two-time factorization and uniform excess windows

Base: `1e5bcb6b3f4295cac4a7d946a038b3125fb99594`.

## The hard analytic increment

For each genuine physical annulus `0 ≤ rho ≤ sigma ≤ R` and anchored time `b`, put

- `m(t) = thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho`,
- `y(t) = thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 t rho sigma`,
- `a = (rho² + sigma²)/2`, `w = rho^6`,
- `B = sqrt(E0(b)) * 3 * thirdFullPhysicalKineticLowBandSourceCeiling244 rho E0(b)`,
- `P = thirdFullPhysicalOuterViscousCapBase244 u b a`.

The physical annular deficit is exactly

`D(t) = w * (a*m(t) - B)^2 - m(t) * (y(t) + w*P)`.

Its two-time difference admits an **exact** factorization:

`D(s)-D(t) = (m(s)-m(t)) * [w*a*(a*(m(s)+m(t))-2*B) - (y(t)+w*P)] - m(s)*(y(s)-y(t))`.

The corresponding absolute value inequality identifies a single genuine
**ledger slope** multiplying the kinetic-mass increment. No surrogate for
the nonlinear Leray residual or replacement for the width cost is introduced.

The standalone `thirdFullKinetic_deficitPolynomial_floor_of_errors244` theorem
proves that a doubled deficit floor survives if the slope is bounded by `C`,
the physical highpass mass by `H`, and the already controlled mass/Young
increments by `etaM`, `etaY` satisfying `etaM*C+H*etaY ≤ epsilon`.

The second independent advance is **one common positive right physical
interval** preserving a doubled-to-single *strict kinetic excess* margin for
all annuli in `[radiusMin, R]` with `0 < radiusMin ≤ R`. Since the radial mean square obeys `0 ≤ a ≤ R²`,
the nonexpansive actual physical highpass and the joint window theorem can
be used with mass tolerance `margin/(R²+1)`. The same interval also controls
the full original Young-width cost with an independently prescribed
positive error.

## Remaining obstruction

For a fully unconditional uniform **deficit floor** on a bounded annular
family, derive a bound on the explicit two-time ledger slope that is
uniform over the relevant radii. It must use actual physical coefficients,
not an assumed universal global PDE regularity estimate. The new algebraic
lemma isolates that task exactly. Uniformity as `R → ∞` and cofinal
dissipation-window thickness still remain open.

All Lean declarations use the existing `PrimeTensor.FirstMonomialTriad`
namespace and are registered in the primary index and audit module.

The lower radius is necessary: a uniform positive kinetic excess over
`0 ≤ rho ≤ sigma ≤ R` would be impossible at `rho = sigma = 0`.
