# Physical H³ transport as a pure sixth-power Fourier flux

Baseline: `bfdd95dd` (`master`).

## Exact cancellation

For an arbitrary complex Schwartz vector `v`, the previously proved full
six-orbit identity includes the longitudinal correction
`thirdFullSchwartzLongitudinalFluxDefect244 v z`. Each of its three terms
contains the Fourier contraction `ξ · û(ξ)` for one of the three momentum
vertices. The existing physical Fourier divergence theorem establishes

`∀ ξ, mixedDot ξ (h3SchwartzTriadPolarization v ξ) = 0`

from literal pointwise physical divergence, including zero frequency.
Therefore **the entire longitudinal defect vanishes for every triad**,
not merely almost everywhere or after integration. The first theorem exposes
this fact as a reusable interface.

The corrected exact physical identity then becomes, for an actual real
solenoidal Schwartz velocity `f`, with precisely the existing Fourier
normalization,

`fullSchwartzThirdCommutator244 f = ((2*pi)^7 / 3) * Im ∫ Flux_6(f,z) dz`.

No separate absolute-integrability or nonzero-frequency input is assumed;
the unrestricted corrected identity already supplies integrability.

## Simultaneous physical snapshot limit

The theorem compiled in `b6cbef2d` selects one genuinely solenoidal real
Schwartz family for each admissible Fourier-compatible physical H³ snapshot,
with exact E₂/E₃ matching and actual old PDE transport convergence. The
second and third theorems remove the correction from each field and transfer
this equality along the original converging sequence. The last theorem
retains the same weighted H³ convergence, Fourier representative, E₂/E₃
limits and pointwise zero correction.

In particular the *uncorrected* sixth-power radial Fourier integral
converges to `velocityH3TransportDerivative3At u t` for the **same sequence**.
This fills the previously explicit physical-longitudinal defect boundary;
it does not show that the signed flux is nonnegative, dissipative, or
controlled by a subcritical energy norm.

## Audit

Four theorems; eight `#check` and `#print axioms` registrations, no new
axioms or proof placeholders. The direct test is:

`lake env lean PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/FullThirdSolenoidalPureSixthPowerFluxLimit.lean`

After this compiles, the hard obstruction is a sign/size estimate for the
**transverse** three-transfer flux itself, not the longitudinal correction.
