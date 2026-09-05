import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Interior.Mode.ODE
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.StateL2

/-!
# Classicalization: quotient-safe raw Fourier L² continuity of the endpoint path

The pointwise raw Fourier coordinate

    ξ ↦ h3SpectralScalarRawFourier (W s i) ξ

is obtained from an `Lp` representative and therefore is not the right object
for transporting Banach-space time continuity through fixed-frequency
evaluation.

The repository already contains the correct quotient-safe replacement:

    h3SpectralFinCoordinateRawFourierL2CLM i

which first projects one finite velocity coordinate and then exactly deweights
the weighted H³ spectral state into its canonical Fourier `L²` class.  This map
is continuous linear and contractive.

The endpoint canonical real path `W` is globally continuous in the weighted H³
state norm.  Composing with the coordinate/deweighting continuous linear map
therefore gives a globally continuous path in raw Fourier `L²`, coordinatewise.

This is the topology needed by the next quotient-safe variation-of-constants
rung.  No pointwise representative, fixed-frequency evaluation, PDE identity,
or new estimate appears here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology BigOperators

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalRawFourierL2Continuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Each finite velocity coordinate of the endpoint canonical real path,
after exact H³ deweighting, is globally continuous as a genuine Fourier `L²`
class. -/
theorem continuous_h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_rawFourierL2
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 ≤ tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (i : Fin 3) :
    Continuous
      (fun s : ℝ =>
        h3SpectralScalarRawFourierL2
          ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
            hNS ht htau hEnd hE hTail hEndpoint) s i)) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau hEnd hE hTail hEndpoint

  have hW : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau hEnd hE hTail hEndpoint

  have hRaw :
      Continuous
        (fun s : ℝ =>
          h3SpectralFinCoordinateRawFourierL2CLM i (W s)) :=
    (h3SpectralFinCoordinateRawFourierL2CLM i).continuous.comp hW

  simpa only [
    W,
    h3SpectralFinCoordinateRawFourierL2CLM_apply
  ] using hRaw

/-- In particular, the quotient-safe raw Fourier `L²` coordinate is continuous
on the full physical overlap interval. -/
theorem continuousOn_h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_rawFourierL2
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 ≤ tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (i : Fin 3) :
    ContinuousOn
      (fun s : ℝ =>
        h3SpectralScalarRawFourierL2
          ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
            hNS ht htau hEnd hE hTail hEndpoint) s i))
      (Set.Icc (0 : ℝ) tau) := by
  exact
    (continuous_h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_rawFourierL2
      hNS ht htau hEnd hE hTail hEndpoint i).continuousOn

/-- Quotient-safe raw Fourier `L²` continuity within the overlap interval at
the left endpoint. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_rawFourierL2_continuousWithinAt_zero
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 ≤ tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (i : Fin 3) :
    ContinuousWithinAt
      (fun s : ℝ =>
        h3SpectralScalarRawFourierL2
          ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
            hNS ht htau hEnd hE hTail hEndpoint) s i))
      (Set.Icc (0 : ℝ) tau)
      0 := by
  exact
    (continuous_h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_rawFourierL2
      hNS ht htau hEnd hE hTail hEndpoint i).continuousAt.continuousWithinAt

/-- Quotient-safe raw Fourier `L²` continuity within the overlap interval at
the right endpoint. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_rawFourierL2_continuousWithinAt_tau
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 ≤ tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (i : Fin 3) :
    ContinuousWithinAt
      (fun s : ℝ =>
        h3SpectralScalarRawFourierL2
          ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
            hNS ht htau hEnd hE hTail hEndpoint) s i))
      (Set.Icc (0 : ℝ) tau)
      tau := by
  exact
    (continuous_h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_rawFourierL2
      hNS ht htau hEnd hE hTail hEndpoint i).continuousAt.continuousWithinAt

end

end Euclidean
end Bridge
end PrimeTensor
