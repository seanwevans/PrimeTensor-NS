import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedCanonicalFirstFrechetTemporalDerivativeRegularity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityRealFirstFrechetBridge

/-!
# Classicalization: canonical real Point3 first-Fréchet bridge

The explicit canonical inverse-Fourier reconstruction now carries the full
first-spatial-derivative temporal regularity package on the complex Fourier
carrier.

The existing selected real first-Fréchet bridge identifies the real `Point3`
first derivative with the real part of the generic complex H³ representative.
The new canonical reconstruction is exactly that generic representative on the
strict positive restart interval.

This file splices those two facts together.  The resulting theorem keeps the
concrete real `Point3` representative on the left, while replacing the
arbitrary complex representative on the right by the explicit canonical
inverse-Fourier reconstruction.

No new differentiability theorem, estimate, or time argument is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedCanonicalRealFirstFrechetBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At every strict positive interior restart time, the first Fréchet
coordinate of the concrete real `Point3` selected representative is exactly
the real part of the corresponding first Fréchet coordinate of the explicit
canonical complex reconstruction. -/
theorem h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_realC1RepresentativeOnPoint3_firstFrechet_axisDirection_eq_re_canonical
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3)
    (a : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    iteratedFDeriv ℝ 1
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (W t i))
        x
        (fun _ : Fin 1 => axisDirection a)
      =
    (iteratedFDeriv ℝ 1
        (h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
          hν U₀ hA hU₀ t i)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)
        (fun _ : Fin 1 => h3FourierAxisDirection a)).re := by
  dsimp only

  have hOld :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_firstFrechet_axisDirection_eq_re
      hν U₀ hA hU₀ ht htR i x a

  dsimp only at hOld

  have hPath :
      h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
          hν U₀ hA hU₀
        =
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ :=
    h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_eq_mildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  rw [← hPath] at hOld

  have hCanonical :
      h3SpectralScalarC1Representative
          ((h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
            hν U₀ hA hU₀) t i)
        =
      h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
        hν U₀ hA hU₀ t i :=
    h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_C1Representative_eq_canonical
      hν U₀ hA hU₀ ht htR.le i

  rw [hCanonical] at hOld

  exact hOld

end

end Euclidean
end Bridge
end PrimeTensor
