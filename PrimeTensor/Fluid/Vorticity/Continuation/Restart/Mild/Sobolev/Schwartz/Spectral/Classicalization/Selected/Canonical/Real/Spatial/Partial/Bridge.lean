import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Canonical.Real.First.Frechet.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Spatial.Partial.Bridge

/-!
# Classicalization: canonical real spatial-partial / first-Fréchet bridge

The canonical real first-Fréchet bridge now identifies the concrete `Point3`
first derivative with the real part of the explicit canonical complex
reconstruction.

The historical selected chain immediately converts that order-one Fréchet
statement into the project's concrete Euclidean derivative language:

    spatial3.d a u_i(t,x)
      =
    Re (D u_i^complex(t,toLp x)[e_a]).

This file transports that exact spatial-partial identity to the canonical
complex reconstruction.  The real selected representative on the left is
unchanged; only the complex representative on the right is replaced by the
explicit canonical inverse-Fourier representative.

No time differentiation, PDE identity, estimate, or mixed-partial commutation
is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedCanonicalRealSpatialPartialBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At every strict positive interior restart time, the concrete real spatial
partial of the selected scalar coordinate is exactly the real part of the
corresponding first Fréchet coordinate of the explicit canonical complex
reconstruction. -/
theorem h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_realC1RepresentativeOnPoint3_spatial_d_eq_re_canonical_firstFrechet
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
    spatial3.d
        a
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (W t i))
        x
      =
    ((fderiv ℝ
        (h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
          hν U₀ hA hU₀ t i)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
      (h3FourierAxisDirection a)).re := by
  dsimp only

  have hOld :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_spatial_d_eq_re_firstFrechet
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
