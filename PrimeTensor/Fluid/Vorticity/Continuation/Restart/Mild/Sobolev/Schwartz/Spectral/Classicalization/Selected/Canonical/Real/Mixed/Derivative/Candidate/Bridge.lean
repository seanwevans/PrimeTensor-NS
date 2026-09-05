import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Canonical.Real.Spatial.Partial.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Mixed.Derivative.Candidate.Bridge

/-!
# Classicalization: canonical real mixed-derivative candidate bridge

The canonical branch now reaches the project's concrete real spatial-partial
language at order one.

The historical selected classicalization stack also proves that taking the real
part of the complex first-Fréchet time-derivative coefficient gives exactly the
concrete real mixed-derivative Navier--Stokes candidate:

    Re (ν Σ_k D³u[e_a,e_k,e_k] - DN[e_a])
      =
    ν Σ_k ∂_a∂_k∂_k u - ∂_a Re N.

This file transports that identity to the explicit canonical inverse-Fourier
reconstruction.  The physical real representative and forcing remain the same
selected restart objects; only the complex representative occurring in the
third-Fréchet trace is replaced by the canonical reconstruction.

No new estimate, derivative interchange, or mixed-partial theorem is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedCanonicalRealMixedDerivativeCandidateBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Taking the real part of the canonical complex first-Fréchet
time-derivative coefficient produces exactly the concrete real mixed-derivative
PDE candidate. -/
theorem h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative_timeDerivativeCandidate_re_eq_mixedDerivativeCandidate
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i a : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let xf : H3FourierPoint3 :=
      (WithLp.toLp 2 : Point3 → H3FourierPoint3) x
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    Complex.re
      ((ν : ℂ) *
          (∑ k : Fin 3,
            iteratedFDeriv ℝ 3
              (h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
                hν U₀ hA hU₀ t i)
              xf
              ![
                ea,
                h3FourierAxisDirection (h3AxisOfFin3 k),
                h3FourierAxisDirection (h3AxisOfFin3 k)
              ])
        -
      (fderiv ℝ
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          xf) ea)
      =
    ν *
        (∑ k : Fin 3,
          spatial3.d
            (h3AxisOfFin3 a)
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W t i))))
            x)
      -
    spatial3.d
      (h3AxisOfFin3 a)
      (fun y : Point3 =>
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          (W t) (W t) i y).re)
      x := by
  dsimp only

  have hOld :=
    h3SelectedVelocity_C1_fderiv_coordinate_timeDerivativeCandidate_re_eq_mixedDerivativeCandidate
      hν U₀ hA hU₀ ht htR i a x

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
