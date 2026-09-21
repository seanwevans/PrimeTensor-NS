import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Third.Frechet.Time.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Mixed.Derivative.Candidate.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Third.Mixed.Derivative.Candidate.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Spatial.Third.Temporal.Derivative.PDE.Form

/-!
# Classicalization: time derivative of a selected real third spatial partial

The selected complex third spatial Fréchet coordinate now has an ordinary time
derivative.  The order-three candidate bridge identifies the real part of that
coefficient with the concrete threefold-spatially differentiated temporal PDE
candidate, while the existing real third-partial bridge identifies the spatial
path itself with the real part of the complex third Fréchet coordinate.

Combining those facts proves

    d/dt (∂ₐ∂ᵦ∂𝑐 uᵢ)(t,x)
      =
    ∂ₐ∂ᵦ∂𝑐 (d/dt uᵢ)(t,x).

No general mixed-partial theorem is invoked.  Both sides are identified with
the same explicit fifth-trace-minus-third-forcing-derivative PDE coefficient.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityRealThirdPartialTimeDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At every strict positive interior restart time, an ordered concrete real
third spatial partial of one selected scalar coordinate has time derivative
equal to the same ordered third spatial partial of the actual temporal
derivative. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_spatial_d_three_hasDerivAt_time
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    HasDerivAt
      (fun r : ℝ =>
        spatial3.d
          (h3AxisOfFin3 a)
          (spatial3.d
            (h3AxisOfFin3 b)
            (spatial3.d
              (h3AxisOfFin3 c)
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (W r i))))
          x)
      (spatial3.d
        (h3AxisOfFin3 a)
        (spatial3.d
          (h3AxisOfFin3 b)
          (spatial3.d
            (h3AxisOfFin3 c)
            (fun y : Point3 =>
              temporal.d
                (fun r : ℝ =>
                  h3SpectralScalarRealC1RepresentativeOnPoint3
                    (W r i) y)
                t)))
        x)
      t := by
  dsimp only

  let R : ℝ :=
    h3FinHeatLerayRestartRadius ν A

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let xf : H3FourierPoint3 :=
    (WithLp.toLp 2 : Point3 → H3FourierPoint3) x

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let eb : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 b)

  let ec : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 c)

  let m : Fin 3 → H3FourierPoint3 :=
    ![ea, eb, ec]

  let C : ℝ → ℂ :=
    fun r : ℝ =>
      iteratedFDeriv ℝ 3
        (h3SpectralScalarC1Representative
          (W r i))
        xf m

  let coefficient : ℂ :=
    (ν : ℂ) *
        (∑ k : Fin 3,
          iteratedFDeriv ℝ 5
            (h3SpectralScalarC1Representative
              (W t i))
            xf
            ![
              ea,
              eb,
              ec,
              h3FourierAxisDirection (h3AxisOfFin3 k),
              h3FourierAxisDirection (h3AxisOfFin3 k)
            ])
      -
    iteratedFDeriv ℝ 3
      (h3RawFinLerayOuterProductDivergenceC0Representative
        (W t) (W t) i)
      xf m

  let P : ℝ → ℝ :=
    fun r : ℝ =>
      spatial3.d
        (h3AxisOfFin3 a)
        (spatial3.d
          (h3AxisOfFin3 b)
          (spatial3.d
            (h3AxisOfFin3 c)
            (h3SpectralScalarRealC1RepresentativeOnPoint3
              (W r i))))
        x

  have hComplex :
      HasDerivAt C coefficient t := by
    dsimp only [C, coefficient, W, xf, ea, eb, ec, m]
    exact
      h3SelectedVelocity_C1_thirdFrechet_coordinate_hasDerivAt_time
        hν U₀ hA hU₀ ht htR i a b c
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

  have hReal :
      HasDerivAt
        (fun r : ℝ => (C r).re)
        coefficient.re
        t := by
    change
      HasDerivAt
        (Complex.reCLM ∘ C)
        (Complex.reCLM coefficient)
        t
    exact
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt
        t hComplex

  have hWindow :
      Set.Ioo (0 : ℝ) R ∈ 𝓝 t := by
    apply Ioo_mem_nhds
    · exact ht
    · simpa only [R] using htR

  have hPathEq :
      P =ᶠ[𝓝 t]
        (fun r : ℝ => (C r).re) := by
    filter_upwards [hWindow] with r hr

    have hBridge :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_spatial_d_three_eq_re_thirdFrechet
        hν U₀ hA hU₀
        hr.1
        (by
          simpa only [R] using hr.2)
        i x
        (h3AxisOfFin3 a)
        (h3AxisOfFin3 b)
        (h3AxisOfFin3 c)

    dsimp only at hBridge
    dsimp only [P, C, W, xf, ea, eb, ec, m]
    exact hBridge

  have hSpatialRaw :
      HasDerivAt
        P
        coefficient.re
        t :=
    hReal.congr_of_eventuallyEq hPathEq

  have hCandidate :
      coefficient.re
        =
      ν *
          (∑ k : Fin 3,
            spatial3.d
              (h3AxisOfFin3 a)
              (spatial3.d
                (h3AxisOfFin3 b)
                (spatial3.d
                  (h3AxisOfFin3 c)
                  (spatial3.d
                    (h3AxisOfFin3 k)
                    (spatial3.d
                      (h3AxisOfFin3 k)
                      (h3SpectralScalarRealC1RepresentativeOnPoint3
                        (W t i))))))
              x)
        -
      spatial3.d
        (h3AxisOfFin3 a)
        (spatial3.d
          (h3AxisOfFin3 b)
          (spatial3.d
            (h3AxisOfFin3 c)
            (fun y : Point3 =>
              (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                (W t) (W t) i y).re)))
        x := by
    dsimp only [coefficient, W, xf, ea, eb, ec, m]
    exact
      h3SelectedVelocity_C1_thirdFrechet_coordinate_timeDerivativeCandidate_re_eq_thirdMixedDerivativeCandidate
        hν U₀ hA hU₀ ht htR i a b c x

  have hPDE :=
    spatial_d3_temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_eq_thirdMixedDerivativeCandidate
      hν U₀ hA hU₀ ht htR i x
      (h3AxisOfFin3 a)
      (h3AxisOfFin3 b)
      (h3AxisOfFin3 c)

  dsimp only at hPDE

  have hCoefficient :
      coefficient.re
        =
      spatial3.d
        (h3AxisOfFin3 a)
        (spatial3.d
          (h3AxisOfFin3 b)
          (spatial3.d
            (h3AxisOfFin3 c)
            (fun y : Point3 =>
              temporal.d
                (fun r : ℝ =>
                  h3SpectralScalarRealC1RepresentativeOnPoint3
                    (W r i) y)
                t)))
        x := by
    exact hCandidate.trans hPDE.symm

  have hSpatial :
      HasDerivAt
        P
        (spatial3.d
          (h3AxisOfFin3 a)
          (spatial3.d
            (h3AxisOfFin3 b)
            (spatial3.d
              (h3AxisOfFin3 c)
              (fun y : Point3 =>
                temporal.d
                  (fun r : ℝ =>
                    h3SpectralScalarRealC1RepresentativeOnPoint3
                      (W r i) y)
                  t)))
          x)
        t :=
    hSpatialRaw.congr_deriv hCoefficient

  dsimp only [P, W] at hSpatial ⊢
  exact hSpatial

end

end Euclidean
end Bridge
end PrimeTensor
