import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Second.Mixed.Derivative.Candidate.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Second.Partial.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Spatial.Second.Temporal.Derivative.PDE.Form

/-!
# Classicalization: time derivative of a selected real second spatial partial

The selected complex second spatial Fréchet coordinate now has an ordinary time
derivative.  The preceding order-two candidate bridge identifies the real part
of that derivative coefficient with the concrete twice-spatially differentiated
temporal PDE candidate, while the selected real second-partial bridge identifies
the spatial path itself with the real part of the complex Hessian coordinate.

Combining those facts proves the actual order-two mixed derivative:

    d/dt (∂ₐ∂ᵦ uᵢ)(t,x)
      =
    ∂ₐ∂ᵦ (d/dt uᵢ)(t,x).

No general mixed-partial theorem is invoked.  Both sides are identified with
the same explicit fourth-trace-minus-forcing-Hessian PDE coefficient.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityRealSecondPartialTimeDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At every strict positive interior restart time, an ordered concrete real
second spatial partial of one selected scalar coordinate has time derivative
equal to the same ordered second spatial partial of the actual temporal
derivative. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_spatial_d_two_hasDerivAt_time
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3)
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
            (h3SpectralScalarRealC1RepresentativeOnPoint3
              (W r i)))
          x)
      (spatial3.d
        (h3AxisOfFin3 a)
        (spatial3.d
          (h3AxisOfFin3 b)
          (fun y : Point3 =>
            temporal.d
              (fun r : ℝ =>
                h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W r i) y)
              t))
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

  let m : Fin 2 → H3FourierPoint3 :=
    ![ea, eb]

  let C : ℝ → ℂ :=
    fun r : ℝ =>
      iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative
          (W r i))
        xf m

  let coefficient : ℂ :=
    (ν : ℂ) *
        (∑ k : Fin 3,
          iteratedFDeriv ℝ 4
            (h3SpectralScalarC1Representative
              (W t i))
            xf
            ![
              ea,
              eb,
              h3FourierAxisDirection (h3AxisOfFin3 k),
              h3FourierAxisDirection (h3AxisOfFin3 k)
            ])
      -
    iteratedFDeriv ℝ 2
      (h3RawFinLerayOuterProductDivergenceC0Representative
        (W t) (W t) i)
      xf m

  let P : ℝ → ℝ :=
    fun r : ℝ =>
      spatial3.d
        (h3AxisOfFin3 a)
        (spatial3.d
          (h3AxisOfFin3 b)
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (W r i)))
        x

  have hComplex :
      HasDerivAt C coefficient t := by
    dsimp only [C, coefficient, W, xf, ea, eb, m]
    exact
      h3SelectedVelocity_C1_secondFrechet_coordinate_hasDerivAt_time
        hν U₀ hA hU₀ ht htR i a b
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
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_secondPartial_eq_re_secondFrechet_axes
        hν U₀ hA hU₀
        hr.1
        (by
          simpa only [R] using hr.2)
        i x
        (h3AxisOfFin3 a)
        (h3AxisOfFin3 b)

    dsimp only at hBridge
    dsimp only [P, C, W, xf, ea, eb, m]
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
                  (h3AxisOfFin3 k)
                  (spatial3.d
                    (h3AxisOfFin3 k)
                    (h3SpectralScalarRealC1RepresentativeOnPoint3
                      (W t i)))))
              x)
        -
      spatial3.d
        (h3AxisOfFin3 a)
        (spatial3.d
          (h3AxisOfFin3 b)
          (fun y : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W t) (W t) i y).re))
        x := by
    dsimp only [coefficient, W, xf, ea, eb, m]
    exact
      h3SelectedVelocity_C1_secondFrechet_coordinate_timeDerivativeCandidate_re_eq_secondMixedDerivativeCandidate
        hν U₀ hA hU₀ ht htR i a b x

  have hPDE :=
    spatial_d2_temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_eq_secondMixedDerivativeCandidate
      hν U₀ hA hU₀ ht htR i x
      (h3AxisOfFin3 a)
      (h3AxisOfFin3 b)

  dsimp only at hPDE

  have hCoefficient :
      coefficient.re
        =
      spatial3.d
        (h3AxisOfFin3 a)
        (spatial3.d
          (h3AxisOfFin3 b)
          (fun y : Point3 =>
            temporal.d
              (fun r : ℝ =>
                h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W r i) y)
              t))
        x := by
    exact hCandidate.trans hPDE.symm

  have hSpatial :
      HasDerivAt
        P
        (spatial3.d
          (h3AxisOfFin3 a)
          (spatial3.d
            (h3AxisOfFin3 b)
            (fun y : Point3 =>
              temporal.d
                (fun r : ℝ =>
                  h3SpectralScalarRealC1RepresentativeOnPoint3
                    (W r i) y)
                t))
          x)
        t :=
    hSpatialRaw.congr_deriv hCoefficient

  dsimp only [P, W] at hSpatial ⊢
  exact hSpatial

end

end Euclidean
end Bridge
end PrimeTensor
