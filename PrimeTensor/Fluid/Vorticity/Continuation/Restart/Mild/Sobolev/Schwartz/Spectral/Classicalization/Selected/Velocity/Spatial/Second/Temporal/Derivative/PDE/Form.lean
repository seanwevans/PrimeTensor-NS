import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Spatial.Temporal.Derivative.PDE.Form
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Time.Derivative.Spatial.C2
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.C2.Spatial.Regularity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spatial.Regularity

/-!
# Classicalization: second spatial derivative of the selected temporal PDE

The selected temporal derivative is now spatially `C²`, and the nonlinear
forcing is spatially `C²`.

At a strict positive restart time we may therefore differentiate the concrete
selected temporal PDE twice in space.  For ordered axes `a,b` this gives

    ∂ₐ∂ᵦ(∂ₜuᵢ)
      =
    ν * Σⱼ ∂ₐ∂ᵦ∂ⱼ∂ⱼuᵢ
      - ∂ₐ∂ᵦ Nᵢ(u,u).

No time/space commutation is used here.  This file only differentiates the
already-proved pointwise temporal PDE in the spatial variables.

The resulting coefficient is exactly the real physical quantity that the
selected second-Fréchet ordinary-time derivative must produce in order to
close the H³ order-two commutation frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocitySecondSpatialTemporalDerivativePDEForm
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-! ## A C⁴ field has C¹ ordered third partials -/

private theorem contDiff_four_thirdPartial_spatialC1
    {f : ScalarField3}
    (hf : ContDiff ℝ 4 f)
    (a b c : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (spatial3.d a
        (spatial3.d b
          (spatial3.d c f))) := by

  have hfC2 :
      SpatialC2 f := by
    unfold SpatialC2
    exact hf.of_le (by norm_num)

  have hFderivC3 :
      ContDiff ℝ 3
        (fderiv ℝ f) := by
    exact
      hf.fderiv_right
        (by norm_num)

  have hFirstC3 :
      SpatialC3
        (spatial3.d c f) := by

    have hDirectional :
        ContDiff ℝ 3
          (fun y : Point3 =>
            (fderiv ℝ f y)
              (axisDirection c)) :=
      hFderivC3.clm_apply
        contDiff_const

    unfold SpatialC3

    change
      ContDiff ℝ 3
        (fun y : Point3 =>
          partialDeriv c f y)

    rw [
      hfC2.partialDeriv_fun_eq c
    ]

    exact hDirectional

  have hSecondC2 :
      SpatialC2
        (spatial3.d b
          (spatial3.d c f)) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
      hFirstC3 b

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      hSecondC2 a

/-! ## Scalar-coordinate formula -/

/--
Twice spatially differentiate the actual selected temporal derivative.

The order is deliberately preserved as `a,b,j,j`; no Schwarz reordering is
needed.
-/
theorem spatial_d2_temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_eq_secondMixedDerivativeCandidate
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3)
    (a b : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    spatial3.d
      a
      (spatial3.d
        b
        (fun y : Point3 =>
          temporal.d
            (fun s : ℝ =>
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (W s i) y)
            t))
      x
      =
    ν *
        (∑ j : Fin 3,
          spatial3.d
            a
            (spatial3.d
              b
              (spatial3.d
                (h3AxisOfFin3 j)
                (spatial3.d
                  (h3AxisOfFin3 j)
                  (h3SpectralScalarRealC1RepresentativeOnPoint3
                    (W t i)))))
            x)
      -
    spatial3.d
      a
      (spatial3.d
        b
        (fun y : Point3 =>
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W t) (W t) i y).re))
      x := by

  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let u : ScalarField3 :=
    h3SpectralScalarRealC1RepresentativeOnPoint3
      (W t i)

  let F : ScalarField3 :=
    fun y : Point3 =>
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        (W t) (W t) i y).re

  let T : ScalarField3 :=
    fun y : Point3 =>
      temporal.d
        (fun s : ℝ =>
          h3SpectralScalarRealC1RepresentativeOnPoint3
            (W s i) y)
        t

  have huC4 :
      ContDiff ℝ 4 u := by
    dsimp only [u, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_contDiff_nat
        4 hν U₀ hA hU₀ ht htR.le i

  have hFC2 :
      SpatialC2 F := by
    unfold SpatialC2
    dsimp only [F, W]
    exact
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_contDiff_two
        hν U₀ hA hU₀ ht htR.le i

  have hFieldFirst :
      spatial3.d b T
        =
      (fun y : Point3 =>
        ν *
            (∑ j : Fin 3,
              spatial3.d
                b
                (spatial3.d
                  (h3AxisOfFin3 j)
                  (spatial3.d
                    (h3AxisOfFin3 j)
                    u))
                y)
          -
        spatial3.d b F y) := by

    funext y

    dsimp only [T, u, F]

    simpa only [W] using
      spatial_d_temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_eq_mixedDerivativeCandidate
        hν U₀ hA hU₀ ht htR i y b

  have hTermC1
      (j : Fin 3) :
      SpatialC1
        (spatial3.d
          b
          (spatial3.d
            (h3AxisOfFin3 j)
            (spatial3.d
              (h3AxisOfFin3 j)
              u))) :=
    contDiff_four_thirdPartial_spatialC1
      huC4
      b
      (h3AxisOfFin3 j)
      (h3AxisOfFin3 j)

  have hForceFirstC1 :
      SpatialC1
        (spatial3.d b F) :=
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      hFC2 b

  have hTrace :
      HasDerivAt
        (fun r : ℝ =>
          ∑ j : Fin 3,
            spatial3.d
              b
              (spatial3.d
                (h3AxisOfFin3 j)
                (spatial3.d
                  (h3AxisOfFin3 j)
                  u))
              (coordinateLine x a r))
        (∑ j : Fin 3,
          spatial3.d
            a
            (spatial3.d
              b
              (spatial3.d
                (h3AxisOfFin3 j)
                (spatial3.d
                  (h3AxisOfFin3 j)
                  u)))
            x)
        (x a) := by

    apply HasDerivAt.fun_sum

    intro j _hj

    exact
      (hTermC1 j).hasDerivAt_coordinateLine_spatial_d
        x a

  have hForce :
      HasDerivAt
        (fun r : ℝ =>
          spatial3.d b F
            (coordinateLine x a r))
        (spatial3.d a
          (spatial3.d b F)
          x)
        (x a) :=
    hForceFirstC1.hasDerivAt_coordinateLine_spatial_d
      x a

  have hTraceDeriv :
      deriv
        (fun r : ℝ =>
          ∑ j : Fin 3,
            spatial3.d
              b
              (spatial3.d
                (h3AxisOfFin3 j)
                (spatial3.d
                  (h3AxisOfFin3 j)
                  u))
              (coordinateLine x a r))
        (x a)
      =
    ∑ j : Fin 3,
      spatial3.d
        a
        (spatial3.d
          b
          (spatial3.d
            (h3AxisOfFin3 j)
            (spatial3.d
              (h3AxisOfFin3 j)
              u)))
        x :=
    hTrace.deriv

  have hForceDeriv :
      deriv
        (fun r : ℝ =>
          spatial3.d b F
            (coordinateLine x a r))
        (x a)
      =
    spatial3.d a
      (spatial3.d b F)
      x :=
    hForce.deriv

  change
    spatial3.d a
        (spatial3.d b T)
        x
      =
    ν *
        (∑ j : Fin 3,
          spatial3.d
            a
            (spatial3.d
              b
              (spatial3.d
                (h3AxisOfFin3 j)
                (spatial3.d
                  (h3AxisOfFin3 j)
                  u)))
            x)
      -
    spatial3.d a
      (spatial3.d b F)
      x

  rw [hFieldFirst]

  change
    partialDeriv a
        (fun y : Point3 =>
          ν *
              (∑ j : Fin 3,
                spatial3.d
                  b
                  (spatial3.d
                    (h3AxisOfFin3 j)
                    (spatial3.d
                      (h3AxisOfFin3 j)
                      u))
                  y)
            -
          spatial3.d b F y)
        x
      =
    ν *
        (∑ j : Fin 3,
          spatial3.d
            a
            (spatial3.d
              b
              (spatial3.d
                (h3AxisOfFin3 j)
                (spatial3.d
                  (h3AxisOfFin3 j)
                  u)))
            x)
      -
    spatial3.d a
      (spatial3.d b F)
      x

  unfold partialDeriv

  change
    deriv
        ((fun r : ℝ =>
            ν *
              (∑ j : Fin 3,
                spatial3.d
                  b
                  (spatial3.d
                    (h3AxisOfFin3 j)
                    (spatial3.d
                      (h3AxisOfFin3 j)
                      u))
                  (coordinateLine x a r)))
          -
        (fun r : ℝ =>
          spatial3.d b F
            (coordinateLine x a r)))
        (x a)
      =
    ν *
        (∑ j : Fin 3,
          spatial3.d
            a
            (spatial3.d
              b
              (spatial3.d
                (h3AxisOfFin3 j)
                (spatial3.d
                  (h3AxisOfFin3 j)
                  u)))
            x)
      -
    spatial3.d a
      (spatial3.d b F)
      x

  rw [
    deriv_sub
      (hTrace.differentiableAt.const_mul ν)
      hForce.differentiableAt,
    deriv_const_mul ν hTrace.differentiableAt,
    hTraceDeriv,
    hForceDeriv
  ]

/-! ## Velocity-component form -/

/--
Velocity-component form of the twice-spatially differentiated selected
temporal PDE.
-/
theorem spatial_d2_temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_eq_secondMixedDerivativeCandidate
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (x : Point3)
    (a b j : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    spatial3.d
      a
      (spatial3.d
        b
        (fun y : Point3 =>
          temporal.d
            (fun s : ℝ =>
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                hν U₀ hA hU₀ s y).component j)
            t))
      x
      =
    ν *
        (∑ k : Fin 3,
          spatial3.d
            a
            (spatial3.d
              b
              (spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (fun y : Point3 =>
                    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                      hν U₀ hA hU₀ t y).component j))))
            x)
      -
    spatial3.d
      a
      (spatial3.d
        b
        (fun y : Point3 =>
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W t) (W t)
            (h3ClassicalizationFinOfAxis j) y).re))
      x := by

  dsimp only

  change
    spatial3.d
      a
      (spatial3.d
        b
        (fun y : Point3 =>
          temporal.d
            (fun s : ℝ =>
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  hν U₀ hA hU₀ s
                  (h3ClassicalizationFinOfAxis j))
                y)
            t))
      x
      =
    ν *
        (∑ k : Fin 3,
          spatial3.d
            a
            (spatial3.d
              b
              (spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (h3SpectralScalarRealC1RepresentativeOnPoint3
                    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                      hν U₀ hA hU₀ t
                      (h3ClassicalizationFinOfAxis j))))))
            x)
      -
    spatial3.d
      a
      (spatial3.d
        b
        (fun y : Point3 =>
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ t)
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ t)
            (h3ClassicalizationFinOfAxis j) y).re))
      x

  exact
    spatial_d2_temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_eq_secondMixedDerivativeCandidate
      hν U₀ hA hU₀ ht htR
      (h3ClassicalizationFinOfAxis j)
      x a b

end

end Euclidean
end Bridge
end PrimeTensor
