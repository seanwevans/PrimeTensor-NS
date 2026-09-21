import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Spatial.Second.Temporal.Derivative.PDE.Form
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.C3.Spatial.Regularity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spatial.Regularity

/-!
# Classicalization: third spatial derivative of the selected temporal PDE

The selected velocity has arbitrary positive-time spatial regularity, and the
instantaneous nonlinear forcing is now spatially `C³`.

Therefore the already-proved twice-spatially differentiated temporal PDE may be
differentiated once more in space.  For ordered axes `a,b,c`:

    ∂ₐ∂ᵦ∂𝑐(∂ₜuᵢ)
      =
    ν * Σⱼ ∂ₐ∂ᵦ∂𝑐∂ⱼ∂ⱼuᵢ
      - ∂ₐ∂ᵦ∂𝑐 Nᵢ(u,u).

The derivative order is kept exactly as written.  No Schwarz reordering and no
time/space commutation is used.  This is the real physical order-three
candidate that the selected third-Fréchet ordinary-time derivative must
eventually produce.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityThirdSpatialTemporalDerivativePDEForm
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-! ## A C⁵ field has C¹ ordered fourth partials -/

private theorem contDiff_five_fourthPartial_spatialC1
    {f : ScalarField3}
    (hf : ContDiff ℝ 5 f)
    (a b c d : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (spatial3.d a
        (spatial3.d b
          (spatial3.d c
            (spatial3.d d f)))) := by

  have hfC3 :
      SpatialC3 f := by
    unfold SpatialC3
    exact hf.of_le (by norm_num)

  have hFirst4 :
      ContDiff ℝ 4
        (fun y : Point3 =>
          partialDeriv d f y) := by
    rw [
      PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_fun_eq
        hfC3 d
    ]
    exact
      (hf.fderiv_right (by norm_num)).clm_apply
        contDiff_const

  have hFirstC3 :
      SpatialC3
        (spatial3.d d f) := by
    unfold SpatialC3
    change
      ContDiff ℝ 3
        (fun y : Point3 =>
          partialDeriv d f y)
    exact hFirst4.of_le (by norm_num)

  have hSecond3 :
      ContDiff ℝ 3
        (fun y : Point3 =>
          partialDeriv c
            (fun z : Point3 =>
              partialDeriv d f z)
            y) := by
    change
      ContDiff ℝ 3
        (fun y : Point3 =>
          partialDeriv c
            (spatial3.d d f)
            y)
    rw [
      PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_fun_eq
        hFirstC3 c
    ]
    exact
      (hFirst4.fderiv_right (by norm_num)).clm_apply
        contDiff_const

  have hSecondC3 :
      SpatialC3
        (spatial3.d c
          (spatial3.d d f)) := by
    unfold SpatialC3
    change
      ContDiff ℝ 3
        (fun y : Point3 =>
          partialDeriv c
            (fun z : Point3 =>
              partialDeriv d f z)
            y)
    exact hSecond3

  have hThirdC2 :
      SpatialC2
        (spatial3.d b
          (spatial3.d c
            (spatial3.d d f))) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
      hSecondC3 b

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      hThirdC2 a

/-! ## Scalar-coordinate formula -/

/--
Threefold spatial differentiation of the actual selected temporal derivative.

The order is deliberately preserved as `a,b,c,j,j`.
-/
theorem spatial_d3_temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_eq_thirdMixedDerivativeCandidate
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3)
    (a b c : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    spatial3.d
      a
      (spatial3.d
        b
        (spatial3.d
          c
          (fun y : Point3 =>
            temporal.d
              (fun s : ℝ =>
                h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W s i) y)
              t)))
      x
      =
    ν *
        (∑ j : Fin 3,
          spatial3.d
            a
            (spatial3.d
              b
              (spatial3.d
                c
                (spatial3.d
                  (h3AxisOfFin3 j)
                  (spatial3.d
                    (h3AxisOfFin3 j)
                    (h3SpectralScalarRealC1RepresentativeOnPoint3
                      (W t i))))))
            x)
      -
    spatial3.d
      a
      (spatial3.d
        b
        (spatial3.d
          c
          (fun y : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W t) (W t) i y).re)))
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

  have huC5 :
      ContDiff ℝ 5 u := by
    dsimp only [u, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_contDiff_nat
        5 hν U₀ hA hU₀ ht htR.le i

  have hFC3 :
      SpatialC3 F := by
    unfold SpatialC3
    dsimp only [F, W]
    exact
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_selectedRestart_real_contDiff_three
        hν U₀ hA hU₀ ht htR.le i

  have hFieldSecond :
      spatial3.d b
          (spatial3.d c T)
        =
      (fun y : Point3 =>
        ν *
            (∑ j : Fin 3,
              spatial3.d
                b
                (spatial3.d
                  c
                  (spatial3.d
                    (h3AxisOfFin3 j)
                    (spatial3.d
                      (h3AxisOfFin3 j)
                      u)))
                y)
          -
        spatial3.d b
          (spatial3.d c F)
          y) := by

    funext y

    dsimp only [T, u, F]

    simpa only [W] using
      spatial_d2_temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_eq_secondMixedDerivativeCandidate
        hν U₀ hA hU₀ ht htR i y b c

  have hTermC1
      (j : Fin 3) :
      SpatialC1
        (spatial3.d
          b
          (spatial3.d
            c
            (spatial3.d
              (h3AxisOfFin3 j)
              (spatial3.d
                (h3AxisOfFin3 j)
                u)))) :=
    contDiff_five_fourthPartial_spatialC1
      huC5
      b
      c
      (h3AxisOfFin3 j)
      (h3AxisOfFin3 j)

  have hForceFirstC2 :
      SpatialC2
        (spatial3.d c F) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
      hFC3 c

  have hForceSecondC1 :
      SpatialC1
        (spatial3.d b
          (spatial3.d c F)) :=
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      hForceFirstC2 b

  have hTrace :
      HasDerivAt
        (fun r : ℝ =>
          ∑ j : Fin 3,
            spatial3.d
              b
              (spatial3.d
                c
                (spatial3.d
                  (h3AxisOfFin3 j)
                  (spatial3.d
                    (h3AxisOfFin3 j)
                    u)))
              (coordinateLine x a r))
        (∑ j : Fin 3,
          spatial3.d
            a
            (spatial3.d
              b
              (spatial3.d
                c
                (spatial3.d
                  (h3AxisOfFin3 j)
                  (spatial3.d
                    (h3AxisOfFin3 j)
                    u))))
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
          spatial3.d b
            (spatial3.d c F)
            (coordinateLine x a r))
        (spatial3.d a
          (spatial3.d b
            (spatial3.d c F))
          x)
        (x a) :=
    hForceSecondC1.hasDerivAt_coordinateLine_spatial_d
      x a

  have hTraceDeriv :
      deriv
        (fun r : ℝ =>
          ∑ j : Fin 3,
            spatial3.d
              b
              (spatial3.d
                c
                (spatial3.d
                  (h3AxisOfFin3 j)
                  (spatial3.d
                    (h3AxisOfFin3 j)
                    u)))
              (coordinateLine x a r))
        (x a)
      =
    ∑ j : Fin 3,
      spatial3.d
        a
        (spatial3.d
          b
          (spatial3.d
            c
            (spatial3.d
              (h3AxisOfFin3 j)
              (spatial3.d
                (h3AxisOfFin3 j)
                u))))
        x :=
    hTrace.deriv

  have hForceDeriv :
      deriv
        (fun r : ℝ =>
          spatial3.d b
            (spatial3.d c F)
            (coordinateLine x a r))
        (x a)
      =
    spatial3.d a
      (spatial3.d b
        (spatial3.d c F))
      x :=
    hForce.deriv

  change
    spatial3.d a
        (spatial3.d b
          (spatial3.d c T))
        x
      =
    ν *
        (∑ j : Fin 3,
          spatial3.d
            a
            (spatial3.d
              b
              (spatial3.d
                c
                (spatial3.d
                  (h3AxisOfFin3 j)
                  (spatial3.d
                    (h3AxisOfFin3 j)
                    u))))
            x)
      -
    spatial3.d a
      (spatial3.d b
        (spatial3.d c F))
      x

  rw [hFieldSecond]

  change
    partialDeriv a
        (fun y : Point3 =>
          ν *
              (∑ j : Fin 3,
                spatial3.d
                  b
                  (spatial3.d
                    c
                    (spatial3.d
                      (h3AxisOfFin3 j)
                      (spatial3.d
                        (h3AxisOfFin3 j)
                        u)))
                  y)
            -
          spatial3.d b
            (spatial3.d c F)
            y)
        x
      =
    ν *
        (∑ j : Fin 3,
          spatial3.d
            a
            (spatial3.d
              b
              (spatial3.d
                c
                (spatial3.d
                  (h3AxisOfFin3 j)
                  (spatial3.d
                    (h3AxisOfFin3 j)
                    u))))
            x)
      -
    spatial3.d a
      (spatial3.d b
        (spatial3.d c F))
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
                    c
                    (spatial3.d
                      (h3AxisOfFin3 j)
                      (spatial3.d
                        (h3AxisOfFin3 j)
                        u)))
                  (coordinateLine x a r)))
          -
        (fun r : ℝ =>
          spatial3.d b
            (spatial3.d c F)
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
                c
                (spatial3.d
                  (h3AxisOfFin3 j)
                  (spatial3.d
                    (h3AxisOfFin3 j)
                    u))))
            x)
      -
    spatial3.d a
      (spatial3.d b
        (spatial3.d c F))
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
Velocity-component form of the threefold-spatially differentiated selected
temporal PDE.
-/
theorem spatial_d3_temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_eq_thirdMixedDerivativeCandidate
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (x : Point3)
    (a b c j : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    spatial3.d
      a
      (spatial3.d
        b
        (spatial3.d
          c
          (fun y : Point3 =>
            temporal.d
              (fun s : ℝ =>
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                  hν U₀ hA hU₀ s y).component j)
              t)))
      x
      =
    ν *
        (∑ k : Fin 3,
          spatial3.d
            a
            (spatial3.d
              b
              (spatial3.d
                c
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (spatial3.d
                    (h3AxisOfFin3 k)
                    (fun y : Point3 =>
                      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                        hν U₀ hA hU₀ t y).component j)))))
            x)
      -
    spatial3.d
      a
      (spatial3.d
        b
        (spatial3.d
          c
          (fun y : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W t) (W t)
              (h3ClassicalizationFinOfAxis j) y).re)))
      x := by

  dsimp only

  change
    spatial3.d
      a
      (spatial3.d
        b
        (spatial3.d
          c
          (fun y : Point3 =>
            temporal.d
              (fun s : ℝ =>
                h3SpectralScalarRealC1RepresentativeOnPoint3
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    hν U₀ hA hU₀ s
                    (h3ClassicalizationFinOfAxis j))
                  y)
              t)))
      x
      =
    ν *
        (∑ k : Fin 3,
          spatial3.d
            a
            (spatial3.d
              b
              (spatial3.d
                c
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (spatial3.d
                    (h3AxisOfFin3 k)
                    (h3SpectralScalarRealC1RepresentativeOnPoint3
                      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                        hν U₀ hA hU₀ t
                        (h3ClassicalizationFinOfAxis j)))))))
            x)
      -
    spatial3.d
      a
      (spatial3.d
        b
        (spatial3.d
          c
          (fun y : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ t)
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ t)
              (h3ClassicalizationFinOfAxis j) y).re)))
      x

  exact
    spatial_d3_temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_eq_thirdMixedDerivativeCandidate
      hν U₀ hA hU₀ ht htR
      (h3ClassicalizationFinOfAxis j)
      x a b c

end

end Euclidean
end Bridge
end PrimeTensor
