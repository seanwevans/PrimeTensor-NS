import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityRealHessianTraceBridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.CubicThirdPartialDifferenceContinuity

/-!
# Classicalization: selected real temporal PDE in concrete spatial derivatives

The preceding bridge rewrites the selected temporal derivative entirely on the
ordinary `Point3` carrier, but the linear term is still expressed as a trace of
second Fréchet derivatives.

The Euclidean partials layer already proves that, for a spatially `C²` scalar
field,

    ∂ᵢ ∂ⱼ f
      =
    D²f[eᵢ,eⱼ].

At every strict positive interior restart time the selected real representative
is spatially `C²`, so each repeated-direction second Fréchet derivative can be
replaced by the concrete nested coordinate derivative.

This gives the exact real PDE

    ∂ₜ uᵢ
      =
    ν * Σⱼ ∂ⱼ∂ⱼ uᵢ
      - Re Nᵢ(u,u)

in the same `spatial3.d` language used by the mixed-regularity candidate.

No new estimate, derivative commutation, or regularity hypothesis is added.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityRealSpatialPDEForm
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Repeated-direction order-two Fréchet evaluation agrees with the concrete
repeated coordinate partial. -/
theorem SpatialC2.spatial_d_square_eq_iteratedFDeriv_two_const
    {f : ScalarField3}
    (hf : SpatialC2 f)
    (x : Point3)
    (a : PrimeTensor.Axis Depth.three) :
    spatial3.d a
        (spatial3.d a f)
        x
      =
    iteratedFDeriv ℝ 2 f x
      (fun _ : Fin 2 => axisDirection a) := by
  have hDirections :
      (![axisDirection a, axisDirection a] :
          Fin 2 → Point3)
        =
      (fun _ : Fin 2 => axisDirection a) := by
    funext k
    fin_cases k <;> rfl

  change
    partialDeriv a
        (fun y : Point3 =>
          partialDeriv a f y)
        x
      =
    iteratedFDeriv ℝ 2 f x
      (fun _ : Fin 2 => axisDirection a)

  simpa only [hDirections] using
    (hf.secondPartial_eq_iteratedFDeriv_two_axes
      x a a)

/-- Scalar-coordinate form of the selected real temporal PDE, now entirely in
the project's concrete nested spatial derivatives. -/
theorem temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_eq_spatialLaplacian_sub_forcing
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    temporal.d
      (fun s : ℝ =>
        h3SpectralScalarRealC1RepresentativeOnPoint3
          (W s i) x)
      t
      =
    ν *
        (∑ j : Fin 3,
          spatial3.d
            (h3AxisOfFin3 j)
            (spatial3.d
              (h3AxisOfFin3 j)
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (W t i)))
            x)
      -
    (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
      (W t) (W t) i x).re := by
  dsimp only

  let f : ScalarField3 :=
    h3SpectralScalarRealC1RepresentativeOnPoint3
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ t i)

  have hfC2 : SpatialC2 f := by
    unfold SpatialC2
    dsimp only [f]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_contDiff_nat
        2 hν U₀ hA hU₀ ht htR.le i

  rw [
    temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_eq_realPoint3SecondFrechetTrace_sub_forcing
      hν U₀ hA hU₀ ht htR i x
  ]

  congr 2

  apply Finset.sum_congr rfl
  intro j _hj

  symm
  exact
    hfC2.spatial_d_square_eq_iteratedFDeriv_two_const
      x (h3AxisOfFin3 j)

/-- Velocity-component form of the same concrete real spatial PDE. -/
theorem temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_eq_spatialLaplacian_sub_forcing
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    temporal.d
      (fun s : ℝ =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν U₀ hA hU₀ s x).component j)
      t
      =
    ν *
        (∑ k : Fin 3,
          spatial3.d
            (h3AxisOfFin3 k)
            (spatial3.d
              (h3AxisOfFin3 k)
              (fun y : Point3 =>
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                  hν U₀ hA hU₀ t y).component j))
            x)
      -
    (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
      (W t) (W t)
      (h3ClassicalizationFinOfAxis j) x).re := by
  dsimp only

  change
    temporal.d
      (fun s : ℝ =>
        h3SpectralScalarRealC1RepresentativeOnPoint3
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ s
            (h3ClassicalizationFinOfAxis j))
          x)
      t
      =
    ν *
        (∑ k : Fin 3,
          spatial3.d
            (h3AxisOfFin3 k)
            (spatial3.d
              (h3AxisOfFin3 k)
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  hν U₀ hA hU₀ t
                  (h3ClassicalizationFinOfAxis j))))
            x)
      -
    (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ t)
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ t)
      (h3ClassicalizationFinOfAxis j) x).re

  exact
    temporal_d_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_eq_spatialLaplacian_sub_forcing
      hν U₀ hA hU₀ ht htR
      (h3ClassicalizationFinOfAxis j)
      x

end

end Euclidean
end Bridge
end PrimeTensor
