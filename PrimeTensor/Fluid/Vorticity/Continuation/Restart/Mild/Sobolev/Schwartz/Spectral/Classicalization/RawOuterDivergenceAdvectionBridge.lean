import PrimeTensor.Bridge.Euclidean.Advection.Divergence
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedPhysicalIncompressibility
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.Realizable

/-!
# Classicalization: unprojected raw outer divergence is physical advection

The previous reconstruction theorem identifies the real inverse Fourier
transform of the unprojected raw nonlinear term with a finite sum of spatial
derivatives of the canonical H³ product representatives.

`H3.Real.C1.Realizable` now upgrades those product representatives pointwise:
for a realizable spectral slice they are literally products of the canonical
real velocity representatives.

Consequently the complete reconstructed raw outer-product divergence is exactly
the Euclidean tensor divergence

    div(u ⊗ u).

The generic Euclidean bridge then gives

    div(u ⊗ u) = (u · ∇)u

whenever the same spectral slice is raw-divergence-free.

This is the exact nonlinear bridge needed before splitting the Leray projection
into advection plus the pressure-gradient complement.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3RawOuterDivergenceAdvectionBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- For a realizable spectral slice, the physical reconstruction of the
unprojected raw outer-product divergence is exactly the ordinary Euclidean
divergence of the reconstructed velocity outer product. -/
theorem h3RawFinOuterProductDivergence_fourierInv_re_eq_realOuterProductDivergenceComponent_of_realizable
    (W : ℝ → H3SpectralFinVectorState)
    (s : ℝ)
    (hReal : H3SpectralVelocityRealizable (W s))
    (i : Fin 3)
    (x : Point3) :
    (FourierTransformInv.fourierInv
      (h3RawFinOuterProductDivergence (W s) (W s) i)
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re
      =
    realOuterProductDivergenceComponent
      (h3SpectralRealVelocityOfPath W)
      s
      x
      (h3AxisOfFin3 i) := by
  have hProd0 :
      h3SpectralScalarRealC1RepresentativeOnPoint3
          (h3WeightedRawProductConvolutionL2
            ((W s) i) ((W s) 0))
        =
      fun y : Point3 =>
        (h3SpectralRealVelocityOfPath W s y).component
            (h3AxisOfFin3 i)
          *
        (h3SpectralRealVelocityOfPath W s y).component
            xAxis := by
    funext y
    rw [
      h3SpectralScalarRealC1RepresentativeOnPoint3_weightedRawProductConvolutionL2_eq_mul_of_realizable
        ((W s) i) ((W s) 0)
        (hReal i) (hReal 0) y
    ]
    change
      h3SpectralVelocityRealC1RepresentativeOnPoint3
          (W s) i y
        *
      h3SpectralVelocityRealC1RepresentativeOnPoint3
          (W s) 0 y
        =
      _
    rw [
      ← h3SpectralRealVelocityOfPath_component_h3AxisOfFin3
        W s y i,
      ← h3SpectralRealVelocityOfPath_component_h3AxisOfFin3
        W s y (0 : Fin 3),
      h3AxisOfFin3_zero
    ]

  have hProd1 :
      h3SpectralScalarRealC1RepresentativeOnPoint3
          (h3WeightedRawProductConvolutionL2
            ((W s) i) ((W s) 1))
        =
      fun y : Point3 =>
        (h3SpectralRealVelocityOfPath W s y).component
            (h3AxisOfFin3 i)
          *
        (h3SpectralRealVelocityOfPath W s y).component
            yAxis := by
    funext y
    rw [
      h3SpectralScalarRealC1RepresentativeOnPoint3_weightedRawProductConvolutionL2_eq_mul_of_realizable
        ((W s) i) ((W s) 1)
        (hReal i) (hReal 1) y
    ]
    change
      h3SpectralVelocityRealC1RepresentativeOnPoint3
          (W s) i y
        *
      h3SpectralVelocityRealC1RepresentativeOnPoint3
          (W s) 1 y
        =
      _
    rw [
      ← h3SpectralRealVelocityOfPath_component_h3AxisOfFin3
        W s y i,
      ← h3SpectralRealVelocityOfPath_component_h3AxisOfFin3
        W s y (1 : Fin 3),
      h3AxisOfFin3_one
    ]

  have hProd2 :
      h3SpectralScalarRealC1RepresentativeOnPoint3
          (h3WeightedRawProductConvolutionL2
            ((W s) i) ((W s) 2))
        =
      fun y : Point3 =>
        (h3SpectralRealVelocityOfPath W s y).component
            (h3AxisOfFin3 i)
          *
        (h3SpectralRealVelocityOfPath W s y).component
            zAxis := by
    funext y
    rw [
      h3SpectralScalarRealC1RepresentativeOnPoint3_weightedRawProductConvolutionL2_eq_mul_of_realizable
        ((W s) i) ((W s) 2)
        (hReal i) (hReal 2) y
    ]
    change
      h3SpectralVelocityRealC1RepresentativeOnPoint3
          (W s) i y
        *
      h3SpectralVelocityRealC1RepresentativeOnPoint3
          (W s) 2 y
        =
      _
    rw [
      ← h3SpectralRealVelocityOfPath_component_h3AxisOfFin3
        W s y i,
      ← h3SpectralRealVelocityOfPath_component_h3AxisOfFin3
        W s y (2 : Fin 3),
      h3AxisOfFin3_two
    ]

  rw [
    h3RawFinOuterProductDivergence_fourierInv_re_eq_sum_productRepresentative_spatialDerivatives
  ]

  unfold realOuterProductDivergenceComponent
  rw [axis_fold_three]

  simp only [
    Fin.sum_univ_three,
    h3AxisOfFin3_zero,
    h3AxisOfFin3_one,
    h3AxisOfFin3_two
  ]

  rw [hProd0, hProd1, hProd2]
  simpa only [add_assoc]

/-- A realizable and raw-divergence-free spectral slice reconstructs the
unprojected raw nonlinear Fourier term exactly as the `RealFluid.advection`
component of its canonical real velocity. -/
theorem h3RawFinOuterProductDivergence_fourierInv_re_eq_advection_of_realizable_of_rawDivergenceFree
    (W : ℝ → H3SpectralFinVectorState)
    (s : ℝ)
    (hReal : H3SpectralVelocityRealizable (W s))
    (hDiv : H3SpectralFinRawDivergenceFree (W s))
    (i : Fin 3)
    (x : Point3) :
    (FourierTransformInv.fourierInv
      (h3RawFinOuterProductDivergence (W s) (W s) i)
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re
      =
    (PrimeTensor.Bridge.RealFluid.advection
      spatial3
      (h3SpectralRealVelocityOfPath W)
      s x).component
        (h3AxisOfFin3 i) := by
  have hC1 :
      ∀ a : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun y : Point3 =>
            (h3SpectralRealVelocityOfPath W s y).component a) := by
    intro a
    change
      SpatialC1
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          ((W s) (h3ClassicalizationFinOfAxis a)))
    exact
      h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_one
        ((W s) (h3ClassicalizationFinOfAxis a))

  calc
    (FourierTransformInv.fourierInv
      (h3RawFinOuterProductDivergence (W s) (W s) i)
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re
        =
      realOuterProductDivergenceComponent
        (h3SpectralRealVelocityOfPath W)
        s x
        (h3AxisOfFin3 i) :=
      h3RawFinOuterProductDivergence_fourierInv_re_eq_realOuterProductDivergenceComponent_of_realizable
        W s hReal i x
    _ =
      (PrimeTensor.Bridge.RealFluid.advection
        spatial3
        (h3SpectralRealVelocityOfPath W)
        s x).component
          (h3AxisOfFin3 i) := by
      exact
        realOuterProductDivergenceComponent_eq_advection_of_divergence_eq_zero
          (h3SpectralRealVelocityOfPath W)
          s x
          (h3AxisOfFin3 i)
          hC1
          (h3SpectralRealVelocityOfPath_divergence_eq_zero_of_rawDivergenceFree
            W s hDiv x)

end

end Euclidean
end Bridge
end PrimeTensor
