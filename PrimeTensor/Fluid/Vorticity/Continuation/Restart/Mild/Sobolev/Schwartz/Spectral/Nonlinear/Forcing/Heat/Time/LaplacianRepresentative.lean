import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.Time.Laplacian
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.FixedLagHessian

/-!
# Physical nonlinear heat time generator as Hessian trace

`Heat.Time.Laplacian` identified the raw Fourier time-generator multiplier with
viscosity times the diagonal second-coordinate multiplier.

This file lifts that algebraic identity through inverse Fourier reconstruction.

At positive heat lag,

    timeGenerator(x)
      = ν * Σⱼ ∂ⱼ∂ⱼ heatForcing(x)
      = ν * trace(Hessian(x)).

The first equality uses only linearity of the Fourier integral.  The second
uses the already-constructed fixed-lag Hessian, whose canonical-axis entries
are exactly the mixed second-coordinate inverse-Fourier representatives.

This is intentionally still a fixed-lag theorem.  The next source-time layer
can combine it with the selected Hessian endpoint integrability already proved
in `SelectedSecondFrechetTimeIntegrability`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped ENNReal NNReal Topology RealInnerProductSpace BigOperators

noncomputable section

noncomputable local instance axisFintypeH3NonlinearHeatTimeLaplacianRepresentative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Physical inverse-Fourier representative of the diagonal second-coordinate
sum. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatLaplacianRepresentative
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3RawFinLerayOuterProductDivergenceHeatLaplacianRawAmplitude
      ν τ U V i)

/-- Inverse Fourier reconstruction commutes with the viscosity scalar in the
raw time-generator/Laplacian identity. -/
theorem h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRepresentative_eq_viscosity_smul_laplacianRepresentative
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRepresentative
        ν τ U V i
      =
    (ν : ℂ) •
      h3RawFinLerayOuterProductDivergenceHeatLaplacianRepresentative
        ν τ U V i := by
  have hRaw :
      h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative
          ν τ U V i
        =
      (ν : ℂ) •
        h3RawFinLerayOuterProductDivergenceHeatLaplacianRawAmplitude
          ν τ U V i := by
    funext ξ
    simp only [Pi.smul_apply, smul_eq_mul]
    exact
      h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative_eq_viscosity_mul_laplacian
        ν τ U V i ξ

  unfold
    h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRepresentative
    h3RawFinLerayOuterProductDivergenceHeatLaplacianRepresentative

  rw [hRaw]

  change
    VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        ((ν : ℂ) •
          h3RawFinLerayOuterProductDivergenceHeatLaplacianRawAmplitude
            ν τ U V i)
      =
    (ν : ℂ) •
      VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        (h3RawFinLerayOuterProductDivergenceHeatLaplacianRawAmplitude
          ν τ U V i)

  exact
    VectorFourier.fourierIntegral_const_smul
      Real.fourierChar
      (volume : Measure H3FourierPoint3)
      (-(innerₗ H3FourierPoint3))
      (h3RawFinLerayOuterProductDivergenceHeatLaplacianRawAmplitude
        ν τ U V i)
      (ν : ℂ)

/-- At positive heat lag, the physical Laplacian representative is the sum of
the three diagonal mixed-second-coordinate representatives. -/
theorem h3RawFinLerayOuterProductDivergenceHeatLaplacianRepresentative_eq_sum_secondCoordinate
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    h3RawFinLerayOuterProductDivergenceHeatLaplacianRepresentative
        ν τ U V i
      =
    fun x =>
      ∑ j : Fin 3,
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
          ν τ U V i j j x := by
  let A0 : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
      ν τ U V i (0 : Fin 3) (0 : Fin 3)

  let A1 : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
      ν τ U V i (1 : Fin 3) (1 : Fin 3)

  let A2 : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
      ν τ U V i (2 : Fin 3) (2 : Fin 3)

  have hA0 :
      Integrable A0 (volume : Measure H3FourierPoint3) := by
    dsimp only [A0]
    exact
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude_integrable
        hν hτ U V i (0 : Fin 3) (0 : Fin 3)

  have hA1 :
      Integrable A1 (volume : Measure H3FourierPoint3) := by
    dsimp only [A1]
    exact
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude_integrable
        hν hτ U V i (1 : Fin 3) (1 : Fin 3)

  have hA2 :
      Integrable A2 (volume : Measure H3FourierPoint3) := by
    dsimp only [A2]
    exact
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude_integrable
        hν hτ U V i (2 : Fin 3) (2 : Fin 3)

  have hInnerNegContinuous :
      Continuous
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          ((-(innerₗ H3FourierPoint3)) p.1) p.2) := by
    change
      Continuous
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          -inner ℝ p.1 p.2)
    exact
      (continuous_inner
        (𝕜 := ℝ)
        (E := H3FourierPoint3)).neg

  have hInv01 :
      FourierTransformInv.fourierInv (A0 + A1)
        =
      FourierTransformInv.fourierInv A0
        +
      FourierTransformInv.fourierInv A1 := by
    change
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (A0 + A1)
        =
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          A0
        +
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          A1

    exact
      VectorFourier.fourierIntegral_add
        (e := Real.fourierChar)
        (μ := (volume : Measure H3FourierPoint3))
        (L := -(innerₗ H3FourierPoint3))
        Real.continuous_fourierChar
        hInnerNegContinuous
        hA0
        hA1

  have hInv012 :
      FourierTransformInv.fourierInv ((A0 + A1) + A2)
        =
      FourierTransformInv.fourierInv (A0 + A1)
        +
      FourierTransformInv.fourierInv A2 := by
    change
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          ((A0 + A1) + A2)
        =
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (A0 + A1)
        +
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          A2

    exact
      VectorFourier.fourierIntegral_add
        (e := Real.fourierChar)
        (μ := (volume : Measure H3FourierPoint3))
        (L := -(innerₗ H3FourierPoint3))
        Real.continuous_fourierChar
        hInnerNegContinuous
        (hA0.add hA1)
        hA2

  have hRaw :
      h3RawFinLerayOuterProductDivergenceHeatLaplacianRawAmplitude
          ν τ U V i
        =
      (A0 + A1) + A2 := by
    funext ξ
    unfold
      h3RawFinLerayOuterProductDivergenceHeatLaplacianRawAmplitude
    rw [Fin.sum_univ_three]
    rfl

  unfold
    h3RawFinLerayOuterProductDivergenceHeatLaplacianRepresentative

  rw [hRaw, hInv012, hInv01]

  funext x
  simp only [Pi.add_apply, Fin.sum_univ_three]

  rfl

/-- The physical Laplacian representative is exactly the trace of the
fixed-lag Hessian on the three canonical Euclidean coordinate directions. -/
theorem h3RawFinLerayOuterProductDivergenceHeatLaplacianRepresentative_eq_hessianTrace
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatLaplacianRepresentative
        ν τ U V i x
      =
    ∑ j : Fin 3,
      h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRepresentative
          ν τ U V i x
          (h3FourierAxisDirection (h3AxisOfFin3 j))
          (h3FourierAxisDirection (h3AxisOfFin3 j)) := by
  have hSum :=
    congrFun
      (h3RawFinLerayOuterProductDivergenceHeatLaplacianRepresentative_eq_sum_secondCoordinate
        hν hτ U V i)
      x

  rw [hSum]

  apply Finset.sum_congr rfl
  intro j hj

  unfold
    h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRepresentative

  rw [h3AssembleSecondCoordinateDerivative_axis_axis]

/-- Final fixed-lag form: the physical nonlinear heat time generator is
viscosity times the trace of the genuine spatial Hessian. -/
theorem h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRepresentative_eq_viscosity_mul_hessianTrace
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRepresentative
        ν τ U V i x
      =
    (ν : ℂ) *
      (∑ j : Fin 3,
        h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRepresentative
            ν τ U V i x
            (h3FourierAxisDirection (h3AxisOfFin3 j))
            (h3FourierAxisDirection (h3AxisOfFin3 j))) := by
  have hGenerator :=
    congrFun
      (h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRepresentative_eq_viscosity_smul_laplacianRepresentative
        ν τ U V i)
      x

  simp only [Pi.smul_apply, smul_eq_mul] at hGenerator

  calc
    h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRepresentative
        ν τ U V i x
        =
      (ν : ℂ) *
        h3RawFinLerayOuterProductDivergenceHeatLaplacianRepresentative
          ν τ U V i x :=
      hGenerator
    _ =
      (ν : ℂ) *
        (∑ j : Fin 3,
          h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRepresentative
              ν τ U V i x
              (h3FourierAxisDirection (h3AxisOfFin3 j))
              (h3FourierAxisDirection (h3AxisOfFin3 j))) := by
      rw [
        h3RawFinLerayOuterProductDivergenceHeatLaplacianRepresentative_eq_hessianTrace
          hν hτ U V i x
      ]

end

end Euclidean
end Bridge
end PrimeTensor
