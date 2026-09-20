import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.Second.Coordinate.Time.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.Fourth.Coordinate.Representative

/-!
# Positive-time mixed heat Hessian generator as a fourth spatial trace

The mixed second-coordinate heat reconstruction now has an ordinary time
derivative with a named generator.  This file identifies that generator
exactly with the heat equation prediction

    ν * Σ_k D⁴ H(t,x)[e_a,e_b,e_k,e_k].

The proof is purely algebraic/Fourier-linear:

* the scalar heat generator is viscosity times the raw Laplacian;
* multiplying by the two fixed coordinate symbols distributes through that
  three-term trace;
* inverse Fourier reconstruction is linear;
* each resulting fourth-coordinate reconstruction is the genuine fourth
  Fréchet evaluation already exposed in the preceding layer.

No new estimate, limit, or derivative interchange is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzHeatTimeSecondCoordinateGeneratorTrace
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Pointwise raw identity: the time generator of an ordered mixed Hessian
coordinate is viscosity times the ordered fourth-coordinate spatial trace. -/
theorem h3SpectralScalarHeatSecondCoordinateTimeGeneratorRawAmplitude_eq_viscosity_mul_fourthTrace
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (a b : Fin 3)
    (ξ : H3FourierPoint3) :
    h3SpectralScalarHeatSecondCoordinateTimeGeneratorRawAmplitude
        ν t G a b ξ
      =
    (ν : ℂ) *
      (∑ k : Fin 3,
        h3SpectralScalarHeatFourthCoordinateRawAmplitude
          ν t G a b k k ξ) := by
  unfold h3SpectralScalarHeatSecondCoordinateTimeGeneratorRawAmplitude

  rw [
    h3SpectralScalarHeatTimeGeneratorRawRepresentative_eq_viscosity_mul_laplacian
      ν t G ξ
  ]

  unfold h3SpectralScalarHeatLaplacianRawAmplitude

  calc
    h3FourierDerivativeSymbol a ξ *
        (h3FourierDerivativeSymbol b ξ *
          ((ν : ℂ) *
            (∑ k : Fin 3,
              h3SpectralScalarHeatSecondDiagonalRawAmplitude
                ν t G k ξ)))
        =
      (ν : ℂ) *
        (h3FourierDerivativeSymbol a ξ *
          (h3FourierDerivativeSymbol b ξ *
            (∑ k : Fin 3,
              h3SpectralScalarHeatSecondDiagonalRawAmplitude
                ν t G k ξ))) := by
      ring
    _ =
      (ν : ℂ) *
        (∑ k : Fin 3,
          h3FourierDerivativeSymbol a ξ *
            (h3FourierDerivativeSymbol b ξ *
              h3SpectralScalarHeatSecondDiagonalRawAmplitude
                ν t G k ξ)) := by
      congr 1
      rw [Finset.mul_sum, Finset.mul_sum]
    _ =
      (ν : ℂ) *
        (∑ k : Fin 3,
          h3SpectralScalarHeatFourthCoordinateRawAmplitude
            ν t G a b k k ξ) := by
      congr 1

/-- The physical mixed-Hessian heat time generator is viscosity times the
genuine fourth spatial Fréchet trace. -/
theorem h3SpectralScalarHeatSecondCoordinateTimeGeneratorRepresentative_eq_viscosity_mul_fourthTrace
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (a b : Fin 3)
    (x : H3FourierPoint3) :
    h3SpectralScalarHeatSecondCoordinateTimeGeneratorRepresentative
        ν t G a b x
      =
    (ν : ℂ) *
      (∑ k : Fin 3,
        iteratedFDeriv ℝ 4
          (h3SpectralScalarHeatC3Representative ν t G)
          x
          ![
            h3FourierAxisDirection (h3AxisOfFin3 a),
            h3FourierAxisDirection (h3AxisOfFin3 b),
            h3FourierAxisDirection (h3AxisOfFin3 k),
            h3FourierAxisDirection (h3AxisOfFin3 k)
          ]) := by
  let A0 : H3FourierPoint3 → ℂ :=
    h3SpectralScalarHeatFourthCoordinateRawAmplitude
      ν t G a b (0 : Fin 3) (0 : Fin 3)

  let A1 : H3FourierPoint3 → ℂ :=
    h3SpectralScalarHeatFourthCoordinateRawAmplitude
      ν t G a b (1 : Fin 3) (1 : Fin 3)

  let A2 : H3FourierPoint3 → ℂ :=
    h3SpectralScalarHeatFourthCoordinateRawAmplitude
      ν t G a b (2 : Fin 3) (2 : Fin 3)

  have hA0 :
      Integrable A0
        (volume : Measure H3FourierPoint3) := by
    dsimp only [A0]
    exact
      h3SpectralScalarHeatFourthCoordinateRawAmplitude_integrable
        hν ht G a b (0 : Fin 3) (0 : Fin 3)

  have hA1 :
      Integrable A1
        (volume : Measure H3FourierPoint3) := by
    dsimp only [A1]
    exact
      h3SpectralScalarHeatFourthCoordinateRawAmplitude_integrable
        hν ht G a b (1 : Fin 3) (1 : Fin 3)

  have hA2 :
      Integrable A2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [A2]
    exact
      h3SpectralScalarHeatFourthCoordinateRawAmplitude_integrable
        hν ht G a b (2 : Fin 3) (2 : Fin 3)

  have hRaw :
      h3SpectralScalarHeatSecondCoordinateTimeGeneratorRawAmplitude
          ν t G a b
        =
      (ν : ℂ) • ((A0 + A1) + A2) := by
    funext ξ
    rw [
      h3SpectralScalarHeatSecondCoordinateTimeGeneratorRawAmplitude_eq_viscosity_mul_fourthTrace
        ν t G a b ξ
    ]
    rw [Fin.sum_univ_three]
    dsimp only [A0, A1, A2, Pi.smul_apply, Pi.add_apply]
    simp only [smul_eq_mul]

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
      FourierTransformInv.fourierInv (A0 + A1) x
        =
      FourierTransformInv.fourierInv A0 x
        +
      FourierTransformInv.fourierInv A1 x := by
    change
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (A0 + A1)
          x
        =
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          A0
          x
        +
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          A1
          x

    exact
      congrFun
        (VectorFourier.fourierIntegral_add
          (e := Real.fourierChar)
          (μ := (volume : Measure H3FourierPoint3))
          (L := -(innerₗ H3FourierPoint3))
          Real.continuous_fourierChar
          hInnerNegContinuous
          hA0
          hA1)
        x

  have hInv012 :
      FourierTransformInv.fourierInv ((A0 + A1) + A2) x
        =
      FourierTransformInv.fourierInv (A0 + A1) x
        +
      FourierTransformInv.fourierInv A2 x := by
    change
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          ((A0 + A1) + A2)
          x
        =
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (A0 + A1)
          x
        +
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          A2
          x

    exact
      congrFun
        (VectorFourier.fourierIntegral_add
          (e := Real.fourierChar)
          (μ := (volume : Measure H3FourierPoint3))
          (L := -(innerₗ H3FourierPoint3))
          Real.continuous_fourierChar
          hInnerNegContinuous
          (hA0.add hA1)
          hA2)
        x

  have hInvSmul :
      FourierTransformInv.fourierInv
          ((ν : ℂ) • ((A0 + A1) + A2))
          x
        =
      (ν : ℂ) *
        FourierTransformInv.fourierInv
          ((A0 + A1) + A2)
          x := by
    change
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          ((ν : ℂ) • ((A0 + A1) + A2))
          x
        =
      (ν : ℂ) *
        VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          ((A0 + A1) + A2)
          x

    simpa only [Pi.smul_apply, smul_eq_mul] using
      congrFun
        (VectorFourier.fourierIntegral_const_smul
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          ((A0 + A1) + A2)
          (ν : ℂ))
        x

  have hFourth0 :=
    h3SpectralScalarHeatFourthCoordinateRepresentative_eq_iteratedFDeriv
      hν ht G a b (0 : Fin 3) (0 : Fin 3) x

  have hFourth1 :=
    h3SpectralScalarHeatFourthCoordinateRepresentative_eq_iteratedFDeriv
      hν ht G a b (1 : Fin 3) (1 : Fin 3) x

  have hFourth2 :=
    h3SpectralScalarHeatFourthCoordinateRepresentative_eq_iteratedFDeriv
      hν ht G a b (2 : Fin 3) (2 : Fin 3) x

  unfold h3SpectralScalarHeatSecondCoordinateTimeGeneratorRepresentative
  rw [hRaw, hInvSmul, hInv012, hInv01]
  dsimp only [A0, A1, A2]

  change
    (ν : ℂ) *
      (h3SpectralScalarHeatFourthCoordinateRepresentative
          ν t G a b (0 : Fin 3) (0 : Fin 3) x
        +
       h3SpectralScalarHeatFourthCoordinateRepresentative
          ν t G a b (1 : Fin 3) (1 : Fin 3) x
        +
       h3SpectralScalarHeatFourthCoordinateRepresentative
          ν t G a b (2 : Fin 3) (2 : Fin 3) x)
      =
    (ν : ℂ) *
      (∑ k : Fin 3,
        iteratedFDeriv ℝ 4
          (h3SpectralScalarHeatC3Representative ν t G)
          x
          ![
            h3FourierAxisDirection (h3AxisOfFin3 a),
            h3FourierAxisDirection (h3AxisOfFin3 b),
            h3FourierAxisDirection (h3AxisOfFin3 k),
            h3FourierAxisDirection (h3AxisOfFin3 k)
          ])

  rw [hFourth0, hFourth1, hFourth2]
  rw [Fin.sum_univ_three]

/-- Direct form consumed by the selected order-two mixed-time closure: the
time derivative of one ordered mixed heat Hessian coordinate is viscosity
times the fourth spatial coordinate trace. -/
theorem h3SpectralScalarHeatSecondCoordinateRepresentative_hasDerivAt_time_eq_viscosity_fourthTrace
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (a b : Fin 3)
    (x : H3FourierPoint3) :
    HasDerivAt
      (fun s : ℝ =>
        h3SpectralScalarHeatSecondCoordinateRepresentative
          ν s G a b x)
      ((ν : ℂ) *
        (∑ k : Fin 3,
          iteratedFDeriv ℝ 4
            (h3SpectralScalarHeatC3Representative ν t G)
            x
            ![
              h3FourierAxisDirection (h3AxisOfFin3 a),
              h3FourierAxisDirection (h3AxisOfFin3 b),
              h3FourierAxisDirection (h3AxisOfFin3 k),
              h3FourierAxisDirection (h3AxisOfFin3 k)
            ]))
      t := by
  have hTime :=
    h3SpectralScalarHeatSecondCoordinateRepresentative_hasDerivAt_time
      hν ht G a b x

  have hGenerator :=
    h3SpectralScalarHeatSecondCoordinateTimeGeneratorRepresentative_eq_viscosity_mul_fourthTrace
      hν ht G a b x

  exact
    hTime.congr_deriv hGenerator

end

end Euclidean
end Bridge
end PrimeTensor
