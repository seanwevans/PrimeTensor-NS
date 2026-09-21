import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.Third.Coordinate.Time.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.Fifth.Coordinate.Continuity

/-!
# Positive-time third heat coordinate generator as a fifth spatial trace

The ordered third-coordinate heat reconstruction now has an ordinary time
derivative with a named generator.  This file identifies that generator with

    ν * Σ_k D⁵ H(t,x)[e_a,e_b,e_c,e_k,e_k].

The proof is algebraic/Fourier-linear.  The heat time generator is viscosity
times the raw Laplacian, the Laplacian is the sum of the three repeated
coordinate multipliers, and the resulting five canonical symbols are exactly
Mathlib's order-five Fourier multiplier.

No new estimate or derivative interchange is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzHeatTimeThirdCoordinateGeneratorTrace
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- On five canonical coordinate directions, Mathlib's generic order-five heat
multiplier is exactly the ordered product of the five project derivative
symbols. -/
theorem h3SpectralScalarHeatFifthCoordinateRawAmplitude_canonical_eq_symbols
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (a b c d e : Fin 3)
    (ξ : H3FourierPoint3) :
    h3SpectralScalarHeatFifthCoordinateRawAmplitude
        ν t G
        ![
          h3FourierAxisDirection (h3AxisOfFin3 a),
          h3FourierAxisDirection (h3AxisOfFin3 b),
          h3FourierAxisDirection (h3AxisOfFin3 c),
          h3FourierAxisDirection (h3AxisOfFin3 d),
          h3FourierAxisDirection (h3AxisOfFin3 e)
        ]
        ξ
      =
    h3FourierDerivativeSymbol a ξ *
      (h3FourierDerivativeSymbol b ξ *
        (h3FourierDerivativeSymbol c ξ *
          (h3FourierDerivativeSymbol d ξ *
            (h3FourierDerivativeSymbol e ξ *
              h3SpectralScalarHeatRawRepresentative ν t G ξ)))) := by
  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)
  let eb : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 b)
  let ec : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 c)
  let ed : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 d)
  let ee : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 e)

  have ha :
      h3FourierDerivativeSymbol a ξ
        =
      ((2 * Real.pi * inner ℝ ξ ea : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [ea]
    rw [h3FourierDerivativeSymbol_eq_inner]
    push_cast
    ring

  have hb :
      h3FourierDerivativeSymbol b ξ
        =
      ((2 * Real.pi * inner ℝ ξ eb : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [eb]
    rw [h3FourierDerivativeSymbol_eq_inner]
    push_cast
    ring

  have hc :
      h3FourierDerivativeSymbol c ξ
        =
      ((2 * Real.pi * inner ℝ ξ ec : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [ec]
    rw [h3FourierDerivativeSymbol_eq_inner]
    push_cast
    ring

  have hd :
      h3FourierDerivativeSymbol d ξ
        =
      ((2 * Real.pi * inner ℝ ξ ed : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [ed]
    rw [h3FourierDerivativeSymbol_eq_inner]
    push_cast
    ring

  have he :
      h3FourierDerivativeSymbol e ξ
        =
      ((2 * Real.pi * inner ℝ ξ ee : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [ee]
    rw [h3FourierDerivativeSymbol_eq_inner]
    push_cast
    ring

  unfold h3SpectralScalarHeatFifthCoordinateRawAmplitude

  simp only [
    VectorFourier.fourierPowSMulRight_apply,
    Fin.prod_univ_succ,
    Finset.univ_eq_empty,
    Finset.prod_empty,
    Matrix.cons_val_zero,
    Matrix.cons_val_one,
    Matrix.head_cons,
    Matrix.tail_cons,
    neg_apply,
    innerSL_apply_apply ℝ,
    smul_eq_mul
  ]

  rw [ha, hb, hc, hd, he]
  dsimp only [ea, eb, ec, ed, ee]
  simp [Complex.real_smul] <;> push_cast <;> ring

/-- Pointwise raw identity: the third-coordinate heat time generator is
viscosity times the fifth-coordinate heat trace. -/
theorem h3SpectralScalarHeatThirdCoordinateTimeGeneratorRawAmplitude_eq_viscosity_mul_fifthTrace
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (a b c : Fin 3)
    (ξ : H3FourierPoint3) :
    h3SpectralScalarHeatThirdCoordinateTimeGeneratorRawAmplitude
        ν t G a b c ξ
      =
    (ν : ℂ) *
      (∑ k : Fin 3,
        h3SpectralScalarHeatFifthCoordinateRawAmplitude
          ν t G
          ![
            h3FourierAxisDirection (h3AxisOfFin3 a),
            h3FourierAxisDirection (h3AxisOfFin3 b),
            h3FourierAxisDirection (h3AxisOfFin3 c),
            h3FourierAxisDirection (h3AxisOfFin3 k),
            h3FourierAxisDirection (h3AxisOfFin3 k)
          ]
          ξ) := by
  unfold h3SpectralScalarHeatThirdCoordinateTimeGeneratorRawAmplitude

  rw [
    h3SpectralScalarHeatTimeGeneratorRawRepresentative_eq_viscosity_mul_laplacian
      ν t G ξ
  ]

  unfold h3SpectralScalarHeatLaplacianRawAmplitude
  unfold h3SpectralScalarHeatSecondDiagonalRawAmplitude

  have hFifth
      (k : Fin 3) :
      h3SpectralScalarHeatFifthCoordinateRawAmplitude
          ν t G
          ![
            h3FourierAxisDirection (h3AxisOfFin3 a),
            h3FourierAxisDirection (h3AxisOfFin3 b),
            h3FourierAxisDirection (h3AxisOfFin3 c),
            h3FourierAxisDirection (h3AxisOfFin3 k),
            h3FourierAxisDirection (h3AxisOfFin3 k)
          ]
          ξ
        =
      h3FourierDerivativeSymbol a ξ *
        (h3FourierDerivativeSymbol b ξ *
          (h3FourierDerivativeSymbol c ξ *
            (h3FourierDerivativeSymbol k ξ *
              (h3FourierDerivativeSymbol k ξ *
                h3SpectralScalarHeatRawRepresentative ν t G ξ)))) :=
    h3SpectralScalarHeatFifthCoordinateRawAmplitude_canonical_eq_symbols
      ν t G a b c k k ξ

  calc
    h3FourierDerivativeSymbol a ξ *
        (h3FourierDerivativeSymbol b ξ *
          (h3FourierDerivativeSymbol c ξ *
            ((ν : ℂ) *
              (∑ k : Fin 3,
                h3FourierDerivativeSymbol k ξ *
                  (h3FourierDerivativeSymbol k ξ *
                    h3SpectralScalarHeatRawRepresentative ν t G ξ)))))
        =
      (ν : ℂ) *
        (h3FourierDerivativeSymbol a ξ *
          (h3FourierDerivativeSymbol b ξ *
            (h3FourierDerivativeSymbol c ξ *
              (∑ k : Fin 3,
                h3FourierDerivativeSymbol k ξ *
                  (h3FourierDerivativeSymbol k ξ *
                    h3SpectralScalarHeatRawRepresentative ν t G ξ))))) := by
      ring
    _ =
      (ν : ℂ) *
        (∑ k : Fin 3,
          h3FourierDerivativeSymbol a ξ *
            (h3FourierDerivativeSymbol b ξ *
              (h3FourierDerivativeSymbol c ξ *
                (h3FourierDerivativeSymbol k ξ *
                  (h3FourierDerivativeSymbol k ξ *
                    h3SpectralScalarHeatRawRepresentative ν t G ξ))))) := by
      congr 1
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    _ =
      (ν : ℂ) *
        (∑ k : Fin 3,
          h3SpectralScalarHeatFifthCoordinateRawAmplitude
            ν t G
            ![
              h3FourierAxisDirection (h3AxisOfFin3 a),
              h3FourierAxisDirection (h3AxisOfFin3 b),
              h3FourierAxisDirection (h3AxisOfFin3 c),
              h3FourierAxisDirection (h3AxisOfFin3 k),
              h3FourierAxisDirection (h3AxisOfFin3 k)
            ]
            ξ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      exact (hFifth k).symm

/-- The physical third-coordinate heat time generator is viscosity times the
genuine fifth spatial Fréchet trace. -/
theorem h3SpectralScalarHeatThirdCoordinateTimeGeneratorRepresentative_eq_viscosity_mul_fifthTrace
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (a b c : Fin 3)
    (x : H3FourierPoint3) :
    h3SpectralScalarHeatThirdCoordinateTimeGeneratorRepresentative
        ν t G a b c x
      =
    (ν : ℂ) *
      (∑ k : Fin 3,
        iteratedFDeriv ℝ 5
          (h3SpectralScalarHeatC3Representative ν t G)
          x
          ![
            h3FourierAxisDirection (h3AxisOfFin3 a),
            h3FourierAxisDirection (h3AxisOfFin3 b),
            h3FourierAxisDirection (h3AxisOfFin3 c),
            h3FourierAxisDirection (h3AxisOfFin3 k),
            h3FourierAxisDirection (h3AxisOfFin3 k)
          ]) := by
  let m0 : Fin 5 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection (h3AxisOfFin3 a),
      h3FourierAxisDirection (h3AxisOfFin3 b),
      h3FourierAxisDirection (h3AxisOfFin3 c),
      h3FourierAxisDirection (h3AxisOfFin3 (0 : Fin 3)),
      h3FourierAxisDirection (h3AxisOfFin3 (0 : Fin 3))
    ]

  let m1 : Fin 5 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection (h3AxisOfFin3 a),
      h3FourierAxisDirection (h3AxisOfFin3 b),
      h3FourierAxisDirection (h3AxisOfFin3 c),
      h3FourierAxisDirection (h3AxisOfFin3 (1 : Fin 3)),
      h3FourierAxisDirection (h3AxisOfFin3 (1 : Fin 3))
    ]

  let m2 : Fin 5 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection (h3AxisOfFin3 a),
      h3FourierAxisDirection (h3AxisOfFin3 b),
      h3FourierAxisDirection (h3AxisOfFin3 c),
      h3FourierAxisDirection (h3AxisOfFin3 (2 : Fin 3)),
      h3FourierAxisDirection (h3AxisOfFin3 (2 : Fin 3))
    ]

  let A0 : H3FourierPoint3 → ℂ :=
    h3SpectralScalarHeatFifthCoordinateRawAmplitude ν t G m0
  let A1 : H3FourierPoint3 → ℂ :=
    h3SpectralScalarHeatFifthCoordinateRawAmplitude ν t G m1
  let A2 : H3FourierPoint3 → ℂ :=
    h3SpectralScalarHeatFifthCoordinateRawAmplitude ν t G m2

  have hA0 : Integrable A0 (volume : Measure H3FourierPoint3) := by
    dsimp only [A0]
    exact h3SpectralScalarHeatFifthCoordinateRawAmplitude_integrable hν ht G m0

  have hA1 : Integrable A1 (volume : Measure H3FourierPoint3) := by
    dsimp only [A1]
    exact h3SpectralScalarHeatFifthCoordinateRawAmplitude_integrable hν ht G m1

  have hA2 : Integrable A2 (volume : Measure H3FourierPoint3) := by
    dsimp only [A2]
    exact h3SpectralScalarHeatFifthCoordinateRawAmplitude_integrable hν ht G m2

  have hRaw :
      h3SpectralScalarHeatThirdCoordinateTimeGeneratorRawAmplitude
          ν t G a b c
        =
      (ν : ℂ) • ((A0 + A1) + A2) := by
    funext ξ
    rw [
      h3SpectralScalarHeatThirdCoordinateTimeGeneratorRawAmplitude_eq_viscosity_mul_fifthTrace
        ν t G a b c ξ
    ]
    rw [Fin.sum_univ_three]
    dsimp only [A0, A1, A2, m0, m1, m2, Pi.smul_apply, Pi.add_apply]
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

  have hFifth0 :=
    h3SpectralScalarHeatFifthCoordinateRepresentative_eq_iteratedFDeriv
      hν ht G m0 x
  have hFifth1 :=
    h3SpectralScalarHeatFifthCoordinateRepresentative_eq_iteratedFDeriv
      hν ht G m1 x
  have hFifth2 :=
    h3SpectralScalarHeatFifthCoordinateRepresentative_eq_iteratedFDeriv
      hν ht G m2 x

  unfold h3SpectralScalarHeatThirdCoordinateTimeGeneratorRepresentative
  rw [hRaw, hInvSmul, hInv012, hInv01]
  dsimp only [A0, A1, A2]

  change
    (ν : ℂ) *
      (h3SpectralScalarHeatFifthCoordinateRepresentative ν t G m0 x
        +
       h3SpectralScalarHeatFifthCoordinateRepresentative ν t G m1 x
        +
       h3SpectralScalarHeatFifthCoordinateRepresentative ν t G m2 x)
      =
    (ν : ℂ) *
      (∑ k : Fin 3,
        iteratedFDeriv ℝ 5
          (h3SpectralScalarHeatC3Representative ν t G)
          x
          ![
            h3FourierAxisDirection (h3AxisOfFin3 a),
            h3FourierAxisDirection (h3AxisOfFin3 b),
            h3FourierAxisDirection (h3AxisOfFin3 c),
            h3FourierAxisDirection (h3AxisOfFin3 k),
            h3FourierAxisDirection (h3AxisOfFin3 k)
          ])

  rw [hFifth0, hFifth1, hFifth2]
  dsimp only [m0, m1, m2]
  rw [Fin.sum_univ_three]

/-- Direct form consumed by the selected order-three mixed-time closure: the
time derivative of one ordered third heat coordinate is viscosity times the
fifth spatial coordinate trace. -/
theorem h3SpectralScalarHeatThirdCoordinateRepresentative_hasDerivAt_time_eq_viscosity_fifthTrace
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (a b c : Fin 3)
    (x : H3FourierPoint3) :
    HasDerivAt
      (fun s : ℝ =>
        h3SpectralScalarHeatThirdCoordinateRepresentative
          ν s G a b c x)
      ((ν : ℂ) *
        (∑ k : Fin 3,
          iteratedFDeriv ℝ 5
            (h3SpectralScalarHeatC3Representative ν t G)
            x
            ![
              h3FourierAxisDirection (h3AxisOfFin3 a),
              h3FourierAxisDirection (h3AxisOfFin3 b),
              h3FourierAxisDirection (h3AxisOfFin3 c),
              h3FourierAxisDirection (h3AxisOfFin3 k),
              h3FourierAxisDirection (h3AxisOfFin3 k)
            ]))
      t := by
  have hTime :=
    h3SpectralScalarHeatThirdCoordinateRepresentative_hasDerivAt_time
      hν ht G a b c x

  have hGenerator :=
    h3SpectralScalarHeatThirdCoordinateTimeGeneratorRepresentative_eq_viscosity_mul_fifthTrace
      hν ht G a b c x

  exact hTime.congr_deriv hGenerator

end

end Euclidean
end Bridge
end PrimeTensor
