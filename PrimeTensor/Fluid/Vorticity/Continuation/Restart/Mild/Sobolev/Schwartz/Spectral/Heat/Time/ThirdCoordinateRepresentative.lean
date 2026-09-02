import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.HessianTraceRepresentative

/-!
# Positive-time scalar heat third coordinate derivatives

The mixed-regularity closure now needs time continuity of the third spatial
Fréchet jet of the positive-time heat reconstruction.  Before proving that
temporal statement, this file isolates the exact spatial Fourier
representation consumed by dominated convergence.

For three canonical coordinate directions `j,k,l`, define the raw amplitude

    D_j(ξ) D_k(ξ) D_l(ξ) heatRaw(ν,t,G,ξ).

Three derivative symbols cost at most

    (2π)^3 |ξ|^3,

so the existing positive-time third-moment smoothing theorem makes this
amplitude integrable.

Mathlib's explicit iterated Fourier derivative formula then identifies its
inverse-Fourier reconstruction exactly with the evaluated third Fréchet
derivative

    D³ heat(t,x)[e_j,e_k,e_l].

No temporal estimate is introduced here.  The next layer can keep the spatial
multiplier fixed and prove continuity in `t` by dominated convergence on a
positive-time neighborhood.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzHeatTimeThirdCoordinateRepresentative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Raw Fourier amplitude for an ordered third coordinate derivative of the
positive-time scalar heat reconstruction. -/
noncomputable def h3SpectralScalarHeatThirdCoordinateRawAmplitude
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (j k l : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  h3FourierDerivativeSymbol j ξ *
    (h3FourierDerivativeSymbol k ξ *
      (h3FourierDerivativeSymbol l ξ *
        h3SpectralScalarHeatRawRepresentative ν t G ξ))

/-- The project's three coordinate derivative symbols are exactly Mathlib's
order-three inverse-Fourier multiplier on the three canonical coordinate
directions. -/
theorem h3SpectralScalarHeatThirdCoordinateRawAmplitude_eq_fourierPowSMulRight
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (j k l : Fin 3)
    (ξ : H3FourierPoint3) :
    let L :
        H3FourierPoint3 →L[ℝ]
          H3FourierPoint3 →L[ℝ] ℝ :=
      -(innerSL ℝ)
    let m : Fin 3 → H3FourierPoint3 :=
      ![
        h3FourierAxisDirection (h3AxisOfFin3 j),
        h3FourierAxisDirection (h3AxisOfFin3 k),
        h3FourierAxisDirection (h3AxisOfFin3 l)
      ]
    VectorFourier.fourierPowSMulRight
        L
        (h3SpectralScalarHeatRawRepresentative ν t G)
        ξ
        3
        m
      =
    h3SpectralScalarHeatThirdCoordinateRawAmplitude
      ν t G j k l ξ := by
  dsimp only

  let ej : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 j)
  let ek : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 k)
  let el : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 l)

  have hj :
      h3FourierDerivativeSymbol j ξ
        =
      ((2 * Real.pi * inner ℝ ξ ej : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [ej]
    rw [h3FourierDerivativeSymbol_eq_inner]
    push_cast
    ring

  have hk :
      h3FourierDerivativeSymbol k ξ
        =
      ((2 * Real.pi * inner ℝ ξ ek : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [ek]
    rw [h3FourierDerivativeSymbol_eq_inner]
    push_cast
    ring

  have hl :
      h3FourierDerivativeSymbol l ξ
        =
      ((2 * Real.pi * inner ℝ ξ el : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [el]
    rw [h3FourierDerivativeSymbol_eq_inner]
    push_cast
    ring

  simp only [
    VectorFourier.fourierPowSMulRight_apply,
    Fin.prod_univ_three,
    neg_apply,
    innerSL_apply_apply ℝ,
    smul_eq_mul
  ]

  unfold h3SpectralScalarHeatThirdCoordinateRawAmplitude
  rw [hj, hk, hl]
  dsimp only [ej, ek, el]
  simp [Complex.real_smul] <;> push_cast <;> ring

/-- Three canonical coordinate derivative symbols cost at most the radial
third heat moment. -/
theorem norm_h3SpectralScalarHeatThirdCoordinateRawAmplitude_le_thirdMoment
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (j k l : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3SpectralScalarHeatThirdCoordinateRawAmplitude
        ν t G j k l ξ‖
      ≤
    (2 * Real.pi) ^ 3 *
      (‖ξ‖ ^ 3 *
        ‖h3SpectralScalarHeatRawRepresentative
          ν t G ξ‖) := by
  unfold h3SpectralScalarHeatThirdCoordinateRawAmplitude
  rw [norm_mul, norm_mul, norm_mul]

  have hj :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ
  have hk :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude k ξ
  have hl :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude l ξ

  have hH :
      0 ≤
        ‖h3SpectralScalarHeatRawRepresentative
          ν t G ξ‖ :=
    norm_nonneg _

  calc
    ‖h3FourierDerivativeSymbol j ξ‖ *
        (‖h3FourierDerivativeSymbol k ξ‖ *
          (‖h3FourierDerivativeSymbol l ξ‖ *
            ‖h3SpectralScalarHeatRawRepresentative
              ν t G ξ‖))
        ≤
      h3FourierGradientMagnitude ξ *
        (‖h3FourierDerivativeSymbol k ξ‖ *
          (‖h3FourierDerivativeSymbol l ξ‖ *
            ‖h3SpectralScalarHeatRawRepresentative
              ν t G ξ‖)) := by
        exact
          mul_le_mul_of_nonneg_right
            hj
            (mul_nonneg
              (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) hH))
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          (‖h3FourierDerivativeSymbol l ξ‖ *
            ‖h3SpectralScalarHeatRawRepresentative
              ν t G ξ‖)) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              hk
              (mul_nonneg (norm_nonneg _) hH))
            (by
              unfold h3FourierGradientMagnitude
              positivity)
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            ‖h3SpectralScalarHeatRawRepresentative
              ν t G ξ‖)) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hl hH)
              (by
                unfold h3FourierGradientMagnitude
                positivity))
            (by
              unfold h3FourierGradientMagnitude
              positivity)
    _ =
      (2 * Real.pi) ^ 3 *
        (‖ξ‖ ^ 3 *
          ‖h3SpectralScalarHeatRawRepresentative
            ν t G ξ‖) := by
        unfold h3FourierGradientMagnitude
        ring

/-- Every ordered third-coordinate raw heat amplitude is integrable at
positive heat time. -/
theorem h3SpectralScalarHeatThirdCoordinateRawAmplitude_integrable
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (j k l : Fin 3) :
    Integrable
      (h3SpectralScalarHeatThirdCoordinateRawAmplitude
        ν t G j k l)
      (volume : Measure H3FourierPoint3) := by
  have hTargetMeas :
      AEStronglyMeasurable
        (h3SpectralScalarHeatThirdCoordinateRawAmplitude
          ν t G j k l)
        (volume : Measure H3FourierPoint3) := by
    unfold h3SpectralScalarHeatThirdCoordinateRawAmplitude
    exact
      (h3FourierDerivativeSymbol_continuous j).aestronglyMeasurable.mul
        ((h3FourierDerivativeSymbol_continuous k).aestronglyMeasurable.mul
          ((h3FourierDerivativeSymbol_continuous l).aestronglyMeasurable.mul
            (h3SpectralScalarHeatRawRepresentative_aestronglyMeasurable
              ν t G)))

  have hMomentInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarHeatRawRepresentative
              ν t G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3SpectralScalarHeatRawRepresentative_moment_integrable
      hν ht G 3 (by norm_num)

  have hMajorantInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) ^ 3 *
            (‖ξ‖ ^ 3 *
              ‖h3SpectralScalarHeatRawRepresentative
                ν t G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMomentInt.const_mul ((2 * Real.pi) ^ 3)

  refine hMajorantInt.mono' hTargetMeas ?_
  exact Filter.Eventually.of_forall fun ξ =>
    norm_h3SpectralScalarHeatThirdCoordinateRawAmplitude_le_thirdMoment
      ν t G j k l ξ

/-- Inverse-Fourier reconstruction of one ordered third-coordinate heat
amplitude. -/
noncomputable def h3SpectralScalarHeatThirdCoordinateRepresentative
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (j k l : Fin 3) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3SpectralScalarHeatThirdCoordinateRawAmplitude
      ν t G j k l)

/-- At positive heat time, the named third-coordinate reconstruction is
exactly the third Fréchet derivative of the scalar heat reconstruction
evaluated on the corresponding ordered coordinate directions. -/
theorem h3SpectralScalarHeatThirdCoordinateRepresentative_eq_iteratedFDeriv
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (j k l : Fin 3)
    (x : H3FourierPoint3) :
    h3SpectralScalarHeatThirdCoordinateRepresentative
        ν t G j k l x
      =
    iteratedFDeriv ℝ 3
      (h3SpectralScalarHeatC3Representative ν t G)
      x
      ![
        h3FourierAxisDirection (h3AxisOfFin3 j),
        h3FourierAxisDirection (h3AxisOfFin3 k),
        h3FourierAxisDirection (h3AxisOfFin3 l)
      ] := by
  let f : H3FourierPoint3 → ℂ :=
    h3SpectralScalarHeatRawRepresentative ν t G

  let L :
      H3FourierPoint3 →L[ℝ]
        H3FourierPoint3 →L[ℝ] ℝ :=
    -(innerSL ℝ)

  let m : Fin 3 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection (h3AxisOfFin3 j),
      h3FourierAxisDirection (h3AxisOfFin3 k),
      h3FourierAxisDirection (h3AxisOfFin3 l)
    ]

  have hMom :
      ∀ (n : ℕ), n ≤ (3 : ℕ∞) →
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ n * ‖f ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro n hn
    have hn3 : n ≤ 3 := by
      exact_mod_cast hn
    dsimp only [f]
    exact
      h3SpectralScalarHeatRawRepresentative_moment_integrable
        hν ht G n hn3

  have hMeas :
      AEStronglyMeasurable
        f
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    exact
      h3SpectralScalarHeatRawRepresentative_aestronglyMeasurable
        ν t G

  have hDeriv :=
    VectorFourier.iteratedFDeriv_fourierIntegral
      (L := L)
      (f := f)
      (μ := (volume : Measure H3FourierPoint3))
      hMom
      hMeas
      (n := 3)
      (by norm_num)

  have hEval :=
    congrArg
      (fun F => F x m)
      hDeriv

  have hRawEq :
      (fun ξ : H3FourierPoint3 =>
        VectorFourier.fourierPowSMulRight
          L f ξ 3 m)
        =
      h3SpectralScalarHeatThirdCoordinateRawAmplitude
        ν t G j k l := by
    funext ξ
    dsimp only [L, f, m]
    exact
      h3SpectralScalarHeatThirdCoordinateRawAmplitude_eq_fourierPowSMulRight
        ν t G j k l ξ

  have hPowInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 3)
        (volume : Measure H3FourierPoint3) :=
    VectorFourier.integrable_fourierPowSMulRight
      L
      (hMom 3 (by norm_num))
      hMeas

  rw [
    Real.fourierIntegral_continuousMultilinearMap_apply'
      hPowInt
  ] at hEval
  rw [hRawEq] at hEval

  unfold
    h3SpectralScalarHeatThirdCoordinateRepresentative
    h3SpectralScalarHeatC3Representative

  change
    VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        (h3SpectralScalarHeatThirdCoordinateRawAmplitude
          ν t G j k l)
        x
      =
    iteratedFDeriv ℝ 3
      (VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        f)
      x m

  exact hEval.symm

end

end Euclidean
end Bridge
end PrimeTensor
