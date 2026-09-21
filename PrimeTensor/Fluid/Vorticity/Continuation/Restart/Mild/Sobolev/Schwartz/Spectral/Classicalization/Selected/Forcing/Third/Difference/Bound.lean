import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.Second.Difference.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.Third.Forcing.Mass

/-!
# Classicalization: third-moment difference bound for the nonlinear forcing

The third spatial Fréchet derivative of the instantaneous forcing is controlled
by the cubic weighted raw Fourier mass of that forcing.

The Leray forcing spends one Fourier power on divergence, so a cubic forcing
moment is controlled by fourth moments of the two state inputs.  Combining the
already-compiled sixth-endpoint estimates with the exact bilinear
polarization

    N(U,U) - N(V,V)
      = N(U-V,U) + N(V,U-V)

gives a quantitative diagonal-difference estimate in terms of coordinatewise
zeroth and fourth state masses.

This is the order-three analogue of
`Selected.Forcing.Second.Difference.Bound`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedForcingThirdDifferenceBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Fourth raw Fourier moments of all state coordinates are enough to obtain
an integrable cubic raw Fourier moment of the complete finite Leray forcing. -/
theorem h3RawFinLerayOuterProductDivergence_thirdMoment_integrable_of_stateFourth
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hU4 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 4 *
              ‖h3SpectralScalarRawFourier (U k) ξ‖)
          (volume : Measure H3FourierPoint3))
    (hV4 :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 4 *
              ‖h3SpectralScalarRawFourier (V j) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 3 *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hDeriv :
      ∀ k j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3FourierDerivativeSymbol j ξ *
                h3RawProductConvolution (U k) (V j) ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k j
    have hConv4 :=
      h3RawProductConvolution_fourthMoment_integrable_of
        (U k) (V j) (hU4 k) (hV4 j)
    exact
      h3FourierDerivative_mul_rawProductConvolution_thirdMoment_integrable_of_fourthMoment
        (U k) (V j) j hConv4

  have hDiv :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3RawFinOuterProductDivergence U V k ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    exact
      h3RawFinOuterProductDivergence_thirdMoment_integrable_of_derivatives
        U V k (hDeriv k)

  exact
    h3RawFinLerayOuterProductDivergence_thirdMoment_integrable_of_divergence
      U V i hDiv

/-- Fully quantitative cubic forcing estimate in terms of coordinatewise
zeroth and fourth state masses. -/
theorem h3RawFinLerayOuterProductDivergenceThirdMass_le_stateMasses
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hU4 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 4 *
              ‖h3SpectralScalarRawFourier (U k) ξ‖)
          (volume : Measure H3FourierPoint3))
    (hV4 :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 4 *
              ‖h3SpectralScalarRawFourier (V j) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    h3RawFinLerayOuterProductDivergenceThirdMass U V i
      ≤
    2 *
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (h3FourierFourthSplitCoefficient *
              (h3SpectralScalarRawFourierFourthMass (U k) *
                  h3SpectralScalarRawFourierL1Mass (V j) +
                h3SpectralScalarRawFourierL1Mass (U k) *
                  h3SpectralScalarRawFourierFourthMass (V j))) := by
  have hDeriv :
      ∀ k j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3FourierDerivativeSymbol j ξ *
                h3RawProductConvolution (U k) (V j) ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k j
    have hConv4 :=
      h3RawProductConvolution_fourthMoment_integrable_of
        (U k) (V j) (hU4 k) (hV4 j)
    exact
      h3FourierDerivative_mul_rawProductConvolution_thirdMoment_integrable_of_fourthMoment
        (U k) (V j) j hConv4

  have hDiv :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3RawFinOuterProductDivergence U V k ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    exact
      h3RawFinOuterProductDivergence_thirdMoment_integrable_of_derivatives
        U V k (hDeriv k)

  have hLeray :=
    h3RawFinLerayOuterProductDivergenceThirdMass_le
      U V i hDiv

  have hDivBound :
      ∀ k : Fin 3,
        h3RawFinOuterProductDivergenceThirdMass U V k
          ≤
        ∑ j : Fin 3,
          h3FourierDerivativeRawProductConvolutionThirdMass
            (U k) (V j) j := by
    intro k
    exact
      h3RawFinOuterProductDivergenceThirdMass_le
        U V k (hDeriv k)

  have hDerivativeBound :
      ∀ k j : Fin 3,
        h3FourierDerivativeRawProductConvolutionThirdMass
            (U k) (V j) j
          ≤
        (2 * Real.pi) *
          (h3FourierFourthSplitCoefficient *
            (h3SpectralScalarRawFourierFourthMass (U k) *
                h3SpectralScalarRawFourierL1Mass (V j) +
              h3SpectralScalarRawFourierL1Mass (U k) *
                h3SpectralScalarRawFourierFourthMass (V j))) := by
    intro k j
    exact
      h3FourierDerivativeRawProductConvolutionThirdMass_le_stateMasses
        (U k) (V j) j (hU4 k) (hV4 j)

  have hDivSum :
      (∑ k : Fin 3,
          h3RawFinOuterProductDivergenceThirdMass U V k)
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          h3FourierDerivativeRawProductConvolutionThirdMass
            (U k) (V j) j :=
    Finset.sum_le_sum fun k _ =>
      hDivBound k

  have hDerivativeSum :
      (∑ k : Fin 3,
          ∑ j : Fin 3,
            h3FourierDerivativeRawProductConvolutionThirdMass
              (U k) (V j) j)
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (h3FourierFourthSplitCoefficient *
              (h3SpectralScalarRawFourierFourthMass (U k) *
                  h3SpectralScalarRawFourierL1Mass (V j) +
                h3SpectralScalarRawFourierL1Mass (U k) *
                  h3SpectralScalarRawFourierFourthMass (V j))) :=
    Finset.sum_le_sum fun k _ =>
      Finset.sum_le_sum fun j _ =>
        hDerivativeBound k j

  exact
    hLeray.trans
      (mul_le_mul_of_nonneg_left
        (hDivSum.trans hDerivativeSum)
        (by norm_num))

/-- The cubic raw Fourier moment of the diagonal forcing difference is bounded
by the cubic moments of the two polarized bilinear pieces. -/
theorem h3RawFinLerayOuterProductDivergence_diagonal_differenceThirdMass_le
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hU4 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 4 *
              ‖h3SpectralScalarRawFourier (U k) ξ‖)
          (volume : Measure H3FourierPoint3))
    (hV4 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 4 *
              ‖h3SpectralScalarRawFourier (V k) ξ‖)
          (volume : Measure H3FourierPoint3))
    (hD4 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 4 *
              ‖h3SpectralScalarRawFourier ((U - V) k) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3RawFinLerayOuterProductDivergence U U i ξ -
            h3RawFinLerayOuterProductDivergence V V i ξ‖)
      ≤
    h3RawFinLerayOuterProductDivergenceThirdMass
        (U - V) U i
      +
    h3RawFinLerayOuterProductDivergenceThirdMass
        V (U - V) i := by
  let P : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3RawFinLerayOuterProductDivergence
        (U - V) U i ξ

  let Q : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3RawFinLerayOuterProductDivergence
        V (U - V) i ξ

  have hP :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖P ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [P]
    exact
      h3RawFinLerayOuterProductDivergence_thirdMoment_integrable_of_stateFourth
        (U - V) U i hD4 hU4

  have hQ :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖Q ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [Q]
    exact
      h3RawFinLerayOuterProductDivergence_thirdMoment_integrable_of_stateFourth
        V (U - V) i hV4 hD4

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖P ξ‖ +
            ‖ξ‖ ^ 3 * ‖Q ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hP.add hQ

  have hDifferenceComplex :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3RawFinLerayOuterProductDivergence U U i ξ -
            h3RawFinLerayOuterProductDivergence V V i ξ)
        (volume : Measure H3FourierPoint3) :=
    (h3RawFinLerayOuterProductDivergence_integrable U U i).sub
      (h3RawFinLerayOuterProductDivergence_integrable V V i)

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 *
            ‖h3RawFinLerayOuterProductDivergence U U i ξ -
              h3RawFinLerayOuterProductDivergence V V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_norm.pow 3).aestronglyMeasurable.mul
      hDifferenceComplex.aestronglyMeasurable.norm

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
            ‖h3RawFinLerayOuterProductDivergence U U i ξ -
              h3RawFinLerayOuterProductDivergence V V i ξ‖
          ≤
        ‖ξ‖ ^ 3 * ‖P ξ‖ +
          ‖ξ‖ ^ 3 * ‖Q ξ‖ := by
    intro ξ

    have hw : 0 ≤ ‖ξ‖ ^ 3 := by positivity

    rw [
      h3RawFinLerayOuterProductDivergence_diagonal_sub
        U V i ξ
    ]

    dsimp only [P, Q]

    calc
      ‖ξ‖ ^ 3 *
          ‖h3RawFinLerayOuterProductDivergence (U - V) U i ξ +
            h3RawFinLerayOuterProductDivergence V (U - V) i ξ‖
          ≤
        ‖ξ‖ ^ 3 *
          (‖h3RawFinLerayOuterProductDivergence (U - V) U i ξ‖ +
            ‖h3RawFinLerayOuterProductDivergence V (U - V) i ξ‖) :=
        mul_le_mul_of_nonneg_left
          (norm_add_le _ _)
          hw
      _ =
        ‖ξ‖ ^ 3 *
            ‖h3RawFinLerayOuterProductDivergence (U - V) U i ξ‖
          +
        ‖ξ‖ ^ 3 *
            ‖h3RawFinLerayOuterProductDivergence V (U - V) i ξ‖ := by
        ring

  have hTarget :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 *
            ‖h3RawFinLerayOuterProductDivergence U U i ξ -
              h3RawFinLerayOuterProductDivergence V V i ξ‖)
        (volume : Measure H3FourierPoint3) := by
    refine hMajor.mono' hTargetMeas ?_
    filter_upwards with ξ
    have hLeft0 :
        0 ≤
          ‖ξ‖ ^ 3 *
            ‖h3RawFinLerayOuterProductDivergence U U i ξ -
              h3RawFinLerayOuterProductDivergence V V i ξ‖ := by
      positivity
    have hRight0 :
        0 ≤
          ‖ξ‖ ^ 3 * ‖P ξ‖ +
            ‖ξ‖ ^ 3 * ‖Q ξ‖ := by
      positivity
    simpa only [
      Real.norm_eq_abs,
      abs_of_nonneg hLeft0,
      abs_of_nonneg hRight0
    ] using hPoint ξ

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3RawFinLerayOuterProductDivergence U U i ξ -
            h3RawFinLerayOuterProductDivergence V V i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (‖ξ‖ ^ 3 * ‖P ξ‖ +
          ‖ξ‖ ^ 3 * ‖Q ξ‖) :=
    integral_mono_ae
      hTarget
      hMajor
      (Filter.Eventually.of_forall hPoint)

  have hSum :
      (∫ ξ : H3FourierPoint3,
        (‖ξ‖ ^ 3 * ‖P ξ‖ +
          ‖ξ‖ ^ 3 * ‖Q ξ‖))
        =
      (∫ ξ : H3FourierPoint3, ‖ξ‖ ^ 3 * ‖P ξ‖) +
        ∫ ξ : H3FourierPoint3, ‖ξ‖ ^ 3 * ‖Q ξ‖ := by
    rw [integral_add hP hQ]

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3RawFinLerayOuterProductDivergence U U i ξ -
            h3RawFinLerayOuterProductDivergence V V i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (‖ξ‖ ^ 3 * ‖P ξ‖ +
          ‖ξ‖ ^ 3 * ‖Q ξ‖) :=
      hIntegral
    _ =
      (∫ ξ : H3FourierPoint3, ‖ξ‖ ^ 3 * ‖P ξ‖) +
        ∫ ξ : H3FourierPoint3, ‖ξ‖ ^ 3 * ‖Q ξ‖ :=
      hSum
    _ =
      h3RawFinLerayOuterProductDivergenceThirdMass
          (U - V) U i
        +
      h3RawFinLerayOuterProductDivergenceThirdMass
          V (U - V) i := by
      rfl

/-- Fully quantitative cubic-moment estimate for the diagonal nonlinear
forcing difference in terms of coordinatewise zeroth and fourth state masses. -/
theorem h3RawFinLerayOuterProductDivergence_diagonal_differenceThirdMass_le_stateMasses
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hU4 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 4 *
              ‖h3SpectralScalarRawFourier (U k) ξ‖)
          (volume : Measure H3FourierPoint3))
    (hV4 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 4 *
              ‖h3SpectralScalarRawFourier (V k) ξ‖)
          (volume : Measure H3FourierPoint3))
    (hD4 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 4 *
              ‖h3SpectralScalarRawFourier ((U - V) k) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3RawFinLerayOuterProductDivergence U U i ξ -
            h3RawFinLerayOuterProductDivergence V V i ξ‖)
      ≤
    2 *
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (h3FourierFourthSplitCoefficient *
              (h3SpectralScalarRawFourierFourthMass ((U - V) k) *
                  h3SpectralScalarRawFourierL1Mass (U j) +
                h3SpectralScalarRawFourierL1Mass ((U - V) k) *
                  h3SpectralScalarRawFourierFourthMass (U j)))
      +
    2 *
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (h3FourierFourthSplitCoefficient *
              (h3SpectralScalarRawFourierFourthMass (V k) *
                  h3SpectralScalarRawFourierL1Mass ((U - V) j) +
                h3SpectralScalarRawFourierL1Mass (V k) *
                  h3SpectralScalarRawFourierFourthMass ((U - V) j))) := by
  have hSplit :=
    h3RawFinLerayOuterProductDivergence_diagonal_differenceThirdMass_le
      U V i hU4 hV4 hD4

  have hLeft :=
    h3RawFinLerayOuterProductDivergenceThirdMass_le_stateMasses
      (U - V) U i hD4 hU4

  have hRight :=
    h3RawFinLerayOuterProductDivergenceThirdMass_le_stateMasses
      V (U - V) i hV4 hD4

  exact
    hSplit.trans
      (add_le_add hLeft hRight)

end

end Euclidean
end Bridge
end PrimeTensor
