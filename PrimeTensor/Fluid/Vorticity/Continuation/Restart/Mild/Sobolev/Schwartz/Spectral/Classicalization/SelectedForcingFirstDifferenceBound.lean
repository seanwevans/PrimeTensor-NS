import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedSecondMomentTimeContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Forcing.HalfHolder
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.FirstForcingMass

/-!
# Classicalization: first-moment difference bound for the nonlinear forcing

The mixed spacetime closure needs time continuity of one spatial derivative of
the instantaneous nonlinear forcing.  On the Fourier side that is exactly
continuity in the first weighted raw `L¹` moment.

The existing endpoint forcing layer already proves the exact bilinear identity

    N(U,U) - N(V,V)
      = N(U-V,U) + N(V,U-V).

`FirstForcingMass` gives a quantitative first-moment bound for any bilinear
forcing `N(F,G)` in terms of the zeroth and second raw Fourier masses of `F`
and `G`.

This file combines those two facts.  If `D = U-V`, then

    M₁(N(U,U)-N(V,V))
      ≤ M₁(N(D,U)) + M₁(N(V,D)),

and each term is bounded by the existing finite forcing state-mass formula.

This is the exact quantitative estimate needed for the next selected-path
continuity increment.  No new convolution or PDE estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedForcingFirstDifferenceBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Second raw Fourier moments of all state coordinates are enough to obtain
one integrable raw Fourier moment of the complete finite Leray forcing. -/
theorem h3RawFinLerayOuterProductDivergence_firstMoment_integrable_of_stateSecond
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hU2 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 *
              ‖h3SpectralScalarRawFourier (U k) ξ‖)
          (volume : Measure H3FourierPoint3))
    (hV2 :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 *
              ‖h3SpectralScalarRawFourier (V j) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hConv2 :
      ∀ k j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 *
              ‖h3RawProductConvolution (U k) (V j) ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k j
    exact
      h3RawProductConvolution_secondMoment_integrable_of
        (U k) (V j) (hU2 k) (hV2 j)

  have hDiv1 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ *
              ‖h3RawFinOuterProductDivergence U V k ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    exact
      h3RawFinOuterProductDivergence_firstMoment_integrable_of_convolutionSecond
        U V k (hConv2 k)

  exact
    h3RawFinLerayOuterProductDivergence_firstMoment_integrable_of_divergenceFirst
      U V i hDiv1

/-- The first raw Fourier moment of the diagonal forcing difference is at most
the sum of the first moments of the two bilinear difference pieces. -/
theorem h3RawFinLerayOuterProductDivergence_diagonal_differenceFirstMass_le
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hU2 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 *
              ‖h3SpectralScalarRawFourier (U k) ξ‖)
          (volume : Measure H3FourierPoint3))
    (hV2 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 *
              ‖h3SpectralScalarRawFourier (V k) ξ‖)
          (volume : Measure H3FourierPoint3))
    (hD2 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 *
              ‖h3SpectralScalarRawFourier ((U - V) k) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ *
          ‖h3RawFinLerayOuterProductDivergence U U i ξ -
            h3RawFinLerayOuterProductDivergence V V i ξ‖)
      ≤
    h3RawFinLerayOuterProductDivergenceFirstMass
        (U - V) U i
      +
    h3RawFinLerayOuterProductDivergenceFirstMass
        V (U - V) i := by
  let A : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3RawFinLerayOuterProductDivergence
        (U - V) U i ξ

  let B : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3RawFinLerayOuterProductDivergence
        V (U - V) i ξ

  have hA :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ * ‖A ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [A]
    exact
      h3RawFinLerayOuterProductDivergence_firstMoment_integrable_of_stateSecond
        (U - V) U i hD2 hU2

  have hB :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ * ‖B ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [B]
    exact
      h3RawFinLerayOuterProductDivergence_firstMoment_integrable_of_stateSecond
        V (U - V) i hV2 hD2

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖A ξ‖ + ‖ξ‖ * ‖B ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hA.add hB

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
          ‖ξ‖ *
            ‖h3RawFinLerayOuterProductDivergence U U i ξ -
              h3RawFinLerayOuterProductDivergence V V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    continuous_norm.aestronglyMeasurable.mul
      hDifferenceComplex.aestronglyMeasurable.norm

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖ξ‖ *
            ‖h3RawFinLerayOuterProductDivergence U U i ξ -
              h3RawFinLerayOuterProductDivergence V V i ξ‖
          ≤
        ‖ξ‖ * ‖A ξ‖ + ‖ξ‖ * ‖B ξ‖ := by
    intro ξ

    have hw : 0 ≤ ‖ξ‖ :=
      norm_nonneg ξ

    rw [
      h3RawFinLerayOuterProductDivergence_diagonal_sub
        U V i ξ
    ]

    dsimp only [A, B]

    calc
      ‖ξ‖ *
          ‖h3RawFinLerayOuterProductDivergence (U - V) U i ξ +
            h3RawFinLerayOuterProductDivergence V (U - V) i ξ‖
          ≤
        ‖ξ‖ *
          (‖h3RawFinLerayOuterProductDivergence (U - V) U i ξ‖ +
            ‖h3RawFinLerayOuterProductDivergence V (U - V) i ξ‖) :=
        mul_le_mul_of_nonneg_left
          (norm_add_le _ _)
          hw
      _ =
        ‖ξ‖ *
            ‖h3RawFinLerayOuterProductDivergence (U - V) U i ξ‖
          +
        ‖ξ‖ *
            ‖h3RawFinLerayOuterProductDivergence V (U - V) i ξ‖ := by
        ring

  have hTarget :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ *
            ‖h3RawFinLerayOuterProductDivergence U U i ξ -
              h3RawFinLerayOuterProductDivergence V V i ξ‖)
        (volume : Measure H3FourierPoint3) := by
    refine hMajor.mono' hTargetMeas ?_
    filter_upwards with ξ
    have hLeft0 :
        0 ≤
          ‖ξ‖ *
            ‖h3RawFinLerayOuterProductDivergence U U i ξ -
              h3RawFinLerayOuterProductDivergence V V i ξ‖ := by
      positivity
    have hRight0 :
        0 ≤ ‖ξ‖ * ‖A ξ‖ + ‖ξ‖ * ‖B ξ‖ := by
      positivity
    simpa only [
      Real.norm_eq_abs,
      abs_of_nonneg hLeft0,
      abs_of_nonneg hRight0
    ] using hPoint ξ

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ *
          ‖h3RawFinLerayOuterProductDivergence U U i ξ -
            h3RawFinLerayOuterProductDivergence V V i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (‖ξ‖ * ‖A ξ‖ + ‖ξ‖ * ‖B ξ‖) :=
    integral_mono_ae
      hTarget
      hMajor
      (Filter.Eventually.of_forall hPoint)

  have hSum :
      (∫ ξ : H3FourierPoint3,
        (‖ξ‖ * ‖A ξ‖ + ‖ξ‖ * ‖B ξ‖))
        =
      (∫ ξ : H3FourierPoint3, ‖ξ‖ * ‖A ξ‖) +
        ∫ ξ : H3FourierPoint3, ‖ξ‖ * ‖B ξ‖ := by
    rw [integral_add hA hB]

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ *
          ‖h3RawFinLerayOuterProductDivergence U U i ξ -
            h3RawFinLerayOuterProductDivergence V V i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (‖ξ‖ * ‖A ξ‖ + ‖ξ‖ * ‖B ξ‖) :=
      hIntegral
    _ =
      (∫ ξ : H3FourierPoint3, ‖ξ‖ * ‖A ξ‖) +
        ∫ ξ : H3FourierPoint3, ‖ξ‖ * ‖B ξ‖ :=
      hSum
    _ =
      h3RawFinLerayOuterProductDivergenceFirstMass
          (U - V) U i
        +
      h3RawFinLerayOuterProductDivergenceFirstMass
          V (U - V) i := by
      rfl

/-- Fully quantitative first-moment estimate for the diagonal nonlinear
forcing difference in terms of coordinatewise zeroth and second state masses. -/
theorem h3RawFinLerayOuterProductDivergence_diagonal_differenceFirstMass_le_stateMasses
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hU2 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 *
              ‖h3SpectralScalarRawFourier (U k) ξ‖)
          (volume : Measure H3FourierPoint3))
    (hV2 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 *
              ‖h3SpectralScalarRawFourier (V k) ξ‖)
          (volume : Measure H3FourierPoint3))
    (hD2 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 *
              ‖h3SpectralScalarRawFourier ((U - V) k) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ *
          ‖h3RawFinLerayOuterProductDivergence U U i ξ -
            h3RawFinLerayOuterProductDivergence V V i ξ‖)
      ≤
    2 *
        ∑ k : Fin 3,
          ∑ j : Fin 3,
            (2 * Real.pi) *
              (2 *
                (h3SpectralScalarRawFourierSecondMass ((U - V) k) *
                    h3SpectralScalarRawFourierL1Mass (U j) +
                  h3SpectralScalarRawFourierL1Mass ((U - V) k) *
                    h3SpectralScalarRawFourierSecondMass (U j)))
      +
    2 *
        ∑ k : Fin 3,
          ∑ j : Fin 3,
            (2 * Real.pi) *
              (2 *
                (h3SpectralScalarRawFourierSecondMass (V k) *
                    h3SpectralScalarRawFourierL1Mass ((U - V) j) +
                  h3SpectralScalarRawFourierL1Mass (V k) *
                    h3SpectralScalarRawFourierSecondMass ((U - V) j))) := by
  have hSplit :=
    h3RawFinLerayOuterProductDivergence_diagonal_differenceFirstMass_le
      U V i hU2 hV2 hD2

  have hLeft :=
    h3RawFinLerayOuterProductDivergenceFirstMass_le_stateMasses
      (U - V) U i hD2 hU2

  have hRight :=
    h3RawFinLerayOuterProductDivergenceFirstMass_le_stateMasses
      V (U - V) i hV2 hD2

  exact
    hSplit.trans
      (add_le_add hLeft hRight)

end

end Euclidean
end Bridge
end PrimeTensor
