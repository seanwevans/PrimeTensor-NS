import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.First.Difference.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.Second.Forcing.Mass

/-!
# Classicalization: second-moment difference bound for the nonlinear forcing

The fresh second-Fréchet Duhamel endpoint needs time continuity of two spatial
derivatives of the instantaneous nonlinear forcing.  On the Fourier side this
is continuity in the second weighted raw `L¹` moment.

The same exact bilinear polarization used at order one gives

    N(U,U) - N(V,V)
      = N(U-V,U) + N(V,U-V).

Because the Leray forcing spends one Fourier power on divergence, controlling
its second weighted mass requires cubic raw Fourier moments of the two input
states.  The fifth endpoint already provides the generic estimate

    M₂(N(F,G))
      <= C * (M₃(F) M₀(G) + M₀(F) M₃(G)).

This file packages the corresponding diagonal-difference estimate.  The proof
is deliberately parallel to `Selected.Forcing.First.Difference.Bound`; the
order shift `state moment n+1 -> forcing moment n` is a candidate for later
inductive extraction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedForcingSecondDifferenceBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Cubic raw Fourier moments of all state coordinates are enough to obtain an
integrable second raw Fourier moment of the complete finite Leray forcing. -/
theorem h3RawFinLerayOuterProductDivergence_secondMoment_integrable_of_stateThird
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hU3 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3SpectralScalarRawFourier (U k) ξ‖)
          (volume : Measure H3FourierPoint3))
    (hV3 :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3SpectralScalarRawFourier (V j) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 2 *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hConv3 :
      ∀ k j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3RawProductConvolution (U k) (V j) ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k j
    exact
      h3RawProductConvolution_thirdMoment_integrable_of
        (U k) (V j) (hU3 k) (hV3 j)

  have hDiv2 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 *
              ‖h3RawFinOuterProductDivergence U V k ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    exact
      h3RawFinOuterProductDivergence_secondMoment_integrable_of_convolutionThird
        U V k (hConv3 k)

  exact
    h3RawFinLerayOuterProductDivergence_secondMoment_integrable_of_divergenceSecond
      U V i hDiv2

/-- The second raw Fourier moment of the diagonal forcing difference is at most
the sum of the second moments of the two bilinear difference pieces. -/
theorem h3RawFinLerayOuterProductDivergence_diagonal_differenceSecondMass_le
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hU3 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3SpectralScalarRawFourier (U k) ξ‖)
          (volume : Measure H3FourierPoint3))
    (hV3 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3SpectralScalarRawFourier (V k) ξ‖)
          (volume : Measure H3FourierPoint3))
    (hD3 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3SpectralScalarRawFourier ((U - V) k) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3RawFinLerayOuterProductDivergence U U i ξ -
            h3RawFinLerayOuterProductDivergence V V i ξ‖)
      ≤
    h3RawFinLerayOuterProductDivergenceSecondMass
        (U - V) U i
      +
    h3RawFinLerayOuterProductDivergenceSecondMass
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
        (fun ξ : H3FourierPoint3 => ‖ξ‖ ^ 2 * ‖P ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [P]
    exact
      h3RawFinLerayOuterProductDivergence_secondMoment_integrable_of_stateThird
        (U - V) U i hD3 hU3

  have hQ :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ ^ 2 * ‖Q ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [Q]
    exact
      h3RawFinLerayOuterProductDivergence_secondMoment_integrable_of_stateThird
        V (U - V) i hV3 hD3

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖P ξ‖ + ‖ξ‖ ^ 2 * ‖Q ξ‖)
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
          ‖ξ‖ ^ 2 *
            ‖h3RawFinLerayOuterProductDivergence U U i ξ -
              h3RawFinLerayOuterProductDivergence V V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_norm.pow 2).aestronglyMeasurable.mul
      hDifferenceComplex.aestronglyMeasurable.norm

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
            ‖h3RawFinLerayOuterProductDivergence U U i ξ -
              h3RawFinLerayOuterProductDivergence V V i ξ‖
          ≤
        ‖ξ‖ ^ 2 * ‖P ξ‖ + ‖ξ‖ ^ 2 * ‖Q ξ‖ := by
    intro ξ

    have hw : 0 ≤ ‖ξ‖ ^ 2 := by positivity

    rw [
      h3RawFinLerayOuterProductDivergence_diagonal_sub
        U V i ξ
    ]

    dsimp only [P, Q]

    calc
      ‖ξ‖ ^ 2 *
          ‖h3RawFinLerayOuterProductDivergence (U - V) U i ξ +
            h3RawFinLerayOuterProductDivergence V (U - V) i ξ‖
          ≤
        ‖ξ‖ ^ 2 *
          (‖h3RawFinLerayOuterProductDivergence (U - V) U i ξ‖ +
            ‖h3RawFinLerayOuterProductDivergence V (U - V) i ξ‖) :=
        mul_le_mul_of_nonneg_left
          (norm_add_le _ _)
          hw
      _ =
        ‖ξ‖ ^ 2 *
            ‖h3RawFinLerayOuterProductDivergence (U - V) U i ξ‖
          +
        ‖ξ‖ ^ 2 *
            ‖h3RawFinLerayOuterProductDivergence V (U - V) i ξ‖ := by
        ring

  have hTarget :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3RawFinLerayOuterProductDivergence U U i ξ -
              h3RawFinLerayOuterProductDivergence V V i ξ‖)
        (volume : Measure H3FourierPoint3) := by
    refine hMajor.mono' hTargetMeas ?_
    filter_upwards with ξ
    have hLeft0 :
        0 ≤
          ‖ξ‖ ^ 2 *
            ‖h3RawFinLerayOuterProductDivergence U U i ξ -
              h3RawFinLerayOuterProductDivergence V V i ξ‖ := by
      positivity
    have hRight0 :
        0 ≤ ‖ξ‖ ^ 2 * ‖P ξ‖ + ‖ξ‖ ^ 2 * ‖Q ξ‖ := by
      positivity
    simpa only [
      Real.norm_eq_abs,
      abs_of_nonneg hLeft0,
      abs_of_nonneg hRight0
    ] using hPoint ξ

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3RawFinLerayOuterProductDivergence U U i ξ -
            h3RawFinLerayOuterProductDivergence V V i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (‖ξ‖ ^ 2 * ‖P ξ‖ + ‖ξ‖ ^ 2 * ‖Q ξ‖) :=
    integral_mono_ae
      hTarget
      hMajor
      (Filter.Eventually.of_forall hPoint)

  have hSum :
      (∫ ξ : H3FourierPoint3,
        (‖ξ‖ ^ 2 * ‖P ξ‖ + ‖ξ‖ ^ 2 * ‖Q ξ‖))
        =
      (∫ ξ : H3FourierPoint3, ‖ξ‖ ^ 2 * ‖P ξ‖) +
        ∫ ξ : H3FourierPoint3, ‖ξ‖ ^ 2 * ‖Q ξ‖ := by
    rw [integral_add hP hQ]

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3RawFinLerayOuterProductDivergence U U i ξ -
            h3RawFinLerayOuterProductDivergence V V i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (‖ξ‖ ^ 2 * ‖P ξ‖ + ‖ξ‖ ^ 2 * ‖Q ξ‖) :=
      hIntegral
    _ =
      (∫ ξ : H3FourierPoint3, ‖ξ‖ ^ 2 * ‖P ξ‖) +
        ∫ ξ : H3FourierPoint3, ‖ξ‖ ^ 2 * ‖Q ξ‖ :=
      hSum
    _ =
      h3RawFinLerayOuterProductDivergenceSecondMass
          (U - V) U i
        +
      h3RawFinLerayOuterProductDivergenceSecondMass
          V (U - V) i := by
      rfl

/-- Fully quantitative second-moment estimate for the diagonal nonlinear
forcing difference in terms of coordinatewise zeroth and cubic state masses. -/
theorem h3RawFinLerayOuterProductDivergence_diagonal_differenceSecondMass_le_stateMasses
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hU3 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3SpectralScalarRawFourier (U k) ξ‖)
          (volume : Measure H3FourierPoint3))
    (hV3 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3SpectralScalarRawFourier (V k) ξ‖)
          (volume : Measure H3FourierPoint3))
    (hD3 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3SpectralScalarRawFourier ((U - V) k) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3RawFinLerayOuterProductDivergence U U i ξ -
            h3RawFinLerayOuterProductDivergence V V i ξ‖)
      ≤
    2 *
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (h3FourierThirdSplitCoefficient *
              (h3SpectralScalarRawFourierThirdMass ((U - V) k) *
                  h3SpectralScalarRawFourierL1Mass (U j) +
                h3SpectralScalarRawFourierL1Mass ((U - V) k) *
                  h3SpectralScalarRawFourierThirdMass (U j)))
      +
    2 *
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (h3FourierThirdSplitCoefficient *
              (h3SpectralScalarRawFourierThirdMass (V k) *
                  h3SpectralScalarRawFourierL1Mass ((U - V) j) +
                h3SpectralScalarRawFourierL1Mass (V k) *
                  h3SpectralScalarRawFourierThirdMass ((U - V) j))) := by
  have hSplit :=
    h3RawFinLerayOuterProductDivergence_diagonal_differenceSecondMass_le
      U V i hU3 hV3 hD3

  have hLeft :=
    h3RawFinLerayOuterProductDivergenceSecondMass_le_stateMasses
      (U - V) U i hD3 hU3

  have hRight :=
    h3RawFinLerayOuterProductDivergenceSecondMass_le_stateMasses
      V (U - V) i hV3 hD3

  exact
    hSplit.trans
      (add_le_add hLeft hRight)

end

end Euclidean
end Bridge
end PrimeTensor
