import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedHighFourierCoordinateL2Frontier

/-!
# Reduce selected high Fourier-coordinate L² to radial weighted raw Fourier L²

The previous frontier asks for `L²` membership of every ordered fourth/fifth
Fourier coordinate multiplier.  Mathlib's generic multiplier estimate gives

    ‖fourierPowSMulRight L f ξ n‖
      ≤ (2π ‖L‖)^n ‖ξ‖^n ‖f ξ‖.

Thus one radial weighted `L²` hypothesis for the selected raw Fourier state at
orders four and five simultaneously controls every ordered coordinate
multiplier.

The proof is deliberately split in two:

1. radial weighted `L²` gives `L²` for the full continuous multilinear
   multiplier;
2. evaluation at a fixed ordered axis tuple is a bounded linear map, so it
   preserves `L²`.

All `L¹`/measurability input needed by the multiplier is already supplied by
the positive-time all-orders moment theorem.

After this file, the remaining diffusion-side analytic frontier is exactly

    ‖ξ‖⁴ raw(W(q)) ∈ L²,
    ‖ξ‖⁵ raw(W(q)) ∈ L²

for every strict positive selected restart time.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedHighRadialFourierL2Frontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Radial weighted complex raw amplitudes -/

noncomputable def h3SelectedRawFourierFourthRadialWeight
    (H : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℂ :=
  ((‖ξ‖ ^ 4 : ℝ) : ℂ) *
    h3SpectralScalarRawFourier H ξ

noncomputable def h3SelectedRawFourierFifthRadialWeight
    (H : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℂ :=
  ((‖ξ‖ ^ 5 : ℝ) : ℂ) *
    h3SpectralScalarRawFourier H ξ

/-! ## Generic evaluation of an L² multilinear multiplier -/

private theorem memLp_fourierPowSMulRight_eval_four_of_radial
    (H : H3SpectralScalarState)
    (hFourthInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 *
            ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3))
    (hRadial :
      MemLp
        (h3SelectedRawFourierFourthRadialWeight H)
        2
        (volume : Measure H3FourierPoint3))
    (m : Fin 4 → H3FourierPoint3) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        (VectorFourier.fourierPowSMulRight
          (-(innerSL ℝ :
            H3FourierPoint3 →L[ℝ]
              H3FourierPoint3 →L[ℝ] ℝ))
          (h3SpectralScalarRawFourier H)
          ξ
          4)
          m)
      2
      (volume : Measure H3FourierPoint3) := by

  let f : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourier H

  let L :
      H3FourierPoint3 →L[ℝ]
        H3FourierPoint3 →L[ℝ] ℝ :=
    -(innerSL ℝ)

  let C : ℝ :=
    (2 * Real.pi * ‖L‖) ^ 4

  have hRawInt :
      Integrable f
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 H)

  have hPowInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 4)
        (volume : Measure H3FourierPoint3) :=
    VectorFourier.integrable_fourierPowSMulRight
      L hFourthInt hRawInt.aestronglyMeasurable

  have hPowLp :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 4)
        2
        (volume : Measure H3FourierPoint3) := by

    refine
      hRadial.of_le_mul
        (c := C)
        hPowInt.aestronglyMeasurable
        ?_

    filter_upwards with ξ

    have hOp :=
      VectorFourier.norm_fourierPowSMulRight_le
        L f ξ 4

    have hPoint :
        ‖VectorFourier.fourierPowSMulRight
            L f ξ 4‖
          ≤
        C * (‖ξ‖ ^ 4 * ‖f ξ‖) := by
      dsimp only [C]
      nlinarith [hOp]

    have hWeightNonneg :
        0 ≤ ‖ξ‖ ^ 4 :=
      pow_nonneg (norm_nonneg ξ) 4

    dsimp only [
      h3SelectedRawFourierFourthRadialWeight,
      f
    ]

    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg hWeightNonneg
    ]

    exact hPoint

  let M2 :
      MeasureTheory.Lp
        (ContinuousMultilinearMap
          ℝ
          (fun _ : Fin 4 => H3FourierPoint3)
          ℂ)
        2
        (volume : Measure H3FourierPoint3) :=
    hPowLp.toLp
      (fun ξ : H3FourierPoint3 =>
        VectorFourier.fourierPowSMulRight
          L f ξ 4)

  let eval :
      ContinuousMultilinearMap
          ℝ
          (fun _ : Fin 4 => H3FourierPoint3)
          ℂ
        →L[ℝ]
      ℂ :=
    ContinuousMultilinearMap.apply
      ℝ
      (fun _ : Fin 4 => H3FourierPoint3)
      ℂ
      m

  let E2 :
      MeasureTheory.Lp
        ℂ
        2
        (volume : Measure H3FourierPoint3) :=
    eval.compLp M2

  have hM2 :
      ((M2 :
          MeasureTheory.Lp
            (ContinuousMultilinearMap
              ℝ
              (fun _ : Fin 4 => H3FourierPoint3)
              ℂ)
            2
            (volume : Measure H3FourierPoint3)) :
        H3FourierPoint3 →
          ContinuousMultilinearMap
            ℝ
            (fun _ : Fin 4 => H3FourierPoint3)
            ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        VectorFourier.fourierPowSMulRight
          L f ξ 4) := by
    dsimp only [M2]
    exact
      MeasureTheory.MemLp.coeFn_toLp hPowLp

  have hE2 :
      ((E2 :
          MeasureTheory.Lp
            ℂ
            2
            (volume : Measure H3FourierPoint3)) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        eval
          (((M2 :
              MeasureTheory.Lp
                (ContinuousMultilinearMap
                  ℝ
                  (fun _ : Fin 4 => H3FourierPoint3)
                  ℂ)
                2
                (volume : Measure H3FourierPoint3)) :
            H3FourierPoint3 →
              ContinuousMultilinearMap
                ℝ
                (fun _ : Fin 4 => H3FourierPoint3)
                ℂ) ξ)) := by
    dsimp only [E2]
    exact
      ContinuousLinearMap.coeFn_compLp
        eval M2

  have hAE :
      (fun ξ : H3FourierPoint3 =>
        (VectorFourier.fourierPowSMulRight
          L f ξ 4) m)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      ((E2 :
          MeasureTheory.Lp
            ℂ
            2
            (volume : Measure H3FourierPoint3)) :
        H3FourierPoint3 → ℂ) := by
    filter_upwards [hM2, hE2] with ξ hξM hξE

    calc
      (VectorFourier.fourierPowSMulRight
          L f ξ 4) m
          =
        eval
          (VectorFourier.fourierPowSMulRight
            L f ξ 4) := by
            rfl
      _ =
        eval
          (((M2 :
              MeasureTheory.Lp
                (ContinuousMultilinearMap
                  ℝ
                  (fun _ : Fin 4 => H3FourierPoint3)
                  ℂ)
                2
                (volume : Measure H3FourierPoint3)) :
            H3FourierPoint3 →
              ContinuousMultilinearMap
                ℝ
                (fun _ : Fin 4 => H3FourierPoint3)
                ℂ) ξ) := by
            rw [hξM]
      _ =
        ((E2 :
            MeasureTheory.Lp
              ℂ
              2
              (volume : Measure H3FourierPoint3)) :
          H3FourierPoint3 → ℂ) ξ :=
            hξE.symm

  have hE2Lp :
      MemLp
        ((E2 :
            MeasureTheory.Lp
              ℂ
              2
              (volume : Measure H3FourierPoint3)) :
          H3FourierPoint3 → ℂ)
        2
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.Lp.memLp E2

  exact
    (memLp_congr_ae hAE).2 hE2Lp

private theorem memLp_fourierPowSMulRight_eval_five_of_radial
    (H : H3SpectralScalarState)
    (hFifthInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 5 *
            ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3))
    (hRadial :
      MemLp
        (h3SelectedRawFourierFifthRadialWeight H)
        2
        (volume : Measure H3FourierPoint3))
    (m : Fin 5 → H3FourierPoint3) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        (VectorFourier.fourierPowSMulRight
          (-(innerSL ℝ :
            H3FourierPoint3 →L[ℝ]
              H3FourierPoint3 →L[ℝ] ℝ))
          (h3SpectralScalarRawFourier H)
          ξ
          5)
          m)
      2
      (volume : Measure H3FourierPoint3) := by

  let f : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourier H

  let L :
      H3FourierPoint3 →L[ℝ]
        H3FourierPoint3 →L[ℝ] ℝ :=
    -(innerSL ℝ)

  let C : ℝ :=
    (2 * Real.pi * ‖L‖) ^ 5

  have hRawInt :
      Integrable f
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 H)

  have hPowInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 5)
        (volume : Measure H3FourierPoint3) :=
    VectorFourier.integrable_fourierPowSMulRight
      L hFifthInt hRawInt.aestronglyMeasurable

  have hPowLp :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 5)
        2
        (volume : Measure H3FourierPoint3) := by

    refine
      hRadial.of_le_mul
        (c := C)
        hPowInt.aestronglyMeasurable
        ?_

    filter_upwards with ξ

    have hOp :=
      VectorFourier.norm_fourierPowSMulRight_le
        L f ξ 5

    have hPoint :
        ‖VectorFourier.fourierPowSMulRight
            L f ξ 5‖
          ≤
        C * (‖ξ‖ ^ 5 * ‖f ξ‖) := by
      dsimp only [C]
      nlinarith [hOp]

    have hWeightNonneg :
        0 ≤ ‖ξ‖ ^ 5 :=
      pow_nonneg (norm_nonneg ξ) 5

    dsimp only [
      h3SelectedRawFourierFifthRadialWeight,
      f
    ]

    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg hWeightNonneg
    ]

    exact hPoint

  let M2 :
      MeasureTheory.Lp
        (ContinuousMultilinearMap
          ℝ
          (fun _ : Fin 5 => H3FourierPoint3)
          ℂ)
        2
        (volume : Measure H3FourierPoint3) :=
    hPowLp.toLp
      (fun ξ : H3FourierPoint3 =>
        VectorFourier.fourierPowSMulRight
          L f ξ 5)

  let eval :
      ContinuousMultilinearMap
          ℝ
          (fun _ : Fin 5 => H3FourierPoint3)
          ℂ
        →L[ℝ]
      ℂ :=
    ContinuousMultilinearMap.apply
      ℝ
      (fun _ : Fin 5 => H3FourierPoint3)
      ℂ
      m

  let E2 :
      MeasureTheory.Lp
        ℂ
        2
        (volume : Measure H3FourierPoint3) :=
    eval.compLp M2

  have hM2 :
      ((M2 :
          MeasureTheory.Lp
            (ContinuousMultilinearMap
              ℝ
              (fun _ : Fin 5 => H3FourierPoint3)
              ℂ)
            2
            (volume : Measure H3FourierPoint3)) :
        H3FourierPoint3 →
          ContinuousMultilinearMap
            ℝ
            (fun _ : Fin 5 => H3FourierPoint3)
            ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        VectorFourier.fourierPowSMulRight
          L f ξ 5) := by
    dsimp only [M2]
    exact
      MeasureTheory.MemLp.coeFn_toLp hPowLp

  have hE2 :
      ((E2 :
          MeasureTheory.Lp
            ℂ
            2
            (volume : Measure H3FourierPoint3)) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        eval
          (((M2 :
              MeasureTheory.Lp
                (ContinuousMultilinearMap
                  ℝ
                  (fun _ : Fin 5 => H3FourierPoint3)
                  ℂ)
                2
                (volume : Measure H3FourierPoint3)) :
            H3FourierPoint3 →
              ContinuousMultilinearMap
                ℝ
                (fun _ : Fin 5 => H3FourierPoint3)
                ℂ) ξ)) := by
    dsimp only [E2]
    exact
      ContinuousLinearMap.coeFn_compLp
        eval M2

  have hAE :
      (fun ξ : H3FourierPoint3 =>
        (VectorFourier.fourierPowSMulRight
          L f ξ 5) m)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      ((E2 :
          MeasureTheory.Lp
            ℂ
            2
            (volume : Measure H3FourierPoint3)) :
        H3FourierPoint3 → ℂ) := by
    filter_upwards [hM2, hE2] with ξ hξM hξE

    calc
      (VectorFourier.fourierPowSMulRight
          L f ξ 5) m
          =
        eval
          (VectorFourier.fourierPowSMulRight
            L f ξ 5) := by
            rfl
      _ =
        eval
          (((M2 :
              MeasureTheory.Lp
                (ContinuousMultilinearMap
                  ℝ
                  (fun _ : Fin 5 => H3FourierPoint3)
                  ℂ)
                2
                (volume : Measure H3FourierPoint3)) :
            H3FourierPoint3 →
              ContinuousMultilinearMap
                ℝ
                (fun _ : Fin 5 => H3FourierPoint3)
                ℂ) ξ) := by
            rw [hξM]
      _ =
        ((E2 :
            MeasureTheory.Lp
              ℂ
              2
              (volume : Measure H3FourierPoint3)) :
          H3FourierPoint3 → ℂ) ξ :=
            hξE.symm

  have hE2Lp :
      MemLp
        ((E2 :
            MeasureTheory.Lp
              ℂ
              2
              (volume : Measure H3FourierPoint3)) :
          H3FourierPoint3 → ℂ)
        2
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.Lp.memLp E2

  exact
    (memLp_congr_ae hAE).2 hE2Lp

/-! ## Radial selected high-frequency L² frontier -/

/--
At every strict positive selected restart time, the fourth and fifth radial
weights of every raw Fourier coordinate belong to complex `L²`.
-/
def H3CanonicalSelectedFourthFifthRadialRawFourierMemLp2OnRestartRadius : Prop :=
  ∀
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t₀ : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E),
      ∀ q : ℝ,
        q ∈
          Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E) →
        let U₀ : H3SpectralVelocityState :=
          h3PreterminalSelectedDecoderAnchorState
            hNS ht₀ hTail
        let hA : 0 < E :=
          lt_of_lt_of_le zero_lt_one hE
        let hU₀ : ‖U₀‖ ≤ E :=
          norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            (one_pos : (0 : ℝ) < 1)
            U₀ hA hU₀
        (
          ∀ j : Fin 3,
            MemLp
              (h3SelectedRawFourierFourthRadialWeight
                (W q j))
              2
              (volume : Measure H3FourierPoint3)
        )
          ∧
        (
          ∀ j : Fin 3,
            MemLp
              (h3SelectedRawFourierFifthRadialWeight
                (W q j))
              2
              (volume : Measure H3FourierPoint3)
        )

/-! ## Radial L² closes every ordered coordinate multiplier -/

theorem h3CanonicalSelectedFourthFifthRawCoordinateMultiplierMemLp2OnRestartRadius_of_radial
    (hRadial :
      H3CanonicalSelectedFourthFifthRadialRawFourierMemLp2OnRestartRadius) :
    H3CanonicalSelectedFourthFifthRawCoordinateMultiplierMemLp2OnRestartRadius := by

  intro E u T t₀ hNS ht₀ hE hTail q hq

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀

  have hR :=
    hRadial E u T t₀ hNS ht₀ hE hTail q hq

  dsimp only at hR ⊢

  constructor

  · intro a b c d j

    let H : H3SpectralScalarState :=
      W q j

    have hFourthInt :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 4 *
              ‖h3SpectralScalarRawFourier H ξ‖)
          (volume : Measure H3FourierPoint3) := by
      dsimp only [H, W, U₀, hA, hU₀]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
          4
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState
            hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
          hq.1
          hq.2.le
          j

    let m : Fin 4 → H3FourierPoint3 :=
      ![
        h3FourierAxisDirection a,
        h3FourierAxisDirection b,
        h3FourierAxisDirection c,
        h3FourierAxisDirection d
      ]

    have hEval :=
      memLp_fourierPowSMulRight_eval_four_of_radial
        H
        hFourthInt
        (by
          dsimp only [H, W, U₀, hA, hU₀]
          exact hR.1 j)
        m

    dsimp only [
      h3SelectedFourthFrechetRawCoordinateMultiplier,
      m
    ] at hEval ⊢

    exact hEval

  · intro a b c d e j

    let H : H3SpectralScalarState :=
      W q j

    have hFifthInt :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 5 *
              ‖h3SpectralScalarRawFourier H ξ‖)
          (volume : Measure H3FourierPoint3) := by
      dsimp only [H, W, U₀, hA, hU₀]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
          5
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState
            hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
          hq.1
          hq.2.le
          j

    let m : Fin 5 → H3FourierPoint3 :=
      ![
        h3FourierAxisDirection a,
        h3FourierAxisDirection b,
        h3FourierAxisDirection c,
        h3FourierAxisDirection d,
        h3FourierAxisDirection e
      ]

    have hEval :=
      memLp_fourierPowSMulRight_eval_five_of_radial
        H
        hFifthInt
        (by
          dsimp only [H, W, U₀, hA, hU₀]
          exact hR.2 j)
        m

    dsimp only [
      h3SelectedFifthFrechetRawCoordinateMultiplier,
      m
    ] at hEval ⊢

    exact hEval

/-! ## BKM closure at the radial weighted raw-Fourier frontier -/

theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_selectedRadialFourthFifthRawFourier_of_transportPressure_of_fullScalarEnergy
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hRadial :
      H3CanonicalSelectedFourthFifthRadialRawFourierMemLp2OnRestartRadius)
    (hTP :
      H3PathEnergyClassProducesTransportPressureMemLp2)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_selectedRawCoordinateMultiplier_of_transportPressure_of_fullScalarEnergy
      hLow
      hDerivative
      (h3CanonicalSelectedFourthFifthRawCoordinateMultiplierMemLp2OnRestartRadius_of_radial
        hRadial)
      hTP
      hFull

end

end Euclidean
end Bridge
end PrimeTensor
