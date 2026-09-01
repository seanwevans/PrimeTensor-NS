import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.CubicTimeContinuity

/-!
# Classicalization: quadratic weighted-Fourier time continuity

The cubic weighted-Fourier difference of the selected restart is already
continuous in time.  For the Hessian continuity needed by the temporal
derivative frontier, only the quadratic weighted topology is required.

No new interpolation scale is needed.  Pointwise,

    ‖ξ‖² ≤ 1 + ‖ξ‖³,

so for any spectral difference with finite cubic moment,

    M₂(H) ≤ m₀(H) + M₃(H).

The raw `L¹` mass is bounded by the ambient H³ norm,

    m₀(H) ≤ C_dw ‖H‖.

Hence along the selected restart,

    M₂(W(r) - W(s))
      ≤ C_dw ‖W(r) - W(s)‖ + M₃(W(r) - W(s)).

The first term tends to zero by H³ continuity and the second by the already
closed cubic time-continuity theorem.  This gives the quadratic Fourier
topology required for pointwise continuity of second spatial derivatives.

No new Navier--Stokes, heat-kernel, or endpoint estimate occurs here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

/-- Keep `H3FourierPoint3`, its norm, and `volume` definitionally aligned with
the generic moment algebra and with the cubic continuity layer. -/
noncomputable local instance axisFintypeH3SchwartzClassicalizationQuadraticTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- Elementary comparison between the quadratic and cubic frequency weights. -/
theorem norm_pow_two_le_one_add_pow_three
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 2 ≤ 1 + ‖ξ‖ ^ 3 := by
  have hx0 : 0 ≤ ‖ξ‖ := norm_nonneg ξ
  by_cases hx1 : ‖ξ‖ ≤ 1
  · have hsq : ‖ξ‖ ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg ‖ξ‖]
    have hcube0 : 0 ≤ ‖ξ‖ ^ 3 :=
      pow_nonneg hx0 3
    linarith
  · have hx1' : 1 ≤ ‖ξ‖ :=
      le_of_lt (lt_of_not_ge hx1)
    have hsq0 : 0 ≤ ‖ξ‖ ^ 2 :=
      pow_nonneg hx0 2
    have hmul0 :=
      mul_le_mul_of_nonneg_left hx1' hsq0
    have hmul :
        ‖ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 * ‖ξ‖ := by
      simpa only [mul_one] using hmul0
    have hcube :
        ‖ξ‖ ^ 2 ≤ ‖ξ‖ ^ 3 := by
      calc
        ‖ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 * ‖ξ‖ := hmul
        _ = ‖ξ‖ ^ 3 := by ring
    exact le_add_of_nonneg_of_le zero_le_one hcube

/-- A finite cubic raw Fourier moment controls the quadratic moment by the
unweighted raw `L¹` mass plus the cubic mass. -/
theorem h3SpectralScalarRawFourierMomentMass_two_le_L1Mass_add_three
    (H : H3SpectralScalarState)
    (hH3 : H3RawFourierMomentIntegrable (3 : ℝ) H) :
    h3SpectralScalarRawFourierMomentMass (2 : ℝ) H
      ≤
    h3SpectralScalarRawFourierL1Mass H
      +
    h3SpectralScalarRawFourierMomentMass (3 : ℝ) H := by
  have hWeight2 :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (2 : ℝ) ξ = ‖ξ‖ ^ 2 := by
    intro ξ
    exact h3FourierMomentWeight_natCast 2 ξ

  have hWeight3 :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (3 : ℝ) ξ = ‖ξ‖ ^ 3 := by
    intro ξ
    exact h3FourierMomentWeight_natCast 3 ξ

  have hRaw0 :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 H)

  have hRaw :
      Integrable
        (h3SpectralScalarRawFourier H)
        (volume : Measure H3FourierPoint3) := by
    simpa only [
      axisFintypeH3SchwartzClassicalizationQuadraticTimeContinuity,
      axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
      axisFintypeH3SpectralL1,
      axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
    ] using hRaw0

  have hRawNorm :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hRaw.norm

  have hH3' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    unfold H3RawFourierMomentIntegrable at hH3
    refine hH3.congr ?_
    filter_upwards with ξ
    rw [hWeight3 ξ]

  let major : H3FourierPoint3 → ℝ :=
    fun ξ =>
      ‖h3SpectralScalarRawFourier H ξ‖
        +
      ‖ξ‖ ^ 3 * ‖h3SpectralScalarRawFourier H ξ‖

  have hMajor :
      Integrable major
        (volume : Measure H3FourierPoint3) := by
    dsimp only [major]
    exact hRawNorm.add hH3'

  have hLeftMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      ((continuous_norm.pow 2).aestronglyMeasurable.mul
        hRawNorm.aestronglyMeasurable)

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarRawFourier H ξ‖
          ≤
        major ξ := by
    intro ξ
    have hWeight :=
      norm_pow_two_le_one_add_pow_three ξ
    have hNorm0 :
        0 ≤ ‖h3SpectralScalarRawFourier H ξ‖ :=
      norm_nonneg _
    have hMul :=
      mul_le_mul_of_nonneg_right hWeight hNorm0
    dsimp only [major]
    calc
      ‖ξ‖ ^ 2 *
          ‖h3SpectralScalarRawFourier H ξ‖
          ≤
        (1 + ‖ξ‖ ^ 3) *
          ‖h3SpectralScalarRawFourier H ξ‖ :=
        hMul
      _ =
        ‖h3SpectralScalarRawFourier H ξ‖
          +
        ‖ξ‖ ^ 3 *
          ‖h3SpectralScalarRawFourier H ξ‖ := by
        ring

  have hLeft :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    refine hMajor.mono' hLeftMeas ?_
    filter_upwards with ξ
    have hNonneg :
        0 ≤
          ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarRawFourier H ξ‖ :=
      mul_nonneg
        (pow_nonneg (norm_nonneg ξ) 2)
        (norm_nonneg _)
    simpa only [
      Real.norm_eq_abs,
      abs_of_nonneg hNonneg
    ] using hPoint ξ

  have hInt :
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3SpectralScalarRawFourier H ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3, major ξ := by
    apply integral_mono_ae hLeft hMajor
    filter_upwards with ξ
    exact hPoint ξ

  have hMass2 :
      h3SpectralScalarRawFourierMomentMass (2 : ℝ) H
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3SpectralScalarRawFourier H ξ‖ := by
    unfold h3SpectralScalarRawFourierMomentMass
    apply integral_congr_ae
    filter_upwards with ξ
    rw [hWeight2 ξ]

  have hMass3 :
      h3SpectralScalarRawFourierMomentMass (3 : ℝ) H
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3SpectralScalarRawFourier H ξ‖ := by
    unfold h3SpectralScalarRawFourierMomentMass
    apply integral_congr_ae
    filter_upwards with ξ
    rw [hWeight3 ξ]

  have hMass0 :
      h3SpectralScalarRawFourierL1Mass H
        =
      ∫ ξ : H3FourierPoint3,
        ‖h3SpectralScalarRawFourier H ξ‖ := by
    unfold h3SpectralScalarRawFourierL1Mass
    simp only [
      axisFintypeH3SchwartzClassicalizationQuadraticTimeContinuity,
      axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
      axisFintypeH3SpectralL1,
      axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
    ]

  have hMajorIntegral :
      (∫ ξ : H3FourierPoint3, major ξ)
        =
      h3SpectralScalarRawFourierL1Mass H
        +
      h3SpectralScalarRawFourierMomentMass (3 : ℝ) H := by
    dsimp only [major]
    rw [integral_add hRawNorm hH3']
    rw [hMass0, hMass3]

  rw [hMass2]
  rw [hMajorIntegral] at hInt
  exact hInt

/-- Cubic moment integrability is preserved by subtraction. -/
theorem h3RawFourierMomentIntegrable_three_sub
    (F G : H3SpectralScalarState)
    (hF3 : H3RawFourierMomentIntegrable (3 : ℝ) F)
    (hG3 : H3RawFourierMomentIntegrable (3 : ℝ) G) :
    H3RawFourierMomentIntegrable (3 : ℝ) (F - G) := by
  have hWeight3 :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (3 : ℝ) ξ = ‖ξ‖ ^ 3 := by
    intro ξ
    exact h3FourierMomentWeight_natCast 3 ξ

  have hRawSubAE0 :=
    h3SpectralScalarRawFourier_sub_ae F G

  have hRawSubAE :
      h3SpectralScalarRawFourier (F - G)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ) := by
    simpa only [
      axisFintypeH3SchwartzClassicalizationQuadraticTimeContinuity,
      axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
      axisFintypeH3SpectralL1,
      axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
    ] using hRawSubAE0

  have hF3' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖h3SpectralScalarRawFourier F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    unfold H3RawFourierMomentIntegrable at hF3
    refine hF3.congr ?_
    filter_upwards with ξ
    rw [hWeight3 ξ]

  have hG3' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3) := by
    unfold H3RawFourierMomentIntegrable at hG3
    refine hG3.congr ?_
    filter_upwards with ξ
    rw [hWeight3 ξ]

  let major : H3FourierPoint3 → ℝ :=
    fun ξ =>
      ‖ξ‖ ^ 3 * ‖h3SpectralScalarRawFourier F ξ‖
        +
      ‖ξ‖ ^ 3 * ‖h3SpectralScalarRawFourier G ξ‖

  have hMajor :
      Integrable major
        (volume : Measure H3FourierPoint3) := by
    dsimp only [major]
    exact hF3'.add hG3'

  have hRawSub0 :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 (F - G))

  have hRawSub :
      Integrable
        (h3SpectralScalarRawFourier (F - G))
        (volume : Measure H3FourierPoint3) := by
    simpa only [
      axisFintypeH3SchwartzClassicalizationQuadraticTimeContinuity,
      axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
      axisFintypeH3SpectralL1,
      axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
    ] using hRawSub0

  have hLeftMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier (F - G) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      ((continuous_norm.pow 3).aestronglyMeasurable.mul
        hRawSub.norm.aestronglyMeasurable)

  have hOrdinary :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier (F - G) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    refine hMajor.mono' hLeftMeas ?_
    exact hRawSubAE.mono (fun ξ hξ => by
      dsimp only [major]
      rw [hξ]
      have hNormSub :=
        norm_sub_le
          (h3SpectralScalarRawFourier F ξ)
          (h3SpectralScalarRawFourier G ξ)
      have hPow0 : 0 ≤ ‖ξ‖ ^ 3 :=
        pow_nonneg (norm_nonneg ξ) 3
      have hMul :=
        mul_le_mul_of_nonneg_left hNormSub hPow0
      have hNonneg :
          0 ≤
            ‖ξ‖ ^ 3 *
              ‖h3SpectralScalarRawFourier F ξ -
                h3SpectralScalarRawFourier G ξ‖ :=
        mul_nonneg hPow0 (norm_nonneg _)
      simpa only [
        Real.norm_eq_abs,
        abs_of_nonneg hNonneg,
        mul_add
      ] using hMul)

  unfold H3RawFourierMomentIntegrable
  refine hOrdinary.congr ?_
  filter_upwards with ξ
  rw [hWeight3 ξ]

/-- Every selected coordinate is continuous in the quadratic weighted raw
Fourier difference topology at each strict positive interior restart time. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_quadraticDifferenceMass_tendsto_zero
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Tendsto
      (fun r : ℝ =>
        h3SpectralScalarRawFourierMomentMass
          (2 : ℝ)
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ r i
            -
            h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ s i))
      (𝓝 s)
      (𝓝 0) := by
  let R₀ : ℝ := h3FinHeatLerayRestartRadius ν A
  let a : ℝ := s / 2
  let b : ℝ := (s + R₀) / 2

  have hR₀ : 0 < R₀ := by
    dsimp only [R₀]
    exact h3FinHeatLerayRestartRadius_pos ν hA

  have hsR₀ : s < R₀ := by
    simpa only [R₀] using hsR

  have ha : 0 < a := by
    dsimp only [a]
    linarith

  have has : a < s := by
    dsimp only [a]
    linarith

  have hsb : s < b := by
    dsimp only [b]
    linarith

  have hab : a ≤ b :=
    le_trans has.le hsb.le

  have hbR₀ : b ≤ R₀ := by
    dsimp only [b]
    linarith

  obtain ⟨BState, BDuhamel, B0, hSlab⟩ :=
    h3SelectedMomentSlab_nat_ge_three
      (ν := ν)
      (A := A)
      (a := a)
      (t := b)
      3 (by norm_num)
      hν U₀ hA hU₀
      ha hab hbR₀

  unfold H3SelectedMomentSlab at hSlab
  rcases hSlab with ⟨_hBState0, _hBDuhamel0, _hB00, hData⟩

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hWcont : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hCoordCont :
      Continuous (fun r : ℝ => W r i) :=
    (continuous_apply i).comp hWcont

  have hDiffCont :
      ContinuousAt
        (fun r : ℝ => W r i - W s i)
        s :=
    hCoordCont.continuousAt.sub continuousAt_const

  have hNormTendsto :
      Tendsto
        (fun r : ℝ => ‖W r i - W s i‖)
        (𝓝 s)
        (𝓝 0) := by
    have hNormCont :=
      hDiffCont.norm
    change
      Tendsto
        (fun r : ℝ => ‖W r i - W s i‖)
        (𝓝 s)
        (𝓝 ‖W s i - W s i‖)
      at hNormCont
    simpa only [sub_self, norm_zero] using hNormCont

  let C : ℝ :=
    h3RawFourierL1DeweightingCoefficient

  have hScaled :
      Tendsto
        (fun r : ℝ =>
          C * ‖W r i - W s i‖)
        (𝓝 s)
        (𝓝 0) := by
    have hConst :
        Tendsto
          (fun _ : ℝ => C)
          (𝓝 s)
          (𝓝 C) :=
      tendsto_const_nhds
    have h := hConst.mul hNormTendsto
    simpa only [mul_zero] using h

  have hCubic :
      Tendsto
        (fun r : ℝ =>
          h3SpectralScalarRawFourierMomentMass
            (3 : ℝ) (W r i - W s i))
        (𝓝 s)
        (𝓝 0) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_cubicDifferenceMass_tendsto_zero
        hν U₀ hA hU₀ hs hsR i

  have hUpper :
      Tendsto
        (fun r : ℝ =>
          C * ‖W r i - W s i‖
            +
          h3SpectralScalarRawFourierMomentMass
            (3 : ℝ) (W r i - W s i))
        (𝓝 s)
        (𝓝 0) := by
    simpa only [add_zero] using hScaled.add hCubic

  have hThree : (((3 : ℕ) : ℝ)) = (3 : ℝ) := by
    norm_num

  have hThirdInt :
      ∀ r ∈ Set.Icc a b,
        H3RawFourierMomentIntegrable
          (3 : ℝ) (W r i) := by
    intro r hr
    have hAt := hData r hr i
    dsimp only at hAt
    rw [hThree] at hAt
    simpa only [W] using hAt.1

  have hsIcc : s ∈ Set.Icc a b :=
    ⟨has.le, hsb.le⟩

  have hsThird :
      H3RawFourierMomentIntegrable
        (3 : ℝ) (W s i) :=
    hThirdInt s hsIcc

  have hInterval :
      Set.Ioo a b ∈ 𝓝 s :=
    Ioo_mem_nhds has hsb

  have hUpperBound :
      ∀ᶠ r in 𝓝 s,
        h3SpectralScalarRawFourierMomentMass
            (2 : ℝ) (W r i - W s i)
          ≤
        C * ‖W r i - W s i‖
          +
        h3SpectralScalarRawFourierMomentMass
          (3 : ℝ) (W r i - W s i) := by
    filter_upwards [hInterval] with r hr

    have hrIcc : r ∈ Set.Icc a b :=
      ⟨hr.1.le, hr.2.le⟩

    have hrThird :
        H3RawFourierMomentIntegrable
          (3 : ℝ) (W r i) :=
      hThirdInt r hrIcc

    have hDiffThird :=
      h3RawFourierMomentIntegrable_three_sub
        (W r i) (W s i) hrThird hsThird

    have hTwo :=
      h3SpectralScalarRawFourierMomentMass_two_le_L1Mass_add_three
        (W r i - W s i) hDiffThird

    have hLow :=
      h3SpectralScalarRawFourierL1Mass_le_norm
        (W r i - W s i)

    dsimp only [C]

    exact
      hTwo.trans
        (add_le_add
          hLow
          (le_refl
            (h3SpectralScalarRawFourierMomentMass
              (3 : ℝ) (W r i - W s i))))

  refine tendsto_order.2 ⟨?_, ?_⟩

  · intro c hc
    exact Filter.Eventually.of_forall (fun r =>
      lt_of_lt_of_le hc
        (h3SpectralScalarRawFourierMomentMass_nonneg
          (2 : ℝ) (W r i - W s i)))

  · intro ε hε
    have hUpperEventually :=
      (tendsto_order.1 hUpper).2 ε hε

    filter_upwards [hUpperBound, hUpperEventually] with r hrBound hrUpper

    exact lt_of_le_of_lt hrBound hrUpper

end
end Euclidean
end Bridge
end PrimeTensor
