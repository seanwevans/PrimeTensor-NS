import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Cubic.Difference.Interpolation

/-!
# Classicalization: cubic weighted-Fourier time continuity

The interpolation estimate from `CubicDifferenceInterpolation` turns the
selected path's H³ continuity and one locally uniform fourth-moment bound into
continuity in the cubic weighted raw-Fourier topology.

The generic theorem below isolates the mechanism.  If a scalar spectral path
`F` is H³-continuous at an interior time `s`, and its fourth raw Fourier moment
is integrable and uniformly bounded on a closed neighborhood `[a,b]` of `s`,
then

    M₃(F(r) - F(s)) → 0  as r → s.

The proof uses the already-compiled estimate

    M₃(F-G)
      ≤ R³ C_dw ‖F-G‖
        + R⁻¹ (M₄(F) + M₄(G)).

For an epsilon, first choose one fixed frequency radius `R` large enough that
the fourth-moment tail is below `ε/2`; then H³ continuity makes the low
frequency term below `ε/2`.

The selected-path specialization obtains the local fourth-moment bound from the
natural moment slab at order four.  Hence every strict interior positive time
of the canonical restart interval has cubic weighted-Fourier time continuity.

No new PDE estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

/-- Keep the norm/measure realization of `H3FourierPoint3` aligned with the
moment algebra and with `CubicDifferenceInterpolation`. -/
noncomputable local instance axisFintypeH3SchwartzClassicalizationCubicTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- Generic local interpolation principle: H³ continuity plus a locally
uniform fourth raw Fourier moment implies cubic weighted-Fourier continuity. -/
theorem h3SpectralScalarRawFourierMomentMass_three_sub_tendsto_zero_of_continuousAt_of_fourthMoment_bound
    (F : ℝ → H3SpectralScalarState)
    {a s b B : ℝ}
    (has : a < s)
    (hsb : s < b)
    (hB0 : 0 ≤ B)
    (hF : ContinuousAt F s)
    (hFourthInt :
      ∀ r ∈ Set.Icc a b,
        H3RawFourierMomentIntegrable (4 : ℝ) (F r))
    (hFourthBound :
      ∀ r ∈ Set.Icc a b,
        h3SpectralScalarRawFourierMomentMass (4 : ℝ) (F r) ≤ B) :
    Tendsto
      (fun r : ℝ =>
        h3SpectralScalarRawFourierMomentMass
          (3 : ℝ) (F r - F s))
      (𝓝 s)
      (𝓝 0) := by
  have hsIcc : s ∈ Set.Icc a b :=
    ⟨has.le, hsb.le⟩

  have hsFourthInt :
      H3RawFourierMomentIntegrable (4 : ℝ) (F s) :=
    hFourthInt s hsIcc

  have hsFourthBound :
      h3SpectralScalarRawFourierMomentMass (4 : ℝ) (F s) ≤ B :=
    hFourthBound s hsIcc

  have hDiffCont :
      ContinuousAt (fun r : ℝ => F r - F s) s :=
    hF.sub continuousAt_const

  have hNormTendsto :
      Tendsto
        (fun r : ℝ => ‖F r - F s‖)
        (𝓝 s)
        (𝓝 0) := by
    have hNormCont :
        ContinuousAt (fun r : ℝ => ‖F r - F s‖) s :=
      hDiffCont.norm
    change
      Tendsto
        (fun r : ℝ => ‖F r - F s‖)
        (𝓝 s)
        (𝓝 ‖F s - F s‖)
      at hNormCont
    simpa only [sub_self, norm_zero] using hNormCont

  refine tendsto_order.2 ⟨?_, ?_⟩

  · intro c hc
    exact Filter.Eventually.of_forall (fun r =>
      lt_of_lt_of_le hc
        (h3SpectralScalarRawFourierMomentMass_nonneg
          (3 : ℝ) (F r - F s)))

  · intro ε hε

    let R : ℝ := 1 + (4 * B) / ε

    have hR : 0 < R := by
      dsimp only [R]
      have hdiv0 : 0 ≤ (4 * B) / ε := by
        exact div_nonneg (mul_nonneg (by norm_num) hB0) hε.le
      linarith

    have hRgt :
        (4 * B) / ε < R := by
      dsimp only [R]
      linarith

    have hBR :
        4 * B < ε * R := by
      have h := (div_lt_iff₀ hε).1 hRgt
      nlinarith

    have hTailBudget :
        R⁻¹ * (B + B) < ε / 2 := by
      rw [inv_mul_eq_div]
      apply (div_lt_iff₀ hR).2
      nlinarith

    let C : ℝ :=
      R ^ 3 * h3RawFourierL1DeweightingCoefficient

    have hC0 : 0 ≤ C := by
      dsimp only [C]
      exact
        mul_nonneg
          (pow_nonneg hR.le 3)
          h3RawFourierL1DeweightingCoefficient_nonneg

    have hC1 : 0 < C + 1 := by
      linarith

    let η : ℝ := ε / (2 * (C + 1))

    have hη : 0 < η := by
      dsimp only [η]
      positivity

    have hNormEventually :
        ∀ᶠ r in 𝓝 s, ‖F r - F s‖ < η :=
      (tendsto_order.1 hNormTendsto).2 η hη

    have hInterval : Set.Ioo a b ∈ 𝓝 s :=
      Ioo_mem_nhds has hsb

    filter_upwards [hInterval, hNormEventually] with r hrIoo hrNorm

    have hrIcc : r ∈ Set.Icc a b :=
      ⟨hrIoo.1.le, hrIoo.2.le⟩

    have hrFourthInt :
        H3RawFourierMomentIntegrable (4 : ℝ) (F r) :=
      hFourthInt r hrIcc

    have hrFourthBound :
        h3SpectralScalarRawFourierMomentMass (4 : ℝ) (F r) ≤ B :=
      hFourthBound r hrIcc

    have hInterp :=
      h3SpectralScalarRawFourierMomentMass_three_sub_le_norm
        (F r) (F s) hR hrFourthInt hsFourthInt

    have hηEq :
        (C + 1) * η = ε / 2 := by
      dsimp only [η]
      field_simp [ne_of_gt hC1] <;> ring

    have hLow :
        (R ^ 3 * h3RawFourierL1DeweightingCoefficient) *
            ‖F r - F s‖
          < ε / 2 := by
      have hCLe : C ≤ C + 1 := by
        linarith
      have hNorm0 : 0 ≤ ‖F r - F s‖ :=
        norm_nonneg _
      have hStep1 :
          C * ‖F r - F s‖
            ≤
          (C + 1) * ‖F r - F s‖ :=
        mul_le_mul_of_nonneg_right hCLe hNorm0
      have hStep2 :
          (C + 1) * ‖F r - F s‖
            <
          (C + 1) * η :=
        mul_lt_mul_of_pos_left hrNorm hC1
      change C * ‖F r - F s‖ < ε / 2
      exact
        lt_of_le_of_lt hStep1
          (hStep2.trans_eq hηEq)

    have hInv0 : 0 ≤ R⁻¹ :=
      inv_nonneg.mpr hR.le

    have hTail :
        R⁻¹ *
            (h3SpectralScalarRawFourierMomentMass (4 : ℝ) (F r) +
              h3SpectralScalarRawFourierMomentMass (4 : ℝ) (F s))
          < ε / 2 := by
      apply lt_of_le_of_lt _ hTailBudget
      exact
        mul_le_mul_of_nonneg_left
          (add_le_add hrFourthBound hsFourthBound)
          hInv0

    have hMassLt :
        h3SpectralScalarRawFourierMomentMass
            (3 : ℝ) (F r - F s)
          < ε := by
      calc
        h3SpectralScalarRawFourierMomentMass
            (3 : ℝ) (F r - F s)
            ≤
          (R ^ 3 * h3RawFourierL1DeweightingCoefficient) *
              ‖F r - F s‖
            +
          R⁻¹ *
            (h3SpectralScalarRawFourierMomentMass (4 : ℝ) (F r) +
              h3SpectralScalarRawFourierMomentMass (4 : ℝ) (F s)) :=
          hInterp
        _ < ε / 2 + ε / 2 :=
          add_lt_add hLow hTail
        _ = ε := by ring

    exact hMassLt

/-- Every coordinate of the selected canonical restart path is continuous in
the cubic weighted raw-Fourier difference topology at each strict positive
interior time of the restart interval. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_cubicDifferenceMass_tendsto_zero
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
          (3 : ℝ)
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

  have hab : a ≤ b := by
    exact le_trans has.le hsb.le

  have hbR₀ : b ≤ R₀ := by
    dsimp only [b]
    linarith

  obtain ⟨BState, BDuhamel, B0, hSlab⟩ :=
    h3SelectedMomentSlab_nat_ge_three
      (ν := ν)
      (A := A)
      (a := a)
      (t := b)
      4 (by norm_num)
      hν U₀ hA hU₀
      ha hab hbR₀

  unfold H3SelectedMomentSlab at hSlab
  rcases hSlab with ⟨hBState0, _hBDuhamel0, _hB00, hData⟩

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hWb :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_continuous_bounded
      hν
      hR₀.le
      U₀
      hA
      hU₀
      (h3FinHeatLerayRestartRadius_smallness ν hA.le)

  have hWcont : Continuous W := by
    simpa only [
      W,
      R₀,
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
    ] using hWb.1

  have hCoordCont : Continuous (fun r : ℝ => W r i) :=
    (continuous_apply i).comp hWcont

  have hFour : (((4 : ℕ) : ℝ)) = (4 : ℝ) := by
    norm_num

  have hFourthInt :
      ∀ r ∈ Set.Icc a b,
        H3RawFourierMomentIntegrable (4 : ℝ) (W r i) := by
    intro r hr
    have hAt := hData r hr i
    dsimp only at hAt
    rw [hFour] at hAt
    simpa only [W] using hAt.1

  have hFourthBound :
      ∀ r ∈ Set.Icc a b,
        h3SpectralScalarRawFourierMomentMass (4 : ℝ) (W r i) ≤ BState := by
    intro r hr
    have hAt := hData r hr i
    dsimp only at hAt
    rw [hFour] at hAt
    simpa only [W] using hAt.2.1

  have hGeneric :=
    h3SpectralScalarRawFourierMomentMass_three_sub_tendsto_zero_of_continuousAt_of_fourthMoment_bound
      (F := fun r : ℝ => W r i)
      (a := a)
      (s := s)
      (b := b)
      (B := BState)
      has hsb hBState0
      hCoordCont.continuousAt
      hFourthInt
      hFourthBound

  simpa only [W] using hGeneric

end
end Euclidean
end Bridge
end PrimeTensor
