import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Quintic.Difference.Interpolation

/-!
# Classicalization: quintic weighted-Fourier time continuity

The quintic interpolation estimate turns the selected path's H³ continuity and
one locally uniform sixth-moment bound into continuity in the quintic weighted
raw-Fourier topology.

If a scalar spectral path `F` is H³-continuous at an interior time `s`, and its
sixth raw Fourier moment is integrable and uniformly bounded on a closed
neighborhood `[a,b]` of `s`, then

    M₅(F(r) - F(s)) → 0  as r → s.

The selected-path specialization obtains the local sixth-moment bound from the
generic natural moment slab at order six.

No new PDE estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationQuinticTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- Generic local interpolation principle: H³ continuity plus a locally
uniform sixth raw Fourier moment implies quintic weighted-Fourier continuity. -/
theorem h3SpectralScalarRawFourierMomentMass_five_sub_tendsto_zero_of_continuousAt_of_sixthMoment_bound
    (F : ℝ → H3SpectralScalarState)
    {a s b B : ℝ}
    (has : a < s)
    (hsb : s < b)
    (hB0 : 0 ≤ B)
    (hF : ContinuousAt F s)
    (hSixthInt :
      ∀ r ∈ Set.Icc a b,
        H3RawFourierMomentIntegrable (6 : ℝ) (F r))
    (hSixthBound :
      ∀ r ∈ Set.Icc a b,
        h3SpectralScalarRawFourierMomentMass (6 : ℝ) (F r) ≤ B) :
    Tendsto
      (fun r : ℝ =>
        h3SpectralScalarRawFourierMomentMass
          (5 : ℝ) (F r - F s))
      (𝓝 s)
      (𝓝 0) := by
  have hsIcc : s ∈ Set.Icc a b :=
    ⟨has.le, hsb.le⟩

  have hsSixthInt :
      H3RawFourierMomentIntegrable (6 : ℝ) (F s) :=
    hSixthInt s hsIcc

  have hsSixthBound :
      h3SpectralScalarRawFourierMomentMass (6 : ℝ) (F s) ≤ B :=
    hSixthBound s hsIcc

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
          (5 : ℝ) (F r - F s)))

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
      R ^ 5 * h3RawFourierL1DeweightingCoefficient

    have hC0 : 0 ≤ C := by
      dsimp only [C]
      exact
        mul_nonneg
          (pow_nonneg hR.le 5)
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

    have hrSixthInt :
        H3RawFourierMomentIntegrable (6 : ℝ) (F r) :=
      hSixthInt r hrIcc

    have hrSixthBound :
        h3SpectralScalarRawFourierMomentMass (6 : ℝ) (F r) ≤ B :=
      hSixthBound r hrIcc

    have hInterp :=
      h3SpectralScalarRawFourierMomentMass_five_sub_le_norm
        (F r) (F s) hR hrSixthInt hsSixthInt

    have hηEq :
        (C + 1) * η = ε / 2 := by
      dsimp only [η]
      field_simp [ne_of_gt hC1] <;> ring

    have hLow :
        (R ^ 5 * h3RawFourierL1DeweightingCoefficient) *
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
            (h3SpectralScalarRawFourierMomentMass (6 : ℝ) (F r) +
              h3SpectralScalarRawFourierMomentMass (6 : ℝ) (F s))
          < ε / 2 := by
      apply lt_of_le_of_lt _ hTailBudget
      exact
        mul_le_mul_of_nonneg_left
          (add_le_add hrSixthBound hsSixthBound)
          hInv0

    have hMassLt :
        h3SpectralScalarRawFourierMomentMass
            (5 : ℝ) (F r - F s)
          < ε := by
      calc
        h3SpectralScalarRawFourierMomentMass
            (5 : ℝ) (F r - F s)
            ≤
          (R ^ 5 * h3RawFourierL1DeweightingCoefficient) *
              ‖F r - F s‖
            +
          R⁻¹ *
            (h3SpectralScalarRawFourierMomentMass (6 : ℝ) (F r) +
              h3SpectralScalarRawFourierMomentMass (6 : ℝ) (F s)) :=
          hInterp
        _ < ε / 2 + ε / 2 :=
          add_lt_add hLow hTail
        _ = ε := by ring

    exact hMassLt

/-- Every coordinate of the selected canonical restart path is continuous in
the quintic weighted raw-Fourier difference topology at each strict positive
interior time of the restart interval. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_quinticDifferenceMass_tendsto_zero
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
          (5 : ℝ)
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
      6 (by norm_num)
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

  have hSix : (((6 : ℕ) : ℝ)) = (6 : ℝ) := by
    norm_num

  have hSixthInt :
      ∀ r ∈ Set.Icc a b,
        H3RawFourierMomentIntegrable (6 : ℝ) (W r i) := by
    intro r hr
    have hAt := hData r hr i
    dsimp only at hAt
    rw [hSix] at hAt
    simpa only [W] using hAt.1

  have hSixthBound :
      ∀ r ∈ Set.Icc a b,
        h3SpectralScalarRawFourierMomentMass (6 : ℝ) (W r i) ≤ BState := by
    intro r hr
    have hAt := hData r hr i
    dsimp only at hAt
    rw [hSix] at hAt
    simpa only [W] using hAt.2.1

  have hGeneric :=
    h3SpectralScalarRawFourierMomentMass_five_sub_tendsto_zero_of_continuousAt_of_sixthMoment_bound
      (F := fun r : ℝ => W r i)
      (a := a)
      (s := s)
      (b := b)
      (B := BState)
      has hsb hBState0
      hCoordCont.continuousAt
      hSixthInt
      hSixthBound

  simpa only [W] using hGeneric

end
end Euclidean
end Bridge
end PrimeTensor
