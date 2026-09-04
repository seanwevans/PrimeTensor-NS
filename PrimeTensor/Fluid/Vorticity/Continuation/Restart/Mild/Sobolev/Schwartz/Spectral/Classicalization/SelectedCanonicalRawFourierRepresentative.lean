import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVariationOfConstantsStateClosure

/-!
# Classicalization: canonical raw Fourier representative of the selected restart state

The selected restart path now satisfies the signed H³ mild identity directly,
without any pointwise Fourier hypotheses.

Pointwise evaluation of an arbitrary `L²` representative is still not a
legitimate way to recover time continuity or the Fourier-mode ODE.  Instead,
this file chooses the explicit representative naturally supplied by the mild
formula:

    heat raw representative
      -
    source-integrated raw Fourier Duhamel amplitude.

The heat term already represents exact H³ deweighting of weighted spectral heat
evolution almost everywhere.  The Duhamel amplitude already represents exact
H³ deweighting of the Banach-valued Duhamel state almost everywhere.  Applying
the continuous linear deweighting map to the selected H³ mild identity and
combining those representative theorems therefore identifies the explicit
formula with the selected state's ordinary raw Fourier representative almost
everywhere.

This is deliberately an almost-everywhere statement.  It does not claim that
the arbitrary `L²` representative chosen by `h3SpectralScalarRawFourier` has
pointwise-in-time regularity.  Subsequent pointwise classicalization can work
with this canonical explicit representative instead.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedCanonicalRawFourierRepresentative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The modern canonical restart-radius physical extension is globally
continuous as an H³-valued path. -/
theorem continuous_h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A) :
    Continuous
      (h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
        hν U₀ hA hU₀) := by
  unfold h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
  exact
    continuous_h3PathPhysicalRealExtension
      (h3FinHeatLerayRestartRadius ν A)
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadius
        hν U₀ hA hU₀)

/-- Every slice of the globally clamped canonical restart extension retains the
fixed-point ball bound `2A`. -/
theorem norm_h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_le_twoA
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (s : ℝ) :
    ‖h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ s‖
      ≤
    2 * A := by
  change
    ‖h3SpectralFinHeatLerayMildSolutionAtRestartRadius
        hν U₀ hA hU₀
        (h3ClampUnitTime
          (s / h3FinHeatLerayRestartRadius ν A))‖
      ≤
    2 * A
  exact
    norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadius_apply_le_twoA
      hν U₀ hA hU₀
      (h3ClampUnitTime
        (s / h3FinHeatLerayRestartRadius ν A))

/-- Canonical explicit raw Fourier representative associated with the selected
restart mild formula. -/
noncomputable def h3SpectralFinHeatLerayRestartRadiusCanonicalRawFourier
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (t : ℝ)
    (i : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  h3SpectralScalarHeatRawRepresentative
      ν t (U₀ i) ξ
    -
  h3SpectralFinHeatLerayDuhamelRawFourierAmplitude
    ν t
    (h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
      hν U₀ hA hU₀)
    (h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
      hν U₀ hA hU₀)
    i ξ

/-- At every strict positive time in the canonical restart interval, the
explicit heat-minus-Duhamel raw formula is an almost-everywhere representative
of the selected weighted H³ state after exact deweighting. -/
theorem h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_rawFourier_ae_eq_canonical
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    h3SpectralScalarRawFourier
        ((h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
          hν U₀ hA hU₀) t i)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3SpectralFinHeatLerayRestartRadiusCanonicalRawFourier
      hν U₀ hA hU₀ t i := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let H : H3SpectralScalarState :=
    h3SpectralScalarHeatApplyNN
      ν hν.le (NNReal.mk t ht.le) (U₀ i)

  let D : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel
      ν t hν W W i

  have hWcont : Continuous W := by
    simpa only [W] using
      continuous_h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hWbound :
      ∀ s : ℝ, ‖W s‖ ≤ 2 * A := by
    intro s
    simpa only [W] using
      norm_h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_le_twoA
        hν U₀ hA hU₀ s

  have hM : 0 ≤ 2 * A := by
    positivity

  have hState :
      W t
        =
      h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk t ht.le) U₀
        -
      h3SpectralFinHeatLerayDuhamel
        ν t hν W W := by
    simpa only [W] using
      h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_variationOfConstants_state
        hν U₀ hA hU₀ ht.le htR

  have hCoordinate :
      W t i = H - D := by
    have h := congrFun hState i
    simpa only [
      H,
      D,
      h3SpectralVelocityHeatApplyNN_apply,
      Pi.sub_apply
    ] using h

  have hRawL2 :
      h3SpectralScalarRawFourierL2 (W t i)
        =
      h3SpectralScalarRawFourierL2 H
        -
      h3SpectralScalarRawFourierL2 D := by
    rw [hCoordinate]
    simpa only [h3SpectralScalarRawFourierL2CLM_apply] using
      h3SpectralScalarRawFourierL2CLM.map_sub H D

  have hFinal :=
    h3SpectralScalarRawFourierL2_ae (W t i)

  rw [hRawL2] at hFinal

  have hHeat :
      ((h3SpectralScalarRawFourierL2 H :
          H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralScalarHeatRawRepresentative
        ν t (U₀ i) := by
    dsimp only [H]
    exact
      h3SpectralScalarRawFourierL2_heatApplyNN_ae_rawRepresentative
        hν ht (U₀ i)

  have hDuhamel :
      ((h3SpectralScalarRawFourierL2 D :
          H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralFinHeatLerayDuhamelRawFourierAmplitude
        ν t W W i := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamel_rawFourierL2_ae_eq_rawAmplitude
        hν ht.le hM hM W W
        hWcont hWcont hWbound hWbound i

  have hSub :=
    MeasureTheory.Lp.coeFn_sub
      (h3SpectralScalarRawFourierL2 H)
      (h3SpectralScalarRawFourierL2 D)

  filter_upwards [
    hFinal,
    hHeat,
    hDuhamel,
    hSub
  ] with ξ hFinalξ hHeatξ hDuhamelξ hSubξ

  simp only [Pi.sub_apply] at hSubξ

  calc
    h3SpectralScalarRawFourier (W t i) ξ
        =
      (((h3SpectralScalarRawFourierL2 H
          -
        h3SpectralScalarRawFourierL2 D :
          H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) ξ) := hFinalξ.symm
    _ =
      ((h3SpectralScalarRawFourierL2 H :
          H3FourierPoint3 → ℂ) ξ)
        -
      ((h3SpectralScalarRawFourierL2 D :
          H3FourierPoint3 → ℂ) ξ) := hSubξ
    _ =
      h3SpectralScalarHeatRawRepresentative
          ν t (U₀ i) ξ
        -
      h3SpectralFinHeatLerayDuhamelRawFourierAmplitude
          ν t W W i ξ := by
      rw [hHeatξ, hDuhamelξ]
    _ =
      h3SpectralFinHeatLerayRestartRadiusCanonicalRawFourier
        hν U₀ hA hU₀ t i ξ := by
      rfl

end

end Euclidean
end Bridge
end PrimeTensor
