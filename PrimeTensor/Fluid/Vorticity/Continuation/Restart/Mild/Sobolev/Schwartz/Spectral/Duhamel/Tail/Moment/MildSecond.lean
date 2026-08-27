import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.FullSecond
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Physical.Solution

/-!
# Second Fourier moment of the selected positive-time mild state

`FullSecond` proves that the complete selected nonlinear Duhamel contribution
has two integrable raw Fourier moments at every positive time in the canonical
restart interval.

The remaining term in the mild fixed-point equation is the free positive-time
heat evolution of the initial state.  The existing heat reconstruction layer
already gives moments through order three for that term.

This file combines those two facts directly at the quotient-safe `L²` level.
For every

    0 < t ≤ h3FinHeatLerayRestartRadius ν A,

the exact selected mild equation

    W(t) = H_t U₀ + D(t)

is pushed through coordinate projection and exact H³ deweighting.  The
pointwise triangle inequality then transfers the order-two Fourier moment from
the heat and Duhamel pieces to the actual named selected state `W(t)`.

This is the positive-time state regularity needed before feeding `W(t)` back
through the quadratic nonlinear forcing.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedMildSecond
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Quotient-safe raw Fourier `L²` state of one coordinate of the free heat
part of the selected mild equation. -/
noncomputable def h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
    {ν t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (ht : 0 < t)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  h3SpectralScalarRawFourierL2
    (h3SpectralScalarHeatApplyNN
      ν hν.le (NNReal.mk t ht.le) (U₀ i))

/-- Coordinate projection followed by deweighting commutes definitionally with
the componentwise spectral velocity heat action. -/
@[simp]
theorem h3SpectralFinCoordinateRawFourierL2CLM_velocityHeatApplyNN
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : NNReal)
    (U : H3SpectralVelocityState)
    (i : Fin 3) :
    h3SpectralFinCoordinateRawFourierL2CLM i
        (h3SpectralVelocityHeatApplyNN ν hν t U)
      =
    h3SpectralScalarRawFourierL2
      (h3SpectralScalarHeatApplyNN ν hν t (U i)) :=
  rfl

/-- The selected free-heat raw Fourier `L²` state is exactly the canonical
positive-time raw heat representative package. -/
theorem h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_eq_heatRepresentativeL2
    {ν t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (ht : 0 < t)
    (i : Fin 3) :
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
        hν U₀ ht i
      =
    h3SpectralScalarHeatRawRepresentativeL2
      ν t hν ht (U₀ i) := by
  unfold h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
  symm
  exact
    h3SpectralScalarHeatRawRepresentativeL2_eq_rawFourierL2_heatApplyNN
      hν ht (U₀ i)

/-- The explicit positive-time heat amplitude is an a.e. representative of
the named free-heat raw Fourier `L²` state. -/
theorem h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_ae_eq_heatRepresentative
    {ν t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (ht : 0 < t)
    (i : Fin 3) :
    ((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
        hν U₀ ht i : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3SpectralScalarHeatRawRepresentative
      ν t (U₀ i) := by
  rw [
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_eq_heatRepresentativeL2
      hν U₀ ht i
  ]
  exact
    h3SpectralScalarHeatRawRepresentativeL2_ae
      (t := t) hν ht (U₀ i)

/-- The named free positive-time heat term has an integrable second raw Fourier
moment. -/
theorem h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_secondMoment_integrable
    {ν t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (ht : 0 < t)
    (i : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 2 *
          ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
              hν U₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hHeat :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarHeatRawRepresentative
              ν t (U₀ i) ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3SpectralScalarHeatRawRepresentative_moment_integrable
      hν ht (U₀ i) 2 (by norm_num)

  have hRep :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_ae_eq_heatRepresentative
      hν U₀ ht i

  have hWeighted :
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 2 *
          ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
              hν U₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 2 *
          ‖h3SpectralScalarHeatRawRepresentative
            ν t (U₀ i) ξ‖) := by
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  exact hHeat.congr hWeighted.symm

/-- Exact selected mild fixed-point equation at a positive physical time inside
the canonical restart interval. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_eq_heat_add_duhamel
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    W t
      =
    h3SpectralVelocityHeatApplyNN
        ν hν.le (NNReal.mk t ht.le) U₀
      +
    h3SpectralFinHeatLerayDuhamel
        ν t hν W W := by
  dsimp only

  let q : Set.Icc (0 : ℝ) (h3FinHeatLerayRestartRadius ν A) :=
    ⟨t, ht.le, htR⟩

  have hMild :=
    h3SpectralFinHeatLerayPhysicalMildSolution_satisfies_mild_at
      (τ := h3FinHeatLerayRestartRadius ν A)
      hν
      (h3FinHeatLerayRestartRadius_pos ν hA).le
      U₀ hA hU₀
      (h3FinHeatLerayRestartRadius_smallness ν hA.le)
      q

  have hqNN :
      h3PhysicalTimePointNN q = NNReal.mk t ht.le := by
    apply Subtype.ext
    rfl

  rw [hqNN] at hMild

  have hMild' :
      h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk t ht.le) U₀
        +
      h3SpectralFinHeatLerayDuhamel
          ν t hν
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀)
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀)
        =
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ t := by
    simpa only [
      q,
      h3SpectralFinHeatLerayPhysicalMildSolution_apply,
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
    ] using hMild

  exact hMild'.symm

/-- Quotient-safe raw Fourier `L²` state of one coordinate of the actual
selected mild solution at physical time `t`. -/
noncomputable def h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (t : ℝ)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  h3SpectralFinCoordinateRawFourierL2CLM i
    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀ t)

/-- Exact heat-plus-Duhamel decomposition after coordinate projection and H³
deweighting. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_eq_heat_add_duhamel
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
        hν U₀ hA hU₀ t i
      =
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
        hν U₀ ht i
      +
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
        (t := t) hν U₀ hA hU₀ i := by
  have hMild :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_eq_heat_add_duhamel
      hν U₀ hA hU₀ ht htR

  have hMap :=
    congrArg
      (h3SpectralFinCoordinateRawFourierL2CLM i)
      hMild

  rw [map_add] at hMap
  rw [h3SpectralFinCoordinateRawFourierL2CLM_velocityHeatApplyNN] at hMap

  simpa only [
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2,
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2,
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2,
    h3SpectralFinCoordinateRawFourierL2CLM_apply
  ] using hMap

/-- The coercion of the selected mild-state raw Fourier `L²` class agrees
almost everywhere with the pointwise sum of its heat and Duhamel pieces. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_heat_add_duhamel
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
        hν U₀ hA hU₀ t i : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
          hν U₀ ht i : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) ξ
        +
      ((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
          (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) ξ) := by
  rw [
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_eq_heat_add_duhamel
      hν U₀ hA hU₀ ht htR i
  ]

  exact
    MeasureTheory.Lp.coeFn_add
      (h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
        hν U₀ ht i)
      (h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
        (t := t) hν U₀ hA hU₀ i)

/-- Every positive-time coordinate of the actual selected mild state has an
integrable second raw Fourier moment throughout the canonical restart window. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_secondMoment_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 2 *
          ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              hν U₀ hA hU₀ t i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let H : H3FourierComplexL2 :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
      hν U₀ ht i

  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := t) hν U₀ hA hU₀ i

  let W : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
      hν U₀ hA hU₀ t i

  have hHeat :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_secondMoment_integrable
        hν U₀ ht i

  have hDuhamel :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_secondMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖H ξ‖ +
            ‖ξ‖ ^ 2 * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHeat.add hDuhamel

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖W ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      ((continuous_norm.pow 2).aestronglyMeasurable).mul
        (MeasureTheory.Lp.aestronglyMeasurable W).norm

  have hRep :
      ((W : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 => H ξ + D ξ) := by
    dsimp only [W, H, D]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_heat_add_duhamel
        hν U₀ hA hU₀ ht htR i

  refine hMajor.mono' hTargetMeas ?_

  filter_upwards [hRep] with ξ hξ

  have hw : 0 ≤ ‖ξ‖ ^ 2 :=
    pow_nonneg (norm_nonneg ξ) 2

  have hTargetNonneg :
      0 ≤ ‖ξ‖ ^ 2 * ‖W ξ‖ :=
    mul_nonneg hw (norm_nonneg _)

  rw [Real.norm_eq_abs, abs_of_nonneg hTargetNonneg]
  rw [hξ]

  calc
    ‖ξ‖ ^ 2 * ‖H ξ + D ξ‖
        ≤
      ‖ξ‖ ^ 2 * (‖H ξ‖ + ‖D ξ‖) :=
      mul_le_mul_of_nonneg_left
        (norm_add_le (H ξ) (D ξ))
        hw
    _ =
      ‖ξ‖ ^ 2 * ‖H ξ‖ +
        ‖ξ‖ ^ 2 * ‖D ξ‖ := by
      ring

end
end Euclidean
end Bridge
end PrimeTensor
