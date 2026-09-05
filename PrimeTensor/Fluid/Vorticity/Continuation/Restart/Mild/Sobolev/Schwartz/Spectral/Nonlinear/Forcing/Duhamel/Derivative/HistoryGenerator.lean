import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.Fresh.Tail.Quotient
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.FullPointwise
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.Derivative

/-!
# Selected Duhamel old-history heat generator

The fresh moving-endpoint quotient is already closed.

For the old-history contribution, the key observation is that the complete
selected Duhamel state has more Fourier regularity than a generic H³ state:
its quotient-safe deweighted Fourier representative has an integrable second
moment.  `SelectedRawFourierAmplitude` identifies that L² representative
almost everywhere with the explicit raw amplitude whose inverse Fourier
transform is the classical selected Duhamel field.

This file transfers the second-moment estimate to that explicit amplitude and
packages its heat orbit and heat generator.

At base time `t`, write `A_t(ξ)` for the explicit selected Duhamel raw
amplitude.  Then

    oldHeat(h, ξ) = m(h, ξ) A_t(ξ)

and

    generator(h, ξ) = (-ν q(ξ)) m(h, ξ) A_t(ξ).

The second moment makes the zero-time generator genuinely L¹.  For every
nonnegative heat increment, heat contractivity gives one fixed integrable
majorant by the zero-time generator norm.  These are exactly the inputs needed
for the next one-sided quotient dominated-convergence step.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3DuhamelHistoryGenerator
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The explicit selected Duhamel raw amplitude inherits the already-proved
integrable second Fourier moment of the quotient-safe L² representative. -/
theorem h3SelectedDuhamelRawFourierAmplitude_secondMoment_integrable
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
          ‖h3SelectedDuhamelRawFourierAmplitude
            ν A t hν U₀ hA hU₀ ht i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hMoment :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_secondMoment_integrable
      hν U₀ hA hU₀ ht htR i

  have hAE :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_ae_eq_rawAmplitude
      hν U₀ hA hU₀ ht i

  refine hMoment.congr ?_
  filter_upwards [hAE] with ξ hξ
  rw [hξ]

/-- Heat evolution of the complete selected Duhamel raw amplitude, with the
elapsed old-history heat increment exposed as the parameter `h`. -/
noncomputable def h3SelectedDuhamelHistoryHeatRawAmplitude
    (ν A t h : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  h3HeatFourierSymbol ν h ξ *
    h3SelectedDuhamelRawFourierAmplitude
      ν A t hν U₀ hA hU₀ ht i ξ

/-- Fourier time generator of the selected old-history heat orbit. -/
noncomputable def h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
    (ν A t h : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  ((-ν * h3FourierGradientSquare ξ : ℝ) : ℂ) *
    h3SelectedDuhamelHistoryHeatRawAmplitude
      ν A t h hν U₀ hA hU₀ ht i ξ

/-- The old-history heat orbit starts at the explicit selected Duhamel raw
amplitude. -/
theorem h3SelectedDuhamelHistoryHeatRawAmplitude_zero
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    h3SelectedDuhamelHistoryHeatRawAmplitude
        ν A t 0 hν U₀ hA hU₀ ht i
      =
    h3SelectedDuhamelRawFourierAmplitude
      ν A t hν U₀ hA hU₀ ht i := by
  funext ξ
  unfold h3SelectedDuhamelHistoryHeatRawAmplitude
  unfold h3HeatFourierSymbol
  simp

/-- Exact norm of the old-history heat generator. -/
theorem norm_h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
        ν A t h hν U₀ hA hU₀ ht i ξ‖
      =
    (ν * (2 * Real.pi) ^ 2) *
      (‖ξ‖ ^ 2 *
        ‖h3SelectedDuhamelHistoryHeatRawAmplitude
          ν A t h hν U₀ hA hU₀ ht i ξ‖) := by
  unfold h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]

  have hq : 0 ≤ h3FourierGradientSquare ξ :=
    h3FourierGradientSquare_nonneg ξ

  have hνq : 0 ≤ ν * h3FourierGradientSquare ξ :=
    mul_nonneg hν.le hq

  rw [
    show -ν * h3FourierGradientSquare ξ
        = -(ν * h3FourierGradientSquare ξ) by ring
  ]
  rw [abs_neg, abs_of_nonneg hνq]

  unfold h3FourierGradientSquare
  ring

/-- On every nonnegative elapsed heat time, the old-history generator is
dominated by the zero-time second-moment density. -/
theorem norm_h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude_le_zero
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 ≤ h)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
        ν A t h hν U₀ hA hU₀ ht i ξ‖
      ≤
    (ν * (2 * Real.pi) ^ 2) *
      (‖ξ‖ ^ 2 *
        ‖h3SelectedDuhamelRawFourierAmplitude
          ν A t hν U₀ hA hU₀ ht i ξ‖) := by
  rw [
    norm_h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
      hν U₀ hA hU₀ ht i ξ
  ]

  unfold h3SelectedDuhamelHistoryHeatRawAmplitude
  rw [norm_mul]

  have hHeat :
      ‖h3HeatFourierSymbol ν h ξ‖ ≤ 1 :=
    norm_h3HeatFourierSymbol_le_one hν.le hh ξ

  have hC : 0 ≤ ν * (2 * Real.pi) ^ 2 := by
    positivity

  have hξ2 : 0 ≤ ‖ξ‖ ^ 2 := by
    positivity

  calc
    (ν * (2 * Real.pi) ^ 2) *
        (‖ξ‖ ^ 2 *
          (‖h3HeatFourierSymbol ν h ξ‖ *
            ‖h3SelectedDuhamelRawFourierAmplitude
              ν A t hν U₀ hA hU₀ ht i ξ‖))
        ≤
      (ν * (2 * Real.pi) ^ 2) *
        (‖ξ‖ ^ 2 *
          (1 *
            ‖h3SelectedDuhamelRawFourierAmplitude
              ν A t hν U₀ hA hU₀ ht i ξ‖)) := by
        gcongr
    _ =
      (ν * (2 * Real.pi) ^ 2) *
        (‖ξ‖ ^ 2 *
          ‖h3SelectedDuhamelRawFourierAmplitude
            ν A t hν U₀ hA hU₀ ht i ξ‖) := by
        ring

/-- The zero-time old-history generator is genuinely Fourier `L¹`. -/
theorem h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude_zero_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
        ν A t 0 hν U₀ hA hU₀ ht i)
      (volume : Measure H3FourierPoint3) := by
  have hMoment :=
    h3SelectedDuhamelRawFourierAmplitude_secondMoment_integrable
      hν U₀ hA hU₀ ht htR i

  have hAmpInt :=
    h3SelectedDuhamelRawFourierAmplitude_integrable
      hν U₀ hA hU₀ ht i

  have hMeas :
      AEStronglyMeasurable
        (h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
          ν A t 0 hν U₀ hA hU₀ ht i)
        (volume : Measure H3FourierPoint3) := by
    unfold h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
    have hCoeff :
        AEStronglyMeasurable
          (fun ξ : H3FourierPoint3 =>
            ((-ν * h3FourierGradientSquare ξ : ℝ) : ℂ))
          (volume : Measure H3FourierPoint3) := by
      apply Continuous.aestronglyMeasurable
      unfold h3FourierGradientSquare
      fun_prop
    exact
      hCoeff.mul
        ((by
          rw [
            h3SelectedDuhamelHistoryHeatRawAmplitude_zero
              hν U₀ hA hU₀ ht i
          ]
          exact hAmpInt.aestronglyMeasurable) :
          AEStronglyMeasurable
            (h3SelectedDuhamelHistoryHeatRawAmplitude
              ν A t 0 hν U₀ hA hU₀ ht i)
            (volume : Measure H3FourierPoint3))

  rw [← integrable_norm_iff hMeas]

  have hScaled :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (ν * (2 * Real.pi) ^ 2) *
            (‖ξ‖ ^ 2 *
              ‖h3SelectedDuhamelRawFourierAmplitude
                ν A t hν U₀ hA hU₀ ht i ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMoment.const_mul (ν * (2 * Real.pi) ^ 2)

  simpa only [
    norm_h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
      hν U₀ hA hU₀ ht i,
    h3SelectedDuhamelHistoryHeatRawAmplitude_zero
      hν U₀ hA hU₀ ht i
  ] using hScaled

/-- Pointwise real-time derivative of the old-history raw heat amplitude. -/
theorem h3SelectedDuhamelHistoryHeatRawAmplitude_hasDerivAt_time
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    HasDerivAt
      (fun r : ℝ =>
        h3SelectedDuhamelHistoryHeatRawAmplitude
          ν A t r hν U₀ hA hU₀ ht i ξ)
      (h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
        ν A t h hν U₀ hA hU₀ ht i ξ)
      h := by
  have hDeriv :=
    (h3HeatFourierSymbol_hasDerivAt_time ν h ξ).mul_const
      (h3SelectedDuhamelRawFourierAmplitude
        ν A t hν U₀ hA hU₀ ht i ξ)

  rw [h3HeatFourierTimeGeneratorSymbol_eq] at hDeriv

  simpa only [
    h3SelectedDuhamelHistoryHeatRawAmplitude,
    h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude,
    mul_assoc
  ] using hDeriv

/-- Physical inverse-Fourier old-history heat orbit. -/
noncomputable def h3SelectedDuhamelHistoryHeatRepresentative
    (ν A t h : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3SelectedDuhamelHistoryHeatRawAmplitude
      ν A t h hν U₀ hA hU₀ ht i)

/-- Physical inverse-Fourier zero-time old-history generator. -/
noncomputable def h3SelectedDuhamelHistoryHeatTimeGeneratorRepresentative
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
      ν A t 0 hν U₀ hA hU₀ ht i)

/-- At zero elapsed heat time, the old-history heat representative is exactly
the canonical selected Duhamel pointwise representative. -/
theorem h3SelectedDuhamelHistoryHeatRepresentative_zero_eq_C1Representative
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    h3SelectedDuhamelHistoryHeatRepresentative
        ν A t 0 hν U₀ hA hU₀ ht i
      =
    h3SelectedDuhamelC1Representative
      ν A t hν U₀ hA hU₀ ht i := by
  unfold
    h3SelectedDuhamelHistoryHeatRepresentative
    h3SelectedDuhamelC1Representative
  rw [
    h3SelectedDuhamelHistoryHeatRawAmplitude_zero
      hν U₀ hA hU₀ ht i
  ]

end

end Euclidean
end Bridge
end PrimeTensor
