import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.HeadGlobalFubini
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.HeadSecond

/-!
# Quotient-safe raw Fourier state of the selected Duhamel head

The midpoint head already has two exact descriptions in the repository.

* The restart theorem identifies it as `H_{t/2} D(t/2)`.
* The original Duhamel definition is the Bochner integral of the long
  retarded kernel on `0..t`.

Splitting the latter integral at `t/2` and comparing with the restart
head/tail decomposition cancels the common terminal-half integral.  Therefore
the named head itself is exactly the long retarded kernel integrated on
`0..t/2`.

This file transports that identity through coordinate projection and exact H³
deweighting.  The result is a quotient-safe Fourier `L²` identity for the head
using the same endpoint-safe raw Fourier kernel already used for the tail.

No fixed-frequency evaluation of an `L²` class is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedHeadStateL2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The named selected midpoint head is exactly the long retarded spectral
kernel integrated on `0..t/2`. -/
theorem h3SpectralFinHeatLerayDuhamelHead_selectedRestart_eq_intervalIntegral
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3SpectralFinHeatLerayDuhamelHead
        ν t hν ht W W
      =
    ∫ s in (0 : ℝ)..(t / 2),
      h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν W W s := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let D : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayDuhamelIntegrand
      ν t hν W W

  have hLong :
      IntervalIntegrable D volume (0 : ℝ) t := by
    dsimp only [D, W]
    exact
      h3SpectralFinHeatLerayDuhamelIntegrand_selectedRestart_intervalIntegrable
        hν U₀ hA hU₀ ht.le

  have hhalf : 0 ≤ t / 2 := by
    linarith

  have hHeadInt :
      IntervalIntegrable D volume (0 : ℝ) (t / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le] at hLong
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hhalf]
    exact
      hLong.mono_set
        (by
          intro s hs
          exact ⟨hs.1, by linarith [hs.2, ht]⟩)

  have hTailInt :
      IntervalIntegrable D volume (t / 2) t := by
    dsimp only [D, W]
    exact
      h3SpectralFinHeatLerayDuhamelIntegrand_selectedRestart_halfTail_intervalIntegrable
        hν U₀ hA hU₀ ht

  have hSplit :
      (∫ s in (0 : ℝ)..(t / 2), D s)
        +
      (∫ s in (t / 2)..t, D s)
        =
      ∫ s in (0 : ℝ)..t, D s :=
    intervalIntegral.integral_add_adjacent_intervals
      hHeadInt hTailInt

  have hRestart :=
    h3SpectralFinHeatLerayDuhamel_selectedRestart_eq_head_add_tail
      hν U₀ hA hU₀ ht

  have hRestart' :
      (∫ s in (0 : ℝ)..t, D s)
        =
      h3SpectralFinHeatLerayDuhamelHead
          ν t hν ht W W
        +
      ∫ s in (t / 2)..t, D s := by
    dsimp only [W] at hRestart
    unfold h3SpectralFinHeatLerayDuhamel at hRestart
    dsimp only [D, W]
    exact hRestart

  have hCancel :
      (∫ s in (0 : ℝ)..(t / 2), D s)
        =
      h3SpectralFinHeatLerayDuhamelHead
        ν t hν ht W W := by
    apply add_right_cancel
    exact hSplit.trans hRestart'

  exact hCancel.symm

/-- The quotient-safe raw Fourier `L²` long-kernel path is interval-integrable
on the selected midpoint head. -/
theorem h3SelectedDuhamelHeadRawFourierL2Integrand_intervalIntegrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    IntervalIntegrable
      (h3SelectedDuhamelTailRawFourierL2Integrand
        ν A t hν U₀ hA hU₀ i)
      volume
      (0 : ℝ)
      (t / 2) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let D : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayDuhamelIntegrand
      ν t hν W W

  have hLong :
      IntervalIntegrable D volume (0 : ℝ) t := by
    dsimp only [D, W]
    exact
      h3SpectralFinHeatLerayDuhamelIntegrand_selectedRestart_intervalIntegrable
        hν U₀ hA hU₀ ht.le

  have hhalf : 0 ≤ t / 2 := by
    linarith

  have hD :
      IntervalIntegrable D volume (0 : ℝ) (t / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le] at hLong
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hhalf]
    exact
      hLong.mono_set
        (by
          intro s hs
          exact ⟨hs.1, by linarith [hs.2, ht]⟩)

  have hMapped :
      IntervalIntegrable
        (fun s : ℝ =>
          h3SpectralFinCoordinateRawFourierL2CLM i (D s))
        volume
        (0 : ℝ)
        (t / 2) := by
    constructor
    · exact
        (h3SpectralFinCoordinateRawFourierL2CLM i).integrable_comp
          hD.1
    · exact
        (h3SpectralFinCoordinateRawFourierL2CLM i).integrable_comp
          hD.2

  refine hMapped.congr ?_
  intro s hs

  dsimp only [
    D,
    W,
    h3SpectralFinCoordinateRawFourierL2CLM_apply
  ]

  exact
    h3SpectralFinHeatLerayDuhamelIntegrand_selectedRestart_rawFourierL2_eq
      hν U₀ hA hU₀ i

/-- Exact H³ deweighting of the actual named selected head is the Fourier
`L²`-valued interval integral of the long retarded raw kernels on `0..t/2`. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_eq_intervalIntegral_longKernel
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
        hν U₀ hA hU₀ ht i
      =
    ∫ s in (0 : ℝ)..(t / 2),
      h3SelectedDuhamelTailRawFourierL2Integrand
        ν A t hν U₀ hA hU₀ i s := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let D : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayDuhamelIntegrand
      ν t hν W W

  have hHeadState :=
    h3SpectralFinHeatLerayDuhamelHead_selectedRestart_eq_intervalIntegral
      hν U₀ hA hU₀ ht

  have hLong :
      IntervalIntegrable D volume (0 : ℝ) t := by
    dsimp only [D, W]
    exact
      h3SpectralFinHeatLerayDuhamelIntegrand_selectedRestart_intervalIntegrable
        hν U₀ hA hU₀ ht.le

  have hhalf : 0 ≤ t / 2 := by
    linarith

  have hD :
      IntervalIntegrable D volume (0 : ℝ) (t / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le] at hLong
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hhalf]
    exact
      hLong.mono_set
        (by
          intro s hs
          exact ⟨hs.1, by linarith [hs.2, ht]⟩)

  have hComm :
      h3SpectralFinCoordinateRawFourierL2CLM i
          (∫ s in (0 : ℝ)..(t / 2), D s)
        =
      ∫ s in (0 : ℝ)..(t / 2),
        h3SpectralFinCoordinateRawFourierL2CLM i (D s) := by
    symm
    exact
      (h3SpectralFinCoordinateRawFourierL2CLM i).intervalIntegral_comp_comm hD

  unfold h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2

  change
    h3SpectralFinCoordinateRawFourierL2CLM i
        (h3SpectralFinHeatLerayDuhamelHead
          ν t hν ht W W)
      =
    ∫ s in (0 : ℝ)..(t / 2),
      h3SelectedDuhamelTailRawFourierL2Integrand
        ν A t hν U₀ hA hU₀ i s

  rw [hHeadState]

  calc
    h3SpectralFinCoordinateRawFourierL2CLM i
        (∫ s in (0 : ℝ)..(t / 2), D s)
        =
      ∫ s in (0 : ℝ)..(t / 2),
        h3SpectralFinCoordinateRawFourierL2CLM i (D s) :=
      hComm
    _ =
      ∫ s in (0 : ℝ)..(t / 2),
        h3SelectedDuhamelTailRawFourierL2Integrand
          ν A t hν U₀ hA hU₀ i s := by
      apply intervalIntegral.integral_congr
      intro s hs
      dsimp only [
        h3SpectralFinCoordinateRawFourierL2CLM_apply,
        D,
        W
      ]
      exact
        h3SpectralFinHeatLerayDuhamelIntegrand_selectedRestart_rawFourierL2_eq
          hν U₀ hA hU₀ i

end

end Euclidean
end Bridge
end PrimeTensor
