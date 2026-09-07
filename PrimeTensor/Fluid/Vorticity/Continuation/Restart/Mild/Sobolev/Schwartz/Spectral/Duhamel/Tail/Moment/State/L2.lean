import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.Amplitude
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.Intertwining
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Selected terminal-tail state in raw Fourier `L²`

`Amplitude` constructs the explicit source-time integrated raw Fourier
amplitude and proves its second Fourier moment is `L¹`.  Before identifying
that pointwise amplitude with the actual spectral tail we first record the
corresponding statement at the quotient-safe `L²` level.

The existing positive-lag intertwining theorem already proves

    rawFourierL2 (HeatLeray_τ(U,V)_i)
      = rawHeatForcingL2(τ,U,V,i).

This file commutes two bounded linear operations through the selected
terminal-tail Bochner integral:

* projection to one `Fin 3` velocity coordinate;
* exact H³ deweighting into Fourier `L²`.

Consequently the actual selected spectral tail, after deweighting, is exactly
the `L²`-valued interval integral of the packaged raw heat-forcing states.

No fixed-frequency evaluation of an `L²` class is used.  The endpoint `s=t`
is represented by zero, matching the endpoint-safe spectral Duhamel
integrand.  The next checkpoint can identify the a.e. representative of this
`L²` integral with the raw amplitude by a genuine Fubini/duality argument.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedTailRawFourierL2State
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Projection to one finite velocity coordinate as a complex linear map. -/
noncomputable def h3SpectralFinCoordinateLinearMap
    (i : Fin 3) :
    H3SpectralFinVectorState →ₗ[ℂ] H3SpectralScalarState where
  toFun := fun U => U i
  map_add' := by
    intro U V
    rfl
  map_smul' := by
    intro c U
    rfl

/-- Projection to one finite velocity coordinate as a contractive complex
continuous linear map. -/
noncomputable def h3SpectralFinCoordinateCLM
    (i : Fin 3) :
    H3SpectralFinVectorState →L[ℂ] H3SpectralScalarState :=
  (h3SpectralFinCoordinateLinearMap i).mkContinuous
    1
    (fun U => by
      change ‖U i‖ ≤ 1 * ‖U‖
      simpa using h3SpectralFinVector_coordinate_norm_le U i)

@[simp]
theorem h3SpectralFinCoordinateCLM_apply
    (i : Fin 3)
    (U : H3SpectralFinVectorState) :
    h3SpectralFinCoordinateCLM i U = U i :=
  rfl

/-- Coordinate projection followed by exact H³ deweighting. -/
noncomputable def h3SpectralFinCoordinateRawFourierL2CLM
    (i : Fin 3) :
    H3SpectralFinVectorState →L[ℂ] H3FourierComplexL2 :=
  h3SpectralScalarRawFourierL2CLM.comp
    (h3SpectralFinCoordinateCLM i)

@[simp]
theorem h3SpectralFinCoordinateRawFourierL2CLM_apply
    (i : Fin 3)
    (U : H3SpectralFinVectorState) :
    h3SpectralFinCoordinateRawFourierL2CLM i U
      =
    h3SpectralScalarRawFourierL2 (U i) :=
  rfl

/-- Quotient-safe raw Fourier `L²` state of one coordinate of the named
selected terminal Duhamel tail. -/
noncomputable def h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  h3SpectralScalarRawFourierL2
    (h3SpectralFinHeatLerayDuhamelSelectedTail
      (t := t) hν U₀ hA hU₀ i)

/-- Fourier `L²` source-time kernel matching exact deweighting of the
endpoint-safe spectral Duhamel integrand. -/
noncomputable def h3SelectedDuhamelTailRawFourierL2Integrand
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (s : ℝ) :
    H3FourierComplexL2 :=
  if hs : s < t then
    h3RawFinLerayOuterProductDivergenceHeatFourierL2
      ν (t - s) hν (sub_pos.mpr hs)
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ s)
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ s)
      i
  else
    0

/-- At every source time, deweighting the actual endpoint-safe spectral
Duhamel integrand gives exactly the packaged raw heat-forcing `L²` kernel. -/
theorem h3SpectralFinHeatLerayDuhamelIntegrand_selectedRestart_rawFourierL2_eq
    {ν A t s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3SpectralScalarRawFourierL2
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν W W s i)
      =
    h3SelectedDuhamelTailRawFourierL2Integrand
      ν A t hν U₀ hA hU₀ i s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  by_cases hs : s < t

  · have hτ : 0 < t - s := sub_pos.mpr hs

    rw [
      h3SpectralFinHeatLerayDuhamelIntegrand,
      dif_pos hτ
    ]

    unfold h3SelectedDuhamelTailRawFourierL2Integrand
    rw [dif_pos hs]

    exact
      h3SpectralFinHeatLerayVelocityApply_rawFourierL2_eq_rawHeatForcingL2
        hν hτ
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ s)
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ s)
        i

  · have hτ : ¬ 0 < t - s := by
      exact not_lt.mpr (sub_nonpos.mpr (le_of_not_gt hs))

    rw [
      h3SpectralFinHeatLerayDuhamelIntegrand,
      dif_neg hτ
    ]

    unfold h3SelectedDuhamelTailRawFourierL2Integrand
    rw [dif_neg hs]

    change h3SpectralScalarRawFourierL2CLM 0 = 0
    exact h3SpectralScalarRawFourierL2CLM.map_zero

/-- The selected spectral Duhamel integrand is genuinely interval-integrable
on the terminal half. -/
theorem h3SpectralFinHeatLerayDuhamelIntegrand_selectedRestart_halfTail_intervalIntegrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    IntervalIntegrable
      (h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν W W)
      volume
      (t / 2)
      t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hLong :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν W W)
        volume
        0
        t := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayDuhamelIntegrand_selectedRestart_intervalIntegrable
        hν U₀ hA hU₀ ht.le

  have hhalf : t / 2 ≤ t := by
    linarith

  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le] at hLong
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hhalf]

  exact
    hLong.mono_set
      (by
        intro s hs
        exact ⟨by linarith [hs.1, ht], hs.2⟩)

/-- Exact H³ deweighting commutes with every genuinely integrable scalar
spectral interval integral. -/
theorem h3SpectralScalarRawFourierL2_intervalIntegral
    {a b : ℝ}
    (F : ℝ → H3SpectralScalarState)
    (hF : IntervalIntegrable F volume a b) :
    h3SpectralScalarRawFourierL2
        (∫ s in a..b, F s)
      =
    ∫ s in a..b,
      h3SpectralScalarRawFourierL2 (F s) := by
  symm
  exact
    h3SpectralScalarRawFourierL2CLM.intervalIntegral_comp_comm hF

/-- The deweighted actual selected tail state is exactly the Fourier
`L²`-valued interval integral of the packaged raw heat-forcing kernels. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_eq_intervalIntegral
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
        (t := t) hν U₀ hA hU₀ i
      =
    ∫ s in (t / 2)..t,
      h3SelectedDuhamelTailRawFourierL2Integrand
        ν A t hν U₀ hA hU₀ i s := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let D : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayDuhamelIntegrand
      ν t hν W W

  have hD :
      IntervalIntegrable
        D
        volume
        (t / 2)
        t := by
    dsimp only [D, W]
    exact
      h3SpectralFinHeatLerayDuhamelIntegrand_selectedRestart_halfTail_intervalIntegrable
        hν U₀ hA hU₀ ht

  have hComm :
      h3SpectralFinCoordinateRawFourierL2CLM i
          (∫ s in (t / 2)..t, D s)
        =
      ∫ s in (t / 2)..t,
        h3SpectralFinCoordinateRawFourierL2CLM i (D s) := by
    symm
    exact
      (h3SpectralFinCoordinateRawFourierL2CLM i).intervalIntegral_comp_comm hD

  change
    h3SpectralFinCoordinateRawFourierL2CLM i
        (∫ s in (t / 2)..t, D s)
      =
    ∫ s in (t / 2)..t,
      h3SelectedDuhamelTailRawFourierL2Integrand
        ν A t hν U₀ hA hU₀ i s

  calc
    h3SpectralFinCoordinateRawFourierL2CLM i
        (∫ s in (t / 2)..t, D s)
        =
      ∫ s in (t / 2)..t,
        h3SpectralFinCoordinateRawFourierL2CLM i (D s) :=
      hComm
    _ =
      ∫ s in (t / 2)..t,
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
