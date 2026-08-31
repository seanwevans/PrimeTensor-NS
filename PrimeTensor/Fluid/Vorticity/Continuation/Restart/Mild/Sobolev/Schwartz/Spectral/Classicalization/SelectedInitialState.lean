import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocitySpatialRegularity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Mild.Physical.Restart.Radius.Closure

/-!
# Classicalization: selected initial state

The positive-time selected velocity is now spatially `C³`, and its complete
third spatial jet is time-continuous on the open restart interval.

The remaining endpoint/gluing work needs the exact initial-value identity for
the Banach-selected physical-time extension.  This file isolates that identity
without introducing any classical reconstruction yet.

There are two elementary ingredients.

* At elapsed time zero the Fourier heat multiplier is exactly one.
* The Duhamel interval is `0..0`, hence its integral is exactly zero.

Evaluating the already-compiled physical mild equation at the zero point of
`[0,τ]` therefore gives

    W 0 = U₀.

The final theorem specializes this identity to the canonical restart radius.
That is the bridge needed next to identify the selected zero slice with the
preterminal spectral encoding.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationSelectedInitialState
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- At zero elapsed time, the scalar weighted-Fourier heat evolution is the
identity. -/
@[simp]
theorem h3SpectralScalarHeatApplyNN_zero
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (G : H3SpectralScalarState) :
    h3SpectralScalarHeatApplyNN ν hν 0 G = G := by
  apply MeasureTheory.Lp.ext

  filter_upwards [
    h3HeatFrequencyApplyNN_coeFn
      ν hν 0 G
  ] with ξ hξ

  change
    h3HeatFrequencyApplyNN ν hν 0 G ξ
      =
    G ξ

  rw [hξ]

  simp [h3HeatFourierSymbol]

/-- At zero elapsed time, the three-component weighted spectral heat evolution
is the identity. -/
@[simp]
theorem h3SpectralVelocityHeatApplyNN_zero
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (U : H3SpectralVelocityState) :
    h3SpectralVelocityHeatApplyNN ν hν 0 U = U := by
  funext j

  exact
    h3SpectralScalarHeatApplyNN_zero
      ν hν (U j)

/-- The heat--Leray Duhamel term vanishes exactly at target time zero. -/
@[simp]
theorem h3SpectralFinHeatLerayDuhamel_zero
    (ν : ℝ)
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState) :
    h3SpectralFinHeatLerayDuhamel
        ν 0 hν U V
      =
    0 := by
  unfold h3SpectralFinHeatLerayDuhamel
  simp

/-- The globally defined physical-time Banach-selected mild extension starts
at the supplied spectral state. -/
theorem h3SpectralFinHeatLerayMildSolutionPhysicalExtension_zero
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1) :
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension
        hν hτ U₀ hA hU₀ hsmall 0
      =
    U₀ := by
  let q0 : Set.Icc (0 : ℝ) τ :=
    ⟨0, le_rfl, hτ⟩

  have hMild :=
    h3SpectralFinHeatLerayPhysicalMildSolution_satisfies_mild_at
      hν hτ U₀ hA hU₀ hsmall q0

  have hq0NN :
      h3PhysicalTimePointNN q0 = 0 := by
    apply Subtype.ext
    rfl

  rw [hq0NN] at hMild

  have hAtZero :
      h3SpectralVelocityHeatApplyNN
          ν hν.le 0 U₀
        -
      h3SpectralFinHeatLerayDuhamel
          ν 0 hν
          (h3SpectralFinHeatLerayMildSolutionPhysicalExtension
            hν hτ U₀ hA hU₀ hsmall)
          (h3SpectralFinHeatLerayMildSolutionPhysicalExtension
            hν hτ U₀ hA hU₀ hsmall)
        =
      h3SpectralFinHeatLerayMildSolutionPhysicalExtension
        hν hτ U₀ hA hU₀ hsmall 0 := by
    simpa only [
      q0,
      h3SpectralFinHeatLerayPhysicalMildSolution_apply
    ] using hMild

  simpa using hAtZero.symm

/-- The selected restart-radius physical extension starts exactly at its
supplied spectral initial state. -/
@[simp]
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_zero
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A) :
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ 0
      =
    U₀ := by
  unfold
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension

  exact
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_zero
      hν
      (h3FinHeatLerayRestartRadius_pos ν hA).le
      U₀
      hA
      hU₀
      (h3FinHeatLerayRestartRadius_smallness ν hA.le)

end
end Euclidean
end Bridge
end PrimeTensor
