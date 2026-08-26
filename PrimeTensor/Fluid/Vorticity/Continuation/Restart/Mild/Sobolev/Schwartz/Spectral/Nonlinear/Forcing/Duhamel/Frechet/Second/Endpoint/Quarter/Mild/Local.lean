import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Mild.Increment
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Duhamel.Local

/-!
# Local terminal quarter-Hölder control of the selected mild path

The positive-base mild increment estimate is already closed, but its free heat
coefficient is tied to the source time.  On a fixed terminal interval `(a,t)`
we can do better: write every source time as `s = a + (s-a)` and use the heat
semigroup orbit estimate with the single positive base `a`.  The nonlinear
part is already uniform on `(a,t)` by `Quarter.Duhamel.Local`.

Thus the selected mild path has one terminal quarter-Hölder coefficient on the
whole interval, exactly in the form consumed by `H3SpectralEndpointQuarterHolderOn`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-- Uniform terminal quarter-Hölder coefficient for the selected mild path on
`(a,t)`. -/
noncomputable def h3MildQuarterSelectedRestartLocalCoefficient
    (ν A a t : ℝ) : ℝ :=
  h3HeatQuarterOrbitCoefficient ν a * A +
    h3DuhamelQuarterSelectedRestartLocalCoefficient ν A t

/-- The local selected-mild coefficient is nonnegative on a nonnegative
parameter range. -/
theorem h3MildQuarterSelectedRestartLocalCoefficient_nonneg
    {ν A a t : ℝ}
    (hν : 0 ≤ ν)
    (hA : 0 ≤ A)
    (ht : 0 ≤ t) :
    0 ≤ h3MildQuarterSelectedRestartLocalCoefficient ν A a t := by
  have hHeat : 0 ≤ h3HeatQuarterOrbitCoefficient ν a :=
    h3HeatQuarterOrbitCoefficient_nonneg hν
  have hDuhamel :
      0 ≤ h3DuhamelQuarterSelectedRestartLocalCoefficient ν A t :=
    h3DuhamelQuarterSelectedRestartLocalCoefficient_nonneg hν hA ht
  unfold h3MildQuarterSelectedRestartLocalCoefficient
  positivity

/-- On every positive terminal interval inside the canonical restart radius,
the Banach-selected mild path satisfies the exact local quarter-Hölder
predicate used by the second-Duhamel endpoint cancellation layer. -/
theorem h3SpectralEndpointQuarterHolderOn_selectedRestart
    {ν A a t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    H3SpectralEndpointQuarterHolderOn
      W a t
      (h3MildQuarterSelectedRestartLocalCoefficient ν A a t) := by
  dsimp only [H3SpectralEndpointQuarterHolderOn]

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  intro s hs

  have hs0 : 0 < s := lt_trans ha hs.1
  have ht0 : 0 ≤ t := (lt_trans ha hat).le
  have hsR : s ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hs.2.le htR

  have hb0 : 0 ≤ s - a := sub_nonneg.mpr hs.1.le
  have hh0 : 0 ≤ t - s := sub_nonneg.mpr hs.2.le

  let aNN : NNReal := ⟨a, ha.le⟩
  let b : NNReal := ⟨s - a, hb0⟩
  let h : NNReal := ⟨t - s, hh0⟩
  let sNN : NNReal := ⟨s, hs0.le⟩
  let tNN : NNReal := ⟨t, ht0⟩

  have hab : aNN + b = sNN := by
    apply Subtype.ext
    change a + (s - a) = s
    ring

  have habh : aNN + b + h = tNN := by
    apply Subtype.ext
    change a + (s - a) + (t - s) = t
    ring

  let Ds : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayDuhamel ν s hν W W
  let Dt : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayDuhamel ν t hν W W

  let qs : Set.Icc (0 : ℝ) (h3FinHeatLerayRestartRadius ν A) :=
    ⟨s, hs0.le, hsR⟩
  let qt : Set.Icc (0 : ℝ) (h3FinHeatLerayRestartRadius ν A) :=
    ⟨t, ht0, htR⟩

  have hMildS0 :=
    h3SpectralFinHeatLerayPhysicalMildSolution_satisfies_mild_at
      hν
      (h3FinHeatLerayRestartRadius_pos ν hA).le
      U₀ hA hU₀
      (h3FinHeatLerayRestartRadius_smallness ν hA.le)
      qs
  have hqsNN :
      h3PhysicalTimePointNN qs = sNN := by
    rfl
  rw [hqsNN] at hMildS0
  have hMildS :
      h3SpectralVelocityHeatApplyNN ν hν.le sNN U₀ + Ds = W s := by
    simpa only [W, Ds, qs,
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension,
      h3SpectralFinHeatLerayPhysicalMildSolution_apply] using hMildS0

  have hMildT0 :=
    h3SpectralFinHeatLerayPhysicalMildSolution_satisfies_mild_at
      hν
      (h3FinHeatLerayRestartRadius_pos ν hA).le
      U₀ hA hU₀
      (h3FinHeatLerayRestartRadius_smallness ν hA.le)
      qt
  have hqtNN :
      h3PhysicalTimePointNN qt = tNN := by
    rfl
  rw [hqtNN] at hMildT0
  have hMildT :
      h3SpectralVelocityHeatApplyNN ν hν.le tNN U₀ + Dt = W t := by
    simpa only [W, Dt, qt,
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension,
      h3SpectralFinHeatLerayPhysicalMildSolution_apply] using hMildT0

  have hHeat0 :=
    norm_h3SpectralVelocityHeatApplyNN_add_add_sub_le_quarter_rpow
      hν aNN b h ha U₀

  have hHeatBase :
      ‖h3SpectralVelocityHeatApplyNN ν hν.le tNN U₀ -
          h3SpectralVelocityHeatApplyNN ν hν.le sNN U₀‖
        ≤
      (h3HeatQuarterOrbitCoefficient ν a * ‖U₀‖) *
        (t - s) ^ ((1 : ℝ) / 4) := by
    rw [habh, hab] at hHeat0
    change
      ‖h3SpectralVelocityHeatApplyNN ν hν.le tNN U₀ -
          h3SpectralVelocityHeatApplyNN ν hν.le sNN U₀‖
        ≤
      (h3HeatQuarterOrbitCoefficient ν a * ‖U₀‖) *
        (t - s) ^ ((1 : ℝ) / 4) at hHeat0
    exact hHeat0

  have hHeatCoeff : 0 ≤ h3HeatQuarterOrbitCoefficient ν a :=
    h3HeatQuarterOrbitCoefficient_nonneg hν.le
  have hPow : 0 ≤ (t - s) ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg hh0 _

  have hHeat :
      ‖h3SpectralVelocityHeatApplyNN ν hν.le sNN U₀ -
          h3SpectralVelocityHeatApplyNN ν hν.le tNN U₀‖
        ≤
      (h3HeatQuarterOrbitCoefficient ν a * A) *
        (t - s) ^ ((1 : ℝ) / 4) := by
    calc
      ‖h3SpectralVelocityHeatApplyNN ν hν.le sNN U₀ -
          h3SpectralVelocityHeatApplyNN ν hν.le tNN U₀‖
          =
        ‖h3SpectralVelocityHeatApplyNN ν hν.le tNN U₀ -
          h3SpectralVelocityHeatApplyNN ν hν.le sNN U₀‖ := by
            exact norm_sub_rev _ _
      _ ≤
        (h3HeatQuarterOrbitCoefficient ν a * ‖U₀‖) *
          (t - s) ^ ((1 : ℝ) / 4) := hHeatBase
      _ ≤
        (h3HeatQuarterOrbitCoefficient ν a * A) *
          (t - s) ^ ((1 : ℝ) / 4) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hU₀ hHeatCoeff)
          hPow

  have hDuhamel :
      ‖Ds - Dt‖
        ≤
      h3DuhamelQuarterSelectedRestartLocalCoefficient ν A t *
        (t - s) ^ ((1 : ℝ) / 4) := by
    dsimp only [Ds, Dt, W]
    exact
      norm_h3SpectralFinHeatLerayDuhamel_selectedRestart_sub_le_quarter_on
        hν U₀ hA hU₀ ha hat htR s hs

  change
    ‖W s - W t‖
      ≤
    h3MildQuarterSelectedRestartLocalCoefficient ν A a t *
      (t - s) ^ ((1 : ℝ) / 4)

  rw [← hMildS, ← hMildT]

  have hDecomp :
      (h3SpectralVelocityHeatApplyNN ν hν.le sNN U₀ + Ds) -
          (h3SpectralVelocityHeatApplyNN ν hν.le tNN U₀ + Dt)
        =
      (h3SpectralVelocityHeatApplyNN ν hν.le sNN U₀ -
          h3SpectralVelocityHeatApplyNN ν hν.le tNN U₀) +
        (Ds - Dt) := by
    abel
  rw [hDecomp]

  calc
    ‖(h3SpectralVelocityHeatApplyNN ν hν.le sNN U₀ -
          h3SpectralVelocityHeatApplyNN ν hν.le tNN U₀) +
        (Ds - Dt)‖
        ≤
      ‖h3SpectralVelocityHeatApplyNN ν hν.le sNN U₀ -
          h3SpectralVelocityHeatApplyNN ν hν.le tNN U₀‖ +
        ‖Ds - Dt‖ :=
      norm_add_le _ _
    _ ≤
      (h3HeatQuarterOrbitCoefficient ν a * A) *
          (t - s) ^ ((1 : ℝ) / 4) +
        h3DuhamelQuarterSelectedRestartLocalCoefficient ν A t *
          (t - s) ^ ((1 : ℝ) / 4) :=
      add_le_add hHeat hDuhamel
    _ =
      h3MildQuarterSelectedRestartLocalCoefficient ν A a t *
        (t - s) ^ ((1 : ℝ) / 4) := by
      unfold h3MildQuarterSelectedRestartLocalCoefficient
      ring

end

end Euclidean
end Bridge
end PrimeTensor
