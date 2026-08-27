import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Head.Real.C3.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Restart.Bound

/-!
# Selected-restart real C³ Duhamel head

The generic midpoint restart identity already isolates the harmless half of the
nonlinear Duhamel term:

    D(t) = H_{t/2} D(t/2) + ∫_{t/2}^t K(t-s,s) ds.

The first term has a fixed positive heat lag and therefore has a real spatial
`C³` representative.  This file specializes that interface to the canonical
Banach-selected restart path, discharging the continuity, boundedness, and
Bochner-integrability hypotheses once and for all.

The remaining classicalization problem is represented by one named selected
terminal-half tail.  No regularity for that tail is asserted here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedDuhamelHeadC3
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SchwartzSelectedDuhamelHeadC3 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The canonical selected terminal-half Duhamel tail.  This is the only part
of the midpoint decomposition whose heat lag can vanish. -/
noncomputable def h3SpectralFinHeatLerayDuhamelSelectedTail
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A) :
    H3SpectralFinVectorState :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀
  ∫ s in (t / 2)..t,
    h3SpectralFinHeatLerayDuhamelIntegrand
      ν t hν W W s

/-- The retarded spectral heat--Leray integrand along the canonical selected
path is genuinely interval-integrable on every nonnegative subtime of the
restart construction. -/
theorem h3SpectralFinHeatLerayDuhamelIntegrand_selectedRestart_intervalIntegrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 ≤ t) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    IntervalIntegrable
      (h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν W W)
      volume
      0
      t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hWcont : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hWbound :
      ∀ s : ℝ, ‖W s‖ ≤ 2 * A := by
    intro s
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        hν U₀ hA hU₀ s

  have h2A : 0 ≤ 2 * A := by
    positivity

  exact
    h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
      hν ht h2A h2A
      W W
      hWcont hWcont
      (fun s _hs => hWbound s)
      (fun s _hs => hWbound s)

/-- The selected midpoint head has a coordinatewise real spatial `C³`
representative. -/
theorem h3SpectralFinHeatLerayDuhamelHeadRealC3RepresentativeOnPoint3_selectedRestart_contDiff_three
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (j : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContDiff ℝ 3
      (h3SpectralFinHeatLerayDuhamelHeadRealC3RepresentativeOnPoint3
        ν t hν ht W W j) := by
  dsimp only
  exact
    h3SpectralFinHeatLerayDuhamelHeadRealC3RepresentativeOnPoint3_contDiff_three
      hν ht
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀)
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀)
      j

/-- The selected real `C³` head representative is the a.e. representative of
the existing real spectral decoder of the same selected head state. -/
theorem h3SpectralFinHeatLerayDuhamelHeadRealC3RepresentativeOnPoint3_selectedRestart_ae_eq_decodeRealL2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (j : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3SpectralFinHeatLerayDuhamelHeadRealC3RepresentativeOnPoint3
        ν t hν ht W W j
      =ᵐ[(volume : Measure Point3)]
    ((h3FromFourierRealL2
        (h3SpectralVelocityDecodeRealL2
          (h3SpectralFinHeatLerayDuhamelHead
            ν t hν ht W W) j) : H3ScalarL2) :
      Point3 → ℝ) := by
  dsimp only
  exact
    h3SpectralFinHeatLerayDuhamelHeadRealC3RepresentativeOnPoint3_ae_eq_decodeRealL2
      hν ht
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀)
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀)
      j

/-- Exact midpoint decomposition of the complete selected Duhamel state into
its positive-lag `C³` head and the named terminal-half tail. -/
theorem h3SpectralFinHeatLerayDuhamel_selectedRestart_eq_head_add_tail
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3SpectralFinHeatLerayDuhamel ν t hν W W
      =
    h3SpectralFinHeatLerayDuhamelHead ν t hν ht W W
      +
    h3SpectralFinHeatLerayDuhamelSelectedTail
      (t := t) hν U₀ hA hU₀ := by
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

  have hHalfPos : 0 < t / 2 := by
    linarith

  have hHalf :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν (t / 2) hν W W)
        volume
        0
        (t / 2) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayDuhamelIntegrand_selectedRestart_intervalIntegrable
        hν U₀ hA hU₀ hHalfPos.le

  have hSplit :=
    h3SpectralFinHeatLerayDuhamel_eq_head_add_tail
      hν ht W W hLong hHalf

  change
    h3SpectralFinHeatLerayDuhamel ν t hν W W
      =
    h3SpectralFinHeatLerayDuhamelHead ν t hν ht W W
      +
    ∫ s in (t / 2)..t,
      h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν W W s

  exact hSplit

end
end Euclidean
end Bridge
end PrimeTensor
