import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Energy.From.L2.Jet
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Energy.Continuity.Minimal

/-!
# Direct continuation from physical H³ L²-jet continuity

The previous bridge showed that strong continuity of the complete physical H³
`L²` jet implies scalar H³-energy continuity.

For the actual continuation argument we can do even less work.  The reduced
endpoint topology only asks for

* zeroth-order physical `L²` coordinates; and
* ordered third-order physical `L²` coordinates.

Both are direct projections of the complete 120-coordinate H³ `L²` jet.

Therefore a radius-wide full-jet continuity frontier implies the endpoint
continuity frontier directly, without passing through scalar energy or spectral
weak+norm reconstruction.

Once endpoint continuity is available, the existing physical-evolution,
local-PDE closure, and real-restart stack completes continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

/-- Radius-wide strong continuity of the complete canonical physical H³ `L²`
jet on every shortened preterminal overlap. -/
def H3PreterminalTailUnitViscosityPhysicalL2JetContinuityFrontierOnRestartRadius
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ q : Set.Icc
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E),
    ∀ hqPos : 0 < (q : ℝ),
      ∀ hEnd : t + (q : ℝ) < T,
        H3PreterminalCanonicalL2JetContinuousOnElapsed
          hNS ht hEnd hTail

/-- Complete physical H³ `L²`-jet continuity immediately gives the exact
zeroth/third endpoint continuity required by the restart stack. -/
theorem h3PreterminalTailUnitViscosityEndpointContinuityOnRestartRadius_of_l2Jet
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hL2 :
      H3PreterminalTailUnitViscosityPhysicalL2JetContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail) :
    H3PreterminalTailUnitViscosityEndpointContinuityFrontierOnRestartRadius
      E u T t hNS ht hE hTail := by
  intro q hqPos hEnd

  have hJet :
      H3PreterminalCanonicalL2JetContinuousOnElapsed
        hNS ht hEnd hTail :=
    hL2 q hqPos hEnd

  have hZero :
      H3PreterminalCanonicalL2ZeroContinuousOnElapsed
        hNS ht hEnd hTail := by
    intro j
    exact hJet (h3JetSlot0 j)

  have hThird :
      H3PreterminalCanonicalL2ThirdContinuousOnElapsed
        hNS ht hEnd hTail := by
    intro j i k l
    exact hJet (h3JetSlot3 j i k l)

  exact
    h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_zero_third
      hNS ht hEnd hTail hZero hThird

/-- Global full physical H³ `L²`-jet continuity frontier for every retained
canonical H³ tail. -/
def H3PreterminalTailUnitViscosityPhysicalL2JetContinuityFrontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailUnitViscosityPhysicalL2JetContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail

/-- A global full-jet continuity frontier yields real restart directly from the
retained terminal H³ control. -/
theorem h3ControlProducesRealRestart_of_unitViscosityPhysicalL2JetContinuity
    (hL2 : H3PreterminalTailUnitViscosityPhysicalL2JetContinuityFrontier) :
    H3ControlProducesRealRestart := by
  intro u T hNS hControl

  rcases hControl with
    ⟨a₀, M, ha₀, hM, hBound⟩

  let E : ℝ :=
    velocityH3CoordinateBudget M

  have hE : 1 ≤ E := by
    dsimp only [E]
    exact one_le_velocityH3CoordinateBudget hM

  have hR :
      0 < h3FinHeatLerayRestartRadius (1 : ℝ) E :=
    h3SpectralPreterminalCanonicalEnergyRestartRadius_pos
      (one_pos : (0 : ℝ) < 1) hE

  have hTa₀ : 0 < T - a₀ := by
    exact sub_pos.mpr ha₀.2

  let ε : ℝ :=
    min
      ((T - a₀) / 2)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E / 2)

  have hHalfTail :
      0 < (T - a₀) / 2 := by
    linarith

  have hHalfRadius :
      0 < h3FinHeatLerayRestartRadius (1 : ℝ) E / 2 := by
    linarith

  have hε : 0 < ε := by
    dsimp only [ε]
    exact lt_min hHalfTail hHalfRadius

  have hεTail :
      ε ≤ (T - a₀) / 2 := by
    dsimp only [ε]
    exact min_le_left _ _

  have hεRadius :
      ε ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E / 2 := by
    dsimp only [ε]
    exact min_le_right _ _

  let t₀ : ℝ :=
    T - ε

  have ht₀T : t₀ < T := by
    dsimp only [t₀]
    linarith

  have ha₀t₀ : a₀ ≤ t₀ := by
    dsimp only [t₀]
    linarith

  have ht₀Pos : 0 < t₀ :=
    lt_of_lt_of_le ha₀.1 ha₀t₀

  have ht₀ :
      t₀ ∈ Set.Ioo (0 : ℝ) T :=
    ⟨ht₀Pos, ht₀T⟩

  have hTail₀ :
      CanonicalH3TailDataFrom u t₀ T E := by
    intro s hs

    have hsOld :
        s ∈ Set.Ico a₀ T := by
      exact
        ⟨
          le_trans ha₀t₀ hs.1,
          hs.2
        ⟩

    have hsBound :
        VelocityH3BoundAt u s M :=
      hBound s hsOld

    exact
      ⟨
        velocityH3IntegrableAt_of_bound hsBound,
        by
          dsimp only [E]
          exact
            velocityH3EnergyAt_le_coordinateBudget_of_bound
              hsBound
      ⟩

  have hEndpoint :
      H3PreterminalTailUnitViscosityEndpointContinuityFrontierOnRestartRadius
        E u T t₀ hNS ht₀ hE hTail₀ :=
    h3PreterminalTailUnitViscosityEndpointContinuityOnRestartRadius_of_l2Jet
      hNS
      ht₀
      hE
      hTail₀
      (hL2 E hE u T t₀ hNS ht₀ hTail₀)

  have hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        (1 : ℝ)
        E
        (one_pos : (0 : ℝ) < 1)
        u
        T
        t₀
        hNS
        ht₀
        hE
        hTail₀ :=
    h3PreterminalTailPhysicalEvolutionOnRestartRadius_of_unitViscosity_endpointContinuity
      hNS
      ht₀
      hE
      hTail₀
      hEndpoint

  have hLocalPDE :
      H3PreterminalTailUnitViscosityLocalPDEAt
        hNS ht₀ hE hTail₀ :=
    h3PreterminalTailUnitViscosityLocalPDEAt_closed_of_evolution
      hNS
      ht₀
      hE
      hTail₀
      hEvolution

  have hCross :
      T - t₀ <
        h3FinHeatLerayRestartRadius (1 : ℝ) E := by
    have hεLtRadius :
        ε <
          h3FinHeatLerayRestartRadius (1 : ℝ) E := by
      have hHalfLt :
          h3FinHeatLerayRestartRadius (1 : ℝ) E / 2
            <
          h3FinHeatLerayRestartRadius (1 : ℝ) E := by
        linarith

      exact
        lt_of_le_of_lt
          hεRadius
          hHalfLt

    dsimp only [t₀]
    linarith

  exact
    h3PreterminalTailUnitViscosityRealRestartAt_of_localPDE
      hNS
      ht₀
      hE
      hTail₀
      hEvolution
      hCross
      hLocalPDE

/-- Full pressure-free continuation from the single physical H³ `L²`-jet
continuity frontier. -/
theorem h3ControlProducesExtension_of_unitViscosityPhysicalL2JetContinuity
    (hL2 : H3PreterminalTailUnitViscosityPhysicalL2JetContinuityFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_realRestart
      (h3ControlProducesRealRestart_of_unitViscosityPhysicalL2JetContinuity
        hL2)

end

end Euclidean
end Bridge
end PrimeTensor
