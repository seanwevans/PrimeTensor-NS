import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Energy.Derivative.Continuity
import PrimeTensor.Fluid.Vorticity.H3.Energy.Derivative.OrderTwoTailLocal
import PrimeTensor.Fluid.Vorticity.H3.Energy.Derivative.OrderThreeTailLocal

/-!
# Assemble the H³ energy derivative using only tail-local higher mixed regularity

The original derivative assembly asked for order-two and order-three mixed
time/space differentiability on the entire preterminal interval `(0,T)`.

That is stronger than the continuation argument uses.  The high-order energy
class begins at a late time `a`, and the restart construction only differentiates
on a still later tail.

This file replaces the global higher mixed assumptions by their tail-local
versions:

* order zero and order one keep the existing preterminal domination packages;
* order two uses `H3Order2VelocityMixedTimeDerivativeOnTail` together with
  `H3Order2EnergyDerivativeDominatedOnTailAt`;
* order three uses `H3Order3VelocityMixedTimeDerivativeOnTail` together with
  `H3Order3EnergyDerivativeDominatedOnTailAt`.

The resulting continuation theorem therefore carries no unnecessary
order-two/order-three commutation claim before the energy-class start time.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3EnergyDerivativeTailLocalAssembly
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The four local dominated-integral witnesses at one tail time.

Orders two and three additionally remember that their domination neighborhoods
remain inside the high-order energy-class tail. -/
structure H3EnergyDerivativeTailLocalDominationDataAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T t : ℝ) : Type where

  order0 :
    H3Order0EnergyDerivativeDominatedAt u T t

  order1 :
    H3Order1EnergyDerivativeDominatedAt u T t

  order2 :
    H3Order2EnergyDerivativeDominatedOnTailAt u a T t

  order3 :
    H3Order3EnergyDerivativeDominatedOnTailAt u a T t

/-- Exact energy-class-side data needed after localizing the higher mixed
regularity to the terminal energy-class tail. -/
def EnergyClassProducesH3EnergyDerivativeTailLocalInputs : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ),
      PreterminalH3EnergyClass u a T →
        H3Order2VelocityMixedTimeDerivativeOnTail u a T
          ∧
        H3Order3VelocityMixedTimeDerivativeOnTail u a T
          ∧
        ∀ t : ℝ,
          t ∈ Set.Ioo a T →
            Nonempty
              (H3EnergyDerivativeTailLocalDominationDataAt
                u a T t)

/-- Assemble all four orderwise derivative identities at one integrable tail
time, using only tail-local higher mixed regularity. -/
theorem h3OrderEnergyDerivativeIdentities_of_integrable_of_tailLocalInputs
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hInt : VelocityH3IntegrableAt u t)
    (hMixed2 :
      H3Order2VelocityMixedTimeDerivativeOnTail u a T)
    (hMixed3 :
      H3Order3VelocityMixedTimeDerivativeOnTail u a T)
    (hDom :
      H3EnergyDerivativeTailLocalDominationDataAt
        u a T t) :
    H3OrderEnergyDerivativeIdentities u t := by
  refine ⟨?_, ?_, ?_, ?_⟩

  · exact
      hasDerivAt_velocityH3Energy0At_of_dominated
        hNS ht hInt hDom.order0

  · exact
      hasDerivAt_velocityH3Energy1At_of_dominated
        hNS ht hInt hDom.order1

  · exact
      hasDerivAt_velocityH3Energy2At_of_tail_mixed_of_tail_dominated
        hMixed2 hInt hDom.order2

  · exact
      hasDerivAt_velocityH3Energy3At_of_tail_mixed_of_tail_dominated
        hMixed3 hInt hDom.order3

/-- Select a late restart inside both the controlled H³ tail and the
high-regularity energy-class tail, now using only tail-local higher mixed
regularity. -/
theorem h3PreterminalTailUnitViscosityLateEnergyContinuousRestartData_of_smoothing_of_energyDerivativeTailLocalInputs
    (hSmooth : H3SeedProducesEnergyClass)
    (hInputs : EnergyClassProducesH3EnergyDerivativeTailLocalInputs)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hControl : TerminalTailH3Control u T) :
    H3PreterminalTailUnitViscosityLateEnergyContinuousRestartData u T := by
  rcases hControl with
    ⟨a₀, M, ha₀, hM, hBound⟩

  have hSeed : PreterminalH3Seed u T := by
    exact
      ⟨
        a₀,
        M,
        ha₀,
        hM,
        hBound a₀ ⟨le_rfl, ha₀.2⟩
      ⟩

  rcases hSmooth u T hNS hSeed with
    ⟨a₁, hClass⟩

  have ha₁ :
      a₁ ∈ Set.Ioo (0 : ℝ) T :=
    hClass.terminal_start

  rcases hInputs u a₁ T hClass with
    ⟨hMixed2, hMixed3, hLocalInputs⟩

  let E : ℝ :=
    velocityH3CoordinateBudget M

  have hE : 1 ≤ E := by
    dsimp only [E]
    exact
      one_le_velocityH3CoordinateBudget hM

  have hR :
      0 <
        h3FinHeatLerayRestartRadius
          (1 : ℝ) E :=
    h3SpectralPreterminalCanonicalEnergyRestartRadius_pos
      (one_pos : (0 : ℝ) < 1)
      hE

  let b : ℝ :=
    max a₀ a₁

  have hbT : b < T := by
    dsimp only [b]
    exact max_lt ha₀.2 ha₁.2

  have ha₀b : a₀ ≤ b := by
    dsimp only [b]
    exact le_max_left _ _

  have ha₁b : a₁ ≤ b := by
    dsimp only [b]
    exact le_max_right _ _

  have hTb :
      0 < T - b := by
    exact sub_pos.mpr hbT

  let ε : ℝ :=
    min
      ((T - b) / 2)
      (h3FinHeatLerayRestartRadius
        (1 : ℝ) E / 2)

  have hHalfTail :
      0 < (T - b) / 2 := by
    linarith

  have hHalfRadius :
      0 <
        h3FinHeatLerayRestartRadius
          (1 : ℝ) E / 2 := by
    linarith

  have hε : 0 < ε := by
    dsimp only [ε]
    exact lt_min hHalfTail hHalfRadius

  have hεTail :
      ε ≤ (T - b) / 2 := by
    dsimp only [ε]
    exact min_le_left _ _

  have hεRadius :
      ε ≤
        h3FinHeatLerayRestartRadius
          (1 : ℝ) E / 2 := by
    dsimp only [ε]
    exact min_le_right _ _

  let t₀ : ℝ :=
    T - ε

  have ht₀T : t₀ < T := by
    dsimp only [t₀]
    linarith

  have hb₀ : b ≤ t₀ := by
    dsimp only [t₀]
    linarith

  have hb₀Strict : b < t₀ := by
    dsimp only [t₀]
    linarith

  have ht₀Pos : 0 < t₀ :=
    lt_of_lt_of_le
      ha₀.1
      (le_trans ha₀b hb₀)

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
          le_trans
            (le_trans ha₀b hb₀)
            hs.1,
          hs.2
        ⟩

    have hsBound :
        VelocityH3BoundAt u s M :=
      hBound s hsOld

    exact
      ⟨
        velocityH3IntegrableAt_of_bound
          hsBound,
        by
          dsimp only [E]
          exact
            velocityH3EnergyAt_le_coordinateBudget_of_bound
              hsBound
      ⟩

  have hDerivativeB :
      ∀ s : ℝ,
        s ∈ Set.Ioo b T →
          H3OrderEnergyDerivativeIdentities u s := by
    intro s hs

    have hsA₀ :
        s ∈ Set.Ico a₀ T := by
      exact
        ⟨
          le_trans ha₀b hs.1.le,
          hs.2
        ⟩

    have hsA₁ :
        s ∈ Set.Ioo a₁ T := by
      exact
        ⟨
          lt_of_le_of_lt ha₁b hs.1,
          hs.2
        ⟩

    have hsPre :
        s ∈ Set.Ioo (0 : ℝ) T := by
      exact
        ⟨
          lt_trans
            (lt_of_lt_of_le ha₀.1 ha₀b)
            hs.1,
          hs.2
        ⟩

    have hsBound :
        VelocityH3BoundAt u s M :=
      hBound s hsA₀

    have hsInt :
        VelocityH3IntegrableAt u s :=
      velocityH3IntegrableAt_of_bound
        hsBound

    rcases hLocalInputs s hsA₁ with
      ⟨hDom⟩

    exact
      h3OrderEnergyDerivativeIdentities_of_integrable_of_tailLocalInputs
        hNS
        hsPre
        hsInt
        hMixed2
        hMixed3
        hDom

  have hCont₀ :
      CanonicalH3EnergyContinuousOnTail
        u t₀ T :=
    canonicalH3EnergyContinuousOnTail_of_derivativeIdentities_after
      hb₀Strict
      ht₀T
      hDerivativeB

  have hCross :
      T - t₀ <
        h3FinHeatLerayRestartRadius
          (1 : ℝ) E := by
    have hεLtRadius :
        ε <
          h3FinHeatLerayRestartRadius
            (1 : ℝ) E := by
      have hHalfLt :
          h3FinHeatLerayRestartRadius
              (1 : ℝ) E / 2
            <
          h3FinHeatLerayRestartRadius
            (1 : ℝ) E := by
        linarith

      exact
        lt_of_le_of_lt
          hεRadius
          hHalfLt

    dsimp only [t₀]
    linarith

  exact
    ⟨
      E,
      t₀,
      hE,
      ht₀,
      hTail₀,
      hCont₀,
      hCross
    ⟩

/-- Real restart from smoothing plus the genuinely tail-local higher
mixed-time/domination inputs. -/
theorem h3ControlProducesRealRestart_of_unitViscositySmoothingEnergyDerivativeTailLocalInputs
    (hSmooth : H3SeedProducesEnergyClass)
    (hInputs : EnergyClassProducesH3EnergyDerivativeTailLocalInputs) :
    H3ControlProducesRealRestart := by
  intro u T hNS hControl

  obtain
    ⟨E, t, hE, ht, hTail, hCont, hCross⟩ :=
    h3PreterminalTailUnitViscosityLateEnergyContinuousRestartData_of_smoothing_of_energyDerivativeTailLocalInputs
      hSmooth
      hInputs
      hNS
      hControl

  have hEndpoint :
      H3PreterminalTailUnitViscosityEndpointContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail :=
    h3PreterminalTailUnitViscosityEndpointContinuityOnRestartRadius_of_energyContinuity_pressureFree
      hNS
      ht
      hE
      hTail
      hCont

  have hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        (1 : ℝ)
        E
        (one_pos : (0 : ℝ) < 1)
        u
        T
        t
        hNS
        ht
        hE
        hTail :=
    h3PreterminalTailPhysicalEvolutionOnRestartRadius_of_unitViscosity_endpointContinuity
      hNS
      ht
      hE
      hTail
      hEndpoint

  have hLocalPDE :
      H3PreterminalTailUnitViscosityLocalPDEAt
        hNS ht hE hTail :=
    h3PreterminalTailUnitViscosityLocalPDEAt_closed_of_evolution
      hNS
      ht
      hE
      hTail
      hEvolution

  exact
    h3PreterminalTailUnitViscosityRealRestartAt_of_localPDE
      hNS
      ht
      hE
      hTail
      hEvolution
      hCross
      hLocalPDE

/-- Pressure-free continuation from smoothing plus only tail-local higher
mixed-time/domination inputs. -/
theorem h3ControlProducesExtension_of_unitViscositySmoothingEnergyDerivativeTailLocalInputs
    (hSmooth : H3SeedProducesEnergyClass)
    (hInputs : EnergyClassProducesH3EnergyDerivativeTailLocalInputs) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_realRestart
      (h3ControlProducesRealRestart_of_unitViscositySmoothingEnergyDerivativeTailLocalInputs
        hSmooth
        hInputs)

end

end Euclidean
end Bridge
end PrimeTensor
