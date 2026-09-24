import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Energy.Continuity.Minimal
import PrimeTensor.Fluid.Vorticity.H3.Energy.Derivative

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3EnergyDerivativeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The remaining differentiation-under-integral obligation on an energy-class tail. -/
def EnergyClassProducesH3OrderEnergyDerivativeIdentities : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ),
      PreterminalH3EnergyClass u a T →
      ∀ t : ℝ,
        t ∈ Set.Ioo a T →
          H3OrderEnergyDerivativeIdentities u t

/-- The older full canonical-data interface implies the smaller derivative-identity interface. -/
theorem energyClassProducesH3OrderEnergyDerivativeIdentities_of_canonicalData
    (hCanonical : EnergyClassProducesCanonicalH3Data) :
    EnergyClassProducesH3OrderEnergyDerivativeIdentities := by
  intro u a T hClass t ht
  have hData : CanonicalH3EnergyDataOnTail u a T :=
    hCanonical u a T hClass
  rcases hData.2.2 with ⟨p, hNS, hAnalytic⟩
  exact (hAnalytic t ht).1

/-- Derivative identities on `(a,T)` give scalar H³-energy continuity on every later tail. -/
theorem canonicalH3EnergyContinuousOnTail_of_derivativeIdentities_after
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a t T : ℝ}
    (hat : a < t)
    (htT : t < T)
    (hDerivative :
      ∀ s : ℝ,
        s ∈ Set.Ioo a T →
          H3OrderEnergyDerivativeIdentities u s) :
    CanonicalH3EnergyContinuousOnTail u t T := by
  intro b hb
  intro s hs
  have hsTail : s ∈ Set.Ioo a T := by
    constructor
    · exact lt_of_lt_of_le hat hs.1
    · exact lt_of_le_of_lt hs.2 hb.2
  exact
    (hasDerivAt_velocityH3EnergyAt
      (hDerivative s hsTail)).continuousAt.continuousWithinAt

/-- Select a late restart strictly inside the energy-class tail, so the derivative identities
supply the scalar energy continuity required by the pressure-free endpoint theorem. -/
theorem h3PreterminalTailUnitViscosityLateEnergyContinuousRestartData_of_smoothing_of_derivativeIdentities
    (hSmooth : H3SeedProducesEnergyClass)
    (hDerivative : EnergyClassProducesH3OrderEnergyDerivativeIdentities)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hControl : TerminalTailH3Control u T) :
    H3PreterminalTailUnitViscosityLateEnergyContinuousRestartData u T := by
  rcases hControl with ⟨a₀, M, ha₀, hM, hBound⟩

  have hSeed : PreterminalH3Seed u T := by
    exact ⟨a₀, M, ha₀, hM, hBound a₀ ⟨le_rfl, ha₀.2⟩⟩

  rcases hSmooth u T hNS hSeed with ⟨a₁, hClass⟩

  have ha₁ : a₁ ∈ Set.Ioo (0 : ℝ) T := hClass.terminal_start

  have hDerivative₁ :
      ∀ s : ℝ,
        s ∈ Set.Ioo a₁ T →
          H3OrderEnergyDerivativeIdentities u s :=
    hDerivative u a₁ T hClass

  let E : ℝ := velocityH3CoordinateBudget M

  have hE : 1 ≤ E := by
    dsimp only [E]
    exact one_le_velocityH3CoordinateBudget hM

  have hR : 0 < h3FinHeatLerayRestartRadius (1 : ℝ) E :=
    h3SpectralPreterminalCanonicalEnergyRestartRadius_pos
      (one_pos : (0 : ℝ) < 1) hE

  let b : ℝ := max a₀ a₁

  have hbT : b < T := by
    dsimp only [b]
    exact max_lt ha₀.2 ha₁.2

  have ha₀b : a₀ ≤ b := by
    dsimp only [b]
    exact le_max_left _ _

  have ha₁b : a₁ ≤ b := by
    dsimp only [b]
    exact le_max_right _ _

  have hTb : 0 < T - b := by linarith

  let ε : ℝ :=
    min ((T - b) / 2)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E / 2)

  have hHalfTail : 0 < (T - b) / 2 := by linarith
  have hHalfRadius :
      0 < h3FinHeatLerayRestartRadius (1 : ℝ) E / 2 := by
    linarith

  have hε : 0 < ε := by
    dsimp only [ε]
    exact lt_min hHalfTail hHalfRadius

  have hεTail : ε ≤ (T - b) / 2 := by
    dsimp only [ε]
    exact min_le_left _ _

  have hεRadius :
      ε ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E / 2 := by
    dsimp only [ε]
    exact min_le_right _ _

  let t₀ : ℝ := T - ε

  have ht₀T : t₀ < T := by
    dsimp only [t₀]
    linarith

  have hb₀ : b ≤ t₀ := by
    dsimp only [t₀]
    linarith

  have hb₀Strict : b < t₀ := by
    dsimp only [t₀]
    linarith

  have ha₁t₀ : a₁ < t₀ := lt_of_le_of_lt ha₁b hb₀Strict

  have ht₀Pos : 0 < t₀ :=
    lt_of_lt_of_le ha₀.1 (le_trans ha₀b hb₀)

  have ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T := ⟨ht₀Pos, ht₀T⟩

  have hTail₀ : CanonicalH3TailDataFrom u t₀ T E := by
    intro s hs
    have hsOld : s ∈ Set.Ico a₀ T := by
      exact ⟨le_trans (le_trans ha₀b hb₀) hs.1, hs.2⟩
    have hsBound : VelocityH3BoundAt u s M := hBound s hsOld
    exact
      ⟨
        velocityH3IntegrableAt_of_bound hsBound,
        by
          dsimp only [E]
          exact velocityH3EnergyAt_le_coordinateBudget_of_bound hsBound
      ⟩

  have hCont₀ : CanonicalH3EnergyContinuousOnTail u t₀ T :=
    canonicalH3EnergyContinuousOnTail_of_derivativeIdentities_after
      ha₁t₀ ht₀T hDerivative₁

  have hCross :
      T - t₀ < h3FinHeatLerayRestartRadius (1 : ℝ) E := by
    have hεLtRadius :
        ε < h3FinHeatLerayRestartRadius (1 : ℝ) E := by
      have hHalfLt :
          h3FinHeatLerayRestartRadius (1 : ℝ) E / 2 <
            h3FinHeatLerayRestartRadius (1 : ℝ) E := by
        linarith
      exact lt_of_le_of_lt hεRadius hHalfLt
    dsimp only [t₀]
    linarith

  exact ⟨E, t₀, hE, ht₀, hTail₀, hCont₀, hCross⟩

/-- Direct real restart from smoothing plus the canonical derivative identities. -/
theorem h3ControlProducesRealRestart_of_unitViscositySmoothingEnergyDerivativeIdentities
    (hSmooth : H3SeedProducesEnergyClass)
    (hDerivative : EnergyClassProducesH3OrderEnergyDerivativeIdentities) :
    H3ControlProducesRealRestart := by
  intro u T hNS hControl

  obtain ⟨E, t, hE, ht, hTail, hCont, hCross⟩ :=
    h3PreterminalTailUnitViscosityLateEnergyContinuousRestartData_of_smoothing_of_derivativeIdentities
      hSmooth hDerivative hNS hControl

  have hEndpoint :
      H3PreterminalTailUnitViscosityEndpointContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail :=
    h3PreterminalTailUnitViscosityEndpointContinuityOnRestartRadius_of_energyContinuity_pressureFree
      hNS ht hE hTail hCont

  have hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        (1 : ℝ) E (one_pos : (0 : ℝ) < 1)
        u T t hNS ht hE hTail :=
    h3PreterminalTailPhysicalEvolutionOnRestartRadius_of_unitViscosity_endpointContinuity
      hNS ht hE hTail hEndpoint

  have hLocalPDE :
      H3PreterminalTailUnitViscosityLocalPDEAt hNS ht hE hTail :=
    h3PreterminalTailUnitViscosityLocalPDEAt_closed_of_evolution
      hNS ht hE hTail hEvolution

  exact
    h3PreterminalTailUnitViscosityRealRestartAt_of_localPDE
      hNS ht hE hTail hEvolution hCross hLocalPDE

/-- Pressure-free continuation reduced to smoothing plus differentiation under the H³ energy integrals. -/
theorem h3ControlProducesExtension_of_unitViscositySmoothingEnergyDerivativeIdentities
    (hSmooth : H3SeedProducesEnergyClass)
    (hDerivative : EnergyClassProducesH3OrderEnergyDerivativeIdentities) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_realRestart
      (h3ControlProducesRealRestart_of_unitViscositySmoothingEnergyDerivativeIdentities
        hSmooth hDerivative)

/-- Compatibility with the older full canonical-data closure. -/
theorem h3ControlProducesExtension_of_unitViscositySmoothingCanonicalEnergy_via_derivativeIdentities
    (hSmooth : H3SeedProducesEnergyClass)
    (hCanonical : EnergyClassProducesCanonicalH3Data) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscositySmoothingEnergyDerivativeIdentities
      hSmooth
      (energyClassProducesH3OrderEnergyDerivativeIdentities_of_canonicalData hCanonical)

end
end Euclidean
end Bridge
end PrimeTensor
