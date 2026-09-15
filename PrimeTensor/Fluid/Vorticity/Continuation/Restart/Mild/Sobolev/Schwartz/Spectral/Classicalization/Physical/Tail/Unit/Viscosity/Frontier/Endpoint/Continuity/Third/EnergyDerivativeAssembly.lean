import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.EnergyDerivativeContinuity
import PrimeTensor.Fluid.Vorticity.H3.Energy.Derivative.OrderThree

/-!
# Assemble the orderwise H³ energy derivatives on the controlled tail

Orders zero through three now have exact derivative theorems.

The continuation argument already carries `TerminalTailH3Control`, hence on the
late controlled tail it already has `VelocityH3IntegrableAt`.  We should not
artificially require `PreterminalH3EnergyClass` itself to produce that
integrability.

This file therefore isolates only the genuinely remaining energy-class
analytic inputs:

* order-two mixed time/space regularity;
* order-three mixed time/space regularity;
* local dominated-integral data for orders zero through three.

At each late time where the external H³ control supplies square integrability,
these inputs assemble to `H3OrderEnergyDerivativeIdentities`.  The existing
pressure-free scalar-energy continuation argument can then be run directly.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3EnergyDerivativeAssembly
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The four local dominated-integral witnesses at one time. -/
structure H3EnergyDerivativeDominationDataAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ) : Type where

  order0 :
    H3Order0EnergyDerivativeDominatedAt u T t

  order1 :
    H3Order1EnergyDerivativeDominatedAt u T t

  order2 :
    H3Order2EnergyDerivativeDominatedAt u T t

  order3 :
    H3Order3EnergyDerivativeDominatedAt u T t

/-- Minimal energy-class-side data still needed by the orderwise derivative
proofs.

Square integrability is intentionally absent.  It is supplied later by the
already-existing terminal H³ control. -/
def EnergyClassProducesH3EnergyDerivativeTailInputs : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ),
      PreterminalH3EnergyClass u a T →
        H3Order2VelocityMixedTimeDerivativeOnPreterminal u T
          ∧
        H3Order3VelocityMixedTimeDerivativeOnPreterminal u T
          ∧
        ∀ t : ℝ,
          t ∈ Set.Ioo a T →
            Nonempty
              (H3EnergyDerivativeDominationDataAt u T t)

/-- Assemble all four orderwise derivative identities at one controlled
preterminal time. -/
theorem h3OrderEnergyDerivativeIdentities_of_integrable_of_tailInputs
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hInt : VelocityH3IntegrableAt u t)
    (hMixed2 :
      H3Order2VelocityMixedTimeDerivativeOnPreterminal u T)
    (hMixed3 :
      H3Order3VelocityMixedTimeDerivativeOnPreterminal u T)
    (hDom : H3EnergyDerivativeDominationDataAt u T t) :
    H3OrderEnergyDerivativeIdentities u t := by
  refine ⟨?_, ?_, ?_, ?_⟩

  · exact
      hasDerivAt_velocityH3Energy0At_of_dominated
        hNS ht hInt hDom.order0

  · exact
      hasDerivAt_velocityH3Energy1At_of_dominated
        hNS ht hInt hDom.order1

  · exact
      hasDerivAt_velocityH3Energy2At_of_mixed_of_dominated
        hMixed2 hInt hDom.order2

  · exact
      hasDerivAt_velocityH3Energy3At_of_mixed_of_dominated
        hMixed3 hInt hDom.order3

/-- Select a late restart inside both the controlled H³ tail and the
high-regularity energy-class tail.  Integrability comes from the former;
mixed-time and domination data come from the latter. -/
theorem h3PreterminalTailUnitViscosityLateEnergyContinuousRestartData_of_smoothing_of_energyDerivativeTailInputs
    (hSmooth : H3SeedProducesEnergyClass)
    (hInputs : EnergyClassProducesH3EnergyDerivativeTailInputs)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hControl : TerminalTailH3Control u T) :
    H3PreterminalTailUnitViscosityLateEnergyContinuousRestartData u T := by
  rcases hControl with ⟨a₀, M, ha₀, hM, hBound⟩

  have hSeed : PreterminalH3Seed u T := by
    exact
      ⟨
        a₀,
        M,
        ha₀,
        hM,
        hBound a₀ ⟨le_rfl, ha₀.2⟩
      ⟩

  rcases hSmooth u T hNS hSeed with ⟨a₁, hClass⟩

  have ha₁ : a₁ ∈ Set.Ioo (0 : ℝ) T :=
    hClass.terminal_start

  rcases hInputs u a₁ T hClass with
    ⟨hMixed2, hMixed3, hLocalInputs⟩

  let E : ℝ :=
    velocityH3CoordinateBudget M

  have hE : 1 ≤ E := by
    dsimp only [E]
    exact one_le_velocityH3CoordinateBudget hM

  have hR :
      0 < h3FinHeatLerayRestartRadius (1 : ℝ) E :=
    h3SpectralPreterminalCanonicalEnergyRestartRadius_pos
      (one_pos : (0 : ℝ) < 1) hE

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

  have hTb : 0 < T - b := by
    linarith

  let ε : ℝ :=
    min
      ((T - b) / 2)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E / 2)

  have hHalfTail :
      0 < (T - b) / 2 := by
    linarith

  have hHalfRadius :
      0 < h3FinHeatLerayRestartRadius (1 : ℝ) E / 2 := by
    linarith

  have hε : 0 < ε := by
    dsimp only [ε]
    exact lt_min hHalfTail hHalfRadius

  have hεTail :
      ε ≤ (T - b) / 2 := by
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
        velocityH3IntegrableAt_of_bound hsBound,
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
      velocityH3IntegrableAt_of_bound hsBound

    rcases hLocalInputs s hsA₁ with
      ⟨hDom⟩

    exact
      h3OrderEnergyDerivativeIdentities_of_integrable_of_tailInputs
        hNS
        hsPre
        hsInt
        hMixed2
        hMixed3
        hDom

  have hCont₀ :
      CanonicalH3EnergyContinuousOnTail u t₀ T :=
    canonicalH3EnergyContinuousOnTail_of_derivativeIdentities_after
      hb₀Strict
      ht₀T
      hDerivativeB

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
    ⟨
      E,
      t₀,
      hE,
      ht₀,
      hTail₀,
      hCont₀,
      hCross
    ⟩

/-- Real restart from smoothing plus the exact remaining orderwise
mixed-time/domination inputs. -/
theorem h3ControlProducesRealRestart_of_unitViscositySmoothingEnergyDerivativeTailInputs
    (hSmooth : H3SeedProducesEnergyClass)
    (hInputs : EnergyClassProducesH3EnergyDerivativeTailInputs) :
    H3ControlProducesRealRestart := by
  intro u T hNS hControl

  obtain
    ⟨E, t, hE, ht, hTail, hCont, hCross⟩ :=
    h3PreterminalTailUnitViscosityLateEnergyContinuousRestartData_of_smoothing_of_energyDerivativeTailInputs
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

/-- Pressure-free continuation now depends only on smoothing plus the explicit
orderwise mixed-time/domination frontier. -/
theorem h3ControlProducesExtension_of_unitViscositySmoothingEnergyDerivativeTailInputs
    (hSmooth : H3SeedProducesEnergyClass)
    (hInputs : EnergyClassProducesH3EnergyDerivativeTailInputs) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_realRestart
      (h3ControlProducesRealRestart_of_unitViscositySmoothingEnergyDerivativeTailInputs
        hSmooth
        hInputs)

end

end Euclidean
end Bridge
end PrimeTensor
