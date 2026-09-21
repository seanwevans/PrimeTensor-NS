import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathTemporalJetSquareFrontier

/-!
# Replace the temporal H³ square frontier by momentum-RHS square mass

The previous reduction isolated the only remaining temporal requirement as
square-integrability of

    D^α ∂ₜu,    |α| ≤ 3.

At every strict energy-class time, however, the already-proved momentum
identities identify these fields exactly with the corresponding differentiated
Navier--Stokes right-hand side.

This file therefore removes the temporal derivative from the analytic
frontier.  The new fixed-time package asks only for square-integrability of

    RHS₀, RHS₁, RHS₂, RHS₃

for the canonical split pressure.

No estimate is used here.  This is only exact PDE substitution.  The remaining
frontier is now purely spatial and can be split next into diffusion, transport,
and pressure mass.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3PathMomentumRHSSquareFrontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Fixed-time momentum-RHS square mass -/

/--
Square-integrability of every differentiated momentum right-hand-side
component through order three.
-/
def H3MomentumRHSSquareIntegrableAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (t : ℝ) : Prop :=
  (
    ∀ j : PrimeTensor.Axis Depth.three,
      SpatialL2SquareIntegrable
        (momentumRHS0Component
          (logSpaceTimeVectorField u)
          p t j)
  )
    ∧
  (
    ∀ i j : PrimeTensor.Axis Depth.three,
      SpatialL2SquareIntegrable
        (momentumRHS1Component
          (logSpaceTimeVectorField u)
          p t i j)
  )
    ∧
  (
    ∀ i k j : PrimeTensor.Axis Depth.three,
      SpatialL2SquareIntegrable
        (momentumRHS2Component
          (logSpaceTimeVectorField u)
          p t i k j)
  )
    ∧
  (
    ∀ i k l j : PrimeTensor.Axis Depth.three,
      SpatialL2SquareIntegrable
        (momentumRHS3Component
          (logSpaceTimeVectorField u)
          p t i k l j)
  )

/--
Path-level momentum-RHS square-mass frontier, using the canonical split
pressure attached to the energy class.
-/
def H3PathEnergyClassProducesMomentumRHSSquareIntegrability : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        ∀ hClass : PreterminalH3EnergyClass u a T,
          ∀ t : ℝ,
            ∀ ht : t ∈ Set.Ioo a T,
              H3MomentumRHSSquareIntegrableAt
                u
                (h3EnergyClassSplitPressureAt hClass ht)
                t

/-! ## Exact PDE substitution -/

/--
At one strict energy-class time, momentum-RHS square-integrability gives
square-integrability of the complete temporal H³ jet by exact Navier--Stokes
identities.
-/
theorem h3TemporalJetSquareIntegrableAt_of_momentumRHSSquareIntegrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hRHS :
      H3MomentumRHSSquareIntegrableAt
        u
        (h3EnergyClassSplitPressureAt hClass ht)
        t) :
    H3TemporalJetSquareIntegrableAt u t := by

  let p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    h3EnergyClassSplitPressureAt hClass ht

  have hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T := by
    dsimp only [p]
    exact
      h3EnergyClassSplitPressureAt_navierStokes
        hClass ht

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 ht.1,
      ht.2
    ⟩

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro j

    have hEq :
        loggedVelocityTemporalComponent u t j
          =
        momentumRHS0Component
          (logSpaceTimeVectorField u)
          p t j :=
      loggedVelocityTemporalComponent_eq_momentumRHS0
        hPDE htAbs j

    rw [hEq]

    dsimp only [p] at *
    exact hRHS.1 j

  · intro i j

    have hEq :
        spatial3.d i
            (loggedVelocityTemporalComponent u t j)
          =
        momentumRHS1Component
          (logSpaceTimeVectorField u)
          p t i j :=
      spatial_d_loggedVelocityTemporalComponent_eq_momentumRHS1
        hPDE htAbs i j

    rw [hEq]

    dsimp only [p] at *
    exact hRHS.2.1 i j

  · intro i k j

    have hEq :
        spatial3.d i
            (spatial3.d k
              (loggedVelocityTemporalComponent u t j))
          =
        momentumRHS2Component
          (logSpaceTimeVectorField u)
          p t i k j :=
      spatial_d2_loggedVelocityTemporalComponent_eq_momentumRHS2
        hPDE htAbs i k j

    rw [hEq]

    dsimp only [p] at *
    exact hRHS.2.2.1 i k j

  · intro i k l j

    have hEq :
        spatial3.d i
            (spatial3.d k
              (spatial3.d l
                (loggedVelocityTemporalComponent u t j)))
          =
        momentumRHS3Component
          (logSpaceTimeVectorField u)
          p t i k l j :=
      spatial_d3_loggedVelocityTemporalComponent_eq_momentumRHS3
        hPDE htAbs i k l j

    rw [hEq]

    dsimp only [p] at *
    exact hRHS.2.2.2 i k l j

/--
Path-level momentum-RHS square mass closes the temporal-jet square frontier.
-/
theorem h3PathEnergyClassProducesTemporalJetSquareIntegrability_of_momentumRHSSquareIntegrability
    (hRHS :
      H3PathEnergyClassProducesMomentumRHSSquareIntegrability) :
    H3PathEnergyClassProducesTemporalJetSquareIntegrability := by

  intro u T hH3 a hClass t ht

  exact
    h3TemporalJetSquareIntegrableAt_of_momentumRHSSquareIntegrable
      hClass
      ht
      (hRHS u T hH3 a hClass t ht)

/-! ## BKM closure at the spatial momentum-RHS frontier -/

/--
BKM continuation with all explicit temporal-jet mass assumptions removed.
The remaining time-side square-mass input is stated entirely through the
spatial Navier--Stokes momentum RHS.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_momentumRHSSquareIntegrability_of_fullScalarEnergy
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hRHS :
      H3PathEnergyClassProducesMomentumRHSSquareIntegrability)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_temporalJetSquareIntegrability_of_fullScalarEnergy
      hLow
      hDerivative
      (h3PathEnergyClassProducesTemporalJetSquareIntegrability_of_momentumRHSSquareIntegrability
        hRHS)
      hFull

end

end Euclidean
end Bridge
end PrimeTensor
