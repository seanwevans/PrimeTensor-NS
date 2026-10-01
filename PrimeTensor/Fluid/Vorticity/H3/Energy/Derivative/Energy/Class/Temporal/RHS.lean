import PrimeTensor.Fluid.Vorticity.H3.Energy.PDE.Decomposition
import PrimeTensor.Fluid.Vorticity.H3.Energy.Regularity

/-!
# Energy-class temporal velocity jets as explicit Navier--Stokes RHS fields

`PreterminalH3EnergyClass` carries an actual pressure witness for the
preterminal Navier--Stokes system.

The PDE decomposition layer already proves

* `∂ₜ uⱼ = RHS₀`,
* `∂ᵢ ∂ₜ uⱼ = RHS₁`,
* `∂ᵢ∂ₖ ∂ₜ uⱼ = RHS₂`,
* `∂ᵢ∂ₖ∂ₗ ∂ₜ uⱼ = RHS₃`.

The higher equalities are exact spatial differentiation of the already-proved
first mixed PDE identity; no interchange of time and higher spatial
differentiation is used here.

This file packages those facts directly from the high-order energy class.
Consequently the remaining order-two/order-three time-regularity problem is
sharply isolated:

    d/dt (D²u) = D²(∂ₜu),
    d/dt (D³u) = D³(∂ₜu).

The right-hand sides themselves are already the concrete momentum fields.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

noncomputable section

/-- The complete temporal-PDE jet identity carried on an energy-class tail. -/
def H3TemporalPDEJetIdentitiesOnTail
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  ∃ p : ℝ → ScalarField3,
    PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T
      ∧
    PressureSpatialC4OnTail p a T
      ∧
    (∀ t : ℝ,
      t ∈ Set.Ioo a T →
        (∀ j : PrimeTensor.Axis Depth.three,
          loggedVelocityTemporalComponent u t j
            =
          momentumRHS0Component
            (logSpaceTimeVectorField u)
            p t j)
        ∧
        (∀ i j : PrimeTensor.Axis Depth.three,
          spatial3.d
              i
              (loggedVelocityTemporalComponent u t j)
            =
          momentumRHS1Component
            (logSpaceTimeVectorField u)
            p t i j)
        ∧
        (∀ i k j : PrimeTensor.Axis Depth.three,
          spatial3.d
              i
              (spatial3.d
                k
                (loggedVelocityTemporalComponent u t j))
            =
          momentumRHS2Component
            (logSpaceTimeVectorField u)
            p t i k j)
        ∧
        (∀ i k l j : PrimeTensor.Axis Depth.three,
          spatial3.d
              i
              (spatial3.d
                k
                (spatial3.d
                  l
                  (loggedVelocityTemporalComponent u t j)))
            =
          momentumRHS3Component
            (logSpaceTimeVectorField u)
            p t i k l j))

/-- Every high-order energy class already supplies the complete temporal-PDE
jet identity on its open terminal tail. -/
theorem preterminalH3EnergyClass_produces_temporalPDEJetIdentities
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hClass : PreterminalH3EnergyClass u a T) :
    H3TemporalPDEJetIdentitiesOnTail u a T := by
  rcases hClass.pressure_witness with
    ⟨p, hPDE, hPressure⟩

  refine ⟨p, hPDE, hPressure, ?_⟩

  intro t ht

  have htPre :
      t ∈ Set.Ioo (0 : ℝ) T := by
    exact
      ⟨
        lt_trans hClass.terminal_start.1 ht.1,
        ht.2
      ⟩

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro j
    exact
      loggedVelocityTemporalComponent_eq_momentumRHS0
        hPDE htPre j

  · intro i j
    exact
      spatial_d_loggedVelocityTemporalComponent_eq_momentumRHS1
        hPDE htPre i j

  · intro i k j
    exact
      spatial_d2_loggedVelocityTemporalComponent_eq_momentumRHS2
        hPDE htPre i k j

  · intro i k l j
    exact
      spatial_d3_loggedVelocityTemporalComponent_eq_momentumRHS3
        hPDE htPre i k l j

/-- In particular, the second spatial derivative of the canonical temporal
velocity field is exactly the order-two momentum RHS throughout the
energy-class tail. -/
theorem preterminalH3EnergyClass_spatial_d2_temporal_eq_momentumRHS2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    ∃ p : ℝ → ScalarField3,
      PreterminalNavierStokes3
          (logSpaceTimeVectorField u)
          p
          T
        ∧
      PressureSpatialC4OnTail p a T
        ∧
      ∀ i k j : PrimeTensor.Axis Depth.three,
        spatial3.d
            i
            (spatial3.d
              k
              (loggedVelocityTemporalComponent u t j))
          =
        momentumRHS2Component
          (logSpaceTimeVectorField u)
          p t i k j := by
  rcases
    preterminalH3EnergyClass_produces_temporalPDEJetIdentities hClass with
    ⟨p, hPDE, hPressure, hJets⟩

  exact
    ⟨
      p,
      hPDE,
      hPressure,
      (hJets t ht).2.2.1
    ⟩

/-- Likewise, the third spatial derivative of the canonical temporal velocity
field is exactly the order-three momentum RHS throughout the energy-class
tail. -/
theorem preterminalH3EnergyClass_spatial_d3_temporal_eq_momentumRHS3
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    ∃ p : ℝ → ScalarField3,
      PreterminalNavierStokes3
          (logSpaceTimeVectorField u)
          p
          T
        ∧
      PressureSpatialC4OnTail p a T
        ∧
      ∀ i k l j : PrimeTensor.Axis Depth.three,
        spatial3.d
            i
            (spatial3.d
              k
              (spatial3.d
                l
                (loggedVelocityTemporalComponent u t j)))
          =
        momentumRHS3Component
          (logSpaceTimeVectorField u)
          p t i k l j := by
  rcases
    preterminalH3EnergyClass_produces_temporalPDEJetIdentities hClass with
    ⟨p, hPDE, hPressure, hJets⟩

  exact
    ⟨
      p,
      hPDE,
      hPressure,
      (hJets t ht).2.2.2
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
