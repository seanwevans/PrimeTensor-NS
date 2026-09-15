import PrimeTensor.Fluid.Vorticity.H3.Energy.Derivative.OrderTwo
import PrimeTensor.Fluid.Vorticity.H3.Energy.Derivative.EnergyClassTemporalRHS

/-!
# Tail-local second-order H³ energy derivative

The first order-two derivative theorem used a mixed-time hypothesis on the
entire preterminal interval `(0,T)`.  That is stronger than continuation needs:
the high-order energy class only exists on a terminal tail `(a,T)`, and the
late restart argument only differentiates there.

This file localizes both ingredients to that same tail:

* the mixed time/space derivative is required only on `(a,T)`;
* the domination neighborhood used by differentiation under the integral is
  explicitly contained in `(a,T)`.

It also records the more PDE-native version of the mixed derivative target:
instead of naming `D²(∂ₜu)` abstractly as the derivative value, one can prove
that `t ↦ D²u` has `momentumRHS2Component` as derivative.  The already-proved
temporal-PDE identity then converts that directly to the canonical mixed
statement.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3EnergyDerivativeOrderTwoTailLocal
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Genuine second-order mixed time/space regularity, only on the high-order
terminal tail. -/
def H3Order2VelocityMixedTimeDerivativeOnTail
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  ∀ s : ℝ,
    s ∈ Set.Ioo a T →
      ∀
        (j i k : PrimeTensor.Axis Depth.three)
        (x : Point3),
        HasDerivAt
          (fun r : ℝ =>
            spatial3.d
              i
              (spatial3.d
                k
                (loggedVelocityComponent u r j))
              x)
          (spatial3.d
            i
            (spatial3.d
              k
              (loggedVelocityTemporalComponent u s j))
            x)
          s

/-- PDE-form second-order time differentiability on a terminal tail.

The derivative value is the already-defined order-two momentum RHS. -/
def H3Order2VelocityTimeDerivativePDEOnTail
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : ℝ → ScalarField3)
    (a T : ℝ) : Prop :=
  ∀ s : ℝ,
    s ∈ Set.Ioo a T →
      ∀
        (j i k : PrimeTensor.Axis Depth.three)
        (x : Point3),
        HasDerivAt
          (fun r : ℝ =>
            spatial3.d
              i
              (spatial3.d
                k
                (loggedVelocityComponent u r j))
              x)
          (momentumRHS2Component
            (logSpaceTimeVectorField u)
            p s i k j x)
          s

/-- The PDE-form derivative target implies the canonical tail-local mixed
derivative statement because the Navier--Stokes equation already identifies
`D²(∂ₜu)` with `momentumRHS2Component`. -/
theorem h3Order2VelocityMixedTimeDerivativeOnTail_of_pde
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : ℝ → ScalarField3}
    {a T : ℝ}
    (hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T)
    (ha : 0 < a)
    (hTime :
      H3Order2VelocityTimeDerivativePDEOnTail u p a T) :
    H3Order2VelocityMixedTimeDerivativeOnTail u a T := by
  intro s hs j i k x

  have hsPre :
      s ∈ Set.Ioo (0 : ℝ) T := by
    exact
      ⟨
        lt_trans ha hs.1,
        hs.2
      ⟩

  have hEq :
      spatial3.d
          i
          (spatial3.d
            k
            (loggedVelocityTemporalComponent u s j))
        =
      momentumRHS2Component
        (logSpaceTimeVectorField u)
        p s i k j :=
    spatial_d2_loggedVelocityTemporalComponent_eq_momentumRHS2
      hPDE hsPre i k j

  have h :=
    hTime s hs j i k x

  rw [hEq]

  exact h

/-- Order-two domination data whose local time neighborhoods stay inside the
same high-order terminal tail. -/
structure H3Order2EnergyDerivativeDominatedOnTailAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T t : ℝ) : Type where

  dominated :
    H3Order2EnergyDerivativeDominatedAt u T t

  timeSet_tail :
    ∀ j i k : PrimeTensor.Axis Depth.three,
      dominated.timeSet j i k ⊆ Set.Ioo a T

/-- One tail-local second-order scalar square-energy term has the expected
derivative. -/
theorem hasDerivAt_spatialSquareEnergy_spatial_d2_loggedVelocityComponent_onTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hMixed :
      H3Order2VelocityMixedTimeDerivativeOnTail u a T)
    (hInt : VelocityH3IntegrableAt u t)
    (hDom : H3Order2EnergyDerivativeDominatedOnTailAt u a T t)
    (j i k : PrimeTensor.Axis Depth.three) :
    HasDerivAt
      (fun s : ℝ =>
        spatialSquareEnergy
          (spatial3.d
            i
            (spatial3.d
              k
              (loggedVelocityComponent u s j))))
      (spatialEnergyPairing
        (spatial3.d
          i
          (spatial3.d
            k
            (loggedVelocityComponent u t j)))
        (spatial3.d
          i
          (spatial3.d
            k
            (loggedVelocityTemporalComponent u t j))))
      t := by
  have hSquareInt :
      Integrable
        (fun x : Point3 =>
          (spatial3.d
            i
            (spatial3.d
              k
              (loggedVelocityComponent u t j))
            x) ^ 2)
        (volume : Measure Point3) := by
    exact
      (hInt j).2.2.1 i k

  have hDiff :
      ∀ᵐ x : Point3 ∂(volume : Measure Point3),
        ∀ s ∈ hDom.dominated.timeSet j i k,
          HasDerivAt
            (fun r : ℝ =>
              (spatial3.d
                i
                (spatial3.d
                  k
                  (loggedVelocityComponent u r j))
                x) ^ 2)
            (2 *
              spatial3.d
                i
                (spatial3.d
                  k
                  (loggedVelocityComponent u s j))
                x *
              spatial3.d
                i
                (spatial3.d
                  k
                  (loggedVelocityTemporalComponent u s j))
                x)
            s := by
    filter_upwards with x
    intro s hs

    have hsTail :
        s ∈ Set.Ioo a T :=
      hDom.timeSet_tail j i k hs

    exact
      hasDerivAt_sq_two_mul
        (f := fun r =>
          spatial3.d
            i
            (spatial3.d
              k
              (loggedVelocityComponent u r j)))
        (ft := fun r =>
          spatial3.d
            i
            (spatial3.d
              k
              (loggedVelocityTemporalComponent u r j)))
        (s := s)
        (x := x)
        (hMixed s hsTail j i k x)

  exact
    hasDerivAt_spatialSquareEnergy_of_dominated
      (f := fun s =>
        spatial3.d
          i
          (spatial3.d
            k
            (loggedVelocityComponent u s j)))
      (ft := fun s =>
        spatial3.d
          i
          (spatial3.d
            k
            (loggedVelocityTemporalComponent u s j)))
      (t := t)
      (S := hDom.dominated.timeSet j i k)
      (bound := hDom.dominated.bound j i k)
      (hDom.dominated.timeSet_mem_nhds j i k)
      (hDom.dominated.square_aestronglyMeasurable j i k)
      hSquareInt
      (hDom.dominated.derivative_aestronglyMeasurable j i k)
      (hDom.dominated.derivative_le_bound j i k)
      (hDom.dominated.bound_integrable j i k)
      hDiff

/-- The complete second-order H³ energy block has its exact derivative using
only tail-local mixed regularity and tail-local domination. -/
theorem hasDerivAt_velocityH3Energy2At_of_tail_mixed_of_tail_dominated
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hMixed :
      H3Order2VelocityMixedTimeDerivativeOnTail u a T)
    (hInt : VelocityH3IntegrableAt u t)
    (hDom : H3Order2EnergyDerivativeDominatedOnTailAt u a T t) :
    HasDerivAt
      (velocityH3Energy2At u)
      (velocityH3FormalDerivative2At u t)
      t := by
  have hEach :
      ∀ j i k : PrimeTensor.Axis Depth.three,
        HasDerivAt
          (fun s : ℝ =>
            spatialSquareEnergy
              (spatial3.d
                i
                (spatial3.d
                  k
                  (loggedVelocityComponent u s j))))
          (spatialEnergyPairing
            (spatial3.d
              i
              (spatial3.d
                k
                (loggedVelocityComponent u t j)))
            (spatial3.d
              i
              (spatial3.d
                k
                (loggedVelocityTemporalComponent u t j))))
          t := by
    intro j i k
    exact
      hasDerivAt_spatialSquareEnergy_spatial_d2_loggedVelocityComponent_onTail
        hMixed hInt hDom j i k

  have hK :
      ∀ j i : PrimeTensor.Axis Depth.three,
        HasDerivAt
          (fun s : ℝ =>
            ∑ k : PrimeTensor.Axis Depth.three,
              spatialSquareEnergy
                (spatial3.d
                  i
                  (spatial3.d
                    k
                    (loggedVelocityComponent u s j))))
          (∑ k : PrimeTensor.Axis Depth.three,
            spatialEnergyPairing
              (spatial3.d
                i
                (spatial3.d
                  k
                  (loggedVelocityComponent u t j)))
              (spatial3.d
                i
                (spatial3.d
                  k
                  (loggedVelocityTemporalComponent u t j))))
          t := by
    intro j i
    apply HasDerivAt.fun_sum
    intro k hk
    exact hEach j i k

  have hI :
      ∀ j : PrimeTensor.Axis Depth.three,
        HasDerivAt
          (fun s : ℝ =>
            ∑ i : PrimeTensor.Axis Depth.three,
              ∑ k : PrimeTensor.Axis Depth.three,
                spatialSquareEnergy
                  (spatial3.d
                    i
                    (spatial3.d
                      k
                      (loggedVelocityComponent u s j))))
          (∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              spatialEnergyPairing
                (spatial3.d
                  i
                  (spatial3.d
                    k
                    (loggedVelocityComponent u t j)))
                (spatial3.d
                  i
                  (spatial3.d
                    k
                    (loggedVelocityTemporalComponent u t j))))
          t := by
    intro j
    apply HasDerivAt.fun_sum
    intro i hi
    exact hK j i

  have hSum :
      HasDerivAt
        (fun s : ℝ =>
          ∑ j : PrimeTensor.Axis Depth.three,
            ∑ i : PrimeTensor.Axis Depth.three,
              ∑ k : PrimeTensor.Axis Depth.three,
                spatialSquareEnergy
                  (spatial3.d
                    i
                    (spatial3.d
                      k
                      (loggedVelocityComponent u s j))))
        (∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              spatialEnergyPairing
                (spatial3.d
                  i
                  (spatial3.d
                    k
                    (loggedVelocityComponent u t j)))
                (spatial3.d
                  i
                  (spatial3.d
                    k
                    (loggedVelocityTemporalComponent u t j))))
        t := by
    apply HasDerivAt.fun_sum
    intro j hj
    exact hI j

  change
    HasDerivAt
      (fun s : ℝ =>
        ∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              spatialSquareEnergy
                (spatial3.d
                  i
                  (spatial3.d
                    k
                    (loggedVelocityComponent u s j))))
      (∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            spatialEnergyPairing
              (spatial3.d
                i
                (spatial3.d
                  k
                  (loggedVelocityComponent u t j)))
              (spatial3.d
                i
                (spatial3.d
                  k
                  (loggedVelocityTemporalComponent u t j))))
      t

  exact hSum

end

end Euclidean
end Bridge
end PrimeTensor
