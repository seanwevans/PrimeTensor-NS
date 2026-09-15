import PrimeTensor.Fluid.Vorticity.H3.Energy.Derivative.OrderThree
import PrimeTensor.Fluid.Vorticity.H3.Energy.Derivative.EnergyClassTemporalRHS

/-!
# Tail-local third-order H³ energy derivative

The original third-order derivative theorem asked for mixed time/space
regularity on the whole preterminal interval `(0,T)`.  The continuation
argument only uses the high-order energy-class tail `(a,T)`.

This file therefore localizes the final H³ block to that tail:

* third-order mixed time/space differentiability is required only on `(a,T)`;
* the local domination neighborhoods are required to remain inside `(a,T)`.

As for order two, the mixed derivative is also exposed in PDE form: it is enough
to prove that `t ↦ D³u` has `momentumRHS3Component` as derivative.  The
already-proved temporal-RHS identity identifies that field with `D³(∂ₜu)`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3EnergyDerivativeOrderThreeTailLocal
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Genuine third-order mixed time/space regularity, only on the high-order
terminal tail. -/
def H3Order3VelocityMixedTimeDerivativeOnTail
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  ∀ s : ℝ,
    s ∈ Set.Ioo a T →
      ∀
        (j i k l : PrimeTensor.Axis Depth.three)
        (x : Point3),
        HasDerivAt
          (fun r : ℝ =>
            spatial3.d
              i
              (spatial3.d
                k
                (spatial3.d
                  l
                  (loggedVelocityComponent u r j)))
              x)
          (spatial3.d
            i
            (spatial3.d
              k
              (spatial3.d
                l
                (loggedVelocityTemporalComponent u s j)))
            x)
          s

/-- PDE-form third-order time differentiability on a terminal tail.

The derivative value is the already-defined order-three momentum RHS. -/
def H3Order3VelocityTimeDerivativePDEOnTail
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : ℝ → ScalarField3)
    (a T : ℝ) : Prop :=
  ∀ s : ℝ,
    s ∈ Set.Ioo a T →
      ∀
        (j i k l : PrimeTensor.Axis Depth.three)
        (x : Point3),
        HasDerivAt
          (fun r : ℝ =>
            spatial3.d
              i
              (spatial3.d
                k
                (spatial3.d
                  l
                  (loggedVelocityComponent u r j)))
              x)
          (momentumRHS3Component
            (logSpaceTimeVectorField u)
            p s i k l j x)
          s

/-- The PDE-form derivative target implies the canonical tail-local mixed
derivative statement because Navier--Stokes already identifies `D³(∂ₜu)` with
`momentumRHS3Component`. -/
theorem h3Order3VelocityMixedTimeDerivativeOnTail_of_pde
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
      H3Order3VelocityTimeDerivativePDEOnTail u p a T) :
    H3Order3VelocityMixedTimeDerivativeOnTail u a T := by
  intro s hs j i k l x

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
            (spatial3.d
              l
              (loggedVelocityTemporalComponent u s j)))
        =
      momentumRHS3Component
        (logSpaceTimeVectorField u)
        p s i k l j :=
    spatial_d3_loggedVelocityTemporalComponent_eq_momentumRHS3
      hPDE hsPre i k l j

  have h :=
    hTime s hs j i k l x

  rw [hEq]

  exact h

/-- Order-three domination data whose local time neighborhoods stay inside the
same high-order terminal tail. -/
structure H3Order3EnergyDerivativeDominatedOnTailAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T t : ℝ) : Type where

  dominated :
    H3Order3EnergyDerivativeDominatedAt u T t

  timeSet_tail :
    ∀ j i k l : PrimeTensor.Axis Depth.three,
      dominated.timeSet j i k l ⊆ Set.Ioo a T

/-- One tail-local third-order scalar square-energy term has the expected
derivative. -/
theorem hasDerivAt_spatialSquareEnergy_spatial_d3_loggedVelocityComponent_onTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hMixed :
      H3Order3VelocityMixedTimeDerivativeOnTail u a T)
    (hInt : VelocityH3IntegrableAt u t)
    (hDom : H3Order3EnergyDerivativeDominatedOnTailAt u a T t)
    (j i k l : PrimeTensor.Axis Depth.three) :
    HasDerivAt
      (fun s : ℝ =>
        spatialSquareEnergy
          (spatial3.d
            i
            (spatial3.d
              k
              (spatial3.d
                l
                (loggedVelocityComponent u s j)))))
      (spatialEnergyPairing
        (spatial3.d
          i
          (spatial3.d
            k
            (spatial3.d
              l
              (loggedVelocityComponent u t j))))
        (spatial3.d
          i
          (spatial3.d
            k
            (spatial3.d
              l
              (loggedVelocityTemporalComponent u t j)))))
      t := by
  have hSquareInt :
      Integrable
        (fun x : Point3 =>
          (spatial3.d
            i
            (spatial3.d
              k
              (spatial3.d
                l
                (loggedVelocityComponent u t j)))
            x) ^ 2)
        (volume : Measure Point3) := by
    exact
      (hInt j).2.2.2 i k l

  have hDiff :
      ∀ᵐ x : Point3 ∂(volume : Measure Point3),
        ∀ s ∈ hDom.dominated.timeSet j i k l,
          HasDerivAt
            (fun r : ℝ =>
              (spatial3.d
                i
                (spatial3.d
                  k
                  (spatial3.d
                    l
                    (loggedVelocityComponent u r j)))
                x) ^ 2)
            (2 *
              spatial3.d
                i
                (spatial3.d
                  k
                  (spatial3.d
                    l
                    (loggedVelocityComponent u s j)))
                x *
              spatial3.d
                i
                (spatial3.d
                  k
                  (spatial3.d
                    l
                    (loggedVelocityTemporalComponent u s j)))
                x)
            s := by
    filter_upwards with x
    intro s hs

    have hsTail :
        s ∈ Set.Ioo a T :=
      hDom.timeSet_tail j i k l hs

    exact
      hasDerivAt_sq_two_mul
        (f := fun r =>
          spatial3.d
            i
            (spatial3.d
              k
              (spatial3.d
                l
                (loggedVelocityComponent u r j))))
        (ft := fun r =>
          spatial3.d
            i
            (spatial3.d
              k
              (spatial3.d
                l
                (loggedVelocityTemporalComponent u r j))))
        (s := s)
        (x := x)
        (hMixed s hsTail j i k l x)

  exact
    hasDerivAt_spatialSquareEnergy_of_dominated
      (f := fun s =>
        spatial3.d
          i
          (spatial3.d
            k
            (spatial3.d
              l
              (loggedVelocityComponent u s j))))
      (ft := fun s =>
        spatial3.d
          i
          (spatial3.d
            k
            (spatial3.d
              l
              (loggedVelocityTemporalComponent u s j))))
      (t := t)
      (S := hDom.dominated.timeSet j i k l)
      (bound := hDom.dominated.bound j i k l)
      (hDom.dominated.timeSet_mem_nhds j i k l)
      (hDom.dominated.square_aestronglyMeasurable j i k l)
      hSquareInt
      (hDom.dominated.derivative_aestronglyMeasurable j i k l)
      (hDom.dominated.derivative_le_bound j i k l)
      (hDom.dominated.bound_integrable j i k l)
      hDiff

/-- The complete third-order H³ energy block has its exact derivative using
only tail-local mixed regularity and tail-local domination. -/
theorem hasDerivAt_velocityH3Energy3At_of_tail_mixed_of_tail_dominated
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hMixed :
      H3Order3VelocityMixedTimeDerivativeOnTail u a T)
    (hInt : VelocityH3IntegrableAt u t)
    (hDom : H3Order3EnergyDerivativeDominatedOnTailAt u a T t) :
    HasDerivAt
      (velocityH3Energy3At u)
      (velocityH3FormalDerivative3At u t)
      t := by
  have hEach :
      ∀ j i k l : PrimeTensor.Axis Depth.three,
        HasDerivAt
          (fun s : ℝ =>
            spatialSquareEnergy
              (spatial3.d
                i
                (spatial3.d
                  k
                  (spatial3.d
                    l
                    (loggedVelocityComponent u s j)))))
          (spatialEnergyPairing
            (spatial3.d
              i
              (spatial3.d
                k
                (spatial3.d
                  l
                  (loggedVelocityComponent u t j))))
            (spatial3.d
              i
              (spatial3.d
                k
                (spatial3.d
                  l
                  (loggedVelocityTemporalComponent u t j)))))
          t := by
    intro j i k l
    exact
      hasDerivAt_spatialSquareEnergy_spatial_d3_loggedVelocityComponent_onTail
        hMixed hInt hDom j i k l

  have hL :
      ∀ j i k : PrimeTensor.Axis Depth.three,
        HasDerivAt
          (fun s : ℝ =>
            ∑ l : PrimeTensor.Axis Depth.three,
              spatialSquareEnergy
                (spatial3.d
                  i
                  (spatial3.d
                    k
                    (spatial3.d
                      l
                      (loggedVelocityComponent u s j)))))
          (∑ l : PrimeTensor.Axis Depth.three,
            spatialEnergyPairing
              (spatial3.d
                i
                (spatial3.d
                  k
                  (spatial3.d
                    l
                    (loggedVelocityComponent u t j))))
              (spatial3.d
                i
                (spatial3.d
                  k
                  (spatial3.d
                    l
                    (loggedVelocityTemporalComponent u t j)))))
          t := by
    intro j i k
    apply HasDerivAt.fun_sum
    intro l hl
    exact hEach j i k l

  have hK :
      ∀ j i : PrimeTensor.Axis Depth.three,
        HasDerivAt
          (fun s : ℝ =>
            ∑ k : PrimeTensor.Axis Depth.three,
              ∑ l : PrimeTensor.Axis Depth.three,
                spatialSquareEnergy
                  (spatial3.d
                    i
                    (spatial3.d
                      k
                      (spatial3.d
                        l
                        (loggedVelocityComponent u s j)))))
          (∑ k : PrimeTensor.Axis Depth.three,
            ∑ l : PrimeTensor.Axis Depth.three,
              spatialEnergyPairing
                (spatial3.d
                  i
                  (spatial3.d
                    k
                    (spatial3.d
                      l
                      (loggedVelocityComponent u t j))))
                (spatial3.d
                  i
                  (spatial3.d
                    k
                    (spatial3.d
                      l
                      (loggedVelocityTemporalComponent u t j)))))
          t := by
    intro j i
    apply HasDerivAt.fun_sum
    intro k hk
    exact hL j i k

  have hI :
      ∀ j : PrimeTensor.Axis Depth.three,
        HasDerivAt
          (fun s : ℝ =>
            ∑ i : PrimeTensor.Axis Depth.three,
              ∑ k : PrimeTensor.Axis Depth.three,
                ∑ l : PrimeTensor.Axis Depth.three,
                  spatialSquareEnergy
                    (spatial3.d
                      i
                      (spatial3.d
                        k
                        (spatial3.d
                          l
                          (loggedVelocityComponent u s j)))))
          (∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              ∑ l : PrimeTensor.Axis Depth.three,
                spatialEnergyPairing
                  (spatial3.d
                    i
                    (spatial3.d
                      k
                      (spatial3.d
                        l
                        (loggedVelocityComponent u t j))))
                  (spatial3.d
                    i
                    (spatial3.d
                      k
                      (spatial3.d
                        l
                        (loggedVelocityTemporalComponent u t j)))))
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
                ∑ l : PrimeTensor.Axis Depth.three,
                  spatialSquareEnergy
                    (spatial3.d
                      i
                      (spatial3.d
                        k
                        (spatial3.d
                          l
                          (loggedVelocityComponent u s j)))))
        (∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              ∑ l : PrimeTensor.Axis Depth.three,
                spatialEnergyPairing
                  (spatial3.d
                    i
                    (spatial3.d
                      k
                      (spatial3.d
                        l
                        (loggedVelocityComponent u t j))))
                  (spatial3.d
                    i
                    (spatial3.d
                      k
                      (spatial3.d
                        l
                        (loggedVelocityTemporalComponent u t j)))))
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
              ∑ l : PrimeTensor.Axis Depth.three,
                spatialSquareEnergy
                  (spatial3.d
                    i
                    (spatial3.d
                      k
                      (spatial3.d
                        l
                        (loggedVelocityComponent u s j)))))
      (∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            ∑ l : PrimeTensor.Axis Depth.three,
              spatialEnergyPairing
                (spatial3.d
                  i
                  (spatial3.d
                    k
                    (spatial3.d
                      l
                      (loggedVelocityComponent u t j))))
                (spatial3.d
                  i
                  (spatial3.d
                    k
                    (spatial3.d
                      l
                      (loggedVelocityTemporalComponent u t j)))))
      t

  exact hSum

end

end Euclidean
end Bridge
end PrimeTensor
