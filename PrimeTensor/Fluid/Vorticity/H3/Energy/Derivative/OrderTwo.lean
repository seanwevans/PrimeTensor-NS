import PrimeTensor.Fluid.Vorticity.H3.Energy.Derivative.OrderOne

/-!
# Second-order canonical H³ energy derivative

Orders zero and one use mixed time regularity already present in the
preterminal Navier--Stokes structure.

At order two a new distinction appears.  The current high-order energy class
provides strong spatial regularity, but it does not itself state that time
differentiation commutes through two spatial derivatives.

This file therefore separates the two remaining analytic inputs:

* `H3Order2VelocityMixedTimeDerivativeOnPreterminal`:
  genuine pointwise `HasDerivAt` for
  `t ↦ ∂ᵢ∂ₖ uⱼ`;
* `H3Order2EnergyDerivativeDominatedAt`:
  the local dominated-integral package for
  `2 (∂ᵢ∂ₖuⱼ)(∂ᵢ∂ₖ∂ₜuⱼ)`.

Given those two inputs and the existing H³ square integrability, the complete
second-order energy block has its exact formal derivative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3EnergyDerivativeOrderTwo
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Genuine second-order mixed time/space regularity on the preterminal
interval.

This is the exact commutation statement missing from the current energy-class
structure. -/
def H3Order2VelocityMixedTimeDerivativeOnPreterminal
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) : Prop :=
  ∀ s : ℝ,
    s ∈ Set.Ioo (0 : ℝ) T →
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

/-- Exact local domination data needed for all second-order square-energy
integrals at one preterminal time. -/
structure H3Order2EnergyDerivativeDominatedAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ) : Type where

  timeSet :
    PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
        PrimeTensor.Axis Depth.three →
          Set ℝ

  bound :
    PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
        PrimeTensor.Axis Depth.three →
          Point3 → ℝ

  timeSet_mem_nhds :
    ∀ j i k : PrimeTensor.Axis Depth.three,
      timeSet j i k ∈ 𝓝 t

  timeSet_preterminal :
    ∀ j i k : PrimeTensor.Axis Depth.three,
      timeSet j i k ⊆ Set.Ioo (0 : ℝ) T

  square_aestronglyMeasurable :
    ∀ j i k : PrimeTensor.Axis Depth.three,
      ∀ᶠ s in 𝓝 t,
        AEStronglyMeasurable
          (fun x : Point3 =>
            (spatial3.d
              i
              (spatial3.d
                k
                (loggedVelocityComponent u s j))
              x) ^ 2)
          (volume : Measure Point3)

  derivative_aestronglyMeasurable :
    ∀ j i k : PrimeTensor.Axis Depth.three,
      AEStronglyMeasurable
        (fun x : Point3 =>
          2 *
            spatial3.d
              i
              (spatial3.d
                k
                (loggedVelocityComponent u t j))
              x *
            spatial3.d
              i
              (spatial3.d
                k
                (loggedVelocityTemporalComponent u t j))
              x)
        (volume : Measure Point3)

  derivative_le_bound :
    ∀ j i k : PrimeTensor.Axis Depth.three,
      ∀ᵐ x : Point3 ∂(volume : Measure Point3),
        ∀ s ∈ timeSet j i k,
          norm
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
            ≤
          bound j i k x

  bound_integrable :
    ∀ j i k : PrimeTensor.Axis Depth.three,
      Integrable
        (bound j i k)
        (volume : Measure Point3)

/-- One second-order scalar square-energy term has the expected derivative. -/
theorem hasDerivAt_spatialSquareEnergy_spatial_d2_loggedVelocityComponent
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hMixed :
      H3Order2VelocityMixedTimeDerivativeOnPreterminal u T)
    (hInt : VelocityH3IntegrableAt u t)
    (hDom : H3Order2EnergyDerivativeDominatedAt u T t)
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
        ∀ s ∈ hDom.timeSet j i k,
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

    have hsPre :
        s ∈ Set.Ioo (0 : ℝ) T :=
      hDom.timeSet_preterminal j i k hs

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
        (hMixed s hsPre j i k x)

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
      (S := hDom.timeSet j i k)
      (bound := hDom.bound j i k)
      (hDom.timeSet_mem_nhds j i k)
      (hDom.square_aestronglyMeasurable j i k)
      hSquareInt
      (hDom.derivative_aestronglyMeasurable j i k)
      (hDom.derivative_le_bound j i k)
      (hDom.bound_integrable j i k)
      hDiff

/-- The complete second-order canonical H³ energy block has its exact formal
time derivative. -/
theorem hasDerivAt_velocityH3Energy2At_of_mixed_of_dominated
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hMixed :
      H3Order2VelocityMixedTimeDerivativeOnPreterminal u T)
    (hInt : VelocityH3IntegrableAt u t)
    (hDom : H3Order2EnergyDerivativeDominatedAt u T t) :
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
      hasDerivAt_spatialSquareEnergy_spatial_d2_loggedVelocityComponent
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
