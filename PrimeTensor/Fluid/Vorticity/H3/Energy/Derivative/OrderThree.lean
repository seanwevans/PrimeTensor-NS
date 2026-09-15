import PrimeTensor.Fluid.Vorticity.H3.Energy.Derivative.OrderTwo

/-!
# Third-order canonical H³ energy derivative

The final H³ energy block follows the same decomposition as order two.

The current energy-class structure supplies high spatial regularity but does
not itself state the third mixed time/space commutation

    d/dt (∂ᵢ∂ₖ∂ₗ uⱼ)
      =
    ∂ᵢ∂ₖ∂ₗ (∂ₜ uⱼ).

This file therefore keeps the two genuinely analytic inputs separate:

* `H3Order3VelocityMixedTimeDerivativeOnPreterminal`;
* `H3Order3EnergyDerivativeDominatedAt`.

Together with the existing third-order square integrability, these imply the
exact formal derivative of `velocityH3Energy3At`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3EnergyDerivativeOrderThree
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Genuine third-order mixed time/space regularity on the preterminal
interval. -/
def H3Order3VelocityMixedTimeDerivativeOnPreterminal
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) : Prop :=
  ∀ s : ℝ,
    s ∈ Set.Ioo (0 : ℝ) T →
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

/-- Exact local domination data needed for all third-order square-energy
integrals at one preterminal time. -/
structure H3Order3EnergyDerivativeDominatedAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ) : Type where

  timeSet :
    PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
        PrimeTensor.Axis Depth.three →
          PrimeTensor.Axis Depth.three →
            Set ℝ

  bound :
    PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
        PrimeTensor.Axis Depth.three →
          PrimeTensor.Axis Depth.three →
            Point3 → ℝ

  timeSet_mem_nhds :
    ∀ j i k l : PrimeTensor.Axis Depth.three,
      timeSet j i k l ∈ 𝓝 t

  timeSet_preterminal :
    ∀ j i k l : PrimeTensor.Axis Depth.three,
      timeSet j i k l ⊆ Set.Ioo (0 : ℝ) T

  square_aestronglyMeasurable :
    ∀ j i k l : PrimeTensor.Axis Depth.three,
      ∀ᶠ s in 𝓝 t,
        AEStronglyMeasurable
          (fun x : Point3 =>
            (spatial3.d
              i
              (spatial3.d
                k
                (spatial3.d
                  l
                  (loggedVelocityComponent u s j)))
              x) ^ 2)
          (volume : Measure Point3)

  derivative_aestronglyMeasurable :
    ∀ j i k l : PrimeTensor.Axis Depth.three,
      AEStronglyMeasurable
        (fun x : Point3 =>
          2 *
            spatial3.d
              i
              (spatial3.d
                k
                (spatial3.d
                  l
                  (loggedVelocityComponent u t j)))
              x *
            spatial3.d
              i
              (spatial3.d
                k
                (spatial3.d
                  l
                  (loggedVelocityTemporalComponent u t j)))
              x)
        (volume : Measure Point3)

  derivative_le_bound :
    ∀ j i k l : PrimeTensor.Axis Depth.three,
      ∀ᵐ x : Point3 ∂(volume : Measure Point3),
        ∀ s ∈ timeSet j i k l,
          norm
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
            ≤
          bound j i k l x

  bound_integrable :
    ∀ j i k l : PrimeTensor.Axis Depth.three,
      Integrable
        (bound j i k l)
        (volume : Measure Point3)

/-- One third-order scalar square-energy term has the expected derivative. -/
theorem hasDerivAt_spatialSquareEnergy_spatial_d3_loggedVelocityComponent
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hMixed :
      H3Order3VelocityMixedTimeDerivativeOnPreterminal u T)
    (hInt : VelocityH3IntegrableAt u t)
    (hDom : H3Order3EnergyDerivativeDominatedAt u T t)
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
        ∀ s ∈ hDom.timeSet j i k l,
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

    have hsPre :
        s ∈ Set.Ioo (0 : ℝ) T :=
      hDom.timeSet_preterminal j i k l hs

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
        (hMixed s hsPre j i k l x)

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
      (S := hDom.timeSet j i k l)
      (bound := hDom.bound j i k l)
      (hDom.timeSet_mem_nhds j i k l)
      (hDom.square_aestronglyMeasurable j i k l)
      hSquareInt
      (hDom.derivative_aestronglyMeasurable j i k l)
      (hDom.derivative_le_bound j i k l)
      (hDom.bound_integrable j i k l)
      hDiff

/-- The complete third-order canonical H³ energy block has its exact formal
time derivative. -/
theorem hasDerivAt_velocityH3Energy3At_of_mixed_of_dominated
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hMixed :
      H3Order3VelocityMixedTimeDerivativeOnPreterminal u T)
    (hInt : VelocityH3IntegrableAt u t)
    (hDom : H3Order3EnergyDerivativeDominatedAt u T t) :
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
      hasDerivAt_spatialSquareEnergy_spatial_d3_loggedVelocityComponent
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
