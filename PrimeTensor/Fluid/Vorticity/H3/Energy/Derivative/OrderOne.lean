import PrimeTensor.Fluid.Vorticity.H3.Energy.Derivative.OrderZero

/-!
# First-order canonical H³ energy derivative

The zeroth-order derivative proof isolates one reusable pattern:

* a genuine pointwise time derivative;
* base-time square integrability;
* local measurability and an integrable dominator;
* the generic square-integral differentiation theorem.

For first spatial derivatives, the genuine pointwise time derivative is already
part of `PreterminalVorticityRegularity3`:

    d/dt (∂ᵢ uⱼ) = ∂ᵢ (∂ₜ uⱼ).

Therefore this file only adds the corresponding order-one domination package
and sums the scalar square-energy derivatives over `(j,i)`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3EnergyDerivativeOrderOne
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Genuine mixed time/space derivative of one first spatial velocity
derivative at every preterminal time. -/
theorem spatial_d_loggedVelocityComponent_hasDerivAt_time
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (i j : PrimeTensor.Axis Depth.three)
    (x : Point3) :
    HasDerivAt
      (fun r : ℝ =>
        spatial3.d
          i
          (loggedVelocityComponent u r j)
          x)
      (spatial3.d
        i
        (loggedVelocityTemporalComponent u s j)
        x)
      s := by
  let p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T :=
    Classical.choose_spec hNS

  have h :=
    hPDE.regularity.velocity_space_time_hasDerivAt
      s hs x i j

  change
    HasDerivAt
      (fun r : ℝ =>
        spatial3.d
          i
          (fun y : Point3 =>
            (logSpaceTimeVectorField u r y).component j)
          x)
      (spatial3.d
        i
        (fun y : Point3 =>
          temporal.d
            (fun r : ℝ =>
              (logSpaceTimeVectorField u r y).component j)
            s)
        x)
      s

  exact h

/-- Exact local domination data needed for all first-order square-energy
integrals at one preterminal time. -/
structure H3Order1EnergyDerivativeDominatedAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ) : Type where

  timeSet :
    PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
        Set ℝ

  bound :
    PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
        Point3 → ℝ

  timeSet_mem_nhds :
    ∀ j i : PrimeTensor.Axis Depth.three,
      timeSet j i ∈ 𝓝 t

  timeSet_preterminal :
    ∀ j i : PrimeTensor.Axis Depth.three,
      timeSet j i ⊆ Set.Ioo (0 : ℝ) T

  square_aestronglyMeasurable :
    ∀ j i : PrimeTensor.Axis Depth.three,
      ∀ᶠ s in 𝓝 t,
        AEStronglyMeasurable
          (fun x : Point3 =>
            (spatial3.d
              i
              (loggedVelocityComponent u s j)
              x) ^ 2)
          (volume : Measure Point3)

  derivative_aestronglyMeasurable :
    ∀ j i : PrimeTensor.Axis Depth.three,
      AEStronglyMeasurable
        (fun x : Point3 =>
          2 *
            spatial3.d
              i
              (loggedVelocityComponent u t j)
              x *
            spatial3.d
              i
              (loggedVelocityTemporalComponent u t j)
              x)
        (volume : Measure Point3)

  derivative_le_bound :
    ∀ j i : PrimeTensor.Axis Depth.three,
      ∀ᵐ x : Point3 ∂(volume : Measure Point3),
        ∀ s ∈ timeSet j i,
          norm
            (2 *
              spatial3.d
                i
                (loggedVelocityComponent u s j)
                x *
              spatial3.d
                i
                (loggedVelocityTemporalComponent u s j)
                x)
            ≤
          bound j i x

  bound_integrable :
    ∀ j i : PrimeTensor.Axis Depth.three,
      Integrable
        (bound j i)
        (volume : Measure Point3)

/-- One first-order scalar square-energy term has the expected derivative. -/
theorem hasDerivAt_spatialSquareEnergy_spatial_d_loggedVelocityComponent
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hInt : VelocityH3IntegrableAt u t)
    (hDom : H3Order1EnergyDerivativeDominatedAt u T t)
    (j i : PrimeTensor.Axis Depth.three) :
    HasDerivAt
      (fun s : ℝ =>
        spatialSquareEnergy
          (spatial3.d
            i
            (loggedVelocityComponent u s j)))
      (spatialEnergyPairing
        (spatial3.d
          i
          (loggedVelocityComponent u t j))
        (spatial3.d
          i
          (loggedVelocityTemporalComponent u t j)))
      t := by
  have hSquareInt :
      Integrable
        (fun x : Point3 =>
          (spatial3.d
            i
            (loggedVelocityComponent u t j)
            x) ^ 2)
        (volume : Measure Point3) := by
    exact
      (hInt j).2.1 i

  have hDiff :
      ∀ᵐ x : Point3 ∂(volume : Measure Point3),
        ∀ s ∈ hDom.timeSet j i,
          HasDerivAt
            (fun r : ℝ =>
              (spatial3.d
                i
                (loggedVelocityComponent u r j)
                x) ^ 2)
            (2 *
              spatial3.d
                i
                (loggedVelocityComponent u s j)
                x *
              spatial3.d
                i
                (loggedVelocityTemporalComponent u s j)
                x)
            s := by
    filter_upwards with x
    intro s hs

    have hsPre :
        s ∈ Set.Ioo (0 : ℝ) T :=
      hDom.timeSet_preterminal j i hs

    exact
      hasDerivAt_sq_two_mul
        (f := fun r =>
          spatial3.d
            i
            (loggedVelocityComponent u r j))
        (ft := fun r =>
          spatial3.d
            i
            (loggedVelocityTemporalComponent u r j))
        (s := s)
        (x := x)
        (spatial_d_loggedVelocityComponent_hasDerivAt_time
          hNS hsPre i j x)

  exact
    hasDerivAt_spatialSquareEnergy_of_dominated
      (f := fun s =>
        spatial3.d
          i
          (loggedVelocityComponent u s j))
      (ft := fun s =>
        spatial3.d
          i
          (loggedVelocityTemporalComponent u s j))
      (t := t)
      (S := hDom.timeSet j i)
      (bound := hDom.bound j i)
      (hDom.timeSet_mem_nhds j i)
      (hDom.square_aestronglyMeasurable j i)
      hSquareInt
      (hDom.derivative_aestronglyMeasurable j i)
      (hDom.derivative_le_bound j i)
      (hDom.bound_integrable j i)
      hDiff

/-- The complete first-order canonical H³ energy block has its exact formal
time derivative. -/
theorem hasDerivAt_velocityH3Energy1At_of_dominated
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hInt : VelocityH3IntegrableAt u t)
    (hDom : H3Order1EnergyDerivativeDominatedAt u T t) :
    HasDerivAt
      (velocityH3Energy1At u)
      (velocityH3FormalDerivative1At u t)
      t := by
  have hEach :
      ∀ j i : PrimeTensor.Axis Depth.three,
        HasDerivAt
          (fun s : ℝ =>
            spatialSquareEnergy
              (spatial3.d
                i
                (loggedVelocityComponent u s j)))
          (spatialEnergyPairing
            (spatial3.d
              i
              (loggedVelocityComponent u t j))
            (spatial3.d
              i
              (loggedVelocityTemporalComponent u t j)))
          t := by
    intro j i
    exact
      hasDerivAt_spatialSquareEnergy_spatial_d_loggedVelocityComponent
        hNS ht hInt hDom j i

  have hInner :
      ∀ j : PrimeTensor.Axis Depth.three,
        HasDerivAt
          (fun s : ℝ =>
            ∑ i : PrimeTensor.Axis Depth.three,
              spatialSquareEnergy
                (spatial3.d
                  i
                  (loggedVelocityComponent u s j)))
          (∑ i : PrimeTensor.Axis Depth.three,
            spatialEnergyPairing
              (spatial3.d
                i
                (loggedVelocityComponent u t j))
              (spatial3.d
                i
                (loggedVelocityTemporalComponent u t j)))
          t := by
    intro j
    apply HasDerivAt.fun_sum
    intro i hi
    exact hEach j i

  have hSum :
      HasDerivAt
        (fun s : ℝ =>
          ∑ j : PrimeTensor.Axis Depth.three,
            ∑ i : PrimeTensor.Axis Depth.three,
              spatialSquareEnergy
                (spatial3.d
                  i
                  (loggedVelocityComponent u s j)))
        (∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            spatialEnergyPairing
              (spatial3.d
                i
                (loggedVelocityComponent u t j))
              (spatial3.d
                i
                (loggedVelocityTemporalComponent u t j)))
        t := by
    apply HasDerivAt.fun_sum
    intro j hj
    exact hInner j

  change
    HasDerivAt
      (fun s : ℝ =>
        ∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            spatialSquareEnergy
              (spatial3.d
                i
                (loggedVelocityComponent u s j)))
      (∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          spatialEnergyPairing
            (spatial3.d
              i
              (loggedVelocityComponent u t j))
            (spatial3.d
              i
              (loggedVelocityTemporalComponent u t j)))
      t

  exact hSum

end

end Euclidean
end Bridge
end PrimeTensor
