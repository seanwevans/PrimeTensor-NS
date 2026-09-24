import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Canonical.Endpoint.From.Low.Tail

/-!
# BKM endpoint: low-frequency control from kinetic energy

The selected BKM endpoint has been reduced to one physical low-frequency
hypothesis:

    ∫ |u_j(t,x)|² dx ≤ L²

uniformly on the strict terminal tail.

This file packages the exact classical input that supplies such an `L` from
the zeroth-order kinetic energy.

If

    E₀(t) ≤ E₀(a)

for every strict tail time, then every individual velocity-component square
energy is bounded by `E₀(a)`.  Taking

    L = sqrt (E₀(a))

therefore gives the previously introduced
`BKMZerothVelocityL2TailBound`.

The canonical selected logarithmic estimate then becomes unconditional once
the kinetic-energy anchor inequality is available.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeBKMEndpointKineticEnergyLowTail
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Anchor-controlled zeroth-order energy -/

/--
The zeroth-order velocity energy never exceeds its value at the tail anchor.
-/
def BKMKineticEnergyControlledFromAnchor
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  ∀ t : ℝ,
    t ∈ Set.Ioo a T →
      velocityH3Energy0At u t
        ≤
      velocityH3Energy0At u a

/--
Each individual velocity component square energy is bounded by the total
zeroth-order velocity energy.
-/
theorem spatialSquareEnergy_loggedVelocityComponent_le_velocityH3Energy0At
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (j : PrimeTensor.Axis Depth.three) :
    spatialSquareEnergy
        (loggedVelocityComponent u t j)
      ≤
    velocityH3Energy0At u t := by

  unfold velocityH3Energy0At

  exact
    Finset.single_le_sum
      (fun k _ =>
        spatialSquareEnergy_nonneg
          (loggedVelocityComponent u t k))
      (Finset.mem_univ j)

/--
Anchor control of the total kinetic energy gives the exact uniform physical
zeroth-order `L²` tail bound needed by the BKM low-frequency estimate.
-/
theorem bkmZerothVelocityL2TailBound_of_kineticEnergyControlledFromAnchor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hEnergy : BKMKineticEnergyControlledFromAnchor u a T) :
    BKMZerothVelocityL2TailBound
      u a T
      (Real.sqrt (velocityH3Energy0At u a)) := by

  refine ⟨Real.sqrt_nonneg _, ?_⟩

  intro t ht j

  have hComponent :
      spatialSquareEnergy
          (loggedVelocityComponent
            u t (h3AxisOfFin3 j))
        ≤
      velocityH3Energy0At u t :=
    spatialSquareEnergy_loggedVelocityComponent_le_velocityH3Energy0At
      u t (h3AxisOfFin3 j)

  have hAnchor :
      velocityH3Energy0At u t
        ≤
      velocityH3Energy0At u a :=
    hEnergy t ht

  have hNonneg :
      0 ≤ velocityH3Energy0At u a :=
    velocityH3Energy0At_nonneg u a

  calc
    spatialSquareEnergy
        (loggedVelocityComponent
          u t (h3AxisOfFin3 j))
        ≤
      velocityH3Energy0At u t :=
      hComponent

    _ ≤
      velocityH3Energy0At u a :=
      hAnchor

    _ =
      (Real.sqrt (velocityH3Energy0At u a)) ^ 2 := by
      symm
      exact Real.sq_sqrt hNonneg

/-! ## Canonical logarithmic endpoint with kinetic anchor control -/

/--
Kinetic-energy anchor control closes the canonical selected logarithmic
actual-gradient bound.
-/
theorem actualVelocityGradientLogBoundFrom_canonicalSelectedBKM_of_kineticEnergyControlledFromAnchor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {g : ℝ → ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ha : a ∈ Set.Ioo (0 : ℝ) T)
    (hg :
      ∀ t : ℝ,
        t ∈ Set.Ioo a T →
          VorticityEnvelope u g t)
    (hProfile :
      H3EnergyProfileFrom
        u a T
        (velocityH3EnergyAt u))
    (hEnergy :
      BKMKineticEnergyControlledFromAnchor
        u a T) :
    ActualVelocityGradientLogBoundFrom
      u a T g
      (velocityH3EnergyAt u)
      (h3BKMCanonicalSelectedLogGradientConstant
        (Real.sqrt (velocityH3Energy0At u a))) := by

  exact
    actualVelocityGradientLogBoundFrom_canonicalSelectedBKM_of_lowTail
      hNS
      ha
      hg
      hProfile
      (bkmZerothVelocityL2TailBound_of_kineticEnergyControlledFromAnchor
        hEnergy)

/--
The logarithmic constant obtained from the kinetic anchor is nonnegative.
-/
theorem h3BKMCanonicalSelectedLogGradientConstant_sqrt_energy0_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a : ℝ) :
    0 ≤
      h3BKMCanonicalSelectedLogGradientConstant
        (Real.sqrt (velocityH3Energy0At u a)) := by

  exact
    h3BKMCanonicalSelectedLogGradientConstant_nonneg
      (Real.sqrt_nonneg _)

end

end Euclidean
end Bridge
end PrimeTensor
