import PrimeTensor.Fluid.Vorticity.Continuation.Landau.TopFlux.VelocityEnvelope

/-!
# L¹ coordinates of the top-order H³ transport flux

The top-order transport boundary vector is

    u (D³uⱼ)².

`VelocityEnvelope` supplies a uniform pointwise bound for every velocity
component on an H³ energy-class slice.  The H³ data itself supplies

    D³uⱼ ∈ L².

Therefore each scalar coordinate

    uᵣ (D³uⱼ)²

is integrable by the elementary `L∞ × L² × L² → L¹` estimate.

This file deliberately proves only flux-coordinate integrability.  Together
with the already-closed total divergence integrability, this is the exact
measure-theoretic input for the expanding-cutoff boundary-at-infinity step.
No fourth spatial derivative is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeLandauTopFluxCoordinateIntegrability
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
Every coordinate of the third-derivative transport flux is integrable.
-/
def H3ThirdDerivativeTransportFluxCoordinateIntegrableAt
    (
      u :
        SpaceTimeVectorField
          ℝ ℝ MulReal Depth.three
    )
    (t : ℝ) : Prop :=
  ∀
    r i k l j : PrimeTensor.Axis Depth.three,
      Integrable
        (
          fun x : Point3 =>
            loggedVelocityComponent u t r x
              *
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (
                      spatial3.d
                        l
                        (loggedVelocityComponent u t j)
                    )
                )
                x
              *
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (
                      spatial3.d
                        l
                        (loggedVelocityComponent u t j)
                    )
                )
                x
            )
        )
        (volume : Measure Point3)

/--
An H³-integrable slice of the energy class automatically has integrable
top-order transport-flux coordinates.
-/
theorem h3ThirdDerivativeTransportFluxCoordinate_integrable_of_h3Energy
    {
      u :
        SpaceTimeVectorField
          ℝ ℝ MulReal Depth.three
    }
    {a T t : ℝ}
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      ht :
        t ∈ Set.Ioo a T
    )
    (
      hH3 :
        VelocityH3IntegrableAt
          u t
    ) :
    H3ThirdDerivativeTransportFluxCoordinateIntegrableAt
      u t := by

  rcases hClass.pressure_witness with
    ⟨p, s, hp4⟩

  have htNS :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans
        hClass.terminal_start.1
        ht.1,
      ht.2
    ⟩

  have hRegular :
      H3OrderThreeTransportRegularityAt
        u t :=
    h3OrderThreeTransportRegularityAt_of_energyClass
      hClass
      ht

  intro r i k l j

  let v : ScalarField3 :=
    loggedVelocityComponent u t r

  let f : ScalarField3 :=
    spatial3.d
      i
      (
        spatial3.d
          k
          (
            spatial3.d
              l
              (loggedVelocityComponent u t j)
          )
      )

  have hv :
      SpatialC1 v := by
    dsimp only [v]

    exact
      s.velocity_component_spatialC1
        htNS r

  have hSecond2 :
      SpatialC2
        (
          spatial3.d
            k
            (
              spatial3.d
                l
                (loggedVelocityComponent u t j)
            )
        ) :=
    (hRegular k l j).2

  have hf :
      SpatialC1 f := by

    dsimp only [f]

    change
      SpatialC1
        (
          fun q =>
            partialDeriv
              i
              (
                spatial3.d
                  k
                  (
                    spatial3.d
                      l
                      (loggedVelocityComponent u t j)
                  )
              )
              q
        )

    exact
      PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
        hSecond2 i

  have hf2 :
      MemLp
        f
        2
        (volume : Measure Point3) := by

    dsimp only [f]

    simpa using
      velocityH3IntegrableAt_third_memLp2
        hH3
        j i k l
        hf.continuous.aestronglyMeasurable

  have hff :
      Integrable
        (
          fun x : Point3 =>
            f x * f x
        )
        (volume : Measure Point3) :=
    hf2.integrable_mul hf2

  have hvBound :
      ∀ x : Point3,
        ‖v x‖
          ≤
        h3RawFourierL1DeweightingCoefficient
          *
        velocityH3EnergyAt u t := by

    intro x

    dsimp only [v]

    exact
      norm_loggedVelocityComponent_le_h3Energy
        hClass ht hH3 r x

  have hFlux :
      Integrable
        (
          fun x : Point3 =>
            v x * (f x * f x)
        )
        (volume : Measure Point3) :=
    hff.bdd_mul
      hv.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hvBound)

  simpa only [v, f] using hFlux

end

end Euclidean
end Bridge
end PrimeTensor
