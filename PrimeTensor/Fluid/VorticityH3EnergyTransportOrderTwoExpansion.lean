import PrimeTensor.Fluid.VorticityH3EnergyTransportOrderTwo

/-!
# Explicit second-order H³ transport commutator expansion

The order-two decomposition already identifies

    C₂(i,k,j)
      =
    ∂ᵢ C₁(k,j)
      +
    (∂ᵢv · ∇)(∂ₖvⱼ).

For the analytic estimate it is useful to expose the derivative hidden in
`∂ᵢ C₁`.  Every resulting term has exactly one first derivative and one
second derivative:

    C₂(i,k,j)
      =
    Σ_r [
        (∂ᵢ∂ₖ v_r)(∂ᵣ v_j)
      + (∂ₖ v_r)(∂ᵢ∂ᵣ v_j)
      + (∂ᵢ v_r)(∂ᵣ∂ₖ v_j)
    ].

Consequently, after pairing with `∂ᵢ∂ₖ v_j`, every cubic density contains one
first derivative and two second derivatives.  Thus order two is controlled by
the first-gradient envelope and Young's inequality; the genuinely new
interpolation term does not appear until derivative order three.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

noncomputable local instance axisFintypeH3EnergyTransportOrderTwoExpansion
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/--
Differentiate the first transport commutator explicitly.  This is only the
coordinate product rule; no estimate is used.
-/
theorem spatial_d_firstTransportCommutator
    {
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    {
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    }
    {T t : ℝ}
    (
      s :
        PreterminalNavierStokes3
          v p T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    )
    (x : Point3)
    (i k j : PrimeTensor.Axis Depth.three) :
    spatial3.d
        i
        (
          firstTransportCommutator
            v t k j
        )
        x
      =
    (
      spatial3.d
          i
          (
            spatial3.d
              k
              (
                fun q =>
                  (v t q).component xAxis
              )
          )
          x
        *
      spatial3.d
          xAxis
          (
            fun q =>
              (v t q).component j
          )
          x
        +
      spatial3.d
          k
          (
            fun q =>
              (v t q).component xAxis
          )
          x
        *
      spatial3.d
          i
          (
            spatial3.d
              xAxis
              (
                fun q =>
                  (v t q).component j
              )
          )
          x
    )
      +
    (
      (
        spatial3.d
            i
            (
              spatial3.d
                k
                (
                  fun q =>
                    (v t q).component yAxis
                )
            )
            x
          *
        spatial3.d
            yAxis
            (
              fun q =>
                (v t q).component j
            )
            x
          +
        spatial3.d
            k
            (
              fun q =>
                (v t q).component yAxis
            )
            x
          *
        spatial3.d
            i
            (
              spatial3.d
                yAxis
                (
                  fun q =>
                    (v t q).component j
                )
            )
            x
      )
        +
      (
        spatial3.d
            i
            (
              spatial3.d
                k
                (
                  fun q =>
                    (v t q).component zAxis
                )
            )
            x
          *
        spatial3.d
            zAxis
            (
              fun q =>
                (v t q).component j
            )
            x
          +
        spatial3.d
            k
            (
              fun q =>
                (v t q).component zAxis
            )
            x
          *
        spatial3.d
            i
            (
              spatial3.d
                zAxis
                (
                  fun q =>
                    (v t q).component j
                )
            )
            x
      )
    ) := by

  have hkx :=
    s.velocity_firstPartial_spatialC1
      ht xAxis k

  have hky :=
    s.velocity_firstPartial_spatialC1
      ht yAxis k

  have hkz :=
    s.velocity_firstPartial_spatialC1
      ht zAxis k

  have hjx :=
    s.velocity_firstPartial_spatialC1
      ht j xAxis

  have hjy :=
    s.velocity_firstPartial_spatialC1
      ht j yAxis

  have hjz :=
    s.velocity_firstPartial_spatialC1
      ht j zAxis

  have hpx :
      SpatialC1
        (
          fun q =>
            spatial3.d
                k
                (
                  fun y =>
                    (v t y).component xAxis
                )
                q
              *
            spatial3.d
                xAxis
                (
                  fun y =>
                    (v t y).component j
                )
                q
        ) :=
    hkx.mul hjx

  have hpy :
      SpatialC1
        (
          fun q =>
            spatial3.d
                k
                (
                  fun y =>
                    (v t y).component yAxis
                )
                q
              *
            spatial3.d
                yAxis
                (
                  fun y =>
                    (v t y).component j
                )
                q
        ) :=
    hky.mul hjy

  have hpz :
      SpatialC1
        (
          fun q =>
            spatial3.d
                k
                (
                  fun y =>
                    (v t y).component zAxis
                )
                q
              *
            spatial3.d
                zAxis
                (
                  fun y =>
                    (v t y).component j
                )
                q
        ) :=
    hkz.mul hjz

  have hpyz :
      SpatialC1
        (
          fun q =>
            spatial3.d
                k
                (
                  fun y =>
                    (v t y).component yAxis
                )
                q
              *
            spatial3.d
                yAxis
                (
                  fun y =>
                    (v t y).component j
                )
                q
              +
            spatial3.d
                k
                (
                  fun y =>
                    (v t y).component zAxis
                )
                q
              *
            spatial3.d
                zAxis
                (
                  fun y =>
                    (v t y).component j
                )
                q
        ) :=
    hpy.add hpz

  unfold firstTransportCommutator

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_add
      hpx hpyz x i,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      hkx hjx x i,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_add
      hpy hpz x i,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      hky hjy x i,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      hkz hjz x i
  ]

/--
A named fully exposed coordinate form of the second transport commutator.
-/
noncomputable def secondTransportCommutatorExpanded
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i k j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  fun x =>
    (
      spatial3.d
          i
          (
            spatial3.d
              k
              (
                fun q =>
                  (v t q).component xAxis
              )
          )
          x
        *
      spatial3.d
          xAxis
          (
            fun q =>
              (v t q).component j
          )
          x
        +
      spatial3.d
          k
          (
            fun q =>
              (v t q).component xAxis
          )
          x
        *
      spatial3.d
          i
          (
            spatial3.d
              xAxis
              (
                fun q =>
                  (v t q).component j
              )
          )
          x
        +
      spatial3.d
          i
          (
            fun q =>
              (v t q).component xAxis
          )
          x
        *
      spatial3.d
          xAxis
          (
            spatial3.d
              k
              (
                fun q =>
                  (v t q).component j
              )
          )
          x
    )
      +
    (
      (
        spatial3.d
            i
            (
              spatial3.d
                k
                (
                  fun q =>
                    (v t q).component yAxis
                )
            )
            x
          *
        spatial3.d
            yAxis
            (
              fun q =>
                (v t q).component j
            )
            x
          +
        spatial3.d
            k
            (
              fun q =>
                (v t q).component yAxis
            )
            x
          *
        spatial3.d
            i
            (
              spatial3.d
                yAxis
                (
                  fun q =>
                    (v t q).component j
                )
            )
            x
          +
        spatial3.d
            i
            (
              fun q =>
                (v t q).component yAxis
            )
            x
          *
        spatial3.d
            yAxis
            (
              spatial3.d
                k
                (
                  fun q =>
                    (v t q).component j
                )
            )
            x
      )
        +
      (
        spatial3.d
            i
            (
              spatial3.d
                k
                (
                  fun q =>
                    (v t q).component zAxis
                )
            )
            x
          *
        spatial3.d
            zAxis
            (
              fun q =>
                (v t q).component j
            )
            x
          +
        spatial3.d
            k
            (
              fun q =>
                (v t q).component zAxis
            )
            x
          *
        spatial3.d
            i
            (
              spatial3.d
                zAxis
                (
                  fun q =>
                    (v t q).component j
                )
            )
            x
          +
        spatial3.d
            i
            (
              fun q =>
                (v t q).component zAxis
            )
            x
          *
        spatial3.d
            zAxis
            (
              spatial3.d
                k
                (
                  fun q =>
                    (v t q).component j
                )
            )
            x
      )
    )

/--
The abstract order-two commutator is exactly its nine-term coordinate
expansion.
-/
theorem secondTransportCommutator_eq_expanded
    {
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    {
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    }
    {T t : ℝ}
    (
      s :
        PreterminalNavierStokes3
          v p T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    )
    (x : Point3)
    (i k j : PrimeTensor.Axis Depth.three) :
    secondTransportCommutator
        v t i k j x
      =
    secondTransportCommutatorExpanded
        v t i k j x := by

  unfold secondTransportCommutator

  rw [
    spatial_d_firstTransportCommutator
      s ht x i k j
  ]

  unfold
    scalarTransportDerivativeCommutator
    secondTransportCommutatorExpanded

  ring

end Euclidean
end Bridge
end PrimeTensor
