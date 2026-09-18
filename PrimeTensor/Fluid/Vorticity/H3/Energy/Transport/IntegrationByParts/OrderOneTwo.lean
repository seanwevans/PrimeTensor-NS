import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.IntegrationByParts.OrderZero
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fourier.Compatibility

/-!
# Automatic H³ transport integration by parts: orders one and two

`OrderZero` packages the generic scalar transport flux theorem.  The first two
differentiated energy levels now follow by choosing

    f = ∂ᵢuⱼ
    f = ∂ᵢ∂ₖuⱼ.

Canonical H³ data supplies all `L²` derivatives through order three.  The
whole-space Sobolev theorem supplies the required `L⁴` membership, and the
Landau gradient envelope controls the matching derivative of each transport
coefficient.

No order-one or order-two whole-space transport IBP hypothesis remains.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3TransportIBPOrderOneTwo
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TransportIBPOrderOneTwo :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- First-derivative transport IBP is automatic from the H³ square-integrability
package and the velocity-gradient envelope. -/
theorem h3FirstDerivativeTransportIntegrationByPartsAt_of_energyClass
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {a T t : ℝ}
    {h : ℝ → ℝ}
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
    )
    (
      hGradient :
        VelocityGradientEnvelope
          u h t
    ) :
    H3FirstDerivativeTransportIntegrationByPartsAt
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

  let v :=
    PrimeTensor.Bridge.logSpaceTimeVectorField
      u

  have hSobolev4 :
      WholeSpaceC1H1ToL4 :=
    wholeSpaceC1H1ToL4_of_wholeSpaceC1H1ToL6
      (
        wholeSpaceC1H1ToL6_of_fderiv
          wholeSpaceC1FDerivL2ToL6_cutoff
      )

  have hvC1 :
      ∀ r : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (v t x).component r) := by
    intro r
    dsimp only [v]

    exact
      s.velocity_component_spatialC1
        htNS r

  have hv2 :
      ∀ r : PrimeTensor.Axis Depth.three,
        MemLp
          (fun x : Point3 =>
            (v t x).component r)
          (ENNReal.ofReal 2)
          volume := by
    intro r

    exact
      memLp_two_of_spatialL2SquareIntegrable
        (hvC1 r).continuous.aestronglyMeasurable
        (hH3 r).1

  have hFirstC1 :
      ∀ i j : PrimeTensor.Axis Depth.three,
        SpatialC1
          (
            spatial3.d i
              (loggedVelocityComponent u t j)
          ) := by
    intro i j

    have h3 :
        SpatialC3
          (loggedVelocityComponent u t j) := by
      change
        SpatialC3
          (
            fun x =>
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u t x
              ).component j
          )

      exact
        s.regularity.velocity_spatial_three
          t htNS j

    exact
      h3.firstPartial_spatialC1 i

  have hFirst2 :
      ∀ i j : PrimeTensor.Axis Depth.three,
        MemLp
          (
            spatial3.d i
              (loggedVelocityComponent u t j)
          )
          (ENNReal.ofReal 2)
          volume := by
    intro i j

    exact
      memLp_two_of_spatialL2SquareIntegrable
        (hFirstC1 i j).continuous.aestronglyMeasurable
        ((hH3 j).2.1 i)

  have hSecondC1 :
      ∀ r i j : PrimeTensor.Axis Depth.three,
        SpatialC1
          (
            spatial3.d r
              (
                spatial3.d i
                  (loggedVelocityComponent u t j)
              )
          ) := by
    intro r i j

    have h3 :
        SpatialC3
          (loggedVelocityComponent u t j) := by
      change
        SpatialC3
          (
            fun x =>
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u t x
              ).component j
          )

      exact
        s.regularity.velocity_spatial_three
          t htNS j

    exact
      h3.secondPartial_spatialC1 r i

  have hSecond2 :
      ∀ r i j : PrimeTensor.Axis Depth.three,
        MemLp
          (
            spatial3.d r
              (
                spatial3.d i
                  (loggedVelocityComponent u t j)
              )
          )
          (ENNReal.ofReal 2)
          volume := by
    intro r i j

    exact
      memLp_two_of_spatialL2SquareIntegrable
        (hSecondC1 r i j).continuous.aestronglyMeasurable
        ((hH3 j).2.2.1 r i)

  have hv4 :
      ∀ r : PrimeTensor.Axis Depth.three,
        MemLp
          (fun x : Point3 =>
            (v t x).component r)
          (ENNReal.ofReal 4)
          volume := by
    intro r

    exact
      hSobolev4
        (fun x : Point3 =>
          (v t x).component r)
        (hvC1 r)
        (hv2 r)
        (fun i =>
          hFirst2 i r)

  have hFirst4 :
      ∀ i j : PrimeTensor.Axis Depth.three,
        MemLp
          (
            spatial3.d i
              (loggedVelocityComponent u t j)
          )
          (ENNReal.ofReal 4)
          volume := by
    intro i j

    exact
      hSobolev4
        (
          spatial3.d i
            (loggedVelocityComponent u t j)
        )
        (hFirstC1 i j)
        (hFirst2 i j)
        (fun r =>
          hSecond2 r i j)

  have hDiagBound :
      ∀
        (r : PrimeTensor.Axis Depth.three)
        (x : Point3),
          ‖spatial3.d
              r
              (fun y : Point3 =>
                (v t y).component r)
              x‖
            ≤
          h t := by
    intro r x
    dsimp only [v]

    simpa only [Real.norm_eq_abs] using
      hGradient r r x

  intro i j

  exact
    transportScalarIntegrationByPartsAt_of_memLp_four
      hvC1
      (hFirstC1 i j)
      hv2
      hv4
      (hFirst2 i j)
      (hFirst4 i j)
      (fun r =>
        hSecond2 r i j)
      hDiagBound

/-- Second-derivative transport IBP is automatic from H³ data as well.  The
only new `L²` input relative to order one is the third spatial derivative,
which is already stored in `VelocityH3IntegrableAt`. -/
theorem h3SecondDerivativeTransportIntegrationByPartsAt_of_energyClass
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {a T t : ℝ}
    {h : ℝ → ℝ}
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
    )
    (
      hGradient :
        VelocityGradientEnvelope
          u h t
    ) :
    H3SecondDerivativeTransportIntegrationByPartsAt
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

  have htTail :
      t ∈ Set.Ico a T :=
    ⟨
      le_of_lt ht.1,
      ht.2
    ⟩

  let v :=
    PrimeTensor.Bridge.logSpaceTimeVectorField
      u

  have hSobolev4 :
      WholeSpaceC1H1ToL4 :=
    wholeSpaceC1H1ToL4_of_wholeSpaceC1H1ToL6
      (
        wholeSpaceC1H1ToL6_of_fderiv
          wholeSpaceC1FDerivL2ToL6_cutoff
      )

  have hvC1 :
      ∀ r : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (v t x).component r) := by
    intro r
    dsimp only [v]

    exact
      s.velocity_component_spatialC1
        htNS r

  have hv2 :
      ∀ r : PrimeTensor.Axis Depth.three,
        MemLp
          (fun x : Point3 =>
            (v t x).component r)
          (ENNReal.ofReal 2)
          volume := by
    intro r

    exact
      memLp_two_of_spatialL2SquareIntegrable
        (hvC1 r).continuous.aestronglyMeasurable
        (hH3 r).1

  have hFirstC1 :
      ∀ r j : PrimeTensor.Axis Depth.three,
        SpatialC1
          (
            spatial3.d r
              (loggedVelocityComponent u t j)
          ) := by
    intro r j

    have h3 :
        SpatialC3
          (loggedVelocityComponent u t j) := by
      change
        SpatialC3
          (
            fun x =>
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u t x
              ).component j
          )

      exact
        s.regularity.velocity_spatial_three
          t htNS j

    exact
      h3.firstPartial_spatialC1 r

  have hFirst2 :
      ∀ r j : PrimeTensor.Axis Depth.three,
        MemLp
          (
            spatial3.d r
              (loggedVelocityComponent u t j)
          )
          (ENNReal.ofReal 2)
          volume := by
    intro r j

    exact
      memLp_two_of_spatialL2SquareIntegrable
        (hFirstC1 r j).continuous.aestronglyMeasurable
        ((hH3 j).2.1 r)

  have hSecondC1 :
      ∀ i k j : PrimeTensor.Axis Depth.three,
        SpatialC1
          (
            spatial3.d i
              (
                spatial3.d k
                  (loggedVelocityComponent u t j)
              )
          ) := by
    intro i k j

    have h3 :
        SpatialC3
          (loggedVelocityComponent u t j) := by
      change
        SpatialC3
          (
            fun x =>
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u t x
              ).component j
          )

      exact
        s.regularity.velocity_spatial_three
          t htNS j

    exact
      h3.secondPartial_spatialC1 i k

  have hSecond2 :
      ∀ i k j : PrimeTensor.Axis Depth.three,
        MemLp
          (
            spatial3.d i
              (
                spatial3.d k
                  (loggedVelocityComponent u t j)
              )
          )
          (ENNReal.ofReal 2)
          volume := by
    intro i k j

    exact
      memLp_two_of_spatialL2SquareIntegrable
        (hSecondC1 i k j).continuous.aestronglyMeasurable
        ((hH3 j).2.2.1 i k)

  have hThird2 :
      ∀ r i k j : PrimeTensor.Axis Depth.three,
        MemLp
          (
            spatial3.d r
              (
                spatial3.d i
                  (
                    spatial3.d k
                      (loggedVelocityComponent u t j)
                  )
              )
          )
          (ENNReal.ofReal 2)
          volume := by
    intro r i k j

    have hBaseC3 :
        SpatialC3
          (
            spatial3.d i
              (
                spatial3.d k
                  (loggedVelocityComponent u t j)
              )
          ) := by
      change
        SpatialC3
          (
            spatial3.d i
              (
                spatial3.d k
                  (
                    fun x =>
                      (
                        PrimeTensor.Bridge.logSpaceTimeVectorField
                          u t x
                      ).component j
                  )
              )
          )

      exact
        hClass.velocity_spatial_five
          t htTail j i k

    have hThirdC1 :
        SpatialC1
          (
            spatial3.d r
              (
                spatial3.d i
                  (
                    spatial3.d k
                      (loggedVelocityComponent u t j)
                  )
              )
          ) :=
      hBaseC3.firstPartial_spatialC1 r

    exact
      velocityH3IntegrableAt_third_memLp2
        hH3
        j r i k
        hThirdC1.continuous.aestronglyMeasurable

  have hv4 :
      ∀ r : PrimeTensor.Axis Depth.three,
        MemLp
          (fun x : Point3 =>
            (v t x).component r)
          (ENNReal.ofReal 4)
          volume := by
    intro r

    exact
      hSobolev4
        (fun x : Point3 =>
          (v t x).component r)
        (hvC1 r)
        (hv2 r)
        (fun i =>
          hFirst2 i r)

  have hSecond4 :
      ∀ i k j : PrimeTensor.Axis Depth.three,
        MemLp
          (
            spatial3.d i
              (
                spatial3.d k
                  (loggedVelocityComponent u t j)
              )
          )
          (ENNReal.ofReal 4)
          volume := by
    intro i k j

    exact
      hSobolev4
        (
          spatial3.d i
            (
              spatial3.d k
                (loggedVelocityComponent u t j)
            )
        )
        (hSecondC1 i k j)
        (hSecond2 i k j)
        (fun r =>
          hThird2 r i k j)

  have hDiagBound :
      ∀
        (r : PrimeTensor.Axis Depth.three)
        (x : Point3),
          ‖spatial3.d
              r
              (fun y : Point3 =>
                (v t y).component r)
              x‖
            ≤
          h t := by
    intro r x
    dsimp only [v]

    simpa only [Real.norm_eq_abs] using
      hGradient r r x

  intro i k j

  exact
    transportScalarIntegrationByPartsAt_of_memLp_four
      hvC1
      (hSecondC1 i k j)
      hv2
      hv4
      (hSecond2 i k j)
      (hSecond4 i k j)
      (fun r =>
        hThird2 r i k j)
      hDiagBound

end

end Euclidean
end Bridge
end PrimeTensor
