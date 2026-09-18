import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.IntegrationByParts.FluxCoordinate
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Analytic.WholeSpaceSobolev

/-!
# Automatic low-order transport integration by parts: order zero

The coordinate theorem in `FluxCoordinate` gives

    ∫ ∂ᵢ(vᵢ f²) = 0

under the H³-compatible exponent pattern.  This file first assembles the three
coordinate statements into the project's honest
`TransportScalarIntegrationByPartsAt` package.

It then specializes to `f = uⱼ`.  Canonical H³ square-integrability gives the
required `L²` data, the now-proved whole-space Sobolev theorem gives `L⁴`, and
the velocity-gradient envelope bounds the matching coefficient derivatives.
Thus the order-zero transport IBP package is no longer an external tail datum.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3TransportIBPOrderZero
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TransportIBPOrderZero :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Assemble the three coordinate flux cancellations into one honest scalar
transport integration-by-parts package. -/
theorem transportScalarIntegrationByPartsAt_of_memLp_four
    {
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    {t : ℝ}
    {f : ScalarField3}
    {B : ℝ}
    (
      hvC1 :
        ∀ i : PrimeTensor.Axis Depth.three,
          SpatialC1
            (fun x : Point3 =>
              (v t x).component i)
    )
    (
      hfC1 :
        SpatialC1 f
    )
    (
      hv2 :
        ∀ i : PrimeTensor.Axis Depth.three,
          MemLp
            (fun x : Point3 =>
              (v t x).component i)
            (ENNReal.ofReal 2)
            volume
    )
    (
      hv4 :
        ∀ i : PrimeTensor.Axis Depth.three,
          MemLp
            (fun x : Point3 =>
              (v t x).component i)
            (ENNReal.ofReal 4)
            volume
    )
    (
      hf2 :
        MemLp f
          (ENNReal.ofReal 2)
          volume
    )
    (
      hf4 :
        MemLp f
          (ENNReal.ofReal 4)
          volume
    )
    (
      hdf2 :
        ∀ i : PrimeTensor.Axis Depth.three,
          MemLp
            (spatial3.d i f)
            (ENNReal.ofReal 2)
            volume
    )
    (
      hdvBound :
        ∀
          (i : PrimeTensor.Axis Depth.three)
          (x : Point3),
            ‖spatial3.d
                i
                (fun y : Point3 =>
                  (v t y).component i)
                x‖
              ≤
            B
    ) :
    TransportScalarIntegrationByPartsAt
      v t f := by

  have hIntX :
      Integrable
        (spatial3.d
          xAxis
          (fun x : Point3 =>
            (v t x).component xAxis
              *
            (f x * f x)))
        volume :=
    scalarFluxCoordinate_spatial_d_integrable_of_memLp_four
      (hvC1 xAxis)
      hfC1
      xAxis
      B
      (hdvBound xAxis)
      hf2
      (hv4 xAxis)
      hf4
      (hdf2 xAxis)

  have hIntY :
      Integrable
        (spatial3.d
          yAxis
          (fun x : Point3 =>
            (v t x).component yAxis
              *
            (f x * f x)))
        volume :=
    scalarFluxCoordinate_spatial_d_integrable_of_memLp_four
      (hvC1 yAxis)
      hfC1
      yAxis
      B
      (hdvBound yAxis)
      hf2
      (hv4 yAxis)
      hf4
      (hdf2 yAxis)

  have hIntZ :
      Integrable
        (spatial3.d
          zAxis
          (fun x : Point3 =>
            (v t x).component zAxis
              *
            (f x * f x)))
        volume :=
    scalarFluxCoordinate_spatial_d_integrable_of_memLp_four
      (hvC1 zAxis)
      hfC1
      zAxis
      B
      (hdvBound zAxis)
      hf2
      (hv4 zAxis)
      hf4
      (hdf2 zAxis)

  have hZeroX :
      (∫ x : Point3,
        spatial3.d
          xAxis
          (fun y : Point3 =>
            (v t y).component xAxis
              *
            (f y * f y))
          x
        ∂volume)
        =
      0 :=
    integral_scalarFluxCoordinate_spatial_d_eq_zero_of_memLp_four
      (hvC1 xAxis)
      hfC1
      xAxis
      B
      (hdvBound xAxis)
      (hv2 xAxis)
      hf2
      (hv4 xAxis)
      hf4
      (hdf2 xAxis)

  have hZeroY :
      (∫ x : Point3,
        spatial3.d
          yAxis
          (fun y : Point3 =>
            (v t y).component yAxis
              *
            (f y * f y))
          x
        ∂volume)
        =
      0 :=
    integral_scalarFluxCoordinate_spatial_d_eq_zero_of_memLp_four
      (hvC1 yAxis)
      hfC1
      yAxis
      B
      (hdvBound yAxis)
      (hv2 yAxis)
      hf2
      (hv4 yAxis)
      hf4
      (hdf2 yAxis)

  have hZeroZ :
      (∫ x : Point3,
        spatial3.d
          zAxis
          (fun y : Point3 =>
            (v t y).component zAxis
              *
            (f y * f y))
          x
        ∂volume)
        =
      0 :=
    integral_scalarFluxCoordinate_spatial_d_eq_zero_of_memLp_four
      (hvC1 zAxis)
      hfC1
      zAxis
      B
      (hdvBound zAxis)
      (hv2 zAxis)
      hf2
      (hv4 zAxis)
      hf4
      (hdf2 zAxis)

  constructor

  · unfold transportScalarFluxDivergenceXYZ

    exact
      hIntX.add
        (hIntY.add hIntZ)

  · unfold TransportScalarFluxVanishesAt
    unfold transportScalarFluxDivergenceXYZ

    have hYZ :
        (∫ x : Point3,
          spatial3.d
              yAxis
              (fun y : Point3 =>
                (v t y).component yAxis
                  *
                (f y * f y))
              x
            +
          spatial3.d
              zAxis
              (fun y : Point3 =>
                (v t y).component zAxis
                  *
                (f y * f y))
              x
          ∂volume)
          =
        (∫ x : Point3,
          spatial3.d
            yAxis
            (fun y : Point3 =>
              (v t y).component yAxis
                *
              (f y * f y))
            x
          ∂volume)
          +
        (∫ x : Point3,
          spatial3.d
            zAxis
            (fun y : Point3 =>
              (v t y).component zAxis
                *
              (f y * f y))
            x
          ∂volume) := by
      exact
        MeasureTheory.integral_add
          hIntY hIntZ

    have hXYZ :
        (∫ x : Point3,
          spatial3.d
              xAxis
              (fun y : Point3 =>
                (v t y).component xAxis
                  *
                (f y * f y))
              x
            +
          (
            spatial3.d
                yAxis
                (fun y : Point3 =>
                  (v t y).component yAxis
                    *
                  (f y * f y))
                x
              +
            spatial3.d
                zAxis
                (fun y : Point3 =>
                  (v t y).component zAxis
                    *
                  (f y * f y))
                x
          )
          ∂volume)
          =
        (∫ x : Point3,
          spatial3.d
            xAxis
            (fun y : Point3 =>
              (v t y).component xAxis
                *
              (f y * f y))
            x
          ∂volume)
          +
        (∫ x : Point3,
          spatial3.d
              yAxis
              (fun y : Point3 =>
                (v t y).component yAxis
                  *
                (f y * f y))
              x
            +
          spatial3.d
              zAxis
              (fun y : Point3 =>
                (v t y).component zAxis
                  *
                (f y * f y))
              x
          ∂volume) := by
      exact
        MeasureTheory.integral_add
          hIntX
          (hIntY.add hIntZ)

    calc
      (∫ x : Point3,
        spatial3.d
            xAxis
            (fun y : Point3 =>
              (v t y).component xAxis
                *
              (f y * f y))
            x
          +
        (
          spatial3.d
              yAxis
              (fun y : Point3 =>
                (v t y).component yAxis
                  *
                (f y * f y))
              x
            +
          spatial3.d
              zAxis
              (fun y : Point3 =>
                (v t y).component zAxis
                  *
                (f y * f y))
              x
        )
        ∂volume)
          =
        (∫ x : Point3,
          spatial3.d
            xAxis
            (fun y : Point3 =>
              (v t y).component xAxis
                *
              (f y * f y))
            x
          ∂volume)
          +
        (∫ x : Point3,
          spatial3.d
              yAxis
              (fun y : Point3 =>
                (v t y).component yAxis
                  *
                (f y * f y))
              x
            +
          spatial3.d
              zAxis
              (fun y : Point3 =>
                (v t y).component zAxis
                  *
                (f y * f y))
              x
          ∂volume) := hXYZ
      _ =
        (∫ x : Point3,
          spatial3.d
            xAxis
            (fun y : Point3 =>
              (v t y).component xAxis
                *
              (f y * f y))
            x
          ∂volume)
          +
        (
          (∫ x : Point3,
            spatial3.d
              yAxis
              (fun y : Point3 =>
                (v t y).component yAxis
                  *
                (f y * f y))
              x
            ∂volume)
            +
          (∫ x : Point3,
            spatial3.d
              zAxis
              (fun y : Point3 =>
                (v t y).component zAxis
                  *
                (f y * f y))
              x
            ∂volume)
        ) := by
          rw [hYZ]
      _ = 0 := by
        rw [hZeroX, hZeroY, hZeroZ]
        ring

/-- The order-zero logged transport IBP package follows from canonical H³
square-integrability and a velocity-gradient envelope. -/
theorem h3TransportEnergyIntegrationByPartsAt_of_energyClass
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
    H3TransportEnergyIntegrationByPartsAt
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
      ∀ i : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (v t x).component i) := by
    intro i
    dsimp only [v]

    exact
      s.velocity_component_spatialC1
        htNS i

  have hv2 :
      ∀ i : PrimeTensor.Axis Depth.three,
        MemLp
          (fun x : Point3 =>
            (v t x).component i)
          (ENNReal.ofReal 2)
          volume := by
    intro i

    exact
      memLp_two_of_spatialL2SquareIntegrable
        (hvC1 i).continuous.aestronglyMeasurable
        (hH3 i).1

  have hdv2 :
      ∀ i r : PrimeTensor.Axis Depth.three,
        MemLp
          (spatial3.d i
            (fun x : Point3 =>
              (v t x).component r))
          (ENNReal.ofReal 2)
          volume := by
    intro i r

    have hC1 :
        SpatialC1
          (spatial3.d i
            (fun x : Point3 =>
              (v t x).component r)) := by
      dsimp only [v]

      exact
        s.velocity_firstPartial_spatialC1
          htNS r i

    exact
      memLp_two_of_spatialL2SquareIntegrable
        hC1.continuous.aestronglyMeasurable
        ((hH3 r).2.1 i)

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
          hdv2 i r)

  have hDiagBound :
      ∀
        (i : PrimeTensor.Axis Depth.three)
        (x : Point3),
          ‖spatial3.d
              i
              (fun y : Point3 =>
                (v t y).component i)
              x‖
            ≤
          h t := by
    intro i x
    dsimp only [v]

    simpa only [Real.norm_eq_abs] using
      hGradient i i x

  have hScalar :
      ∀ j : PrimeTensor.Axis Depth.three,
        TransportScalarIntegrationByPartsAt
          v t
          (fun x : Point3 =>
            (v t x).component j) := by
    intro j

    exact
      transportScalarIntegrationByPartsAt_of_memLp_four
        hvC1
        (hvC1 j)
        hv2
        hv4
        (hv2 j)
        (hv4 j)
        (fun i =>
          hdv2 i j)
        hDiagBound

  unfold H3TransportEnergyIntegrationByPartsAt
  unfold TransportEnergyIntegrationByPartsAt

  constructor

  · intro j

    have hInt :=
      (hScalar j).1

    simpa [
      v,
      transportEnergyFluxDivergenceXYZ,
      transportScalarFluxDivergenceXYZ
    ] using
      hInt

  · intro j

    have hZero :=
      (hScalar j).2

    simpa [
      v,
      transportEnergyFluxDivergenceXYZ,
      transportScalarFluxDivergenceXYZ,
      TransportEnergyFluxVanishesAt,
      TransportScalarFluxVanishesAt
    ] using
      hZero

end

end Euclidean
end Bridge
end PrimeTensor
