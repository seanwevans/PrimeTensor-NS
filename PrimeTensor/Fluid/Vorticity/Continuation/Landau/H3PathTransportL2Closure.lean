import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathClosedArbitraryFourthVelocityJets
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Regularity.Closure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.IntegrationByParts.OrderOneTwo

/-!
# Close the H³ transport L² frontier

The selected Duhamel/Fourier branch now supplies every ordered fourth spatial
velocity derivative in physical `L²`.  This is the last input needed to close
the differentiated advection fields themselves.

At one strict H³ energy-class time:

* `u` is pointwise bounded by the canonical H³ spectral evaluation estimate;
* `Du` is pointwise bounded by the canonical gradient estimate;
* `Du`, `D²u`, and `D³u` belong to `L²` from the H³ slice;
* `D²u` belongs to `L⁴` by the existing whole-space H¹ -> L⁴ theorem;
* arbitrary ordered `D⁴u` belongs to `L²` by the closed selected restart chain.

Thus every product occurring in differentiated transport through order three is
one of

    L∞ * L²,
    L⁴ * L⁴,

and therefore belongs to `L²`.  No new analytic hypothesis remains on the
transport side.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3PathTransportL2Closure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathTransportL2Closure :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

local instance holderTripleFourFourTwoH3PathTransportL2Closure :
    ENNReal.HolderTriple
      (4 : ENNReal)
      (4 : ENNReal)
      (2 : ENNReal) := by
  have hReal : Real.HolderTriple 4 4 2 := by
    rw [Real.holderTriple_iff]
    norm_num
  simpa using hReal.ennrealOfReal

/-! ## Generic product helpers -/

private theorem memLp2_mul_of_bounded_left
    {f g : ScalarField3}
    {B : ℝ}
    (hfBound : ∀ x : Point3, ‖f x‖ ≤ B)
    (hg2 :
      MemLp g
        (ENNReal.ofReal 2)
        (volume : Measure Point3))
    (hMeas :
      AEStronglyMeasurable
        (fun x : Point3 => f x * g x)
        (volume : Measure Point3)) :
    MemLp
      (fun x : Point3 => f x * g x)
      (ENNReal.ofReal 2)
      (volume : Measure Point3) := by
  refine hg2.of_le_mul (c := B) hMeas ?_
  filter_upwards with x
  rw [norm_mul]
  exact
    mul_le_mul_of_nonneg_right
      (hfBound x)
      (norm_nonneg _)

private theorem memLp2_mul_of_bounded_right
    {f g : ScalarField3}
    {B : ℝ}
    (hf2 :
      MemLp f
        (ENNReal.ofReal 2)
        (volume : Measure Point3))
    (hgBound : ∀ x : Point3, ‖g x‖ ≤ B)
    (hMeas :
      AEStronglyMeasurable
        (fun x : Point3 => f x * g x)
        (volume : Measure Point3)) :
    MemLp
      (fun x : Point3 => f x * g x)
      (ENNReal.ofReal 2)
      (volume : Measure Point3) := by
  refine hf2.of_le_mul (c := B) hMeas ?_
  filter_upwards with x
  rw [norm_mul]
  calc
    ‖f x‖ * ‖g x‖
        ≤
      ‖f x‖ * B :=
      mul_le_mul_of_nonneg_left
        (hgBound x)
        (norm_nonneg _)
    _ = B * ‖f x‖ := by ring

private theorem memLp_add_pointwise
    {f g : ScalarField3}
    {p : ENNReal}
    (hf :
      MemLp f p
        (volume : Measure Point3))
    (hg :
      MemLp g p
        (volume : Measure Point3)) :
    MemLp
      (fun x : Point3 => f x + g x)
      p
      (volume : Measure Point3) := by
  have hSum :
      MemLp (f + g) p
        (volume : Measure Point3) :=
    hf.add hg
  have hAE :
      (fun x : Point3 => f x + g x)
        =ᵐ[(volume : Measure Point3)]
      (f + g) := by
    filter_upwards with x
    rfl
  exact (memLp_congr_ae hAE).2 hSum

private theorem memLp2_mul_of_memLp4
    {f g : ScalarField3}
    (hf4 :
      MemLp f
        (ENNReal.ofReal 4)
        (volume : Measure Point3))
    (hg4 :
      MemLp g
        (ENNReal.ofReal 4)
        (volume : Measure Point3)) :
    MemLp
      (fun x : Point3 => f x * g x)
      (ENNReal.ofReal 2)
      (volume : Measure Point3) := by
  have hf4' :
      MemLp f (4 : ENNReal) (volume : Measure Point3) := by
    simpa using hf4
  have hg4' :
      MemLp g (4 : ENNReal) (volume : Measure Point3) := by
    simpa using hg4
  have h2 :
      MemLp
        (fun x : Point3 => f x * g x)
        (2 : ENNReal)
        (volume : Measure Point3) := by
    exact hg4'.mul' hf4'
  simpa using h2

/-! ## One-time transport closure -/

/--
At one strict energy-class time, arbitrary fourth-jet `L²` control closes all
four differentiated transport levels.
-/
theorem h3TransportMemLp2At_of_arbitraryFourthVelocityJet
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hPath : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hFourth : H3ArbitraryFourthVelocityJetMemLp2At u t) :
    (
      ∀ j : PrimeTensor.Axis Depth.three,
        MemLp
          (momentumTransport0Component
            (logSpaceTimeVectorField u)
            t j)
          2
          (volume : Measure Point3)
    )
      ∧
    (
      ∀ i j : PrimeTensor.Axis Depth.three,
        MemLp
          (momentumTransport1Component
            (logSpaceTimeVectorField u)
            t i j)
          2
          (volume : Measure Point3)
    )
      ∧
    (
      ∀ i k j : PrimeTensor.Axis Depth.three,
        MemLp
          (momentumTransport2Component
            (logSpaceTimeVectorField u)
            t i k j)
          2
          (volume : Measure Point3)
    )
      ∧
    (
      ∀ i k l j : PrimeTensor.Axis Depth.three,
        MemLp
          (momentumTransport3Component
            (logSpaceTimeVectorField u)
            t i k l j)
          2
          (volume : Measure Point3)
    ) := by

  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  have htTail : t ∈ Set.Ico a T :=
    ⟨le_of_lt ht.1, ht.2⟩

  have hH3 : VelocityH3IntegrableAt u t :=
    hPath.velocity_h3_integrable t htAbs

  rcases hClass.pressure_witness with
    ⟨p, s, hp4⟩

  let v := logSpaceTimeVectorField u

  have hLogged
      (j : PrimeTensor.Axis Depth.three) :
      loggedVelocityComponent u t j
        =
      (fun x : Point3 =>
        (logSpaceTimeVectorField u t x).component j) := by
    rfl

  have hBaseC1
      (j : PrimeTensor.Axis Depth.three) :
      SpatialC1 (loggedVelocityComponent u t j) := by
    unfold loggedVelocityComponent
    exact s.velocity_component_spatialC1 htAbs j

  have hFirstC1
      (i j : PrimeTensor.Axis Depth.three) :
      SpatialC1
        (spatial3.d i
          (loggedVelocityComponent u t j)) := by
    unfold loggedVelocityComponent
    exact s.velocity_firstPartial_spatialC1 htAbs j i

  have hSecondC1
      (i k j : PrimeTensor.Axis Depth.three) :
      SpatialC1
        (spatial3.d i
          (spatial3.d k
            (loggedVelocityComponent u t j))) := by
    have h3 : SpatialC3 (loggedVelocityComponent u t j) := by
      unfold loggedVelocityComponent
      exact s.regularity.velocity_spatial_three t htAbs j
    have hk2 :
        SpatialC2
          (spatial3.d k
            (loggedVelocityComponent u t j)) := by
      change
        SpatialC2
          (fun y =>
            partialDeriv k
              (loggedVelocityComponent u t j) y)
      exact
        PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
          h3 k
    change
      SpatialC1
        (fun y =>
          partialDeriv i
            (spatial3.d k
              (loggedVelocityComponent u t j)) y)
    exact
      PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
        hk2 i

  have hThirdC1
      (i k l j : PrimeTensor.Axis Depth.three) :
      SpatialC1
        (spatial3.d i
          (spatial3.d k
            (spatial3.d l
              (loggedVelocityComponent u t j)))) := by
    have hTwoC3 :
        SpatialC3
          (spatial3.d k
            (spatial3.d l
              (loggedVelocityComponent u t j))) := by
      change
        SpatialC3
          (spatial3.d k
            (spatial3.d l
              (fun x : Point3 =>
                (logSpaceTimeVectorField u t x).component j)))
      exact
        hClass.velocity_spatial_five
          t htTail j k l
    have hi2 :
        SpatialC2
          (spatial3.d i
            (spatial3.d k
              (spatial3.d l
                (loggedVelocityComponent u t j)))) := by
      change
        SpatialC2
          (fun y =>
            partialDeriv i
              (spatial3.d k
                (spatial3.d l
                  (loggedVelocityComponent u t j))) y)
      exact
        PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
          hTwoC3 i
    exact hi2.of_le (by norm_num)

  have hFirst2
      (i j : PrimeTensor.Axis Depth.three) :
      MemLp
        (spatial3.d i
          (loggedVelocityComponent u t j))
        (ENNReal.ofReal 2)
        (volume : Measure Point3) := by
    exact
      memLp_two_of_spatialL2SquareIntegrable
        (hFirstC1 i j).continuous.aestronglyMeasurable
        ((hH3 j).2.1 i)

  have hSecond2
      (i k j : PrimeTensor.Axis Depth.three) :
      MemLp
        (spatial3.d i
          (spatial3.d k
            (loggedVelocityComponent u t j)))
        (ENNReal.ofReal 2)
        (volume : Measure Point3) := by
    exact
      memLp_two_of_spatialL2SquareIntegrable
        (hSecondC1 i k j).continuous.aestronglyMeasurable
        ((hH3 j).2.2.1 i k)

  have hThird2
      (i k l j : PrimeTensor.Axis Depth.three) :
      MemLp
        (spatial3.d i
          (spatial3.d k
            (spatial3.d l
              (loggedVelocityComponent u t j))))
        (ENNReal.ofReal 2)
        (volume : Measure Point3) := by
    exact
      velocityH3IntegrableAt_third_memLp2
        hH3 j i k l
        (hThirdC1 i k l j).continuous.aestronglyMeasurable

  have hSobolev4 : WholeSpaceC1H1ToL4 :=
    wholeSpaceC1H1ToL4_of_wholeSpaceC1H1ToL6
      (wholeSpaceC1H1ToL6_of_fderiv
        wholeSpaceC1FDerivL2ToL6_cutoff)

  have hSecond4
      (i k j : PrimeTensor.Axis Depth.three) :
      MemLp
        (spatial3.d i
          (spatial3.d k
            (loggedVelocityComponent u t j)))
        (ENNReal.ofReal 4)
        (volume : Measure Point3) := by
    exact
      hSobolev4
        (spatial3.d i
          (spatial3.d k
            (loggedVelocityComponent u t j)))
        (hSecondC1 i k j)
        (hSecond2 i k j)
        (fun r => hThird2 r i k j)

  let B0 : ℝ :=
    h3RawFourierL1DeweightingCoefficient
      * velocityH3EnergyAt u t

  let B1 : ℝ :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
      * velocityH3EnergyAt u t

  have hVelBound
      (r : PrimeTensor.Axis Depth.three)
      (x : Point3) :
      ‖loggedVelocityComponent u t r x‖ ≤ B0 := by
    dsimp only [B0]
    exact
      norm_loggedVelocityComponent_le_h3Energy
        hClass ht hH3 r x

  have hGradBound
      (i j : PrimeTensor.Axis Depth.three)
      (x : Point3) :
      ‖spatial3.d i
          (loggedVelocityComponent u t j) x‖
        ≤ B1 := by
    dsimp only [B1]
    exact
      norm_loggedVelocityComponent_spatial_d_le_h3Energy
        hClass ht hH3 i j x

  have hUD1
      (r j : PrimeTensor.Axis Depth.three) :
      MemLp
        (fun x : Point3 =>
          loggedVelocityComponent u t r x
            * spatial3.d r
                (loggedVelocityComponent u t j) x)
        (ENNReal.ofReal 2)
        (volume : Measure Point3) := by
    exact
      memLp2_mul_of_bounded_left
        (hVelBound r)
        (hFirst2 r j)
        ((hBaseC1 r).continuous.aestronglyMeasurable.mul
          (hFirstC1 r j).continuous.aestronglyMeasurable)

  have hD1D1
      (a r b j : PrimeTensor.Axis Depth.three) :
      MemLp
        (fun x : Point3 =>
          spatial3.d a
              (loggedVelocityComponent u t r) x
            * spatial3.d b
                (loggedVelocityComponent u t j) x)
        (ENNReal.ofReal 2)
        (volume : Measure Point3) := by
    exact
      memLp2_mul_of_bounded_left
        (hGradBound a r)
        (hFirst2 b j)
        ((hFirstC1 a r).continuous.aestronglyMeasurable.mul
          (hFirstC1 b j).continuous.aestronglyMeasurable)

  have hUD2
      (r i j : PrimeTensor.Axis Depth.three) :
      MemLp
        (fun x : Point3 =>
          loggedVelocityComponent u t r x
            * spatial3.d r
                (spatial3.d i
                  (loggedVelocityComponent u t j)) x)
        (ENNReal.ofReal 2)
        (volume : Measure Point3) := by
    exact
      memLp2_mul_of_bounded_left
        (hVelBound r)
        (hSecond2 r i j)
        ((hBaseC1 r).continuous.aestronglyMeasurable.mul
          (hSecondC1 r i j).continuous.aestronglyMeasurable)

  have hD2D1
      (a b r c j : PrimeTensor.Axis Depth.three) :
      MemLp
        (fun x : Point3 =>
          spatial3.d a
              (spatial3.d b
                (loggedVelocityComponent u t r)) x
            * spatial3.d c
                (loggedVelocityComponent u t j) x)
        (ENNReal.ofReal 2)
        (volume : Measure Point3) := by
    exact
      memLp2_mul_of_bounded_right
        (hSecond2 a b r)
        (hGradBound c j)
        ((hSecondC1 a b r).continuous.aestronglyMeasurable.mul
          (hFirstC1 c j).continuous.aestronglyMeasurable)

  have hD1D2
      (a r b c j : PrimeTensor.Axis Depth.three) :
      MemLp
        (fun x : Point3 =>
          spatial3.d a
              (loggedVelocityComponent u t r) x
            * spatial3.d b
                (spatial3.d c
                  (loggedVelocityComponent u t j)) x)
        (ENNReal.ofReal 2)
        (volume : Measure Point3) := by
    exact
      memLp2_mul_of_bounded_left
        (hGradBound a r)
        (hSecond2 b c j)
        ((hFirstC1 a r).continuous.aestronglyMeasurable.mul
          (hSecondC1 b c j).continuous.aestronglyMeasurable)

  have hUD3
      (r i k j : PrimeTensor.Axis Depth.three) :
      MemLp
        (fun x : Point3 =>
          loggedVelocityComponent u t r x
            * spatial3.d r
                (spatial3.d i
                  (spatial3.d k
                    (loggedVelocityComponent u t j))) x)
        (ENNReal.ofReal 2)
        (volume : Measure Point3) := by
    exact
      memLp2_mul_of_bounded_left
        (hVelBound r)
        (hThird2 r i k j)
        ((hBaseC1 r).continuous.aestronglyMeasurable.mul
          (hThirdC1 r i k j).continuous.aestronglyMeasurable)

  have hD3D1
      (a b c r d j : PrimeTensor.Axis Depth.three) :
      MemLp
        (fun x : Point3 =>
          spatial3.d a
              (spatial3.d b
                (spatial3.d c
                  (loggedVelocityComponent u t r))) x
            * spatial3.d d
                (loggedVelocityComponent u t j) x)
        (ENNReal.ofReal 2)
        (volume : Measure Point3) := by
    exact
      memLp2_mul_of_bounded_right
        (hThird2 a b c r)
        (hGradBound d j)
        ((hThirdC1 a b c r).continuous.aestronglyMeasurable.mul
          (hFirstC1 d j).continuous.aestronglyMeasurable)

  have hD1D3
      (a r b c d j : PrimeTensor.Axis Depth.three) :
      MemLp
        (fun x : Point3 =>
          spatial3.d a
              (loggedVelocityComponent u t r) x
            * spatial3.d b
                (spatial3.d c
                  (spatial3.d d
                    (loggedVelocityComponent u t j))) x)
        (ENNReal.ofReal 2)
        (volume : Measure Point3) := by
    exact
      memLp2_mul_of_bounded_left
        (hGradBound a r)
        (hThird2 b c d j)
        ((hFirstC1 a r).continuous.aestronglyMeasurable.mul
          (hThirdC1 b c d j).continuous.aestronglyMeasurable)

  have hD2D2
      (a b r c d j : PrimeTensor.Axis Depth.three) :
      MemLp
        (fun x : Point3 =>
          spatial3.d a
              (spatial3.d b
                (loggedVelocityComponent u t r)) x
            * spatial3.d c
                (spatial3.d d
                  (loggedVelocityComponent u t j)) x)
        (ENNReal.ofReal 2)
        (volume : Measure Point3) := by
    exact
      memLp2_mul_of_memLp4
        (hSecond4 a b r)
        (hSecond4 c d j)

  have hUD4
      (r i k l j : PrimeTensor.Axis Depth.three) :
      MemLp
        (fun x : Point3 =>
          loggedVelocityComponent u t r x
            * spatial3.d r
                (spatial3.d i
                  (spatial3.d k
                    (spatial3.d l
                      (loggedVelocityComponent u t j)))) x)
        (ENNReal.ofReal 2)
        (volume : Measure Point3) := by
    have hFourth2 :
        MemLp
          (spatial3.d r
            (spatial3.d i
              (spatial3.d k
                (spatial3.d l
                  (loggedVelocityComponent u t j)))))
          (ENNReal.ofReal 2)
          (volume : Measure Point3) := by
      simpa using hFourth r i k l j
    exact
      memLp2_mul_of_bounded_left
        (hVelBound r)
        hFourth2
        ((hBaseC1 r).continuous.aestronglyMeasurable.mul
          hFourth2.1)

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro j
    change
      MemLp
        (fun x : Point3 =>
          loggedVelocityComponent u t xAxis x
              * spatial3.d xAxis
                  (loggedVelocityComponent u t j) x
            +
          (loggedVelocityComponent u t yAxis x
              * spatial3.d yAxis
                  (loggedVelocityComponent u t j) x
            +
           loggedVelocityComponent u t zAxis x
              * spatial3.d zAxis
                  (loggedVelocityComponent u t j) x))
        2
        (volume : Measure Point3)
    have hYZ :=
      memLp_add_pointwise
        (hUD1 yAxis j)
        (hUD1 zAxis j)
    have hXYZ :=
      memLp_add_pointwise
        (hUD1 xAxis j)
        hYZ
    simpa using hXYZ

  · intro i j

    have hComm :
        MemLp
          (firstTransportCommutator v t i j)
          (ENNReal.ofReal 2)
          (volume : Measure Point3) := by
      dsimp only [v]
      unfold firstTransportCommutator
      have hYZ :=
        memLp_add_pointwise
          (hD1D1 i yAxis yAxis j)
          (hD1D1 i zAxis zAxis j)
      have hXYZ :=
        memLp_add_pointwise
          (hD1D1 i xAxis xAxis j)
          hYZ
      rw [
        hLogged xAxis,
        hLogged yAxis,
        hLogged zAxis,
        hLogged j
      ] at hXYZ
      exact hXYZ

    have hPure :
        MemLp
          (firstTransportedDerivative v t i j)
          (ENNReal.ofReal 2)
          (volume : Measure Point3) := by
      dsimp only [v]
      unfold firstTransportedDerivative h3ScalarTransport
      have hYZ :=
        memLp_add_pointwise
          (hUD2 yAxis i j)
          (hUD2 zAxis i j)
      have hXYZ :=
        memLp_add_pointwise
          (hUD2 xAxis i j)
          hYZ
      rw [hLogged j] at hXYZ
      exact hXYZ

    rw [momentumTransport1Component_eq_commutator_add_transport
      s htAbs i j]
    simpa [v] using
      memLp_add_pointwise hComm hPure

  · intro i k j

    have hAxis
        (r : PrimeTensor.Axis Depth.three) :
        MemLp
          (secondTransportCommutatorAxisBlock v t i k j r)
          (ENNReal.ofReal 2)
          (volume : Measure Point3) := by
      dsimp only [v]
      unfold secondTransportCommutatorAxisBlock
      have h23 :=
        memLp_add_pointwise
          (hD1D2 k r i r j)
          (hD1D2 i r r k j)
      have h123 :=
        memLp_add_pointwise
          (hD2D1 i k r r j)
          h23
      rw [hLogged r, hLogged j] at h123
      simpa only [add_assoc] using h123

    have hCommEq :
        secondTransportCommutator v t i k j
          =
        fun x : Point3 =>
          secondTransportCommutatorAxisBlock
              v t i k j xAxis x
            +
          (secondTransportCommutatorAxisBlock
              v t i k j yAxis x
            +
           secondTransportCommutatorAxisBlock
              v t i k j zAxis x) := by
      funext x
      rw [secondTransportCommutator_eq_expanded
        s htAbs x i k j]
      exact
        secondTransportCommutatorExpanded_eq_axisBlocks
          t x i k j

    have hComm :
        MemLp
          (secondTransportCommutator v t i k j)
          (ENNReal.ofReal 2)
          (volume : Measure Point3) := by
      rw [hCommEq]
      exact
        memLp_add_pointwise
          (hAxis xAxis)
          (memLp_add_pointwise
            (hAxis yAxis)
            (hAxis zAxis))

    have hPure :
        MemLp
          (secondTransportedDerivative v t i k j)
          (ENNReal.ofReal 2)
          (volume : Measure Point3) := by
      dsimp only [v]
      unfold secondTransportedDerivative h3ScalarTransport
      have hYZ :=
        memLp_add_pointwise
          (hUD3 yAxis i k j)
          (hUD3 zAxis i k j)
      have hXYZ :=
        memLp_add_pointwise
          (hUD3 xAxis i k j)
          hYZ
      rw [hLogged j] at hXYZ
      exact hXYZ

    rw [momentumTransport2Component_eq_commutator_add_transport
      s htAbs i k j]
    simpa [v] using
      memLp_add_pointwise hComm hPure

  · intro i k l j

    have hRegular :
        H3OrderThreeTransportRegularityAt u t :=
      h3OrderThreeTransportRegularityAt_of_energyClass
        hClass ht

    have hAxis
        (r : PrimeTensor.Axis Depth.three) :
        MemLp
          (thirdTransportCommutatorAxisBlock v t i k l j r)
          (ENNReal.ofReal 2)
          (volume : Measure Point3) := by
      dsimp only [v]
      unfold
        thirdTransportCommutatorAxisBlock
        secondTransportCommutatorAxisDerivativeBlock
      have h1 := hD3D1 i k l r r j
      have h2 := hD2D2 k l r i r j
      have h3 := hD2D2 i l r k r j
      have h4 := hD1D3 l r i k r j
      have h5 := hD2D2 i k r r l j
      have h6 := hD1D3 k r i r l j
      have h7 := hD1D3 i r r k l j
      have h67 := memLp_add_pointwise h6 h7
      have h567 := memLp_add_pointwise h5 h67
      have h4567 := memLp_add_pointwise h4 h567
      have h34567 := memLp_add_pointwise h3 h4567
      have h234567 := memLp_add_pointwise h2 h34567
      have h1234567 := memLp_add_pointwise h1 h234567
      rw [hLogged r, hLogged j] at h1234567
      simpa only [add_assoc] using h1234567

    have hCommEq :
        thirdTransportCommutator v t i k l j
          =
        fun x : Point3 =>
          thirdTransportCommutatorAxisBlock
              v t i k l j xAxis x
            +
          (thirdTransportCommutatorAxisBlock
              v t i k l j yAxis x
            +
           thirdTransportCommutatorAxisBlock
              v t i k l j zAxis x) := by
      funext x
      rw [thirdTransportCommutator_eq_expanded
        s htAbs x i k l j]
      rfl

    have hComm :
        MemLp
          (thirdTransportCommutator v t i k l j)
          (ENNReal.ofReal 2)
          (volume : Measure Point3) := by
      rw [hCommEq]
      exact
        memLp_add_pointwise
          (hAxis xAxis)
          (memLp_add_pointwise
            (hAxis yAxis)
            (hAxis zAxis))

    have hPure :
        MemLp
          (thirdTransportedDerivative v t i k l j)
          (ENNReal.ofReal 2)
          (volume : Measure Point3) := by
      dsimp only [v]
      unfold thirdTransportedDerivative h3ScalarTransport
      have hYZ :=
        memLp_add_pointwise
          (hUD4 yAxis i k l j)
          (hUD4 zAxis i k l j)
      have hXYZ :=
        memLp_add_pointwise
          (hUD4 xAxis i k l j)
          hYZ
      rw [hLogged j] at hXYZ
      exact hXYZ

    rw [momentumTransport3Component_eq_commutator_add_transport
      s htAbs hRegular i k l j]
    simpa [v] using
      memLp_add_pointwise hComm hPure

/-! ## Path closure and BKM frontier reduction -/

/-- The full path-level transport `L²` frontier is now closed outright. -/
theorem h3PathEnergyClassProducesTransportMemLp2_closed :
    H3PathEnergyClassProducesTransportMemLp2 := by
  intro u T hPath a hClass t ht

  have hFourth :
      H3ArbitraryFourthVelocityJetMemLp2At u t :=
    h3PathEnergyClassProducesArbitraryFourthVelocityJetMemLp2_closed
      u T hPath a hClass t ht

  exact
    h3TransportMemLp2At_of_arbitraryFourthVelocityJet
      hPath hClass ht hFourth

/--
After closing transport, the split BKM continuation theorem retains pressure as
the only member of the old transport/pressure mass package.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_pressure_of_fullScalarEnergy
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hPressure :
      H3PathEnergyClassProducesPressureMemLp2)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by
  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_transport_of_pressure_of_fullScalarEnergy
      hLow
      hDerivative
      h3PathEnergyClassProducesTransportMemLp2_closed
      hPressure
      hFull

end

end Euclidean
end Bridge
end PrimeTensor
