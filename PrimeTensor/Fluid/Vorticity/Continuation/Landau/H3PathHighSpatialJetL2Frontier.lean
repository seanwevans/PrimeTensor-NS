import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathHighDiffusionL2Frontier

/-!
# Reduce high diffusion L² mass to fourth/fifth velocity jets

`H3PathHighDiffusionL2Frontier` showed that only

    D² Δu,  D³ Δu

remain beyond the retained H³ slice.

For the positive-time smoothing machinery, however, the natural objects are
ordinary spatial velocity derivatives, not differentiated Laplacians.

Using the `C⁵` spatial regularity already carried by
`PreterminalH3EnergyClass`, this file expands the two remaining diffusion
fields into the three coordinate Laplacian summands:

    D² Δu_j = Σ_a D² D_a² u_j,
    D³ Δu_j = Σ_a D³ D_a² u_j.

Thus the genuine diffusion frontier becomes simply physical `L²` membership of
the fourth and fifth spatial velocity jets.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3PathHighSpatialJetL2Frontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathHighSpatialJetL2Frontier :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Regularity helpers for differentiating the Laplacian expansion -/

private theorem spatialC1_of_spatialC3_highSpatialJet
    {f : ScalarField3}
    (hf : SpatialC3 f) :
    SpatialC1 f := by
  exact hf.of_le (by norm_num)

private theorem firstPartial_spatialC1_of_spatialC3_highSpatialJet
    {f : ScalarField3}
    (hf : SpatialC3 f)
    (i : PrimeTensor.Axis Depth.three) :
    SpatialC1 (spatial3.d i f) := by
  have hf2 : SpatialC2 f :=
    hf.of_le (by norm_num)
  exact
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      hf2 i

private theorem secondPartial_spatialC1_of_spatialC3_highSpatialJet
    {f : ScalarField3}
    (hf : SpatialC3 f)
    (i k : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (spatial3.d i (spatial3.d k f)) := by
  have hk2 : SpatialC2 (spatial3.d k f) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
      hf k
  exact
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      hk2 i

/-! ## Exact high-diffusion expansions -/

private theorem momentumDiffusion2Component_eq_fourthJetSum
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (i k j : PrimeTensor.Axis Depth.three) :
    momentumDiffusion2Component
        (logSpaceTimeVectorField u)
        t i k j
      =
    fun x : Point3 =>
      spatial3.d i
          (spatial3.d k
            (spatial3.d xAxis
              (spatial3.d xAxis
                (loggedVelocityComponent u t j)))) x
        +
      (
        spatial3.d i
            (spatial3.d k
              (spatial3.d yAxis
                (spatial3.d yAxis
                  (loggedVelocityComponent u t j)))) x
          +
        spatial3.d i
            (spatial3.d k
              (spatial3.d zAxis
                (spatial3.d zAxis
                  (loggedVelocityComponent u t j)))) x
      ) := by

  let f : ScalarField3 :=
    loggedVelocityComponent u t j

  have htTail :
      t ∈ Set.Ico a T :=
    ⟨le_of_lt ht.1, ht.2⟩

  have hPure3
      (q : PrimeTensor.Axis Depth.three) :
      SpatialC3
        (spatial3.d q (spatial3.d q f)) := by
    dsimp only [f, loggedVelocityComponent]
    exact
      hClass.velocity_spatial_five
        t htTail j q q

  have hLap :
      momentumDiffusion0Component
          (logSpaceTimeVectorField u)
          t j
        =
      fun x : Point3 =>
        spatial3.d xAxis (spatial3.d xAxis f) x
          +
        (
          spatial3.d yAxis (spatial3.d yAxis f) x
            +
          spatial3.d zAxis (spatial3.d zAxis f) x
        ) := by
    funext x
    unfold momentumDiffusion0Component
    dsimp only [f, loggedVelocityComponent]
    exact
      laplacian3_eq
        (fun y : Point3 =>
          (logSpaceTimeVectorField u t y).component j)
        x

  have hFirst :
      spatial3.d k
          (momentumDiffusion0Component
            (logSpaceTimeVectorField u)
            t j)
        =
      fun x : Point3 =>
        spatial3.d k
            (spatial3.d xAxis (spatial3.d xAxis f)) x
          +
        (
          spatial3.d k
              (spatial3.d yAxis (spatial3.d yAxis f)) x
            +
          spatial3.d k
              (spatial3.d zAxis (spatial3.d zAxis f)) x
        ) := by

    have hx :
        SpatialC1
          (spatial3.d xAxis (spatial3.d xAxis f)) :=
      spatialC1_of_spatialC3_highSpatialJet
        (hPure3 xAxis)

    have hy :
        SpatialC1
          (spatial3.d yAxis (spatial3.d yAxis f)) :=
      spatialC1_of_spatialC3_highSpatialJet
        (hPure3 yAxis)

    have hz :
        SpatialC1
          (spatial3.d zAxis (spatial3.d zAxis f)) :=
      spatialC1_of_spatialC3_highSpatialJet
        (hPure3 zAxis)

    have hyz :
        SpatialC1
          (fun x : Point3 =>
            spatial3.d yAxis (spatial3.d yAxis f) x
              +
            spatial3.d zAxis (spatial3.d zAxis f) x) :=
      hy.add hz

    rw [hLap]
    funext x

    simp only [spatial3] at hx hy hz hyz ⊢

    rw [
      PrimeTensor.Bridge.Euclidean.SpatialC1.spatial_d_add
        hx hyz x k,
      PrimeTensor.Bridge.Euclidean.SpatialC1.spatial_d_add
        hy hz x k
    ]

  have hx1 :
      SpatialC1
        (spatial3.d k
          (spatial3.d xAxis (spatial3.d xAxis f))) :=
    firstPartial_spatialC1_of_spatialC3_highSpatialJet
      (hPure3 xAxis) k

  have hy1 :
      SpatialC1
        (spatial3.d k
          (spatial3.d yAxis (spatial3.d yAxis f))) :=
    firstPartial_spatialC1_of_spatialC3_highSpatialJet
      (hPure3 yAxis) k

  have hz1 :
      SpatialC1
        (spatial3.d k
          (spatial3.d zAxis (spatial3.d zAxis f))) :=
    firstPartial_spatialC1_of_spatialC3_highSpatialJet
      (hPure3 zAxis) k

  unfold momentumDiffusion2Component momentumDiffusion1Component
  have hyz1 :
      SpatialC1
        (fun x : Point3 =>
          spatial3.d k
              (spatial3.d yAxis (spatial3.d yAxis f)) x
            +
          spatial3.d k
              (spatial3.d zAxis (spatial3.d zAxis f)) x) :=
    hy1.add hz1

  rw [hFirst]
  funext x

  dsimp only [f] at hx1 hy1 hz1 hyz1 ⊢
  simp only [spatial3] at hx1 hy1 hz1 hyz1 ⊢

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial_d_add
      hx1 hyz1 x i,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial_d_add
      hy1 hz1 x i
  ]

private theorem momentumDiffusion3Component_eq_fifthJetSum
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (i k l j : PrimeTensor.Axis Depth.three) :
    momentumDiffusion3Component
        (logSpaceTimeVectorField u)
        t i k l j
      =
    fun x : Point3 =>
      spatial3.d i
          (spatial3.d k
            (spatial3.d l
              (spatial3.d xAxis
                (spatial3.d xAxis
                  (loggedVelocityComponent u t j))))) x
        +
      (
        spatial3.d i
            (spatial3.d k
              (spatial3.d l
                (spatial3.d yAxis
                  (spatial3.d yAxis
                    (loggedVelocityComponent u t j))))) x
          +
        spatial3.d i
            (spatial3.d k
              (spatial3.d l
                (spatial3.d zAxis
                  (spatial3.d zAxis
                    (loggedVelocityComponent u t j))))) x
      ) := by

  let f : ScalarField3 :=
    loggedVelocityComponent u t j

  have htTail :
      t ∈ Set.Ico a T :=
    ⟨le_of_lt ht.1, ht.2⟩

  have hPure3
      (q : PrimeTensor.Axis Depth.three) :
      SpatialC3
        (spatial3.d q (spatial3.d q f)) := by
    dsimp only [f, loggedVelocityComponent]
    exact
      hClass.velocity_spatial_five
        t htTail j q q

  have hDiff2 :=
    momentumDiffusion2Component_eq_fourthJetSum
      hClass ht k l j

  have hx1 :
      SpatialC1
        (spatial3.d k
          (spatial3.d l
            (spatial3.d xAxis (spatial3.d xAxis f)))) :=
    secondPartial_spatialC1_of_spatialC3_highSpatialJet
      (hPure3 xAxis) k l

  have hy1 :
      SpatialC1
        (spatial3.d k
          (spatial3.d l
            (spatial3.d yAxis (spatial3.d yAxis f)))) :=
    secondPartial_spatialC1_of_spatialC3_highSpatialJet
      (hPure3 yAxis) k l

  have hz1 :
      SpatialC1
        (spatial3.d k
          (spatial3.d l
            (spatial3.d zAxis (spatial3.d zAxis f)))) :=
    secondPartial_spatialC1_of_spatialC3_highSpatialJet
      (hPure3 zAxis) k l

  unfold momentumDiffusion3Component
  change
    spatial3.d i
        (momentumDiffusion2Component
          (logSpaceTimeVectorField u)
          t k l j)
      =
    _

  have hyz1 :
      SpatialC1
        (fun x : Point3 =>
          spatial3.d k
              (spatial3.d l
                (spatial3.d yAxis (spatial3.d yAxis f))) x
            +
          spatial3.d k
              (spatial3.d l
                (spatial3.d zAxis (spatial3.d zAxis f))) x) :=
    hy1.add hz1

  rw [hDiff2]
  funext x

  dsimp only [f] at hx1 hy1 hz1 hyz1 ⊢
  simp only [spatial3] at hx1 hy1 hz1 hyz1 ⊢

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial_d_add
      hx1 hyz1 x i,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial_d_add
      hy1 hz1 x i
  ]

/-! ## Fourth/fifth spatial velocity L² frontier -/

/--
Physical `L²` membership of every fourth and fifth spatial derivative of the
old logged velocity, written in the derivative ordering needed by the
Laplacian expansion.
-/
def H3FourthFifthVelocityJetMemLp2At
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : Prop :=
  (
    ∀ i k q j : PrimeTensor.Axis Depth.three,
      MemLp
        (spatial3.d i
          (spatial3.d k
            (spatial3.d q
              (spatial3.d q
                (loggedVelocityComponent u t j)))))
        2
        (volume : Measure Point3)
  )
    ∧
  (
    ∀ i k l q j : PrimeTensor.Axis Depth.three,
      MemLp
        (spatial3.d i
          (spatial3.d k
            (spatial3.d l
              (spatial3.d q
                (spatial3.d q
                  (loggedVelocityComponent u t j))))))
        2
        (volume : Measure Point3)
  )

def H3PathEnergyClassProducesFourthFifthVelocityJetMemLp2 : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        ∀ _hClass : PreterminalH3EnergyClass u a T,
          ∀ t : ℝ,
            t ∈ Set.Ioo a T →
              H3FourthFifthVelocityJetMemLp2At u t

/-! ## Fourth/fifth jets close the high-diffusion frontier -/

theorem h3HighDiffusionMemLp2At_of_fourthFifthVelocityJetMemLp2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hJet : H3FourthFifthVelocityJetMemLp2At u t) :
    H3HighDiffusionMemLp2At u t := by

  constructor

  · intro i k j
    rw [
      momentumDiffusion2Component_eq_fourthJetSum
        hClass ht i k j
    ]
    exact
      (hJet.1 i k xAxis j).add
        ((hJet.1 i k yAxis j).add
          (hJet.1 i k zAxis j))

  · intro i k l j
    rw [
      momentumDiffusion3Component_eq_fifthJetSum
        hClass ht i k l j
    ]
    exact
      (hJet.2 i k l xAxis j).add
        ((hJet.2 i k l yAxis j).add
          (hJet.2 i k l zAxis j))

theorem h3PathEnergyClassProducesHighDiffusionMemLp2_of_fourthFifthVelocityJetMemLp2
    (hJet :
      H3PathEnergyClassProducesFourthFifthVelocityJetMemLp2) :
    H3PathEnergyClassProducesHighDiffusionMemLp2 := by

  intro u T hH3 a hClass t ht

  exact
    h3HighDiffusionMemLp2At_of_fourthFifthVelocityJetMemLp2
      hClass
      ht
      (hJet u T hH3 a hClass t ht)

/-! ## BKM closure at the fourth/fifth spatial-jet frontier -/

theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_fourthFifthVelocityJet_of_transportPressure_of_fullScalarEnergy
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hJet :
      H3PathEnergyClassProducesFourthFifthVelocityJetMemLp2)
    (hTP :
      H3PathEnergyClassProducesTransportPressureMemLp2)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_highDiffusion_of_transportPressure_of_fullScalarEnergy
      hLow
      hDerivative
      (h3PathEnergyClassProducesHighDiffusionMemLp2_of_fourthFifthVelocityJetMemLp2
        hJet)
      hTP
      hFull

end

end Euclidean
end Bridge
end PrimeTensor
