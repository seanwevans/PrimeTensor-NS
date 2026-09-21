import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathMomentumSplitL2Frontier

/-!
# Remove the low-order diffusion L² hypotheses from the H³ momentum frontier

The separated momentum frontier asks for physical `L²` membership of
diffusion, transport, and pressure through differentiated order three.

For diffusion, the first two levels are not genuine new assumptions.

* order zero is `Δu`, hence a finite sum of second spatial derivatives of `u`;
* order one is `D Δu`, hence a finite sum of third spatial derivatives of `u`.

Both are already in `L²` at every strict time of a
`LoggedPreterminalH3PathAdmissible` solution, because the retained H³ slice
contains all velocity derivatives through order three.

Therefore the genuine diffusion mass frontier begins only at

    D² Δu   and   D³ Δu,

equivalently at spatial velocity orders four and five.

This file proves the low-order diffusion `L²` facts automatically and replaces
the full diffusion package by a high-diffusion package containing only orders
two and three.  Transport and pressure remain unchanged.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3PathHighDiffusionL2Frontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathHighDiffusionL2Frontier :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Low-order diffusion is already H³ data -/

/--
The undifferentiated componentwise Laplacian belongs to physical `L²` at every
strict H³-path time.
-/
theorem h3MomentumDiffusion0_memLp2_of_pathAdmissible
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (j : PrimeTensor.Axis Depth.three) :
    MemLp
      (momentumDiffusion0Component
        (logSpaceTimeVectorField u)
        t j)
      2
      (volume : Measure Point3) := by

  have hInt :
      VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t ht

  have hMeas :
      VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes
      ht

  have hjInt := hInt j
  have hjMeas := hMeas j
  dsimp only at hjInt hjMeas

  let f : ScalarField3 :=
    loggedVelocityComponent u t j

  have hxx :
      MemLp
        (spatial3.d xAxis
          (spatial3.d xAxis f))
        2
        (volume : Measure Point3) := by
    dsimp only [f]
    simpa using
      (memLp_two_of_spatialL2SquareIntegrable
        (hjMeas.2.2.1 xAxis xAxis)
        (hjInt.2.2.1 xAxis xAxis))

  have hyy :
      MemLp
        (spatial3.d yAxis
          (spatial3.d yAxis f))
        2
        (volume : Measure Point3) := by
    dsimp only [f]
    simpa using
      (memLp_two_of_spatialL2SquareIntegrable
        (hjMeas.2.2.1 yAxis yAxis)
        (hjInt.2.2.1 yAxis yAxis))

  have hzz :
      MemLp
        (spatial3.d zAxis
          (spatial3.d zAxis f))
        2
        (volume : Measure Point3) := by
    dsimp only [f]
    simpa using
      (memLp_two_of_spatialL2SquareIntegrable
        (hjMeas.2.2.1 zAxis zAxis)
        (hjInt.2.2.1 zAxis zAxis))

  have hEq :
      momentumDiffusion0Component
          (logSpaceTimeVectorField u)
          t j
        =
      fun x : Point3 =>
        spatial3.d xAxis
            (spatial3.d xAxis f) x
          +
        (spatial3.d yAxis
            (spatial3.d yAxis f) x
          +
         spatial3.d zAxis
            (spatial3.d zAxis f) x) := by
    funext x
    unfold momentumDiffusion0Component
    dsimp only [f, loggedVelocityComponent]
    exact
      laplacian3_eq
        (fun y : Point3 =>
          (logSpaceTimeVectorField u t y).component j)
        x

  rw [hEq]
  exact hxx.add (hyy.add hzz)

/--
One spatial derivative of the componentwise Laplacian belongs to physical
`L²` at every strict H³-path time.
-/
theorem h3MomentumDiffusion1_memLp2_of_pathAdmissible
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (i j : PrimeTensor.Axis Depth.three) :
    MemLp
      (momentumDiffusion1Component
        (logSpaceTimeVectorField u)
        t i j)
      2
      (volume : Measure Point3) := by

  have hInt :
      VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t ht

  have hMeas :
      VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes
      ht

  have hjInt := hInt j
  have hjMeas := hMeas j
  dsimp only at hjInt hjMeas

  let f : ScalarField3 :=
    loggedVelocityComponent u t j

  obtain ⟨p, hNS⟩ :=
    hH3.navier_stokes

  have hf3 :
      SpatialC3 f := by
    dsimp only [f, loggedVelocityComponent]
    exact
      hNS.regularity.velocity_spatial_three
        t ht j

  have hxxx :
      MemLp
        (spatial3.d i
          (spatial3.d xAxis
            (spatial3.d xAxis f)))
        2
        (volume : Measure Point3) := by
    dsimp only [f]
    simpa using
      (memLp_two_of_spatialL2SquareIntegrable
        (hjMeas.2.2.2 i xAxis xAxis)
        (hjInt.2.2.2 i xAxis xAxis))

  have hyyy :
      MemLp
        (spatial3.d i
          (spatial3.d yAxis
            (spatial3.d yAxis f)))
        2
        (volume : Measure Point3) := by
    dsimp only [f]
    simpa using
      (memLp_two_of_spatialL2SquareIntegrable
        (hjMeas.2.2.2 i yAxis yAxis)
        (hjInt.2.2.2 i yAxis yAxis))

  have hzzz :
      MemLp
        (spatial3.d i
          (spatial3.d zAxis
            (spatial3.d zAxis f)))
        2
        (volume : Measure Point3) := by
    dsimp only [f]
    simpa using
      (memLp_two_of_spatialL2SquareIntegrable
        (hjMeas.2.2.2 i zAxis zAxis)
        (hjInt.2.2.2 i zAxis zAxis))

  have hEq :
      momentumDiffusion1Component
          (logSpaceTimeVectorField u)
          t i j
        =
      fun x : Point3 =>
        spatial3.d i
            (spatial3.d xAxis
              (spatial3.d xAxis f)) x
          +
        (spatial3.d i
            (spatial3.d yAxis
              (spatial3.d yAxis f)) x
          +
         spatial3.d i
            (spatial3.d zAxis
              (spatial3.d zAxis f)) x) := by
    funext x
    unfold momentumDiffusion1Component momentumDiffusion0Component
    dsimp only [f, loggedVelocityComponent]
    exact
      PrimeTensor.Bridge.Euclidean.SpatialC3.spatial_d_laplacian3
        hf3 x i

  rw [hEq]
  exact hxxx.add (hyyy.add hzzz)

/-! ## Genuine high-diffusion frontier -/

/--
Only the order-two and order-three differentiated diffusion fields remain as
new `L²` data beyond H³.
-/
def H3HighDiffusionMemLp2At
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : Prop :=
  (
    ∀ i k j : PrimeTensor.Axis Depth.three,
      MemLp
        (momentumDiffusion2Component
          (logSpaceTimeVectorField u)
          t i k j)
        2
        (volume : Measure Point3)
  )
    ∧
  (
    ∀ i k l j : PrimeTensor.Axis Depth.three,
      MemLp
        (momentumDiffusion3Component
          (logSpaceTimeVectorField u)
          t i k l j)
        2
        (volume : Measure Point3)
  )

/--
The transport and pressure pieces retain their full order-zero through
order-three `L²` requirements.
-/
def H3TransportPressureMemLp2At
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (t : ℝ) : Prop :=
  (
    ∀ j : PrimeTensor.Axis Depth.three,
      MemLp
          (momentumTransport0Component
            (logSpaceTimeVectorField u)
            t j)
          2
          (volume : Measure Point3)
        ∧
      MemLp
          (momentumPressure0Component
            p t j)
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
        ∧
      MemLp
          (momentumPressure1Component
            p t i j)
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
        ∧
      MemLp
          (momentumPressure2Component
            p t i k j)
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
        ∧
      MemLp
          (momentumPressure3Component
            p t i k l j)
          2
          (volume : Measure Point3)
  )

def H3PathEnergyClassProducesHighDiffusionMemLp2 : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        ∀ _hClass : PreterminalH3EnergyClass u a T,
          ∀ t : ℝ,
            t ∈ Set.Ioo a T →
              H3HighDiffusionMemLp2At u t

def H3PathEnergyClassProducesTransportPressureMemLp2 : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        ∀ hClass : PreterminalH3EnergyClass u a T,
          ∀ t : ℝ,
            ∀ ht : t ∈ Set.Ioo a T,
              H3TransportPressureMemLp2At
                u
                (h3EnergyClassSplitPressureAt hClass ht)
                t

/-! ## Reconstruct the previous split frontier -/

/--
H³ supplies low diffusion automatically, so high diffusion together with the
transport/pressure package reconstructs the previous full split `L²` frontier.
-/
theorem h3PathEnergyClassProducesMomentumSplitMemLp2_of_highDiffusion_of_transportPressure
    (hDiffusion :
      H3PathEnergyClassProducesHighDiffusionMemLp2)
    (hTP :
      H3PathEnergyClassProducesTransportPressureMemLp2) :
    H3PathEnergyClassProducesMomentumSplitMemLp2 := by

  intro u T hH3 a hClass t ht

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 ht.1,
      ht.2
    ⟩

  have hHigh :=
    hDiffusion u T hH3 a hClass t ht

  have hTransportPressure :=
    hTP u T hH3 a hClass t ht

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro j
    exact
      ⟨
        h3MomentumDiffusion0_memLp2_of_pathAdmissible
          hH3 htAbs j,
        (hTransportPressure.1 j).1,
        (hTransportPressure.1 j).2
      ⟩

  · intro i j
    exact
      ⟨
        h3MomentumDiffusion1_memLp2_of_pathAdmissible
          hH3 htAbs i j,
        (hTransportPressure.2.1 i j).1,
        (hTransportPressure.2.1 i j).2
      ⟩

  · intro i k j
    exact
      ⟨
        hHigh.1 i k j,
        (hTransportPressure.2.2.1 i k j).1,
        (hTransportPressure.2.2.1 i k j).2
      ⟩

  · intro i k l j
    exact
      ⟨
        hHigh.2 i k l j,
        (hTransportPressure.2.2.2 i k l j).1,
        (hTransportPressure.2.2.2 i k l j).2
      ⟩

/-! ## BKM closure at the high-diffusion frontier -/

/--
BKM continuation with the diffusion mass assumption reduced to only the
genuinely super-H³ levels `D²Δu` and `D³Δu`.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_highDiffusion_of_transportPressure_of_fullScalarEnergy
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hDiffusion :
      H3PathEnergyClassProducesHighDiffusionMemLp2)
    (hTP :
      H3PathEnergyClassProducesTransportPressureMemLp2)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_momentumSplitMemLp2_of_fullScalarEnergy
      hLow
      hDerivative
      (h3PathEnergyClassProducesMomentumSplitMemLp2_of_highDiffusion_of_transportPressure
        hDiffusion hTP)
      hFull

end

end Euclidean
end Bridge
end PrimeTensor
