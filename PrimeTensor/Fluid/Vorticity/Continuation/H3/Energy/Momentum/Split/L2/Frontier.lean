import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Momentum.RHS.Square.Frontier

/-!
# Split the H³ momentum-RHS mass frontier into diffusion, transport, and pressure

`H3PathMomentumRHSSquareFrontier` removed the temporal derivative from the
remaining mass condition.  Its fixed-time hypothesis still treats the complete
momentum right-hand side as one field.

The exact momentum decomposition already gives, through order three,

    RHS = diffusion - transport - pressure.

This file makes those three analytic mechanisms independent.  At each order we
ask that the diffusion, transport, and pressure component fields belong to
physical `L²`.  Mathlib's `MemLp.sub` then reconstructs `L²` membership of the
complete RHS, and hence its square-integrability.

No new Navier--Stokes estimate is introduced here.  The canonical energy-class
pressure already carries the exact higher-order momentum split.

After this reduction, the open whole-space mass frontier has three named
pieces:

* differentiated diffusion in `L²`;
* differentiated transport in `L²`;
* differentiated pressure in `L²`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3PathMomentumSplitL2Frontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathMomentumSplitL2Frontier :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Generic L² recombination -/

/--
An `L²` real field has integrable pointwise square.
-/
private theorem spatialL2SquareIntegrable_of_memLp_two_h3MomentumSplit
    {f : ScalarField3}
    (hf :
      MemLp
        f
        2
        (volume : Measure Point3)) :
    SpatialL2SquareIntegrable f := by

  unfold SpatialL2SquareIntegrable

  have hSq :=
    hf.norm.integrable_sq

  simpa only [
    Real.norm_eq_abs,
    sq_abs
  ] using hSq

/--
If three real fields belong to `L²`, then their ordered difference
`d - q - r` has integrable square.
-/
private theorem spatialL2SquareIntegrable_sub_sub_of_memLp_two_h3MomentumSplit
    {d q r : ScalarField3}
    (hd :
      MemLp
        d
        2
        (volume : Measure Point3))
    (hq :
      MemLp
        q
        2
        (volume : Measure Point3))
    (hr :
      MemLp
        r
        2
        (volume : Measure Point3)) :
    SpatialL2SquareIntegrable
      (fun x : Point3 =>
        d x - q x - r x) := by

  have h :
      MemLp
        (d - q - r)
        2
        (volume : Measure Point3) :=
    (hd.sub hq).sub hr

  have hSq :
      SpatialL2SquareIntegrable
        (d - q - r) :=
    spatialL2SquareIntegrable_of_memLp_two_h3MomentumSplit
      h

  simpa only [
    SpatialL2SquareIntegrable,
    Pi.sub_apply
  ] using hSq

/-! ## Fixed-time split L² package -/

/--
Every diffusion, transport, and pressure component through differentiated
order three belongs to physical `L²`.
-/
def H3MomentumSplitMemLp2At
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (t : ℝ) : Prop :=
  (
    ∀ j : PrimeTensor.Axis Depth.three,
      MemLp
          (momentumDiffusion0Component
            (logSpaceTimeVectorField u)
            t j)
          2
          (volume : Measure Point3)
        ∧
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
          (momentumDiffusion1Component
            (logSpaceTimeVectorField u)
            t i j)
          2
          (volume : Measure Point3)
        ∧
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
          (momentumDiffusion2Component
            (logSpaceTimeVectorField u)
            t i k j)
          2
          (volume : Measure Point3)
        ∧
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
          (momentumDiffusion3Component
            (logSpaceTimeVectorField u)
            t i k l j)
          2
          (volume : Measure Point3)
        ∧
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

/--
Path-level split `L²` momentum frontier for the canonical energy-class
pressure.
-/
def H3PathEnergyClassProducesMomentumSplitMemLp2 : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        ∀ hClass : PreterminalH3EnergyClass u a T,
          ∀ t : ℝ,
            ∀ ht : t ∈ Set.Ioo a T,
              H3MomentumSplitMemLp2At
                u
                (h3EnergyClassSplitPressureAt hClass ht)
                t

/-! ## Split L² closes complete RHS square mass -/

/--
At one time, `L²` membership of the three momentum pieces at every order
implies square-integrability of the complete differentiated momentum RHS.
-/
theorem h3MomentumRHSSquareIntegrableAt_of_splitMemLp2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three}
    {t : ℝ}
    (hSplit :
      HigherOrderMomentumRHSSplitsAt
        (logSpaceTimeVectorField u)
        p
        t)
    (hL2 :
      H3MomentumSplitMemLp2At
        u p t) :
    H3MomentumRHSSquareIntegrableAt
      u p t := by

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro j

    rw [
      momentumRHS0Component_eq_split
        (logSpaceTimeVectorField u)
        p t j
    ]

    exact
      spatialL2SquareIntegrable_sub_sub_of_memLp_two_h3MomentumSplit
        (hL2.1 j).1
        (hL2.1 j).2.1
        (hL2.1 j).2.2

  · intro i j

    rw [
      momentumRHS1Component_eq_split
        (logSpaceTimeVectorField u)
        p t i j
    ]

    exact
      spatialL2SquareIntegrable_sub_sub_of_memLp_two_h3MomentumSplit
        (hL2.2.1 i j).1
        (hL2.2.1 i j).2.1
        (hL2.2.1 i j).2.2

  · intro i k j

    rw [hSplit.1 i k j]

    exact
      spatialL2SquareIntegrable_sub_sub_of_memLp_two_h3MomentumSplit
        (hL2.2.2.1 i k j).1
        (hL2.2.2.1 i k j).2.1
        (hL2.2.2.1 i k j).2.2

  · intro i k l j

    rw [hSplit.2 i k l j]

    exact
      spatialL2SquareIntegrable_sub_sub_of_memLp_two_h3MomentumSplit
        (hL2.2.2.2 i k l j).1
        (hL2.2.2.2 i k l j).2.1
        (hL2.2.2.2 i k l j).2.2

/--
The path-level split `L²` frontier implies the combined momentum-RHS
square-integrability frontier.
-/
theorem h3PathEnergyClassProducesMomentumRHSSquareIntegrability_of_splitMemLp2
    (hSplitL2 :
      H3PathEnergyClassProducesMomentumSplitMemLp2) :
    H3PathEnergyClassProducesMomentumRHSSquareIntegrability := by

  intro u T hH3 a hClass t ht

  exact
    h3MomentumRHSSquareIntegrableAt_of_splitMemLp2
      (h3EnergyClassSplitPressureAt_momentumRHSSplits
        hClass ht)
      (hSplitL2 u T hH3 a hClass t ht)

/-! ## BKM closure at the separated spatial L² frontier -/

/--
BKM continuation with the remaining momentum mass hypothesis separated into
diffusion, transport, and pressure `L²` membership through order three.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_momentumSplitMemLp2_of_fullScalarEnergy
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hSplitL2 :
      H3PathEnergyClassProducesMomentumSplitMemLp2)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_momentumRHSSquareIntegrability_of_fullScalarEnergy
      hLow
      hDerivative
      (h3PathEnergyClassProducesMomentumRHSSquareIntegrability_of_splitMemLp2
        hSplitL2)
      hFull

end

end Euclidean
end Bridge
end PrimeTensor
