import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathTemporalPairingFrontier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Bridge

/-!
# Reduce the H³ temporal-pairing frontier to temporal-jet L² membership

`H3PathTemporalPairingFrontier` isolated the exact temporal products used by
the full H³ energy argument:

    D^α u · D^α ∂ₜu,     |α| ≤ 3.

The old factor is already an `L²` field at every strict time of a
`LoggedPreterminalH3PathAdmissible` solution.  Therefore the remaining
whole-space requirement can be stated more canonically as `L²` membership of
the temporal jet itself.

This file introduces

    H3TemporalJetMemLp2At

and proves, by the `L² × L² → L¹` Hölder inequality, that it implies the
temporal-energy pairing integrability package from the preceding frontier.

The resulting BKM theorem replaces four explicit product-integrability
families by one orderwise temporal-jet `L²` interface.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3PathTemporalJetL2Frontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathTemporalJetL2Frontier :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Temporal H³ jet in L² -/

/--
Every spatial derivative through order three of the pointwise temporal
velocity derivative belongs to physical `L²` at one time.
-/
def H3TemporalJetMemLp2At
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : Prop :=
  (
    ∀ j : PrimeTensor.Axis Depth.three,
      MemLp
        (loggedVelocityTemporalComponent u t j)
        2
        (volume : Measure Point3)
  )
    ∧
  (
    ∀ i j : PrimeTensor.Axis Depth.three,
      MemLp
        (spatial3.d i
          (loggedVelocityTemporalComponent u t j))
        2
        (volume : Measure Point3)
  )
    ∧
  (
    ∀ i k j : PrimeTensor.Axis Depth.three,
      MemLp
        (spatial3.d i
          (spatial3.d k
            (loggedVelocityTemporalComponent u t j)))
        2
        (volume : Measure Point3)
  )
    ∧
  (
    ∀ i k l j : PrimeTensor.Axis Depth.three,
      MemLp
        (spatial3.d i
          (spatial3.d k
            (spatial3.d l
              (loggedVelocityTemporalComponent u t j))))
        2
        (volume : Measure Point3)
  )

/--
Path-level temporal-jet `L²` frontier.
-/
def H3PathEnergyClassProducesTemporalJetMemLp2 : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        ∀ hClass : PreterminalH3EnergyClass u a T,
          ∀ t : ℝ,
            t ∈ Set.Ioo a T →
              H3TemporalJetMemLp2At u t

/-! ## Generic L² × L² → L¹ bridge -/

/--
Two real physical `L²` fields have an integrable pointwise product.
-/
private theorem integrable_mul_of_memLp_two_two_h3TemporalJet
    {f g : ScalarField3}
    (hf :
      MemLp
        f
        2
        (volume : Measure Point3))
    (hg :
      MemLp
        g
        2
        (volume : Measure Point3)) :
    Integrable
      (fun x : Point3 => f x * g x)
      (volume : Measure Point3) := by

  have hMeas :
      AEStronglyMeasurable
        (fun x : Point3 => f x * g x)
        (volume : Measure Point3) :=
    hf.1.mul hg.1

  rw [← MeasureTheory.integrable_norm_iff hMeas]

  have hAbs :
      Integrable
        (fun x : Point3 =>
          ‖f x‖ * ‖g x‖)
        (volume : Measure Point3) :=
    MemLp.integrable_mul
      hf.norm
      hg.norm

  simpa only [
    Real.norm_eq_abs,
    abs_mul
  ] using hAbs

/-! ## Temporal L² jet closes temporal energy pairings -/

/--
At one strict H³-path time, `L²` membership of the complete temporal jet
implies integrability of every temporal energy-pairing product.

The first factor is supplied automatically by H³-path admissibility.
-/
theorem h3TemporalEnergyPairingIntegrableAt_of_temporalJetMemLp2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTemporal : H3TemporalJetMemLp2At u t) :
    H3TemporalEnergyPairingIntegrableAt u t := by

  have hInt :
      VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t ht

  have hMeas :
      VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes
      ht

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro j

    have hjInt := hInt j
    have hjMeas := hMeas j
    dsimp only at hjInt hjMeas

    have hOld :
        MemLp
          (loggedVelocityComponent u t j)
          2
          (volume : Measure Point3) := by
      simpa using
        (memLp_two_of_spatialL2SquareIntegrable
          hjMeas.1
          hjInt.1)

    exact
      integrable_mul_of_memLp_two_two_h3TemporalJet
        hOld
        (hTemporal.1 j)

  · intro i j

    have hjInt := hInt j
    have hjMeas := hMeas j
    dsimp only at hjInt hjMeas

    have hOld :
        MemLp
          (spatial3.d i
            (loggedVelocityComponent u t j))
          2
          (volume : Measure Point3) := by
      simpa using
        (memLp_two_of_spatialL2SquareIntegrable
          (hjMeas.2.1 i)
          (hjInt.2.1 i))

    exact
      integrable_mul_of_memLp_two_two_h3TemporalJet
        hOld
        (hTemporal.2.1 i j)

  · intro i k j

    have hjInt := hInt j
    have hjMeas := hMeas j
    dsimp only at hjInt hjMeas

    have hOld :
        MemLp
          (spatial3.d i
            (spatial3.d k
              (loggedVelocityComponent u t j)))
          2
          (volume : Measure Point3) := by
      simpa using
        (memLp_two_of_spatialL2SquareIntegrable
          (hjMeas.2.2.1 i k)
          (hjInt.2.2.1 i k))

    exact
      integrable_mul_of_memLp_two_two_h3TemporalJet
        hOld
        (hTemporal.2.2.1 i k j)

  · intro i k l j

    have hjInt := hInt j
    have hjMeas := hMeas j
    dsimp only at hjInt hjMeas

    have hOld :
        MemLp
          (spatial3.d i
            (spatial3.d k
              (spatial3.d l
                (loggedVelocityComponent u t j))))
          2
          (volume : Measure Point3) := by
      simpa using
        (memLp_two_of_spatialL2SquareIntegrable
          (hjMeas.2.2.2 i k l)
          (hjInt.2.2.2 i k l))

    exact
      integrable_mul_of_memLp_two_two_h3TemporalJet
        hOld
        (hTemporal.2.2.2 i k l j)

/--
Path-level temporal-jet `L²` membership implies the exact temporal-pairing
frontier.
-/
theorem h3PathEnergyClassProducesTemporalEnergyPairingIntegrability_of_temporalJetMemLp2
    (hTemporal :
      H3PathEnergyClassProducesTemporalJetMemLp2) :
    H3PathEnergyClassProducesTemporalEnergyPairingIntegrability := by

  intro u T hH3 a hClass t ht

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 ht.1,
      ht.2
    ⟩

  exact
    h3TemporalEnergyPairingIntegrableAt_of_temporalJetMemLp2
      hH3
      htAbs
      (hTemporal u T hH3 a hClass t ht)

/-! ## BKM closure at the temporal-jet L² frontier -/

/--
BKM continuation with temporal product integrability replaced by the canonical
orderwise `L²` temporal-jet interface.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_temporalJetMemLp2_of_fullScalarEnergy
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hTemporal :
      H3PathEnergyClassProducesTemporalJetMemLp2)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_temporalPairings_of_fullScalarEnergy
      hLow
      hDerivative
      (h3PathEnergyClassProducesTemporalEnergyPairingIntegrability_of_temporalJetMemLp2
        hTemporal)
      hFull

end

end Euclidean
end Bridge
end PrimeTensor
