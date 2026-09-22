import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathPressureL2Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathClosedHighVelocityJets
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathHighDiffusionL2Frontier
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathExactEnergyFrontier

/-!
# Close the H³ PDE pairing frontier from physical L² mass

The spatial mass work has now closed every factor appearing in the canonical
H³ momentum pairings:

* the velocity H³ jet is in physical `L²` by path admissibility;
* diffusion is in physical `L²` through order three;
* transport is in physical `L²` through order three;
* pressure is in physical `L²` through order three.

Therefore each product in `H3PDEPairingIntegrableAt` belongs to `L¹` by
`L² × L² → L¹`.  This closes the exact PDE pairing frontier outright.

Consequently the current BKM continuation theorem no longer needs the pairing
part of `H3PathEnergyClassProducesFullScalarEnergyData`: only the two scalar
pressure/diffusion sign conclusions remain.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3PathPDEPairingL2Closure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathPDEPairingL2Closure :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Two real physical `L²` fields have an integrable pointwise product. -/
private theorem integrable_mul_of_memLp_two_two_h3PDEPairingL2Closure
    {f g : ScalarField3}
    (hf : MemLp f 2 (volume : Measure Point3))
    (hg : MemLp g 2 (volume : Measure Point3)) :
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
        (fun x : Point3 => ‖f x‖ * ‖g x‖)
        (volume : Measure Point3) :=
    MemLp.integrable_mul hf.norm hg.norm

  simpa only [Real.norm_eq_abs, abs_mul] using hAbs

/-- All diffusion/transport/pressure momentum components through order three
belong to physical `L²` on every admissible H³ path. -/
theorem h3PathEnergyClassProducesMomentumSplitMemLp2_closed :
    H3PathEnergyClassProducesMomentumSplitMemLp2 := by
  have hTP :
      H3PathEnergyClassProducesTransportPressureMemLp2 :=
    h3PathEnergyClassProducesTransportPressureMemLp2_of_transport_of_pressure
      h3PathEnergyClassProducesTransportMemLp2_closed
      h3PathEnergyClassProducesPressureMemLp2_closed

  exact
    h3PathEnergyClassProducesMomentumSplitMemLp2_of_highDiffusion_of_transportPressure
      h3PathEnergyClassProducesHighDiffusionMemLp2_closed
      hTP

/-- The complete exact PDE pairing-integrability frontier is closed outright
from the physical `L²` mass already established for all spatial factors. -/
theorem h3PathEnergyClassProducesPDEPairingIntegrability_closed :
    H3PathEnergyClassProducesPDEPairingIntegrability := by
  intro u T hH3 a hClass t ht

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 ht.1,
      ht.2
    ⟩

  have hInt :
      VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs

  have hMeas :
      VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs

  have hSplit :
      H3MomentumSplitMemLp2At
        u
        (h3EnergyClassSplitPressureAt hClass ht)
        t :=
    h3PathEnergyClassProducesMomentumSplitMemLp2_closed
      u T hH3 a hClass t ht

  unfold H3PDEPairingIntegrableAt
  dsimp only
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
      ⟨
        integrable_mul_of_memLp_two_two_h3PDEPairingL2Closure
          hOld (hSplit.1 j).1,
        integrable_mul_of_memLp_two_two_h3PDEPairingL2Closure
          hOld (hSplit.1 j).2.1,
        integrable_mul_of_memLp_two_two_h3PDEPairingL2Closure
          hOld (hSplit.1 j).2.2
      ⟩

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
      ⟨
        integrable_mul_of_memLp_two_two_h3PDEPairingL2Closure
          hOld (hSplit.2.1 i j).1,
        integrable_mul_of_memLp_two_two_h3PDEPairingL2Closure
          hOld (hSplit.2.1 i j).2.1,
        integrable_mul_of_memLp_two_two_h3PDEPairingL2Closure
          hOld (hSplit.2.1 i j).2.2
      ⟩

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
      ⟨
        integrable_mul_of_memLp_two_two_h3PDEPairingL2Closure
          hOld (hSplit.2.2.1 i k j).1,
        integrable_mul_of_memLp_two_two_h3PDEPairingL2Closure
          hOld (hSplit.2.2.1 i k j).2.1,
        integrable_mul_of_memLp_two_two_h3PDEPairingL2Closure
          hOld (hSplit.2.2.1 i k j).2.2
      ⟩

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
      ⟨
        integrable_mul_of_memLp_two_two_h3PDEPairingL2Closure
          hOld (hSplit.2.2.2 i k l j).1,
        integrable_mul_of_memLp_two_two_h3PDEPairingL2Closure
          hOld (hSplit.2.2.2 i k l j).2.1,
        integrable_mul_of_memLp_two_two_h3PDEPairingL2Closure
          hOld (hSplit.2.2.2 i k l j).2.2
      ⟩

/-- After closing all spatial pairings, the exact BKM frontier needs from the
old full-scalar package only pressure cancellation and diffusion
nonpositivity. -/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_fullScalarSigns
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hSigns :
      H3PathEnergyClassProducesFullScalarSigns) :
    H3PathVorticityL1LinfProducesExtension := by
  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_exactEnergy
      hLow
      hDerivative
      h3PathEnergyClassProducesPDEPairingIntegrability_closed
      hSigns

end

end Euclidean
end Bridge
end PrimeTensor
