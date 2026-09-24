import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Majorant.Path.Scalar.Energy.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Tail.Low.Scalar.Full.Frontier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Balance.Frontier

/-!
# Separate the BKM low-frequency tail from the full H³ scalar frontier under path majorants

The preceding path-majorant closure still used
`H3PathEnergyClassProducesScalarEnergyData`, whose order-zero pressure and
diffusion signs serve only one purpose: manufacturing the time-independent
physical `L²` tail bound required by the logarithmic BKM endpoint.

The full H³ differential inequality itself needs only

* diffusion pairing integrability;
* pressure pairing integrability;
* total H³ pressure cancellation;
* total H³ diffusion nonpositivity.

Those four fields are exactly
`H3PathEnergyClassProducesFullScalarEnergyData`.

This file therefore combines the already-closed path-specific derivative
majorants with the previously separated low-frequency interface.  The public
BKM frontier becomes

1. `H3PathEnergyClassProducesBKMZerothVelocityL2LateTail`;
2. `H3PathEnergyClassProducesH3EnergyDerivativeMajorants`;
3. `H3PathEnergyClassProducesFullScalarEnergyData`.

No order-zero pressure/diffusion sign is required by the full H³ spatial
frontier, and no global higher-time or global-majorant hypothesis reappears.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory

noncomputable section

/--
Path-specific derivative majorants plus the full-order diffusion/pressure
product families reconstruct the exact PDE pairing interface.
-/
theorem h3PathEnergyClassProducesPDEPairingIntegrability_of_pathMajorants_of_fullScalarEnergy
    (hMajorants :
      H3PathEnergyClassProducesH3EnergyDerivativeMajorants)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathEnergyClassProducesPDEPairingIntegrability := by

  intro u T hH3 a hClass t ht

  rcases
    hMajorants u T hH3 a hClass t ht
  with
    ⟨hMajorant⟩

  rcases
    hFull u T hH3 a hClass t ht
  with
    ⟨
      hDiffusionPairing,
      hPressurePairing,
      hPressure,
      hDiffusion
    ⟩

  exact
    h3PDEPairingIntegrableAt_of_majorants_of_diffusion_pressure
      hClass
      ht
      (h3EnergyClassSplitPressureAt_navierStokes
        hClass ht)
      (h3EnergyClassSplitPressureAt_momentumRHSSplits
        hClass ht)
      hMajorant
      hDiffusionPairing
      hPressurePairing

/--
The low-frequency tail may now be supplied independently of the full H³
pressure/diffusion analysis.

Together with path-specific derivative majorants and full-order scalar energy
data, it closes the exact-energy BKM theorem.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_pathMajorants_of_fullScalarEnergy
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hMajorants :
      H3PathEnergyClassProducesH3EnergyDerivativeMajorants)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  have hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities :=
    h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_of_pathMajorants
      hMajorants

  have hPairing :
      H3PathEnergyClassProducesPDEPairingIntegrability :=
    h3PathEnergyClassProducesPDEPairingIntegrability_of_pathMajorants_of_fullScalarEnergy
      hMajorants
      hFull

  have hSigns :
      H3PathEnergyClassProducesFullScalarSigns :=
    h3PathEnergyClassProducesFullScalarSigns_of_fullScalarEnergy
      hFull

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_exactEnergy
      hLow
      hDerivative
      hPairing
      hSigns

/--
Compatibility with the preceding six-field scalar-energy route.

If order-zero signs are available, they manufacture the low-frequency tail;
projection supplies the full-order spatial package.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_pathMajorants_of_scalarEnergy_via_fullScalar
    (hMajorants :
      H3PathEnergyClassProducesH3EnergyDerivativeMajorants)
    (hScalar :
      H3PathEnergyClassProducesScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  have hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail :=
    h3PathEnergyClassProducesBKMZerothVelocityL2LateTail_of_pathMajorants_of_scalarEnergy
      hMajorants
      hScalar

  have hFull :
      H3PathEnergyClassProducesFullScalarEnergyData :=
    h3PathEnergyClassProducesFullScalarEnergyData_of_scalarEnergy
      hScalar

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_pathMajorants_of_fullScalarEnergy
      hLow
      hMajorants
      hFull

end

end Euclidean
end Bridge
end PrimeTensor
