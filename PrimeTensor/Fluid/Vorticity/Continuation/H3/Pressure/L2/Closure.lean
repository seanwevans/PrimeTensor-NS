import PrimeTensor.Fluid.Vorticity.Continuation.H3.Pressure.L2.Order.Three
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Transport.L2.Closure

/-!
# Close the full H³ pressure L² frontier

Pressure components of orders zero through three are now all known to belong
to physical `L²` at every strict H³ energy-class time.  This file packages the
four component theorems into the exact path-level pressure predicate used by the
split BKM continuation theorem.

Since the transport frontier was already closed, this also removes the final
pressure assumption from that spatial-mass branch of the continuation theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-- The complete path-level pressure `L²` frontier is closed outright. -/
theorem h3PathEnergyClassProducesPressureMemLp2_closed :
    H3PathEnergyClassProducesPressureMemLp2 := by
  intro u T hH3 a hClass t ht

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro j
    exact
      h3PathEnergyClassProducesPressure0MemLp2_closed
        u T hH3 a hClass t ht j

  · intro i j
    exact
      h3PathEnergyClassProducesPressure1MemLp2_closed
        u T hH3 a hClass t ht i j

  · intro i k j
    exact
      h3PathEnergyClassProducesPressure2MemLp2_closed
        u T hH3 a hClass t ht i k j

  · intro i k l j
    exact
      h3PathEnergyClassProducesPressure3MemLp2_closed
        u T hH3 a hClass t ht i k l j

/-- With both transport and pressure closed, the old spatial mass package no
longer appears as a hypothesis in the BKM continuation frontier. -/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_fullScalarEnergy
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by
  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_pressure_of_fullScalarEnergy
      hLow
      hDerivative
      h3PathEnergyClassProducesPressureMemLp2_closed
      hFull

end

end Euclidean
end Bridge
end PrimeTensor
