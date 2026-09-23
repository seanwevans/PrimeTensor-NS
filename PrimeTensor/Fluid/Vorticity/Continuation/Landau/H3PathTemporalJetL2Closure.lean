import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathPDEPairingL2Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathTemporalJetSquareFrontier

/-!
# Close the complete H³ temporal jet in physical L²

The spatial momentum factors are already closed in physical `L²` through
differentiated order three:

* diffusion through order three;
* transport through order three;
* pressure through order three.

The existing frontier reductions then give, without any new estimate,

    split L²
      -> momentum RHS square-integrability
      -> temporal H³ jet square-integrability
      -> temporal H³ jet MemLp 2.

This packages the resulting path-level theorem for reuse in the direct
Hilbert-space differentiation of the remaining order-two and order-three
energy blocks.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory

noncomputable section

/-- Every differentiated momentum RHS through order three has integrable
physical square on every strict H³ energy-class time. -/
theorem h3PathEnergyClassProducesMomentumRHSSquareIntegrability_closed :
    H3PathEnergyClassProducesMomentumRHSSquareIntegrability := by
  exact
    h3PathEnergyClassProducesMomentumRHSSquareIntegrability_of_splitMemLp2
      h3PathEnergyClassProducesMomentumSplitMemLp2_closed

/-- Every spatial derivative through order three of the temporal velocity
belongs to physical `L²` square mass on every strict H³ energy-class time. -/
theorem h3PathEnergyClassProducesTemporalJetSquareIntegrability_closed :
    H3PathEnergyClassProducesTemporalJetSquareIntegrability := by
  exact
    h3PathEnergyClassProducesTemporalJetSquareIntegrability_of_momentumRHSSquareIntegrability
      h3PathEnergyClassProducesMomentumRHSSquareIntegrability_closed

/-- The complete old-path temporal H³ jet belongs to physical `L²` at every
strict energy-class time. -/
theorem h3PathEnergyClassProducesTemporalJetMemLp2_closed :
    H3PathEnergyClassProducesTemporalJetMemLp2 := by
  exact
    h3PathEnergyClassProducesTemporalJetMemLp2_of_squareIntegrability
      h3PathEnergyClassProducesTemporalJetSquareIntegrability_closed

end

end Euclidean
end Bridge
end PrimeTensor
