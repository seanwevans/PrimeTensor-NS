import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedDuhamelTailRadialL2Closure

/-!
# Remove the selected Duhamel tail radial L² hypothesis from the H³ BKM frontier

The previous module closed the only genuinely singular high-radial Duhamel
input:

    |ξ|⁴ Tail(q,ξ) ∈ L²,
    |ξ|⁵ Tail(q,ξ) ∈ L².

The existing continuation reduction already knows how to turn that terminal
half-tail statement into the complete selected Duhamel fourth/fifth radial
`L²` package and then into the BKM continuation theorem.

This file therefore discharges the selected Duhamel tail hypothesis entirely.
The remaining continuation frontier consists only of:

* the late-time zeroth-order velocity `L²` tail;
* the order-energy derivative identities;
* transport/pressure `L²` data;
* the full scalar-energy data.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

noncomputable section

/--
The selected terminal-tail fourth/fifth radial Fourier `L²` input is automatic,
so it can be removed from the H³-path BKM continuation frontier.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_transportPressure_of_fullScalarEnergy
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hTP :
      H3PathEnergyClassProducesTransportPressureMemLp2)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_selectedDuhamelTailFourthFifthRadialL2_of_transportPressure_of_fullScalarEnergy
      hLow
      hDerivative
      h3CanonicalSelectedDuhamelTailFourthFifthRadialRawFourierMemLp2OnRestartRadius
      hTP
      hFull

end

end Euclidean
end Bridge
end PrimeTensor
