import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Projected.RHS.Weak.Evolution.Old.Joint
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.FTC.Global.Closure

/-!
# Global continuation closure from old temporal joint continuity

The local endpoint-independent chain is now closed:

    old temporal-derivative joint continuity
      -> compact-support local domination
      -> projected-RHS weak evolution
      -> scalar projected-RHS weak FTC.

This file packages that chain only on the canonical H³ tails used by the
continuation argument.

The remaining analytic frontier is therefore one spacetime regularity
statement:

    (t,x) ↦ ∂ₜu_i(t,x)

is jointly continuous on the open preterminal cylinder for every velocity
coordinate, whenever the old solution lies in the retained canonical H³ tail
class.

No endpoint continuity, pressure integrability, temporal product integrability,
or weak-FTC hypothesis remains in the final continuation theorem below.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongOldJointGlobalClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Tail-scoped old temporal-derivative joint-continuity frontier.

This is deliberately scoped to the exact canonical H³ tails consumed by the
continuation argument rather than all admissible preterminal solutions. -/
def H3PreterminalTailUnitViscosityZeroOldTemporalDerivativeJointContinuityFrontier :
    Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous
        u T

/-- Tail-scoped old temporal joint continuity supplies the radius-wide scalar
projected-RHS weak-FTC frontier. -/
theorem h3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier_of_oldTemporalDerivativeJointContinuity
    (hOldJoint :
      H3PreterminalTailUnitViscosityZeroOldTemporalDerivativeJointContinuityFrontier) :
    H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier := by
  intro E hE u T t hNS ht hTail

  have hJoint :
      H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous
        u T :=
    hOldJoint E hE u T t hNS ht hTail

  intro q hqPos hEnd

  exact
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed_of_oldTemporalDerivativeJointlyContinuous
      hNS
      ht
      hqPos
      hEnd
      hE
      hTail
      hJoint

/-- Global continuation closure from old temporal-derivative joint continuity
on canonical H³ tails. -/
theorem h3ControlProducesExtension_of_unitViscosityZeroOldTemporalDerivativeJointContinuityClosed
    (hOldJoint :
      H3PreterminalTailUnitViscosityZeroOldTemporalDerivativeJointContinuityFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityZeroProjectedRHSWeakFTCClosed
      (h3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier_of_oldTemporalDerivativeJointContinuity
        hOldJoint)

/-- A stronger global statement applying to every admissible preterminal
solution immediately gives the tail-scoped frontier. -/
theorem H3PreterminalTailUnitViscosityZeroOldTemporalDerivativeJointContinuityFrontier_of_allAdmissible
    (hAll :
      ∀
        (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
        (T : ℝ),
          LoggedPreterminalNavierStokesAdmissible u T →
          H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous
            u T) :
    H3PreterminalTailUnitViscosityZeroOldTemporalDerivativeJointContinuityFrontier := by
  intro E hE u T t hNS ht hTail
  exact hAll u T hNS

/-- Fully global old temporal joint continuity is consequently sufficient for
the continuation conclusion. -/
theorem h3ControlProducesExtension_of_allAdmissibleOldTemporalDerivativeJointContinuity
    (hAll :
      ∀
        (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
        (T : ℝ),
          LoggedPreterminalNavierStokesAdmissible u T →
          H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous
            u T) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityZeroOldTemporalDerivativeJointContinuityClosed
      (H3PreterminalTailUnitViscosityZeroOldTemporalDerivativeJointContinuityFrontier_of_allAdmissible
        hAll)

end

end Euclidean
end Bridge
end PrimeTensor
