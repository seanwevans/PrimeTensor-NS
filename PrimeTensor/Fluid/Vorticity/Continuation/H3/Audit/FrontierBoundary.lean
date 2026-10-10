import PrimeTensor.Fluid.Vorticity.Continuation.H3.Vorticity.Apriori.Frontier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Restart.Direct
import PrimeTensor.Fluid.Vorticity.Continuation.Frontier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Strong.H3.Endpoint.Path

/-!
# H³ frontier boundaries: closed restart, missing estimate, and endpoint literature

This module deliberately does NOT claim Navier--Stokes global regularity.
It records three distinct, UNPROVED analytic/translation interfaces:

* `H3AuditUniformTerminalTailControl`: an a-priori uniform H³ terminal bound
  for *every* admissible H³ path;
* `H3AuditSeededStrongPathBridge`: the additional bridge from the seeded
  preterminal PDE interface into the stronger H³ path interface;
* `H3AuditOnePhysicalEndpointLiteratureBridge`: the proposed translation from
  one physical-vorticity-component strong H³ endpoint hypothesis into an
  established one-velocity-component regularity criterion.

The implications below are kernel-checkable logical reductions using already
closed restart theorems. They do not discharge any of these three hypotheses.
Clay's Form A additionally requires a separately formalized class of smooth,
rapidly decaying divergence-free initial data, local existence from those data,
iteration/global assembly, initial-value agreement, and global finite energy.
This module does not define `ClayFormA` because those bridges are not in place.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

noncomputable section

/-- Missing universal bound on the full preterminal H³ path class.
Unlike a conditional terminal clock, this is a genuinely global a-priori
assertion; it is NOT proved here. -/
def H3AuditUniformTerminalTailControl : Prop :=
  ∀ (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (T : ℝ),
    LoggedPreterminalH3PathAdmissible u T →
    TerminalTailH3Control u T

/-- Separate missing eligibility bridge for seeded preterminal solutions.
This implication is not provided by a single H³ seed without further
regularity/propagation arguments. It is NOT proved here. -/
def H3AuditSeededStrongPathBridge : Prop :=
  ∀ (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (T : ℝ),
    LoggedPreterminalNavierStokesAdmissible u T →
    PreterminalH3Seed u T →
    LoggedPreterminalH3PathAdmissible u T

/-- A literature-transfer frontier, not a formalization of the cited theorem.
The physical endpoint predicate supplies two transverse velocity components
with pathwise strong spectral H³ limits. To use the published one-component
criterion one must still prove a physical homogeneous Sobolev norm bridge,
finite-time integration, and compatibility with its local strong-solution
class. NONE of these bridges is asserted by this definition. -/
def H3AuditOnePhysicalEndpointLiteratureBridge : Prop :=
  ∀ (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
      (T a : ℝ)
      (hH3 : LoggedPreterminalH3PathAdmissible u T)
      (hClass : PreterminalH3EnergyClass u a T)
      (i : Fin 3),
    H3TerminalActualVorticityStrongH3EndpointPath hH3 i →
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T

/-- The only missing hypothesis in the path-specific restart route is the
UNIVERSAL bound. The pathwise restart theorem itself is already closed. -/
theorem h3Audit_allH3PathsExtend_of_uniformTailControl
    (hUniform : H3AuditUniformTerminalTailControl) :
    EveryH3PathPreterminalNavierStokesSolutionExtends := by
  intro u T hH3
  exact h3PathH3ControlProducesExtension
    u T hH3 (hUniform u T hH3)

/-- An H³-path continuation statement can be lifted to the *seeded* PDE
interface only when the seeded-to-path eligibility bridge is also provided.
This is NOT a reduction to Clay Form A. -/
theorem h3Audit_everySeededExtends_of_H3Extension_and_pathBridge
    (hAllH3 : EveryH3PathPreterminalNavierStokesSolutionExtends)
    (hPath : H3AuditSeededStrongPathBridge) :
    EverySeededPreterminalNavierStokesSolutionExtends := by
  intro u T hNS hSeed
  exact hAllH3 u T (hPath u T hNS hSeed)

/-- Explicit two-premise seeded continuation factorization. Neither
universal H³ tail control nor the path-eligibility bridge is proved. -/
theorem h3Audit_everySeededExtends_of_uniformTailControl_and_pathBridge
    (hUniform : H3AuditUniformTerminalTailControl)
    (hPath : H3AuditSeededStrongPathBridge) :
    EverySeededPreterminalNavierStokesSolutionExtends := by
  exact h3Audit_everySeededExtends_of_H3Extension_and_pathBridge
    (h3Audit_allH3PathsExtend_of_uniformTailControl hUniform) hPath

/-- If the ONE-component literature bridge were formally established,
nonextension would rule out even one `hPhysical` endpoint. This differs
from the EXISTING theorem that two distinct physical endpoint predicates
force continuation. The bridge is currently an explicit hypothesis. -/
theorem h3Audit_noExtension_excludes_onePhysicalEndpoint_of_literatureBridge
    (hBridge : H3AuditOnePhysicalEndpointLiteratureBridge)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T) :
    ∀ i : Fin 3,
      ¬ H3TerminalActualVorticityStrongH3EndpointPath hH3 i := by
  intro i hPhysical
  exact hNoExtension (hBridge u T a hH3 hClass i hPhysical)

/-- Failure of the universal H³ a-priori estimate is necessary if an
admissible H³ path genuinely fails to continue. This does not construct
such a path. -/
theorem h3Audit_noExtension_excludes_terminalTailControl
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T) :
    ¬ TerminalTailH3Control u T := by
  intro hTail
  exact hNoExtension
    (h3PathH3ControlProducesExtension u T hH3 hTail)

end
end Euclidean
end Bridge
end PrimeTensor
