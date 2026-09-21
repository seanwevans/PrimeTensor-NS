import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrder2SelectedReduction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Second.Mixed.Derivative.Absolute.Time

/-!
# Close H³-path order-two mixed commutation from the selected restart

The selected real order-two mixed derivative has now been proved in absolute
time.  Its statement is exactly the analytic hypothesis isolated by
`H3PathOrder2SelectedReduction`.

This file therefore performs two final packaging steps:

* specialize the absolute-time selected theorem to unit viscosity and the
  canonical decoder anchor state, producing
  `H3CanonicalSelectedOrder2MixedTimeCommutationOnRestartRadius`;
* feed that result into the already-proved selected/old transport theorem,
  closing `H3PathEnergyClassProducesOrder2MixedTimeCommutationOnTail`.

No new estimate, differentiation, overlap argument, or PDE identity is added.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory
open scoped Topology

noncomputable section

noncomputable local instance axisFintypeH3PathOrder2SelectedClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical selected restart satisfies the exact order-two mixed-time
commutation proposition isolated by the H³ path reduction. -/
theorem h3CanonicalSelectedOrder2MixedTimeCommutationOnRestartRadius :
    H3CanonicalSelectedOrder2MixedTimeCommutationOnRestartRadius := by
  intro E u T t₀ hNS ht₀ hE hTail
  intro s hs
  intro j i k x

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_spatial_d_two_hasDerivAt_absoluteTime
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState
        hNS ht₀ hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail)
      hs
      x i k j

/-- The order-two mixed-time commutation required by the old H³ path now
follows from the closed selected restart theorem and the existing canonical
selected/old overlap transport. -/
theorem h3PathEnergyClassProducesOrder2MixedTimeCommutationOnTail :
    H3PathEnergyClassProducesOrder2MixedTimeCommutationOnTail := by
  exact
    h3PathEnergyClassProducesOrder2MixedTimeCommutationOnTail_of_selected
      h3CanonicalSelectedOrder2MixedTimeCommutationOnRestartRadius

end

end Euclidean
end Bridge
end PrimeTensor
