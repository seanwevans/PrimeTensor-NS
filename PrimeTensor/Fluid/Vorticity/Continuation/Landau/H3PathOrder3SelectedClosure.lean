import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrder3SelectedReduction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Third.Mixed.Derivative.Absolute.Time

/-!
# Close H³-path order-three mixed commutation from the selected restart

The selected real order-three mixed derivative has now been proved in absolute
time.  Its statement is exactly the analytic hypothesis isolated by
`H3PathOrder3SelectedReduction`.

This file performs the two final packaging steps:

* specialize the absolute-time selected theorem to unit viscosity and the
  canonical decoder anchor state, producing
  `H3CanonicalSelectedOrder3MixedTimeCommutationOnRestartRadius`;
* feed that result into the already-proved selected/old transport theorem,
  closing `H3PathEnergyClassProducesOrder3MixedTimeCommutationOnTail`.

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

noncomputable local instance axisFintypeH3PathOrder3SelectedClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical selected restart satisfies the exact order-three mixed-time
commutation proposition isolated by the H³ path reduction. -/
theorem h3CanonicalSelectedOrder3MixedTimeCommutationOnRestartRadius :
    H3CanonicalSelectedOrder3MixedTimeCommutationOnRestartRadius := by
  intro E u T t₀ hNS ht₀ hE hTail
  intro s hs
  intro j i k l x

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_spatial_d_three_hasDerivAt_absoluteTime
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState
        hNS ht₀ hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail)
      hs
      x i k l j

/-- The order-three mixed-time commutation required by the old H³ path now
follows from the closed selected restart theorem and the existing canonical
selected/old overlap transport. -/
theorem h3PathEnergyClassProducesOrder3MixedTimeCommutationOnTail :
    H3PathEnergyClassProducesOrder3MixedTimeCommutationOnTail := by
  exact
    h3PathEnergyClassProducesOrder3MixedTimeCommutationOnTail_of_selected
      h3CanonicalSelectedOrder3MixedTimeCommutationOnRestartRadius

end

end Euclidean
end Bridge
end PrimeTensor
