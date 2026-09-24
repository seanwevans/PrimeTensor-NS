import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Selected.Flux.Automatic
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Energy.Reduction

/-!
# Automatic selected--old projected-RHS energy estimate

The spatial weak--strong argument is now closed without an external transport
hypothesis.

The favorable diffusion reduction gives

    2 ⟪D, RΔ⟫ ≤ -2 ⟪D, NΔ⟫,

while automatic selected scalar-flux cancellation gives

    -2 ⟪D, NΔ⟫ ≤ 6 B ‖D‖².

This file records their direct composition:

    2 ⟪D, RΔ⟫ ≤ 6 B ‖D‖²,

with

    B = C₁ (2E).

No selected-gradient datum, interaction-integrability datum, old-transport
integration-by-parts datum, or selected-flux datum remains in the theorem
statement.

This estimate is deliberately independent of how the temporal argument is
closed.  In particular it can be consumed by the endpoint-independent weak
FTC route rather than forcing the final uniqueness proof through a strong old
`L²` derivative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

attribute [local instance]
  point3MeasureSpaceH3SelectedOldWeakStrongTransportIntegralBound

noncomputable local instance axisFintypeH3SelectedOldWeakStrongProjectedRHSEnergyAutomatic
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Fully automatic weak--strong projected-RHS quadratic estimate. -/
theorem two_inner_selectedOldUnitProjectedRHSDifference_le_six_mul_norm_sq_alternate_auto
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau) :
    2 *
      inner ℝ
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q)
        (h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
          hNS ht hEnd hE hTail htauR q)
      ≤
    6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q‖ ^ 2 := by
  have hReduction :
      2 *
        inner ℝ
          (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
            (one_pos : (0 : ℝ) < 1)
            hNS ht hEnd hE hTail q)
          (h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
            hNS ht hEnd hE hTail htauR q)
        ≤
      -2 *
        inner ℝ
          (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
            (one_pos : (0 : ℝ) < 1)
            hNS ht hEnd hE hTail q)
          (h3PreterminalSelectedOldUnitLerayForcingDifferenceOnElapsed
            hNS ht hEnd hE hTail htauR q) :=
    h3PreterminalSelectedOldUnitProjectedRHS_two_inner_le_neg_two_leray
      hNS ht hEnd hE hTail htauR q

  have hNonlinear :
      -2 *
        inner ℝ
          (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
            (one_pos : (0 : ℝ) < 1)
            hNS ht hEnd hE hTail q)
          (h3PreterminalSelectedOldUnitLerayForcingDifferenceOnElapsed
            hNS ht hEnd hE hTail htauR q)
        ≤
      6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
            (one_pos : (0 : ℝ) < 1)
            hNS ht hEnd hE hTail q‖ ^ 2 :=
    neg_two_inner_selectedOldUnitLerayForcingDifference_le_six_mul_norm_sq_alternate_auto
      hNS ht hEnd hE hTail htauR q

  exact hReduction.trans hNonlinear

end

end Euclidean
end Bridge
end PrimeTensor
