import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongEnergyReduction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongTransportPairingBound

/-!
# Selected--old projected RHS energy bound

The previous two checkpoints now meet exactly:

* diffusion reduction:
    `2 ⟪D, RΔ⟫ ≤ -2 ⟪D, NΔ⟫`;
* weak--strong transport estimate:
    `-2 ⟪D, NΔ⟫ ≤ 6 B ‖D‖²`.

Therefore the full selected-minus-old unit-viscosity projected RHS satisfies

    2 ⟪D, RΔ⟫ ≤ 6 B ‖D‖².

This is the precise differential Grönwall estimate needed once the concrete
branch derivative difference is identified with `RΔ`.

No additional PDE analysis occurs in this file.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongProjectedRHSEnergyBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Full projected-RHS relative-energy estimate:

    2 ⟪D, RΔ⟫ ≤ 6 B ‖D‖².

The factor `6` is inherited unchanged from the weak--strong transport bound;
the diffusion contribution has favorable sign and is simply discarded. -/
theorem two_inner_selectedOldUnitProjectedRHSDifference_le_six_mul_norm_sq
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
    (q : Set.Icc (0 : ℝ) tau)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hGradient :
      ∀
        (x : Point3)
        (j i : PrimeTensor.Axis Depth.three),
        abs
          (spatial3.d
            i
            (fun y =>
              ((h3PreterminalSelectedWeakStrongVelocity
                (one_pos : (0 : ℝ) < 1)
                hNS ht hE hTail)
                (q : ℝ) y).component j)
            x)
          ≤ B)
    (hInteraction :
      MeasureTheory.Integrable
        (h3PreterminalSelectedOldWeakStrongAbsInteractionDensity
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail (q : ℝ))
        (volume : Measure Point3))
    (hIBP :
      H3PreterminalSelectedOldWeakStrongTransportIntegrationByPartsAt
        hNS ht hEnd hE hTail q) :
    2 *
      inner ℝ
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q)
        (h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
          hNS ht hEnd hE hTail htauR q)
      ≤
    6 * B *
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q‖ ^ 2 := by
  have hReduction :=
    h3PreterminalSelectedOldUnitProjectedRHS_two_inner_le_neg_two_leray
      hNS ht hEnd hE hTail htauR q

  have hTransport :=
    neg_two_inner_selectedOldUnitLerayForcingDifference_le_six_mul_norm_sq
      hNS ht hEnd hE hTail htauR q
      B hB hGradient hInteraction hIBP

  exact hReduction.trans hTransport

end

end Euclidean
end Bridge
end PrimeTensor
