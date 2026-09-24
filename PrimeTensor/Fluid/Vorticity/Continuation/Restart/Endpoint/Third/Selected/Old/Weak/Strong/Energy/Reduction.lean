import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Diffusion.Sign

/-!
# Selected--old weak--strong energy reduction

The concrete selected-minus-old projected RHS already splits as

    RΔ = LΔ - NΔ,

and the preceding diffusion-sign file proves

    ⟪D, LΔ⟫ ≤ 0

for the concrete selected-minus-old physical velocity difference `D`.

This file performs only the Hilbert-space step that discards that favorable
linear term.  The relative-energy pairing is therefore reduced to the single
nonlinear/Leray pairing

    ⟪D, RΔ⟫ ≤ -⟪D, NΔ⟫,

and, in the normalization used by the squared-norm derivative,

    2 ⟪D, RΔ⟫ ≤ -2 ⟪D, NΔ⟫.

No temporal derivative, endpoint continuity, or nonlinear transport estimate
is introduced here.  The next analytic task is exactly the weak--strong
transport cancellation and bound.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongEnergyReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The favorable concrete diffusion term may be discarded from the
selected-minus-old projected-RHS pairing. -/
theorem h3PreterminalSelectedOldUnitProjectedRHS_inner_le_neg_leray
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
    inner ℝ
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q)
        (h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
          hNS ht hEnd hE hTail htauR q)
      ≤
    - inner ℝ
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q)
        (h3PreterminalSelectedOldUnitLerayForcingDifferenceOnElapsed
          hNS ht hEnd hE hTail htauR q) := by
  rw [
    inner_h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed_eq
      hNS ht hEnd hE hTail htauR q
  ]

  have hDiffusion :=
    h3PreterminalSelectedOldUnitDiffusion_inner_nonpos
      hNS ht hEnd hE hTail htauR q

  linarith

/-- Squared-norm normalization of the same reduction.  This is the exact form
consumed by the relative-energy/Gronwall calculation. -/
theorem h3PreterminalSelectedOldUnitProjectedRHS_two_inner_le_neg_two_leray
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
    2 * inner ℝ
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q)
        (h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
          hNS ht hEnd hE hTail htauR q)
      ≤
    -2 * inner ℝ
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q)
        (h3PreterminalSelectedOldUnitLerayForcingDifferenceOnElapsed
          hNS ht hEnd hE hTail htauR q) := by
  have h :=
    h3PreterminalSelectedOldUnitProjectedRHS_inner_le_neg_leray
      hNS ht hEnd hE hTail htauR q

  linarith

end

end Euclidean
end Bridge
end PrimeTensor
