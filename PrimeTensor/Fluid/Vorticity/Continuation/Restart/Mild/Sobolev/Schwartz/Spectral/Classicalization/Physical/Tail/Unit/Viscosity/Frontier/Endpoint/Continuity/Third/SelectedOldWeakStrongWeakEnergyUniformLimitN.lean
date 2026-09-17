import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakEnergyUniformCollapse

/-!
# Remove the uniform mesh parameter

The preceding finite-mesh estimate is

    ‖D(q)‖²
      ≤ 6 G(E) ∫₀^q ‖D(r)‖² dr
        + 24 ε C(E) q
        + 108 C(E)² q² / n.

For fixed positive `ε`, apply it with `n + 1`.  The final term tends to zero,
and `le_of_tendsto` therefore removes the mesh parameter without changing the
other terms.

No `ε → 0` passage is performed in this file.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergyUniformLimitN
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The selected--old weak-energy inequality after removing the uniform mesh
parameter, but before removing the positive approximation tolerance. -/
theorem norm_sq_selectedOldDifferenceReal_le_energyIntegral_add_epsilonError
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q ε : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail)
    (hq : q ∈ Set.Icc (0 : ℝ) tau)
    (hε : 0 < ε) :
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
        hNS ht hEnd hE hTail q‖ ^ 2
      ≤
    6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
      (∫ r in (0 : ℝ)..q,
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail r‖ ^ 2)
      +
    24 * ε * h3UnitViscosityZeroRHSBound E * q := by
  let A : ℝ :=
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
        hNS ht hEnd hE hTail q‖ ^ 2

  let M : ℝ :=
    6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
      (∫ r in (0 : ℝ)..q,
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail r‖ ^ 2)
      +
    24 * ε * h3UnitViscosityZeroRHSBound E * q

  let K : ℝ :=
    108 * (h3UnitViscosityZeroRHSBound E) ^ 2 * q ^ 2

  have hInv :
      Tendsto
        (fun n : ℕ =>
          (1 : ℝ) / (((n + 1 : ℕ) : ℝ)))
        atTop
        (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat

  have hK :
      Tendsto
        (fun n : ℕ =>
          K / (((n + 1 : ℕ) : ℝ)))
        atTop
        (𝓝 0) := by
    have hConst :
        Tendsto
          (fun _n : ℕ => K)
          atTop
          (𝓝 K) :=
      tendsto_const_nhds

    have hMul :=
      hConst.mul hInv

    simpa only [div_eq_mul_inv, one_div, one_mul, mul_zero] using hMul

  have hRHS :
      Tendsto
        (fun n : ℕ =>
          M + K / (((n + 1 : ℕ) : ℝ)))
        atTop
        (𝓝 M) := by
    simpa only [add_zero] using
      tendsto_const_nhds.add hK

  have hBound :
      ∀ᶠ n : ℕ in atTop,
        A
          ≤
        M + K / (((n + 1 : ℕ) : ℝ)) := by
    filter_upwards [] with n

    have hFinite :=
      norm_sq_selectedOldDifferenceReal_le_energyIntegral_add_uniformErrors
        hNS ht htau hEnd hE hTail htauR hPressure
        hq (n + 1) (Nat.succ_pos n) hε

    dsimp only [A, M, K]

    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hFinite

  have hLimit :
      A ≤ M :=
    ge_of_tendsto hRHS hBound

  simpa only [A, M] using hLimit

end

end Euclidean
end Bridge
end PrimeTensor
