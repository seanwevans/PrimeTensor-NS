import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakEnergyUniformLimitN

/-!
# Remove the weak self-test approximation tolerance

After removing the uniform mesh parameter, the selected--old difference obeys

    ‖D(q)‖²
      ≤ 6 G(E) ∫₀^q ‖D(r)‖² dr
        + 24 ε C(E) q

for every `ε > 0`.

Apply this estimate to the positive sequence `εₙ = 1/(n+1)`.  The residual
term tends to zero, so the order-closed limit theorem gives the exact
Grönwall-ready inequality

    ‖D(q)‖²
      ≤ 6 G(E) ∫₀^q ‖D(r)‖² dr.

No differentiability of the old branch is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergyEpsilonLimit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact selected--old relative-energy integral inequality after both the mesh
and weak-test approximation errors have been removed. -/
theorem norm_sq_selectedOldDifferenceReal_le_energyIntegral
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
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
    (hq : q ∈ Set.Icc (0 : ℝ) tau) :
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
        hNS ht hEnd hE hTail q‖ ^ 2
      ≤
    6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
      (∫ r in (0 : ℝ)..q,
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail r‖ ^ 2) := by
  let A : ℝ :=
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
        hNS ht hEnd hE hTail q‖ ^ 2

  let M : ℝ :=
    6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
      (∫ r in (0 : ℝ)..q,
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail r‖ ^ 2)

  let K : ℝ :=
    24 * h3UnitViscosityZeroRHSBound E * q

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
          K * ((1 : ℝ) / (((n + 1 : ℕ) : ℝ))))
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

    simpa only [mul_zero] using hMul

  have hRHS :
      Tendsto
        (fun n : ℕ =>
          M + K * ((1 : ℝ) / (((n + 1 : ℕ) : ℝ))))
        atTop
        (𝓝 M) := by
    have hConst :
        Tendsto
          (fun _n : ℕ => M)
          atTop
          (𝓝 M) :=
      tendsto_const_nhds

    simpa only [add_zero] using
      hConst.add hK

  have hBound :
      ∀ᶠ n : ℕ in atTop,
        A
          ≤
        M + K * ((1 : ℝ) / (((n + 1 : ℕ) : ℝ))) := by
    filter_upwards [] with n

    have hεn :
        0 <
          (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) := by
      positivity

    have hApprox :=
      norm_sq_selectedOldDifferenceReal_le_energyIntegral_add_epsilonError
        hNS ht htau hEnd hE hTail htauR hPressure
        hq hεn

    dsimp only [A, M, K]

    calc
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail q‖ ^ 2
          ≤
        6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
            (∫ r in (0 : ℝ)..q,
              ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                hNS ht hEnd hE hTail r‖ ^ 2)
          +
        24 *
            ((1 : ℝ) / (((n + 1 : ℕ) : ℝ))) *
            h3UnitViscosityZeroRHSBound E * q := hApprox
      _ =
        6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
            (∫ r in (0 : ℝ)..q,
              ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                hNS ht hEnd hE hTail r‖ ^ 2)
          +
        (24 * h3UnitViscosityZeroRHSBound E * q) *
          ((1 : ℝ) / (((n + 1 : ℕ) : ℝ))) := by
            ring

  have hLimit :
      A ≤ M :=
    ge_of_tendsto hRHS hBound

  simpa only [A, M] using hLimit

end

end Euclidean
end Bridge
end PrimeTensor
