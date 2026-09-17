import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakEnergyDensity

/-!
# Two-time weak evolution for the selected--old energy path

The family-level weak FTC is currently packaged from the common initial time:

    <Phi, D(q)> = integral_0^q <Phi, RDelta(r)> dr.

The partition energy argument needs the corresponding identity between arbitrary
elapsed times `a` and `b`.

No new analysis is required.  Subtract the two initial-time identities and use
Mathlib's interval-integral subtraction law

    integral_0^b f - integral_0^a f = integral_a^b f.

The same file records the result both for the concrete closed-subtype velocity
difference and for its ambient-real extension.

No strong old derivative, endpoint continuity, or vector-valued Bochner FTC is
introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergyIncrement
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Arbitrary two-time weak evolution identity for the concrete selected--old
difference path. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldDifference_sub_eq_projectedRHSDifference_intervalIntegral_of_allPressureDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
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
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (a b : Set.Icc (0 : ℝ) tau) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
            (one_pos : (0 : ℝ) < 1)
            hNS ht hEnd hE hTail b
          -
        h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
            (one_pos : (0 : ℝ) < 1)
            hNS ht hEnd hE hTail a)
      =
    ∫ r in (a : ℝ)..(b : ℝ),
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
          hNS ht hEnd hE hTail htauR r) := by
  let F : ℝ → ℝ :=
    fun r : ℝ =>
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
          hNS ht hEnd hE hTail htauR r)

  have hB :=
    inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldDifference_eq_projectedRHSDifference_intervalIntegral_of_allDivergenceFreePressureDefect
      hNS ht htau hEnd hE hTail htauR hPressure
      φ hφ b

  have hA :=
    inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldDifference_eq_projectedRHSDifference_intervalIntegral_of_allDivergenceFreePressureDefect
      hNS ht htau hEnd hE hTail htauR hPressure
      φ hφ a

  have hIntB :
      IntervalIntegrable
        F
        volume
        (0 : ℝ)
        (b : ℝ) := by
    dsimp only [F]
    exact
      intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldProjectedRHSDifferenceReal_of_allPressureDefect
        hNS ht htau hEnd hE hTail htauR hPressure
        φ hφ b

  have hIntA :
      IntervalIntegrable
        F
        volume
        (0 : ℝ)
        (a : ℝ) := by
    dsimp only [F]
    exact
      intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldProjectedRHSDifferenceReal_of_allPressureDefect
        hNS ht htau hEnd hE hTail htauR hPressure
        φ hφ a

  rw [inner_sub_right]

  change
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail b)
      -
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail a)
      =
    ∫ r in (a : ℝ)..(b : ℝ), F r

  rw [hB, hA]

  exact
    intervalIntegral.integral_interval_sub_left
      hIntB hIntA

/-- Ambient-real version of the arbitrary two-time weak evolution identity. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldDifferenceReal_sub_eq_projectedRHSDifference_intervalIntegral_of_allPressureDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau a b : ℝ}
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
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (ha : a ∈ Set.Icc (0 : ℝ) tau)
    (hb : b ∈ Set.Icc (0 : ℝ) tau) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
            hNS ht hEnd hE hTail b
          -
        h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
            hNS ht hEnd hE hTail a)
      =
    ∫ r in a..b,
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
          hNS ht hEnd hE hTail htauR r) := by
  rw [
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_apply_of_mem
      hNS ht hEnd hE hTail hb,
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_apply_of_mem
      hNS ht hEnd hE hTail ha
  ]

  exact
    inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldDifference_sub_eq_projectedRHSDifference_intervalIntegral_of_allPressureDefect
      hNS ht htau hEnd hE hTail htauR hPressure
      φ hφ ⟨a, ha⟩ ⟨b, hb⟩

end

end Euclidean
end Bridge
end PrimeTensor
