import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakRHSDifferenceFTC
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalPressureFamily

/-!
# Family-level selected--old weak RHS-difference FTC

The single-integrand selected--old weak FTC currently asks, for each individual
compact divergence-free test `φ`, for the old endpoint-independent temporal
product-integrability input.

The zeroth-order endpoint branch already packages the exact uniform hypothesis
needed to discharge that test-by-test assumption:

    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed.

Under this family-level pressure frontier, every compact smooth
divergence-free weak test has the required product integrability on every
shortened elapsed interval.

This file therefore removes the final test-local temporal hypothesis from the
selected--old weak evolution identity.  What remains is a statement uniform in
all divergence-free compact tests:

    <Φ, D(q)> = ∫₀^q <Φ, RΔ(r)> dr.

That is the form needed by the closed-span / weak-determining layer.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakRHSDifferencePressureFamily
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Under the family-level pressure frontier, the old projected-RHS weak
pairing is interval-integrable for every divergence-free compact test and every
shortened elapsed interval. -/
theorem intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_oldProjectedRHSReal_of_allDivergenceFreePressureDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (q : Set.Icc (0 : ℝ) tau) :
    IntervalIntegrable
      (fun r : ℝ =>
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r))
      volume
      (0 : ℝ)
      (q : ℝ) := by
  exact
    intervalIntegrable_inner_h3WeakTestVectorPhysicalL2Hilbert_oldProjectedRHSReal_of_productIntegrable
      hNS ht hEnd hTail φ hφ q
      (H3PreterminalLoggedVelocityTemporalProductIntegrableTo_of_allDivergenceFreePressureDefect
        hNS ht hEnd hE hTail hPressure
        φ hφ q.property.1 q.property.2)

/-- Under the family-level pressure frontier, every divergence-free compact
weak test sees the selected--old velocity difference as the time integral of
the single selected-minus-old projected-RHS pairing. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldDifference_eq_projectedRHSDifference_intervalIntegral_of_allDivergenceFreePressureDefect
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
    (q : Set.Icc (0 : ℝ) tau) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q)
      =
    ∫ r in (0 : ℝ)..(q : ℝ),
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
          hNS ht hEnd hE hTail htauR r) := by
  exact
    inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldDifference_eq_projectedRHSDifference_intervalIntegral_of_productIntegrable
      hNS ht htau hEnd hE hTail htauR
      φ hφ q
      (H3PreterminalLoggedVelocityTemporalProductIntegrableTo_of_allDivergenceFreePressureDefect
        hNS ht hEnd hE hTail hPressure
        φ hφ q.property.1 q.property.2)

/-- Curried form convenient for topological closure and weak-determining
arguments. -/
theorem all_divergenceFree_inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldDifference_eq_projectedRHSDifference_intervalIntegral_of_allPressureDefect
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
    (q : Set.Icc (0 : ℝ) tau) :
    ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
            (one_pos : (0 : ℝ) < 1)
            hNS ht hEnd hE hTail q)
        =
      ∫ r in (0 : ℝ)..(q : ℝ),
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
            hNS ht hEnd hE hTail htauR r) := by
  intro φ hφ

  exact
    inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldDifference_eq_projectedRHSDifference_intervalIntegral_of_allDivergenceFreePressureDefect
      hNS ht htau hEnd hE hTail htauR hPressure φ hφ q

end

end Euclidean
end Bridge
end PrimeTensor
