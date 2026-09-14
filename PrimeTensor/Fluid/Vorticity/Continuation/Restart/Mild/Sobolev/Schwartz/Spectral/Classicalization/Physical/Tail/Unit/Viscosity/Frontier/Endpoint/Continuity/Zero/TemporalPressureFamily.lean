import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalProjectedRHSHilbertPairing

/-!
# Zeroth-order endpoint continuity: all divergence-free pressure-mass frontier

The endpoint-independent old weak FTC branch has now reduced the quantitative
zeroth-order endpoint problem to one explicit pressure regularity statement.

For a fixed compact smooth divergence-free weak test `φ`, the existing frontier

    H3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassUniformlyBoundedOnElapsed

is enough to justify spacetime Fubini and yields the native Hilbert estimate

    ‖⟪Φ, U(q) - U(0)⟫‖
      ≤
    3 * ‖Φ‖ * h3UnitViscosityZeroRHSBound E * q.

The density step needs that same hypothesis for every divergence-free compact
weak test.  This file names that exact family-level frontier and packages its
two immediate consequences:

* every divergence-free compact weak test has the required endpoint-independent
  temporal product integrability;
* every such test satisfies the quantitative Hilbert weak-increment estimate.

No endpoint `L²` continuity, pressure uniqueness, decay, or harmonic Liouville
statement is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroTemporalPressureFamily
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Family-level form of the sole remaining pressure-mass obstruction in the
endpoint-independent coordinatewise Fubini route. -/
def H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    Prop :=
  ∀ φ : H3WeakTestVector,
    H3WeakTestVectorDivergenceFree φ →
    H3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassUniformlyBoundedOnElapsed
      hNS ht hEnd hTail φ

/-- Under the all-tests pressure-mass frontier, every divergence-free compact
weak test has the endpoint-independent product integrability needed by the old
pointwise temporal FTC, on every shortened elapsed interval. -/
theorem H3PreterminalLoggedVelocityTemporalProductIntegrableTo_of_allDivergenceFreePressureDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
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
    (hq0 : 0 ≤ q)
    (hqtau : q ≤ tau) :
    H3PreterminalLoggedVelocityTemporalProductIntegrableTo
      hNS t q φ := by
  exact
    H3PreterminalLoggedVelocityTemporalProductIntegrableTo_of_pressureDefect
      hNS ht hEnd hE hTail φ hq0 hqtau
      (hPressure φ hφ)

/-- The all-tests pressure-mass frontier gives the native Hilbert weak velocity
increment estimate for every divergence-free compact smooth test. -/
theorem norm_inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementTo_le_of_allDivergenceFreePressureDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (q : Set.Icc (0 : ℝ) tau) :
    ‖inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail q)‖
      ≤
    ((3 * ‖h3WeakTestVectorPhysicalL2Hilbert φ‖)
      *
    h3UnitViscosityZeroRHSBound E)
      *
    (q : ℝ) := by
  exact
    norm_inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementTo_le_of_pressureDefect
      hNS ht htau hEnd hE hTail
      φ hφ q
      (hPressure φ hφ)

/-- Equivalent curried form convenient for the forthcoming closure argument. -/
theorem all_divergenceFree_norm_inner_velocityIncrementTo_le_of_allDivergenceFreePressureDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail)
    (q : Set.Icc (0 : ℝ) tau) :
    ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      ‖inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
            hNS ht htau hEnd hTail q)‖
        ≤
      ((3 * ‖h3WeakTestVectorPhysicalL2Hilbert φ‖)
        *
      h3UnitViscosityZeroRHSBound E)
        *
      (q : ℝ) := by
  intro φ hφ
  exact
    norm_inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementTo_le_of_allDivergenceFreePressureDefect
      hNS ht htau hEnd hE hTail hPressure φ hφ q

end

end Euclidean
end Bridge
end PrimeTensor
