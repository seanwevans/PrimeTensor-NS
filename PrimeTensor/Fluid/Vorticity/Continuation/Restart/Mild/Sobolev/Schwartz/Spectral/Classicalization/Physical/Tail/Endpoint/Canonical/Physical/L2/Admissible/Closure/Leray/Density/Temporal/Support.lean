import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Reduction

/-!
# Classicalization: reduce temporal domination to a supportwise uniform bound

`Temporal.Reduction` isolated the sole remaining endpoint analytic frontier:

    every compact smooth divergence-free weak test
      satisfies temporal local domination.

The domination predicate asks for an integrable spatial majorant of

    |φᵢ(x) ∂ₜWᵢ(r,x)|

uniformly for `r` in a neighborhood of a fixed strict elapsed time.

Because each weak test component is compactly supported, it is enough to bound
the temporal derivative itself by a single scalar constant on the support of
that component.  The majorant can then be chosen as

    x ↦ C * ‖φᵢ(x)‖,

which is integrable by compact support.

This file formalizes exactly that reduction.  It does not yet prove the
supportwise temporal-derivative bound; that is the next genuine regularity
checkpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityTemporalSupport
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Supportwise scalar bound at one strict elapsed time -/

/-- For one weak test and one strict elapsed time, every coordinate temporal
derivative is uniformly bounded on the nonzero support of that test coordinate,
through one common time neighborhood for that coordinate. -/
def H3PreterminalTailCanonicalWeakTemporalDerivativeLocallyBoundedOnSupportAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (s : ℝ)
    (φ : H3WeakTestVector) : Prop :=
  ∀ i : Fin 3,
    ∃ S : Set ℝ,
      S ∈ 𝓝 s
      ∧
      S ⊆ Set.Ioo (0 : ℝ) tau
      ∧
      ∃ C : ℝ,
        0 ≤ C
        ∧
        ∀ x : Point3,
          φ i x ≠ 0 →
          ∀ r : ℝ,
            r ∈ S →
            ‖temporal.d
                (fun q : ℝ =>
                  (h3SpectralRealVelocityOfPath
                    (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                      hNS ht htau.le hEnd hE hTail hEndpoint)
                    q x).component
                      (h3AxisOfFin3 i))
                r‖
              ≤
            C

/-! ## Supportwise bound gives the exact local domination predicate -/

/-- A scalar uniform bound for the temporal derivative on the compact support
of each test coordinate yields the integrable majorant required by the weak
FTC. -/
theorem H3PreterminalTailCanonicalWeakTemporalLocalDominationAt_of_derivativeLocallyBoundedOnSupport
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (s : ℝ)
    (φ : H3WeakTestVector)
    (hBound :
      H3PreterminalTailCanonicalWeakTemporalDerivativeLocallyBoundedOnSupportAt
        hNS ht htau hEnd hE hTail hEndpoint s φ) :
    H3PreterminalTailCanonicalWeakTemporalLocalDominationAt
      hNS ht htau hEnd hE hTail hEndpoint s φ := by
  intro i

  rcases hBound i with
    ⟨S, hS, hSsub, C, hC0, hC⟩

  refine ⟨S, hS, hSsub, ?_⟩

  let bound : Point3 → ℝ :=
    fun x => C * ‖φ i x‖

  have hNormIntegrable :
      Integrable
        (fun x : Point3 => ‖φ i x‖)
        (volume : Measure Point3) := by
    exact
      (φ i).continuous.norm.integrable_of_hasCompactSupport
        (φ i).hasCompactSupport.norm

  have hBoundIntegrable :
      Integrable bound
        (volume : Measure Point3) := by
    dsimp only [bound]
    exact Integrable.const_mul hNormIntegrable C

  refine ⟨bound, hBoundIntegrable, ?_⟩

  filter_upwards with x

  intro r hr

  by_cases hx : φ i x = 0

  · change
      ‖(φ i x) *
          temporal.d
            (fun q : ℝ =>
              (h3SpectralRealVelocityOfPath
                (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                  hNS ht htau.le hEnd hE hTail hEndpoint)
                q x).component
                  (h3AxisOfFin3 i))
            r‖
        ≤
      bound x

    dsimp only [bound]
    rw [hx]
    norm_num

  · have hDerivative :
        ‖temporal.d
            (fun q : ℝ =>
              (h3SpectralRealVelocityOfPath
                (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                  hNS ht htau.le hEnd hE hTail hEndpoint)
                q x).component
                  (h3AxisOfFin3 i))
            r‖
          ≤
        C :=
      hC x hx r hr

    change
      ‖(φ i x) *
          temporal.d
            (fun q : ℝ =>
              (h3SpectralRealVelocityOfPath
                (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                  hNS ht htau.le hEnd hE hTail hEndpoint)
                q x).component
                  (h3AxisOfFin3 i))
            r‖
        ≤
      bound x

    dsimp only [bound]

    calc
      ‖(φ i x) *
          temporal.d
            (fun q : ℝ =>
              (h3SpectralRealVelocityOfPath
                (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                  hNS ht htau.le hEnd hE hTail hEndpoint)
                q x).component
                  (h3AxisOfFin3 i))
            r‖
          =
        ‖φ i x‖ *
          ‖temporal.d
            (fun q : ℝ =>
              (h3SpectralRealVelocityOfPath
                (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                  hNS ht htau.le hEnd hE hTail hEndpoint)
                q x).component
                  (h3AxisOfFin3 i))
            r‖ := by
              exact norm_mul _ _
      _ ≤ ‖φ i x‖ * C :=
        mul_le_mul_of_nonneg_left
          hDerivative
          (norm_nonneg _)
      _ = C * ‖φ i x‖ := by
        rw [mul_comm]

/-! ## Global generatorwise support-bound frontier -/

/-- Exact remaining supportwise regularity frontier: every compact smooth
divergence-free weak test has locally uniformly bounded temporal derivative on
the support of each of its coordinates, at every strict elapsed time. -/
def H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporalDerivativeLocallyBoundedOnSupport
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail) : Prop :=
  ∀ φ : H3WeakTestVector,
    H3WeakTestVectorDivergenceFree φ →
    ∀ s : ℝ,
      s ∈ Set.Ioo (0 : ℝ) tau →
      H3PreterminalTailCanonicalWeakTemporalDerivativeLocallyBoundedOnSupportAt
        hNS ht htau hEnd hE hTail hEndpoint s φ

/-- The supportwise temporal-derivative bound closes the generatorwise local
domination frontier isolated in `Temporal.Reduction`. -/
theorem H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporallyLocallyDominated_of_derivativeLocallyBoundedOnSupport
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hBound :
      H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporalDerivativeLocallyBoundedOnSupport
        hNS ht htau hEnd hE hTail hEndpoint) :
    H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporallyLocallyDominated
      hNS ht htau hEnd hE hTail hEndpoint := by
  intro φ hDiv
  intro s hs

  exact
    H3PreterminalTailCanonicalWeakTemporalLocalDominationAt_of_derivativeLocallyBoundedOnSupport
      hNS ht htau hEnd hE hTail hEndpoint s φ
      (hBound φ hDiv s hs)

/-- Consequently, the supportwise temporal-derivative bound alone is enough to
close the physical `L²` vector evolution identity. -/
theorem h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_derivativeLocallyBoundedOnSupport
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hBound :
      H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporalDerivativeLocallyBoundedOnSupport
        hNS ht htau hEnd hE hTail hEndpoint) :
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert
        hNS ht htau hEnd hTail
      =
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbert
      hNS ht htau hEnd hE hTail hEndpoint := by
  apply
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_all_divergenceFreeWeakTests_temporallyLocallyDominated
      hNS ht htau hEnd hE hTail hEndpoint

  exact
    H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporallyLocallyDominated_of_derivativeLocallyBoundedOnSupport
      hNS ht htau hEnd hE hTail hEndpoint hBound

end

end Euclidean
end Bridge
end PrimeTensor
