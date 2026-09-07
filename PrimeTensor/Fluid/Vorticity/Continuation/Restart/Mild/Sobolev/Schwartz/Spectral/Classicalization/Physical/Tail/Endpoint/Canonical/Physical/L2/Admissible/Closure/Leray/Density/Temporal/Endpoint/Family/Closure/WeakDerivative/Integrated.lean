import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.WeakDerivative

/-!
# Reduce the scalar weak-derivative frontier to integrated weak momentum

The scalar weak-derivative route no longer needs coordinatewise spacetime
Fubini.  Its remaining input can be weakened once more.

For one compact smooth divergence-free weak test `φ`, write

    Pφ(q) = <φ, W(q)>
    Gφ(q) = <φ, projectedRHS(q)>.

Both scalar functions are already continuous on the closed elapsed interval.

It is therefore enough to prove the integrated weak momentum identity

    Pφ(q) - Pφ(0) = ∫₀^q Gφ(s) ds

for every `q ∈ [0,tau]`.

Indeed, locally on `(0,tau)` the right-hand side is an ordinary differentiable
interval integral with derivative `Gφ(q)`.  Since the integrated identity makes
`Pφ` locally equal to that primitive, the scalar `HasDerivAt` frontier follows.

This is the natural target for a distributional/time-integrated proof of the
old preterminal momentum equation: no joint continuity of `∂ₜu` and no
differentiation under the spatial integral is built into the hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

/-- Integrated scalar weak momentum for every divergence-free compact smooth
test and every shortened elapsed target. -/
def H3PreterminalTailCanonicalAllDivergenceFreeWeakVelocityPairingsSatisfyIntegratedProjectedRHSOnElapsed
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
    ∀ q : Set.Icc (0 : ℝ) tau,
      h3PreterminalTailCanonicalWeakVelocityPairingReal
          hNS ht htau hEnd hE hTail hEndpoint φ (q : ℝ)
        -
      h3PreterminalTailCanonicalWeakVelocityPairingReal
          hNS ht htau hEnd hE hTail hEndpoint φ 0
        =
      ∫ s in (0 : ℝ)..(q : ℝ),
        h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
          hNS ht htau hEnd hE hTail hEndpoint φ s

/-- Integrated weak momentum implies the exact scalar weak-pairing derivative
frontier used by the endpoint physical `L²` closure. -/
theorem H3PreterminalTailCanonicalAllDivergenceFreeWeakVelocityPairingsHaveProjectedRHSDerivativeOnElapsed_of_integratedProjectedRHS
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
    (hIntegrated :
      H3PreterminalTailCanonicalAllDivergenceFreeWeakVelocityPairingsSatisfyIntegratedProjectedRHSOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint) :
    H3PreterminalTailCanonicalAllDivergenceFreeWeakVelocityPairingsHaveProjectedRHSDerivativeOnElapsed
      hNS ht htau hEnd hE hTail hEndpoint := by
  intro φ hφ q hq

  let P : ℝ → ℝ :=
    h3PreterminalTailCanonicalWeakVelocityPairingReal
      hNS ht htau hEnd hE hTail hEndpoint φ

  let G : ℝ → ℝ :=
    h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
      hNS ht htau hEnd hE hTail hEndpoint φ

  have hGContinuous :
      ContinuousOn G (Set.Icc (0 : ℝ) tau) := by
    dsimp only [G]
    exact
      continuousOn_h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ

  have hGAt :
      ∀ y ∈ Set.Ioo (0 : ℝ) tau,
        ContinuousAt G y := by
    intro y hy
    exact
      ContinuousWithinAt.continuousAt
        (hGContinuous y ⟨hy.1.le, hy.2.le⟩)
        (Icc_mem_nhds hy.1 hy.2)

  have hSub :
      Set.Icc (0 : ℝ) q
        ⊆ Set.Icc (0 : ℝ) tau := by
    intro y hy
    exact
      ⟨hy.1, hy.2.trans hq.2.le⟩

  have hGIntegrable :
      IntervalIntegrable G volume (0 : ℝ) q := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hq.1.le]
    exact hGContinuous.mono hSub

  have hGMeasurable :
      StronglyMeasurableAtFilter
        G
        (𝓝 q)
        (volume : Measure ℝ) := by
    exact
      ContinuousAt.stronglyMeasurableAtFilter
        (μ := (volume : Measure ℝ))
        isOpen_Ioo
        hGAt
        q
        hq

  have hIntegralDerivative :
      HasDerivAt
        (fun y : ℝ =>
          ∫ s in (0 : ℝ)..y, G s)
        (G q)
        q :=
    intervalIntegral.integral_hasDerivAt_right
      hGIntegrable
      hGMeasurable
      (hGAt q hq)

  let J : ℝ → ℝ :=
    fun y =>
      P 0 + ∫ s in (0 : ℝ)..y, G s

  have hJDerivative :
      HasDerivAt J (G q) q := by
    dsimp only [J]
    exact hIntegralDerivative.const_add (P 0)

  have hJEq :
      ∀ y ∈ Set.Icc (0 : ℝ) tau,
        J y = P y := by
    intro y hy

    have hEq :=
      hIntegrated φ hφ ⟨y, hy⟩

    dsimp only [J, P, G]
    dsimp only [P, G] at hEq
    linarith

  have hIccNeighborhood :
      Set.Icc (0 : ℝ) tau ∈ 𝓝 q :=
    Icc_mem_nhds hq.1 hq.2

  have hEventuallyEq :
      P =ᶠ[𝓝 q] J := by
    filter_upwards [hIccNeighborhood] with y hy
    exact (hJEq y hy).symm

  have hPDerivative :
      HasDerivAt P (G q) q :=
    hJDerivative.congr_of_eventuallyEq hEventuallyEq

  dsimp only [P, G] at hPDerivative ⊢
  exact hPDerivative

/-- Hence the integrated weak momentum identity is already sufficient for the
genuine physical `L²` evolution family on every shortened target. -/
theorem h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_eq_BochnerProjectedRHSTo_of_all_integratedWeakPairings
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
    (hIntegrated :
      H3PreterminalTailCanonicalAllDivergenceFreeWeakVelocityPairingsSatisfyIntegratedProjectedRHSOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
        hNS ht htau hEnd hTail q
      =
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbertTo
      hNS ht htau hEnd hE hTail hEndpoint q := by
  apply
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_eq_BochnerProjectedRHSTo_of_all_weakPairingDerivatives
      hNS ht htau hEnd hE hTail hEndpoint

  exact
    H3PreterminalTailCanonicalAllDivergenceFreeWeakVelocityPairingsHaveProjectedRHSDerivativeOnElapsed_of_integratedProjectedRHS
      hNS ht htau hEnd hE hTail hEndpoint hIntegrated

end

end Euclidean
end Bridge
end PrimeTensor
