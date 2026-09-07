import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.FourierL2HeatGeneratorFTC
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.FourierL2IntegralEquation
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Raw.Fourier.L2.Continuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Physical L² temporal admissibility: endpoint evolution derivative

The heat semigroup now has its quotient-safe integrated generator identity.  To
derive a retarded variation-of-constants formula for the endpoint path, the
remaining input is not one final-time increment identity but an integral
evolution identity for every intermediate target.

This file isolates that exact hypothesis in raw Fourier `L²`:

    raw(W(q)) - raw(W(0))
      = ∫₀^q [Δ̂ raw(W(s)) - F̂(s)] ds,
      0 ≤ q ≤ τ.

The hypothesis is intentionally stated as a family on the fixed endpoint path
and fixed spectral RHS.  A later weak-RHS/physical-L² bridge will discharge it;
nothing here hides that dependency.

Because the spectral RHS is already continuous on `[0,τ]`, FTC-1 upgrades the
family immediately to the ordinary Banach-space derivative on the open
interval:

    d/dq raw(W(q))
      = Δ̂ raw(W(q)) - F̂(q).

This is the evolution derivative needed by the quotient-safe interaction
picture in the next variation-of-constants step.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2EndpointEvolutionDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The endpoint canonical velocity path after exact H³ deweighting, packaged
as one three-component raw Fourier `L²` path. -/
noncomputable def h3PreterminalTailCanonicalRawFourierL2VelocityReal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 ≤ tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (s : ℝ) :
    H3RawFourierL2FinVectorState :=
  h3SpectralFinVectorRawFourierL2
    (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau hEnd hE hTail hEndpoint s)

@[simp]
theorem h3PreterminalTailCanonicalRawFourierL2VelocityReal_apply
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 ≤ tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (s : ℝ)
    (i : Fin 3) :
    h3PreterminalTailCanonicalRawFourierL2VelocityReal
        hNS ht htau hEnd hE hTail hEndpoint s i
      =
    h3SpectralScalarRawFourierL2
      ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau hEnd hE hTail hEndpoint s) i) :=
  rfl

/-- The deweighted endpoint path is globally continuous in the genuine raw
Fourier `L²` product space. -/
theorem continuous_h3PreterminalTailCanonicalRawFourierL2VelocityReal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 ≤ tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail) :
    Continuous
      (h3PreterminalTailCanonicalRawFourierL2VelocityReal
        hNS ht htau hEnd hE hTail hEndpoint) := by
  apply continuous_pi
  intro i
  exact
    continuous_h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_rawFourierL2
      hNS ht htau hEnd hE hTail hEndpoint i

/-- Family form of the quotient-safe endpoint integral evolution equation.

This is the precise conditional input needed for variation of constants.  It is
stronger than one final-time identity and is deliberately left visible as a
hypothesis until the weak physical `L²` evolution bridge is closed. -/
def H3PreterminalTailCanonicalRawFourierL2IntegralEvolutionOnElapsed
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
  ∀ q ∈ Set.Icc (0 : ℝ) tau,
    h3PreterminalTailCanonicalRawFourierL2VelocityReal
          hNS ht htau.le hEnd hE hTail hEndpoint q
        -
      h3PreterminalTailCanonicalRawFourierL2VelocityReal
          hNS ht htau.le hEnd hE hTail hEndpoint 0
      =
    ∫ s in (0 : ℝ)..q,
      h3PreterminalTailCanonicalSpectralProjectedRHSFourierL2Real
        hNS ht htau hEnd hE hTail hEndpoint s

/-- A family of quotient-safe integral evolution identities differentiates
ordinarily at every strict interior elapsed time. -/
theorem h3PreterminalTailCanonicalRawFourierL2VelocityReal_hasDerivAt_of_integralEvolution
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hEvolution :
      H3PreterminalTailCanonicalRawFourierL2IntegralEvolutionOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint)
    (hq : q ∈ Set.Ioo (0 : ℝ) tau) :
    HasDerivAt
      (h3PreterminalTailCanonicalRawFourierL2VelocityReal
        hNS ht htau.le hEnd hE hTail hEndpoint)
      (h3PreterminalTailCanonicalSpectralProjectedRHSFourierL2Real
        hNS ht htau hEnd hE hTail hEndpoint q)
      q := by
  let D : ℝ → H3RawFourierL2FinVectorState :=
    h3PreterminalTailCanonicalRawFourierL2VelocityReal
      hNS ht htau.le hEnd hE hTail hEndpoint

  let G : ℝ → H3RawFourierL2FinVectorState :=
    h3PreterminalTailCanonicalSpectralProjectedRHSFourierL2Real
      hNS ht htau hEnd hE hTail hEndpoint

  have hGContinuous :
      ContinuousOn G (Set.Icc (0 : ℝ) tau) := by
    dsimp only [G]
    exact
      continuousOn_h3PreterminalTailCanonicalSpectralProjectedRHSFourierL2Real
        hNS ht htau hEnd hE hTail hEndpoint

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

  let J : ℝ → H3RawFourierL2FinVectorState :=
    fun y =>
      D 0 + ∫ s in (0 : ℝ)..y, G s

  have hJDerivative :
      HasDerivAt J (G q) q := by
    dsimp only [J]
    exact hIntegralDerivative.const_add (D 0)

  have hJEq :
      ∀ y ∈ Set.Icc (0 : ℝ) tau,
        J y = D y := by
    intro y hy
    have hEq := hEvolution y hy
    dsimp only [J, D, G]
    rw [← hEq]
    abel

  have hIccNeighborhood :
      Set.Icc (0 : ℝ) tau ∈ 𝓝 q :=
    Icc_mem_nhds hq.1 hq.2

  have hEventuallyEq :
      D =ᶠ[𝓝 q] J := by
    filter_upwards [hIccNeighborhood] with y hy
    exact (hJEq y hy).symm

  have hDDerivative :
      HasDerivAt D (G q) q :=
    hJDerivative.congr_of_eventuallyEq hEventuallyEq

  dsimp only [D, G] at hDDerivative ⊢
  exact hDDerivative

/-- Right-derivative form, ready for the interaction-picture FTC argument. -/
theorem h3PreterminalTailCanonicalRawFourierL2VelocityReal_hasDerivWithinAt_right_of_integralEvolution
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hEvolution :
      H3PreterminalTailCanonicalRawFourierL2IntegralEvolutionOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint)
    (hq : q ∈ Set.Ioo (0 : ℝ) tau) :
    HasDerivWithinAt
      (h3PreterminalTailCanonicalRawFourierL2VelocityReal
        hNS ht htau.le hEnd hE hTail hEndpoint)
      (h3PreterminalTailCanonicalSpectralProjectedRHSFourierL2Real
        hNS ht htau hEnd hE hTail hEndpoint q)
      (Set.Ioi q)
      q := by
  exact
    (h3PreterminalTailCanonicalRawFourierL2VelocityReal_hasDerivAt_of_integralEvolution
      hNS ht htau hEnd hE hTail hEndpoint hEvolution hq).hasDerivWithinAt

end

end Euclidean
end Bridge
end PrimeTensor
