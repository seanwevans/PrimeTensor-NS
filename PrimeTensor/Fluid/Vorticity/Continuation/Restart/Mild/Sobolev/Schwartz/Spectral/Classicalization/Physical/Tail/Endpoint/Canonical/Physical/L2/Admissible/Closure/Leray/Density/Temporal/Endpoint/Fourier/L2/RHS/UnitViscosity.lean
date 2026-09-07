import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.Evolution.Derivative

/-!
# Physical L² temporal admissibility: unit-viscosity endpoint RHS

The quotient-safe endpoint evolution derivative is now available on the open
elapsed interval.  Before building the interaction picture, we make the
normalization explicit.

The normalized physical endpoint equation appearing in
`FourierL2IntegralEquation` is

    raw(W)' = Δ̂ raw(W) - F̂,

with coefficient exactly `1` in front of the Laplacian.  Therefore the heat
generator used to cancel the linear term in variation of constants is the
unit-viscosity generator.

This file packages the endpoint forcing as a three-component raw Fourier `L²`
state, identifies the literal spectral RHS with

    A₁(W(s)) - F̂(s),

and restates the endpoint derivative in that form.  No arbitrary viscosity
parameter is introduced into the normalized physical PDE.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2EndpointUnitViscosityRHS
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Three-component quotient-safe Leray forcing of the normalized endpoint
path. -/
noncomputable def h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2Vector
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
  fun i : Fin 3 =>
    h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2
      hNS ht htau hEnd hE hTail hEndpoint s i

@[simp]
theorem h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2Vector_apply
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
    h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2Vector
        hNS ht htau hEnd hE hTail hEndpoint s i
      =
    h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2
      hNS ht htau hEnd hE hTail hEndpoint s i :=
  rfl

/-- Unit-viscosity quotient-safe generator of a weighted H³ velocity state. -/
noncomputable def h3RawFourierL2UnitGeneratorStateVector
    (U : H3SpectralFinVectorState) :
    H3RawFourierL2FinVectorState :=
  fun i : Fin 3 =>
    h3RawFourierL2HeatGeneratorState
      1 (U i)

@[simp]
theorem h3RawFourierL2UnitGeneratorStateVector_apply
    (U : H3SpectralFinVectorState)
    (i : Fin 3) :
    h3RawFourierL2UnitGeneratorStateVector U i
      =
    h3RawFourierL2HeatGeneratorState 1 (U i) :=
  rfl

/-- At unit viscosity, the packaged heat generator is exactly the raw Fourier
Laplacian on the weighted H³ generator domain. -/
theorem h3RawFourierL2UnitGeneratorStateVector_eq_laplacian
    (U : H3SpectralFinVectorState) :
    h3RawFourierL2UnitGeneratorStateVector U
      =
    h3SpectralFinVectorLaplacianRawFourierL2 U := by
  funext i
  unfold h3RawFourierL2UnitGeneratorStateVector
  unfold h3RawFourierL2HeatGeneratorState
  simp

/-- The literal endpoint spectral RHS is precisely unit heat generator minus
the quotient-safe Leray forcing vector. -/
theorem h3PreterminalTailCanonicalSpectralProjectedRHSFourierL2Real_eq_unitGenerator_sub_forcing
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail) :
    h3PreterminalTailCanonicalSpectralProjectedRHSFourierL2Real
        hNS ht htau hEnd hE hTail hEndpoint s
      =
    h3RawFourierL2UnitGeneratorStateVector
        (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint s)
      -
    h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2Vector
      hNS ht htau.le hEnd hE hTail hEndpoint s := by
  funext i
  simp only [
    h3PreterminalTailCanonicalSpectralProjectedRHSFourierL2Real_apply,
    Pi.sub_apply,
    h3RawFourierL2UnitGeneratorStateVector_apply,
    h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2Vector_apply
  ]
  unfold h3RawFourierL2HeatGeneratorState
  simp

/-- Conditional endpoint evolution derivative, rewritten in the exact
unit-viscosity generator-minus-forcing form needed for interaction-picture
cancellation. -/
theorem h3PreterminalTailCanonicalRawFourierL2VelocityReal_hasDerivAt_unitGenerator_sub_forcing
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
      (h3RawFourierL2UnitGeneratorStateVector
          (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
            hNS ht htau.le hEnd hE hTail hEndpoint q)
        -
       h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2Vector
          hNS ht htau.le hEnd hE hTail hEndpoint q)
      q := by
  have hDerivative :=
    h3PreterminalTailCanonicalRawFourierL2VelocityReal_hasDerivAt_of_integralEvolution
      hNS ht htau hEnd hE hTail hEndpoint hEvolution hq

  rw [
    h3PreterminalTailCanonicalSpectralProjectedRHSFourierL2Real_eq_unitGenerator_sub_forcing
      hNS ht htau hEnd hE hTail hEndpoint
  ] at hDerivative

  exact hDerivative

/-- Right-derivative version of the same normalized endpoint equation. -/
theorem h3PreterminalTailCanonicalRawFourierL2VelocityReal_hasDerivWithinAt_right_unitGenerator_sub_forcing
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
      (h3RawFourierL2UnitGeneratorStateVector
          (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
            hNS ht htau.le hEnd hE hTail hEndpoint q)
        -
       h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2Vector
          hNS ht htau.le hEnd hE hTail hEndpoint q)
      (Set.Ioi q)
      q := by
  exact
    (h3PreterminalTailCanonicalRawFourierL2VelocityReal_hasDerivAt_unitGenerator_sub_forcing
      hNS ht htau hEnd hE hTail hEndpoint hEvolution hq).hasDerivWithinAt

end

end Euclidean
end Bridge
end PrimeTensor
