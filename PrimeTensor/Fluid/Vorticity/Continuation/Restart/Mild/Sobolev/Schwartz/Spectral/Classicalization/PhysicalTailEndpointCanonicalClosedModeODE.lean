import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailEndpointCanonicalWeightedForcing

/-!
# Classicalization: endpoint canonical closed mode ODE reduction

The endpoint-canonical physical-evolution theorem currently exposes two
pointwise Fourier hypotheses:

* raw Fourier mode continuity on every positive subinterval;
* the concrete heat--Leray mode ODE on the open elapsed interval.

Those are not independent if the mode ODE is available at the elapsed
endpoints as well.  By definition, `H3FinHeatLerayModeODEAt` is a
coordinatewise `HasDerivAt` statement.  Differentiability at every point of the
closed elapsed interval therefore gives continuity there automatically.

This file packages that elementary implication.  The old preterminal
PDE-to-spectral frontier is thereby reduced to one mode-side statement:

    H3FinHeatLerayModeODEAt ν ξ W s

for every fixed frequency `ξ` and every `s ∈ [0,τ]`.

No Fourier/PDE identity is asserted here.  In particular, this file does not
pretend that Banach `L²` path continuity gives pointwise Fourier continuity.
The next analytic bridge must genuinely derive the closed mode ODE from the
old preterminal Navier--Stokes equation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology BigOperators

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalClosedModeODE
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A concrete heat--Leray mode ODE on a closed interval automatically gives
continuity of every raw Fourier coordinate on every contained subinterval. -/
theorem h3FinHeatLerayModeODEAt_closed_gives_rawFourier_continuousOn
    {nu tau : ℝ}
    (W : ℝ → H3SpectralFinVectorState)
    (hODE :
      ∀ xi : H3FourierPoint3,
        ∀ s ∈ Set.Icc (0 : ℝ) tau,
          H3FinHeatLerayModeODEAt nu xi W s) :
    ∀ q : ℝ,
      0 ≤ q →
      q ≤ tau →
      ∀ xi : H3FourierPoint3, ∀ i : Fin 3,
        ContinuousOn
          (fun s : ℝ =>
            h3SpectralScalarRawFourier (W s i) xi)
          (Set.Icc (0 : ℝ) q) := by
  intro q hq hqTau xi i s hs

  have hsTau :
      s ∈ Set.Icc (0 : ℝ) tau := by
    exact
      ⟨
        hs.1,
        le_trans hs.2 hqTau
      ⟩

  have hMode :=
    hODE xi s hsTau

  unfold H3FinHeatLerayModeODEAt at hMode
  unfold H3FinHeatModeODEAt at hMode

  exact
    (hMode i).continuousAt.continuousWithinAt

/-- Endpoint physical evolution follows from endpoint `L²` continuity and one
closed-interval concrete heat--Leray mode ODE hypothesis.

Raw-mode continuity is supplied by differentiability; weighted forcing was
already discharged from global path continuity. -/
theorem h3PreterminalTailPhysicalEvolutionAt_of_endpoint_closed_mode_ODE
    {nu E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hnu : 0 < nu)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hODE :
      ∀ xi : H3FourierPoint3,
        ∀ s ∈ Set.Icc (0 : ℝ) tau,
          H3FinHeatLerayModeODEAt
            nu xi
            (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
              hNS ht htau.le hEnd hE hTail hEndpoint)
            s) :
    H3PreterminalTailPhysicalEvolutionAt
      hnu
      hNS
      ht
      htau.le
      hEnd
      hE
      hTail := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  apply
    h3PreterminalTailPhysicalEvolutionAt_of_endpoint_mode_continuity_and_ODE
      hnu
      hNS
      ht
      htau
      hEnd
      hE
      hTail
      hEndpoint

  · intro q hq hqTau xi i

    have hContinuous :=
      h3FinHeatLerayModeODEAt_closed_gives_rawFourier_continuousOn
        (nu := nu)
        (tau := tau)
        W
        (by
          intro xi' s hs
          dsimp only [W]
          exact hODE xi' s hs)
        q
        hq.le
        hqTau
        xi
        i

    simpa only [W] using hContinuous

  · intro xi s hs

    have hsClosed :
        s ∈ Set.Icc (0 : ℝ) tau := by
      exact ⟨hs.1.le, hs.2.le⟩

    exact hODE xi s hsClosed

end

end Euclidean
end Bridge
end PrimeTensor
