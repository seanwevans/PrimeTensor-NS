import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Initial.State
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spectral.Fin.Heat.Leray.Variation.Of.Constants.State

/-!
# Classicalization: endpoint canonical variation of constants

The endpoint-only canonical physical path is now known to start exactly at the
retained H³ spectral anchor.

This file packages the normalized path back into a globally indexed real-time
spectral path and records the structural facts needed by the general
variation-of-constants theorem:

* global continuity;
* the uniform `2E` bound inherited from the retained H³ tail;
* the exact initial state.

For one positive elapsed target `q ≤ τ`, the general finite-H³
variation-of-constants theorem then reduces the restarted mild identity to
exactly three Fourier-mode inputs:

1. continuity of each raw Fourier mode on `[0,q]`;
2. the concrete heat--Leray mode ODE on `(0,q)`;
3. weighted source-time integrability of the Leray forcing.

No new PDE-to-Fourier calculation or forcing estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology BigOperators

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalVariationOfConstants
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The endpoint-only canonical physical path, normalized to unit time and
extended back to a globally indexed real-time spectral path. -/
noncomputable def h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
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
    ℝ → H3SpectralVelocityState :=
  h3PathPhysicalRealExtension
    tau
    (h3SpectralNormalizedPathOfPhysical
      htau
      (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
        hNS ht hEnd hE hTail hEndpoint))

/-- The globally indexed endpoint canonical path is continuous. -/
theorem continuous_h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
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
      (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau hEnd hE hTail hEndpoint) := by
  unfold h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint

  exact
    continuous_h3PathPhysicalRealExtension
      tau
      (h3SpectralNormalizedPathOfPhysical
        htau
        (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
          hNS ht hEnd hE hTail hEndpoint))

/-- Every real-time value of the normalized endpoint canonical extension stays
inside the same `2E` ball. -/
theorem norm_h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_le_twoE
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
    ‖h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau hEnd hE hTail hEndpoint s‖
      ≤
    2 * E := by
  let P : H3SpectralPhysicalVelocityPath tau :=
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
      hNS ht hEnd hE hTail hEndpoint

  let V : H3SpectralVelocityPath :=
    h3SpectralNormalizedPathOfPhysical htau P

  have hPbound :
      ∀ q : Set.Icc (0 : ℝ) tau,
        ‖P q‖ ≤ 2 * E := by
    intro q

    dsimp only [
      P,
      h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
    ]

    exact
      norm_h3PreterminalCanonicalSpectralPhysicalPath_apply_le_twoA
        hNS
        ht
        hEnd
        hE
        (canonicalH3TailDataFrom_integrableOnElapsed
          hEnd hTail)
        (canonicalH3TailDataFrom_energyOnElapsed_le_twoE
          hE hEnd hTail)
        (h3PreterminalTailCanonicalSpectralStateContinuousOnElapsed_of_l2Endpoint
          hNS ht hEnd hTail hEndpoint)
        q

  have hTwoE : 0 ≤ 2 * E := by
    linarith

  have hVbound :
      ‖V‖ ≤ 2 * E := by
    exact
      norm_h3SpectralNormalizedPathOfPhysical_le_of_forall
        htau hTwoE P hPbound

  change
    ‖h3PathPhysicalRealExtension tau V s‖
      ≤
    2 * E

  exact
    le_trans
      (norm_h3PathPhysicalRealExtension_le tau V s)
      hVbound

/-- The normalized real-time endpoint canonical path starts exactly at the
retained H³ spectral anchor. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_zero
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
        hNS ht hEnd hTail) :
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint 0
      =
    h3PreterminalCanonicalAnchorSpectralState
      hNS
      ht
      (canonicalH3TailDataFrom_at_anchor ht hTail).1 := by
  unfold h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint

  exact
    h3PreterminalTailCanonicalNormalizedPhysicalExtensionOfL2Endpoint_zero
      hNS ht htau hEnd hE hTail hEndpoint

/-- One positive target-time variation-of-constants identity for the endpoint
canonical path.

All path-level Banach hypotheses are discharged internally.  The caller
supplies only the three concrete Fourier-mode inputs. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_variationOfConstants
    {nu E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
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
    (hq : 0 < q)
    (_hqTau : q ≤ tau)
    (hFContinuous :
      ∀ xi : H3FourierPoint3, ∀ i : Fin 3,
        ContinuousOn
          (fun s : ℝ =>
            h3SpectralScalarRawFourier
              ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                hNS ht htau.le hEnd hE hTail hEndpoint) s i)
              xi)
          (Set.Icc (0 : ℝ) q))
    (hODE :
      ∀ xi : H3FourierPoint3,
        ∀ s ∈ Set.Ioo (0 : ℝ) q,
          H3FinHeatLerayModeODEAt
            nu xi
            (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
              hNS ht htau.le hEnd hE hTail hEndpoint)
            s)
    (hWeightedForcing :
      ∀ xi : H3FourierPoint3, ∀ i : Fin 3,
        IntervalIntegrable
          (fun s : ℝ =>
            Real.exp
                (nu * h3FourierGradientSquare xi * s)
              •
            h3RawFinLerayOuterProductDivergence
              ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                hNS ht htau.le hEnd hE hTail hEndpoint) s)
              ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                hNS ht htau.le hEnd hE hTail hEndpoint) s)
              i xi)
          volume
          0
          q) :
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint q
      =
    h3SpectralVelocityHeatApplyNN
        nu hnu.le
        (NNReal.mk q hq.le)
        (h3PreterminalCanonicalAnchorSpectralState
          hNS
          ht
          (canonicalH3TailDataFrom_at_anchor ht hTail).1)
      -
    h3SpectralFinHeatLerayDuhamel
      nu q hnu
      (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint)
      (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint) := by
  let W : ℝ → H3SpectralVelocityState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  have hWcont : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint

  have hWbound :
      ∀ s : ℝ, ‖W s‖ ≤ 2 * E := by
    intro s
    dsimp only [W]
    exact
      norm_h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_le_twoE
        hNS ht htau.le hEnd hE hTail hEndpoint s

  have hTwoE : 0 ≤ 2 * E := by
    linarith

  have hState :=
    h3FinHeatLerayVariationOfConstants_retarded_state
      hnu
      hq
      hTwoE
      W
      hWcont
      hWbound
      (by
        simpa only [W] using hFContinuous)
      (by
        simpa only [W] using hODE)
      (by
        simpa only [W] using hWeightedForcing)

  have hInitial :
      W 0
        =
      h3PreterminalCanonicalAnchorSpectralState
        hNS
        ht
        (canonicalH3TailDataFrom_at_anchor ht hTail).1 := by
    dsimp only [W]
    exact
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_zero
        hNS ht htau hEnd hE hTail hEndpoint

  rw [hInitial] at hState

  simpa only [W] using hState

end

end Euclidean
end Bridge
end PrimeTensor
