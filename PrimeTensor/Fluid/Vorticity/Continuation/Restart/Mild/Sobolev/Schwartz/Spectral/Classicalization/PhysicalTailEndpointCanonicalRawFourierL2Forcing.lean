import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailEndpointCanonicalRawFourierL2Diffusion
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.C0.Bridge

/-!
# Classicalization: quotient-safe endpoint Leray forcing in raw Fourier L²

`PhysicalTailEndpointCanonicalRawFourierL2Diffusion` packages the linear
Laplacian contribution of the old endpoint path as a genuine Fourier `L²`
state.

This file does the corresponding bookkeeping for the nonlinear term already
used by the heat--Leray mild equation.  At every endpoint-canonical spectral
slice we package

    h3RawFinLerayOuterProductDivergence U U i

with the repository's existing `MemLp 2` theorem, producing a canonical
`H3FourierComplexL2` forcing state.

The bundled state has exactly the expected raw Leray-divergence representative
almost everywhere.  On the physical interval, the same forcing package built
from the globally indexed normalized real path agrees exactly with the package
built from the bounded physical path.

No new nonlinear estimate, pressure identity, time derivative, or
fixed-frequency evaluation is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology BigOperators

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalRawFourierL2Forcing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Quotient-safe raw Fourier `L²` Leray forcing of one endpoint-canonical
physical slice. -/
noncomputable def h3PreterminalTailCanonicalLerayForcingFourierL2OnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  let U : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
      hNS ht hEnd hE hTail hEndpoint q
  h3RawFinLerayOuterProductDivergenceFourierL2 U U i

/-- The quotient-safe endpoint forcing has the raw Leray-divergence amplitude
as its representative almost everywhere. -/
theorem h3PreterminalTailCanonicalLerayForcingFourierL2OnElapsed_ae
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    ((h3PreterminalTailCanonicalLerayForcingFourierL2OnElapsed
        hNS ht hEnd hE hTail hEndpoint q i : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3RawFinLerayOuterProductDivergence
      (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
        hNS ht hEnd hE hTail hEndpoint q)
      (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
        hNS ht hEnd hE hTail hEndpoint q)
      i := by
  unfold h3PreterminalTailCanonicalLerayForcingFourierL2OnElapsed
  unfold h3RawFinLerayOuterProductDivergenceFourierL2
  exact
    MemLp.coeFn_toLp
      (h3RawFinLerayOuterProductDivergence_memLp2
        (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
          hNS ht hEnd hE hTail hEndpoint q)
        (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
          hNS ht hEnd hE hTail hEndpoint q)
        i)

/-- Quotient-safe raw Fourier `L²` Leray forcing of the globally indexed
normalized endpoint path. -/
noncomputable def h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2
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
    H3FourierComplexL2 :=
  let U : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau hEnd hE hTail hEndpoint s
  h3RawFinLerayOuterProductDivergenceFourierL2 U U i

/-- The normalized-real forcing package has the exact raw Leray-divergence
representative almost everywhere. -/
theorem h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2_ae
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
    ((h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2
        hNS ht htau hEnd hE hTail hEndpoint s i : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3RawFinLerayOuterProductDivergence
      (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau hEnd hE hTail hEndpoint s)
      (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau hEnd hE hTail hEndpoint s)
      i := by
  unfold h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2
  unfold h3RawFinLerayOuterProductDivergenceFourierL2
  exact
    MemLp.coeFn_toLp
      (h3RawFinLerayOuterProductDivergence_memLp2
        (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau hEnd hE hTail hEndpoint s)
        (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau hEnd hE hTail hEndpoint s)
        i)

/-- On the genuine physical interval, the normalized-real forcing state is
exactly the forcing state of the corresponding bounded physical path slice. -/
theorem h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2_eq_on_physical
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
    (hs : s ∈ Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2
        hNS ht htau.le hEnd hE hTail hEndpoint s i
      =
    h3PreterminalTailCanonicalLerayForcingFourierL2OnElapsed
      hNS ht hEnd hE hTail hEndpoint ⟨s, hs⟩ i := by
  let P : H3SpectralPhysicalVelocityPath tau :=
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
      hNS ht hEnd hE hTail hEndpoint

  let q : Set.Icc (0 : ℝ) tau :=
    ⟨s, hs⟩

  have hRecover :
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint s
        =
      P q := by
    unfold h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
    exact
      h3PathPhysicalRealExtension_normalizedPhysical_apply
        htau P q

  unfold h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2
  unfold h3PreterminalTailCanonicalLerayForcingFourierL2OnElapsed

  rw [hRecover]

end

end Euclidean
end Bridge
end PrimeTensor
