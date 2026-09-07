import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.Duhamel.Identification
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.VariationOfConstants.Endpoint

/-!
# Endpoint-closed spectral Duhamel identification

The existing Duhamel identification is stated for `q ∈ (0,tau)`, but its
integral-identification proof only uses positivity of `q`.  The endpoint-safe
variation-of-constants theorem now also allows `q = tau`.

This file therefore records the same coordinatewise and vector Duhamel
identifications for `q ∈ (0,tau]`, then composes them with endpoint-safe
quotient variation of constants.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointDuhamelIdentificationEndpoint
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Coordinatewise endpoint-closed identification of the retarded forcing
integral with the raw-`L²` image of the spectral Duhamel state. -/
theorem h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal_integral_apply_eq_duhamelRawFourierL2_to
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
    (hq : q ∈ Set.Ioc (0 : ℝ) tau)
    (i : Fin 3) :
    (∫ s in (0 : ℝ)..q,
      h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
        hNS ht htau.le hEnd hE hTail hEndpoint q s i)
      =
    h3SpectralScalarRawFourierL2
      (h3SpectralFinHeatLerayDuhamel
        1 q one_pos
        (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint)
        (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint)
        i) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  have hKernel :
      (∫ s in (0 : ℝ)..q,
        h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
          hNS ht htau.le hEnd hE hTail hEndpoint q s i)
        =
      ∫ s in (0 : ℝ)..q,
        h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
          1 q one_pos W W i s := by
    apply
      intervalIntegral.integral_congr_Ioo_of_le
        hq.1.le
    intro s hs
    dsimp only [W]
    exact
      h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal_apply_eq_duhamelIntegrand_of_lt
        hNS ht htau hEnd hE hTail hEndpoint hs.2 i

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

  have hDuhamel :=
    h3SpectralFinHeatLerayDuhamel_rawFourierL2_eq_intervalIntegral
      (ν := 1)
      (t := q)
      (MU := 2 * E)
      (MV := 2 * E)
      one_pos
      hq.1.le
      hTwoE
      hTwoE
      W W
      hWcont hWcont
      hWbound hWbound
      i

  calc
    (∫ s in (0 : ℝ)..q,
      h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
        hNS ht htau.le hEnd hE hTail hEndpoint q s i)
        =
      ∫ s in (0 : ℝ)..q,
        h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
          1 q one_pos W W i s :=
      hKernel
    _ =
      h3SpectralScalarRawFourierL2
        (h3SpectralFinHeatLerayDuhamel
          1 q one_pos W W i) :=
      hDuhamel.symm

/-- Full vector endpoint-closed identification of the retarded Bochner integral
with the deweighted spectral Duhamel state. -/
theorem h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal_integral_eq_spectralDuhamelRawFourierL2Vector_to
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
    (hq : q ∈ Set.Ioc (0 : ℝ) tau) :
    (∫ s in (0 : ℝ)..q,
      h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
        hNS ht htau.le hEnd hE hTail hEndpoint q s)
      =
    h3PreterminalTailCanonicalSpectralDuhamelRawFourierL2Vector
      hNS ht htau.le hEnd hE hTail hEndpoint q := by
  let P :
      Fin 3 →
        (H3RawFourierL2FinVectorState →L[ℝ]
          H3FourierComplexL2) :=
    fun i =>
      ContinuousLinearMap.proj (R := ℝ) i

  have hInt :
      IntervalIntegrable
        (h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
          hNS ht htau.le hEnd hE hTail hEndpoint q)
        volume
        0
        q :=
    h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal_intervalIntegrable
      hNS ht htau hEnd hE hTail hEndpoint
      (q := q)

  funext i

  have hComm :
      P i
          (∫ s in (0 : ℝ)..q,
            h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
              hNS ht htau.le hEnd hE hTail hEndpoint q s)
        =
      ∫ s in (0 : ℝ)..q,
        P i
          (h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
            hNS ht htau.le hEnd hE hTail hEndpoint q s) := by
    symm
    exact
      (P i).intervalIntegral_comp_comm hInt

  change
    P i
        (∫ s in (0 : ℝ)..q,
          h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
            hNS ht htau.le hEnd hE hTail hEndpoint q s)
      =
    h3SpectralScalarRawFourierL2
      (h3SpectralFinHeatLerayDuhamel
        1 q one_pos
        (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint)
        (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint)
        i)

  rw [hComm]

  change
    (∫ s in (0 : ℝ)..q,
      h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
        hNS ht htau.le hEnd hE hTail hEndpoint q s i)
      =
    h3SpectralScalarRawFourierL2
      (h3SpectralFinHeatLerayDuhamel
        1 q one_pos
        (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint)
        (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint)
        i)

  exact
    h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal_integral_apply_eq_duhamelRawFourierL2_to
      hNS ht htau hEnd hE hTail hEndpoint hq i

/-- Endpoint-closed quotient-safe variation of constants written with the
repository's actual spectral heat--Leray Duhamel state. -/
theorem h3PreterminalTailCanonicalRawFourierL2VariationOfConstants_eq_spectralDuhamel_of_integralEvolution_to
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
    (hq : q ∈ Set.Ioc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalRawFourierL2VelocityReal
        hNS ht htau.le hEnd hE hTail hEndpoint q
      =
    h3RawFourierL2HeatApplyNN
        1 zero_le_one
        (Real.toNNReal q)
        (h3SpectralFinVectorRawFourierL2
          (h3PreterminalCanonicalAnchorSpectralState
            hNS
            ht
            (canonicalH3TailDataFrom_at_anchor ht hTail).1))
      -
    h3PreterminalTailCanonicalSpectralDuhamelRawFourierL2Vector
      hNS ht htau.le hEnd hE hTail hEndpoint q := by
  have hVOC :=
    h3PreterminalTailCanonicalRawFourierL2VariationOfConstants_of_integralEvolution_to
      hNS ht htau hEnd hE hTail hEndpoint hEvolution hq

  have hDuhamel :=
    h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal_integral_eq_spectralDuhamelRawFourierL2Vector_to
      hNS ht htau hEnd hE hTail hEndpoint hq

  rw [hDuhamel] at hVOC
  exact hVOC

end

end Euclidean
end Bridge
end PrimeTensor
