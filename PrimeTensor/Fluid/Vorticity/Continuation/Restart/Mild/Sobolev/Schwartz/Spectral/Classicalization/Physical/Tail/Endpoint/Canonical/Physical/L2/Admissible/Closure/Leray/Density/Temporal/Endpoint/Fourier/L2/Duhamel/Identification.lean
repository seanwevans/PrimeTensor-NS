import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.VariationOfConstants
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spectral.Fin.Heat.Leray.Duhamel.Raw.Fourier.L2

/-!
# Physical L² temporal admissibility: identify the endpoint retarded integral with Duhamel

The quotient-safe endpoint variation-of-constants theorem now has the correct
retarded raw Fourier `L²` integral

    ∫₀^q S₁(q-s) F(W(s)) ds.

The repository already contains the actual spectral heat--Leray Duhamel state
used by the mild solver, together with a quotient-safe theorem identifying its
H³ deweighting with an interval integral of positive-lag raw forcing kernels.

This file proves those are the same object.

There are three steps.

1. At every strictly positive lag, applying the raw Fourier heat semigroup to
   the unheated `L²` forcing package is exactly the existing positive-lag raw
   heat-forcing package.
2. Hence the new continuous retarded kernel and the existing endpoint-safe
   Duhamel integrand agree on the open source interval `(0,q)`.  Their values at
   the endpoints are irrelevant to the interval integral, so
   `intervalIntegral.integral_congr_Ioo_of_le` identifies the integrals.
3. Coordinate projection commutes with the Bochner interval integral, yielding
   equality of the full three-component raw `L²` state with the deweighted
   spectral Duhamel term.

Thus the conditional non-circular variation-of-constants route now lands
exactly on the repository's established mild Duhamel object.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2EndpointDuhamelIdentification
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- At a strictly positive lag, quotient-safe heat evolution of the unheated
raw forcing `L²` class is exactly the repository's existing positive-lag raw
heat-forcing `L²` class. -/
theorem h3HeatFrequencyApplyNN_rawFinLerayOuterProductDivergenceFourierL2_eq_heat
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    h3HeatFrequencyApplyNN
        ν hν.le (Real.toNNReal τ)
        (h3RawFinLerayOuterProductDivergenceFourierL2
          U V i)
      =
    h3RawFinLerayOuterProductDivergenceHeatFourierL2
      ν τ hν hτ U V i := by
  apply MeasureTheory.Lp.ext

  have hHeat :=
    h3HeatFrequencyApplyNN_coeFn
      ν hν.le (Real.toNNReal τ)
      (h3RawFinLerayOuterProductDivergenceFourierL2
        U V i)

  have hRaw :
      ((h3RawFinLerayOuterProductDivergenceFourierL2
          U V i : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3RawFinLerayOuterProductDivergence U V i := by
    unfold h3RawFinLerayOuterProductDivergenceFourierL2
    exact
      MemLp.coeFn_toLp
        (h3RawFinLerayOuterProductDivergence_memLp2
          U V i)

  have hOut :
      ((h3RawFinLerayOuterProductDivergenceHeatFourierL2
          ν τ hν hτ U V i : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3RawFinLerayOuterProductDivergenceHeatRepresentative
        ν τ U V i := by
    unfold h3RawFinLerayOuterProductDivergenceHeatFourierL2
    exact
      MemLp.coeFn_toLp
        (h3RawFinLerayOuterProductDivergenceHeatRepresentative_memLp2
          hν hτ U V i)

  filter_upwards [hHeat, hRaw, hOut] with
      ξ hHeatξ hRawξ hOutξ

  rw [hHeatξ, hRawξ, hOutξ]

  have hTime :
      ((Real.toNNReal τ : ℝ≥0) : ℝ) = τ :=
    Real.coe_toNNReal τ hτ.le

  rw [hTime]

  rfl

/-- On a strict source time `s < q`, the new retarded endpoint kernel is
exactly the endpoint-safe raw Fourier `L²` integrand of the existing spectral
Duhamel state. -/
theorem h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal_apply_eq_duhamelIntegrand_of_lt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hs : s < q)
    (i : Fin 3) :
    h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
        hNS ht htau.le hEnd hE hTail hEndpoint q s i
      =
    h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
      1 q one_pos
      (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint)
      (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint)
      i s := by
  have hlag : 0 < q - s :=
    sub_pos.mpr hs

  unfold h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
  unfold h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2Vector
  unfold h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2

  change
    h3HeatFrequencyApplyNN
        1 zero_le_one
        (Real.toNNReal (q - s))
        (h3RawFinLerayOuterProductDivergenceFourierL2
          (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
            hNS ht htau.le hEnd hE hTail hEndpoint s)
          (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
            hNS ht htau.le hEnd hE hTail hEndpoint s)
          i)
      =
    h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
      1 q one_pos
      (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint)
      (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint)
      i s

  simp only [
    h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand,
    dif_pos hlag
  ]

  exact
    h3HeatFrequencyApplyNN_rawFinLerayOuterProductDivergenceFourierL2_eq_heat
      one_pos hlag
      (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint s)
      (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint s)
      i

/-- Coordinatewise, the new quotient-safe retarded forcing integral is exactly
the H³-deweighted coordinate of the repository's spectral Duhamel state. -/
theorem h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal_integral_apply_eq_duhamelRawFourierL2
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
    (hq : q ∈ Set.Ioo (0 : ℝ) tau)
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

/-- Three-component raw Fourier `L²` deweighting of the actual spectral
heat--Leray Duhamel state along the endpoint canonical path. -/
noncomputable def h3PreterminalTailCanonicalSpectralDuhamelRawFourierL2Vector
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
    (q : ℝ) :
    H3RawFourierL2FinVectorState :=
  fun i : Fin 3 =>
    h3SpectralScalarRawFourierL2
      (h3SpectralFinHeatLerayDuhamel
        1 q one_pos
        (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau hEnd hE hTail hEndpoint)
        (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau hEnd hE hTail hEndpoint)
        i)

/-- The full vector Bochner integral in the new conditional VOC is exactly the
deweighted existing spectral Duhamel state. -/
theorem h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal_integral_eq_spectralDuhamelRawFourierL2Vector
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
    (hq : q ∈ Set.Ioo (0 : ℝ) tau) :
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
    h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal_integral_apply_eq_duhamelRawFourierL2
      hNS ht htau hEnd hE hTail hEndpoint hq i

/-- Conditional quotient-safe endpoint variation of constants, now written
with the repository's actual spectral heat--Leray Duhamel state rather than a
parallel retarded integral. -/
theorem h3PreterminalTailCanonicalRawFourierL2VariationOfConstants_eq_spectralDuhamel_of_integralEvolution
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
    h3PreterminalTailCanonicalRawFourierL2VariationOfConstants_of_integralEvolution
      hNS ht htau hEnd hE hTail hEndpoint hEvolution hq

  have hDuhamel :=
    h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal_integral_eq_spectralDuhamelRawFourierL2Vector
      hNS ht htau hEnd hE hTail hEndpoint hq

  rw [hDuhamel] at hVOC
  exact hVOC

end

end Euclidean
end Bridge
end PrimeTensor
