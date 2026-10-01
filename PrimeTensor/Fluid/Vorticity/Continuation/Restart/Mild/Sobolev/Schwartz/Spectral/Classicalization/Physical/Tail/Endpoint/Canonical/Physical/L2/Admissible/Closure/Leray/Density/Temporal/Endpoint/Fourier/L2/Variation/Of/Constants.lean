import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.Interaction.Derivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Physical L² temporal admissibility: quotient-safe endpoint variation of constants

The interaction-picture derivative is now available entirely in the raw
Fourier `L²` quotient space.  This file integrates it.

For fixed final elapsed time `q`, package the positive retarded forcing kernel

    R_q(s) = S₁(q-s) F(s).

The normalized-real endpoint forcing is globally strongly continuous after
composition with the already-proved continuous nonlinear Fourier `L²` forcing
map.  Joint strong continuity of the raw heat action then gives continuity of
both `R_q` and the interaction path

    I_q(s) = S₁(q-s) raw(W(s)).

The previous derivative theorem reads

    I_q'(s) = -R_q(s)

on the strict interior.  The one-sided Banach-valued FTC therefore gives

    raw(W(q))
      =
    S₁(q) raw(W(0))
      -
    ∫₀^q R_q(s) ds.

Finally `W(0)` is replaced by the retained canonical H³ spectral anchor.

The theorem remains explicitly conditional on
`H3PreterminalTailCanonicalRawFourierL2IntegralEvolutionOnElapsed`.  This file
does not discharge that temporal frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2EndpointVariationOfConstants
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The three-component normalized-real endpoint Leray forcing is globally
strongly continuous in raw Fourier `L²`. -/
theorem continuous_h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2Vector
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
    Continuous
      (h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2Vector
        hNS ht htau.le hEnd hE hTail hEndpoint) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  have hW : Continuous W :=
    continuous_h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  have hPair :
      Continuous
        (fun s : ℝ => (W s, W s)) :=
    Continuous.prodMk hW hW

  apply continuous_pi
  intro i

  have hForcing :=
    (continuous_h3RawFinLerayOuterProductDivergenceFourierL2 i).comp
      hPair

  change
    Continuous
      (fun s : ℝ =>
        h3RawFinLerayOuterProductDivergenceFourierL2
          (W s) (W s) i)

  simpa only [Function.comp_def] using hForcing

/-- The raw Fourier heat CLM commutes with negation. -/
@[simp]
theorem h3RawFourierL2HeatApplyNN_neg
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (r : ℝ≥0)
    (U : H3RawFourierL2FinVectorState) :
    h3RawFourierL2HeatApplyNN
        ν hν r (-U)
      =
    - h3RawFourierL2HeatApplyNN
        ν hν r U := by
  change
    h3RawFourierL2HeatCLM ν hν r (-U)
      =
    - h3RawFourierL2HeatCLM ν hν r U
  exact map_neg
    (h3RawFourierL2HeatCLM ν hν r) U

/-- Positive retarded quotient-safe forcing kernel at fixed final elapsed time
`q`. -/
noncomputable def h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
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
    (q s : ℝ) :
    H3RawFourierL2FinVectorState :=
  h3RawFourierL2HeatApplyNN
    1 zero_le_one
    (Real.toNNReal (q - s))
    (h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2Vector
      hNS ht htau hEnd hE hTail hEndpoint s)

/-- For every fixed final time, the retarded forcing kernel is globally
strongly continuous. -/
theorem continuous_h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
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
        hNS ht hEnd hTail) :
    Continuous
      (h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
        hNS ht htau.le hEnd hE hTail hEndpoint q) := by
  let Tm : ℝ → ℝ≥0 :=
    fun s => Real.toNNReal (q - s)

  let F : ℝ → H3RawFourierL2FinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2Vector
      hNS ht htau.le hEnd hE hTail hEndpoint

  have hSub :
      Continuous
        (fun s : ℝ => q - s) :=
    continuous_const.sub continuous_id

  have hTm :
      Continuous Tm := by
    dsimp only [Tm]
    exact continuous_real_toNNReal.comp hSub

  have hF :
      Continuous F := by
    dsimp only [F]
    exact
      continuous_h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2Vector
        hNS ht htau hEnd hE hTail hEndpoint

  rw [continuous_iff_continuousAt]
  intro s

  change
    Tendsto
      (fun y : ℝ =>
        h3RawFourierL2HeatApplyNN
          1 zero_le_one
          (Tm y) (F y))
      (𝓝 s)
      (𝓝
        (h3RawFourierL2HeatApplyNN
          1 zero_le_one
          (Tm s) (F s)))

  exact
    tendsto_h3RawFourierL2HeatApplyNN_moving
      1 zero_le_one
      hTm.continuousAt
      hF.continuousAt

/-- The retarded forcing kernel is Bochner interval-integrable on every finite
elapsed interval. -/
theorem h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal_intervalIntegrable
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
        hNS ht hEnd hTail) :
    IntervalIntegrable
      (h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
        hNS ht htau.le hEnd hE hTail hEndpoint q)
      volume
      0
      q := by
  exact
    (continuous_h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
      hNS ht htau hEnd hE hTail hEndpoint).intervalIntegrable
      0 q

/-- For fixed `q`, the quotient-safe interaction path is globally strongly
continuous. -/
theorem continuous_h3PreterminalTailCanonicalRawFourierL2InteractionReal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
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
      (h3PreterminalTailCanonicalRawFourierL2InteractionReal
        hNS ht htau hEnd hE hTail hEndpoint q) := by
  let Tm : ℝ → ℝ≥0 :=
    fun s => Real.toNNReal (q - s)

  let D : ℝ → H3RawFourierL2FinVectorState :=
    h3PreterminalTailCanonicalRawFourierL2VelocityReal
      hNS ht htau hEnd hE hTail hEndpoint

  have hSub :
      Continuous
        (fun s : ℝ => q - s) :=
    continuous_const.sub continuous_id

  have hTm :
      Continuous Tm := by
    dsimp only [Tm]
    exact continuous_real_toNNReal.comp hSub

  have hD :
      Continuous D := by
    dsimp only [D]
    exact
      continuous_h3PreterminalTailCanonicalRawFourierL2VelocityReal
        hNS ht htau hEnd hE hTail hEndpoint

  rw [continuous_iff_continuousAt]
  intro s

  change
    Tendsto
      (fun y : ℝ =>
        h3RawFourierL2HeatApplyNN
          1 zero_le_one
          (Tm y) (D y))
      (𝓝 s)
      (𝓝
        (h3RawFourierL2HeatApplyNN
          1 zero_le_one
          (Tm s) (D s)))

  exact
    tendsto_h3RawFourierL2HeatApplyNN_moving
      1 zero_le_one
      hTm.continuousAt
      hD.continuousAt

/-- The interaction derivative is exactly the negative positive-retarded
forcing kernel. -/
theorem h3PreterminalTailCanonicalRawFourierL2InteractionReal_hasDerivWithinAt_right_neg_retardedForcing_of_integralEvolution
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
    (hEvolution :
      H3PreterminalTailCanonicalRawFourierL2IntegralEvolutionOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint)
    (hq : q ∈ Set.Ioo (0 : ℝ) tau)
    (hs : s ∈ Set.Ioo (0 : ℝ) q) :
    HasDerivWithinAt
      (h3PreterminalTailCanonicalRawFourierL2InteractionReal
        hNS ht htau.le hEnd hE hTail hEndpoint q)
      (- h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
        hNS ht htau.le hEnd hE hTail hEndpoint q s)
      (Set.Ioi s)
      s := by
  have hDerivative :=
    h3PreterminalTailCanonicalRawFourierL2InteractionReal_hasDerivWithinAt_right_of_integralEvolution
      hNS ht htau hEnd hE hTail hEndpoint hEvolution hq hs

  simpa only [
    h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal,
    h3RawFourierL2HeatApplyNN_neg
  ] using hDerivative

/-- FTC for the quotient-safe interaction picture. -/
theorem h3PreterminalTailCanonicalRawFourierL2InteractionReal_sub_eq_neg_retardedForcingIntegral_of_integralEvolution
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
    h3PreterminalTailCanonicalRawFourierL2InteractionReal
          hNS ht htau.le hEnd hE hTail hEndpoint q q
        -
      h3PreterminalTailCanonicalRawFourierL2InteractionReal
          hNS ht htau.le hEnd hE hTail hEndpoint q 0
      =
    -
      ∫ s in (0 : ℝ)..q,
        h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
          hNS ht htau.le hEnd hE hTail hEndpoint q s := by
  let I : ℝ → H3RawFourierL2FinVectorState :=
    h3PreterminalTailCanonicalRawFourierL2InteractionReal
      hNS ht htau.le hEnd hE hTail hEndpoint q

  let R : ℝ → H3RawFourierL2FinVectorState :=
    h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
      hNS ht htau.le hEnd hE hTail hEndpoint q

  have hIContinuous :
      ContinuousOn I (Set.Icc (0 : ℝ) q) :=
    (continuous_h3PreterminalTailCanonicalRawFourierL2InteractionReal
      hNS ht htau.le hEnd hE hTail hEndpoint).continuousOn

  have hRight :
      ∀ s ∈ Set.Ioo (0 : ℝ) q,
        HasDerivWithinAt
          I
          (-R s)
          (Set.Ioi s)
          s := by
    intro s hs
    dsimp only [I, R]
    exact
      h3PreterminalTailCanonicalRawFourierL2InteractionReal_hasDerivWithinAt_right_neg_retardedForcing_of_integralEvolution
        hNS ht htau hEnd hE hTail hEndpoint hEvolution hq hs

  have hIntegrable :
      IntervalIntegrable
        (fun s : ℝ => -R s)
        volume
        0
        q := by
    have hR :=
      h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal_intervalIntegrable
        hNS ht htau hEnd hE hTail hEndpoint
        (q := q)
    dsimp only [R]
    exact hR.neg

  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      hq.1.le
      hIContinuous
      hRight
      hIntegrable

  dsimp only [I, R] at hFTC

  rw [intervalIntegral.integral_neg] at hFTC

  exact hFTC.symm

/-- At final interaction time, the backward heat lag vanishes. -/
@[simp]
theorem h3PreterminalTailCanonicalRawFourierL2InteractionReal_final
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 ≤ tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail) :
    h3PreterminalTailCanonicalRawFourierL2InteractionReal
        hNS ht htau hEnd hE hTail hEndpoint q q
      =
    h3PreterminalTailCanonicalRawFourierL2VelocityReal
      hNS ht htau hEnd hE hTail hEndpoint q := by
  unfold h3PreterminalTailCanonicalRawFourierL2InteractionReal
  simp

/-- At interaction time zero, the path is the final-time heat evolution of the
retained canonical spectral anchor. -/
theorem h3PreterminalTailCanonicalRawFourierL2InteractionReal_zero
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
        hNS ht hEnd hTail) :
    h3PreterminalTailCanonicalRawFourierL2InteractionReal
        hNS ht htau.le hEnd hE hTail hEndpoint q 0
      =
    h3RawFourierL2HeatApplyNN
      1 zero_le_one
      (Real.toNNReal q)
      (h3SpectralFinVectorRawFourierL2
        (h3PreterminalCanonicalAnchorSpectralState
          hNS
          ht
          (canonicalH3TailDataFrom_at_anchor ht hTail).1)) := by
  unfold h3PreterminalTailCanonicalRawFourierL2InteractionReal
  rw [sub_zero]

  change
    h3RawFourierL2HeatApplyNN
        1 zero_le_one
        (Real.toNNReal q)
        (h3SpectralFinVectorRawFourierL2
          (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
            hNS ht htau.le hEnd hE hTail hEndpoint 0))
      =
    h3RawFourierL2HeatApplyNN
      1 zero_le_one
      (Real.toNNReal q)
      (h3SpectralFinVectorRawFourierL2
        (h3PreterminalCanonicalAnchorSpectralState
          hNS
          ht
          (canonicalH3TailDataFrom_at_anchor ht hTail).1))

  rw [
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_zero
      hNS ht htau hEnd hE hTail hEndpoint
  ]

/-- Conditional quotient-safe raw Fourier `L²` variation-of-constants formula
for every strict positive target time inside the elapsed interval. -/
theorem h3PreterminalTailCanonicalRawFourierL2VariationOfConstants_of_integralEvolution
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
    ∫ s in (0 : ℝ)..q,
      h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
        hNS ht htau.le hEnd hE hTail hEndpoint q s := by
  have hFTC :=
    h3PreterminalTailCanonicalRawFourierL2InteractionReal_sub_eq_neg_retardedForcingIntegral_of_integralEvolution
      hNS ht htau hEnd hE hTail hEndpoint hEvolution hq

  rw [
    h3PreterminalTailCanonicalRawFourierL2InteractionReal_final
      hNS ht htau.le hEnd hE hTail hEndpoint,
    h3PreterminalTailCanonicalRawFourierL2InteractionReal_zero
      hNS ht htau hEnd hE hTail hEndpoint
  ] at hFTC

  calc
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
        +
      (h3PreterminalTailCanonicalRawFourierL2VelocityReal
          hNS ht htau.le hEnd hE hTail hEndpoint q
        -
       h3RawFourierL2HeatApplyNN
          1 zero_le_one
          (Real.toNNReal q)
          (h3SpectralFinVectorRawFourierL2
            (h3PreterminalCanonicalAnchorSpectralState
              hNS
              ht
              (canonicalH3TailDataFrom_at_anchor ht hTail).1))) := by
            abel
    _ =
      h3RawFourierL2HeatApplyNN
          1 zero_le_one
          (Real.toNNReal q)
          (h3SpectralFinVectorRawFourierL2
            (h3PreterminalCanonicalAnchorSpectralState
              hNS
              ht
              (canonicalH3TailDataFrom_at_anchor ht hTail).1))
        +
      (-
        ∫ s in (0 : ℝ)..q,
          h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
            hNS ht htau.le hEnd hE hTail hEndpoint q s) := by
              rw [hFTC]
    _ =
      h3RawFourierL2HeatApplyNN
          1 zero_le_one
          (Real.toNNReal q)
          (h3SpectralFinVectorRawFourierL2
            (h3PreterminalCanonicalAnchorSpectralState
              hNS
              ht
              (canonicalH3TailDataFrom_at_anchor ht hTail).1))
        -
      ∫ s in (0 : ℝ)..q,
        h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
          hNS ht htau.le hEnd hE hTail hEndpoint q s := by
            abel

end

end Euclidean
end Bridge
end PrimeTensor
