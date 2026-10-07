import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Integral.Majorant

/-!
# Canonical interval-integral obstruction

The synchronized temporal oscillation already gives one fixed positive gap
between the natural top-dissipation radial tails at the canonical time pair

    σ (m (q n)),  σ n

and at the common cutoff `q n + 1`.

Therefore every scalar profile that majorizes all natural-tail increments must
carry at least that fixed amount of absolute interval integral on each of these
canonical intervals.  In particular, no such profile can have terminal
interval integrals vanishing at `T`.

This is the exact noncircular dynamic consequence of the canonical oscillation:
no integrability assumption on the scalar profile is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1200000

/--
Every common scalar increment majorant has a fixed nonvanishing interval
integral along one pair of subsequences of a prescribed canonical terminal
sequence.
-/
def H3TerminalPhysicalTopDissipationNaturalRadialTailCanonicalIntervalIntegralObstructionSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ m q : ℕ → ℕ,
      Tendsto m atTop atTop
        ∧
      Tendsto q atTop atTop
        ∧
      ∃ hσ :
        ∀ n : ℕ,
          σ n ∈ Set.Ioo a T,
        Tendsto σ atTop (𝓝 T)
          ∧
        Tendsto
          (fun n : ℕ => σ (m (q n)))
          atTop
          (𝓝 T)
          ∧
        ∀ g : ℝ → ℝ,
          H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIncrementMajorizedBy
              hH3 hClass g
            →
          ∀ n : ℕ,
            δ
              ≤
            abs
              (
                ∫ r in
                    σ (m (q n))..σ n,
                  g r
              )

/--
A synchronized canonical temporal oscillation forces the interval-integral
obstruction on the same `σ`, `m`, and `q`.
-/
theorem canonicalIntervalIntegralObstructionSubsequenceOf_of_temporalOscillationSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hOsc :
      H3TerminalPhysicalTopDissipationNaturalRadialTailTemporalOscillationSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalTopDissipationNaturalRadialTailCanonicalIntervalIntegralObstructionSubsequenceOf
      hH3 hClass σ := by

  obtain
    ⟨
      δ,
      hδ,
      m,
      q,
      hmTop,
      hqTop,
      hσ,
      hSigma,
      hSigmaMQ,
      hGap
    ⟩ :=
    hOsc

  refine
    ⟨
      δ,
      hδ,
      m,
      q,
      hmTop,
      hqTop,
      hσ,
      hSigma,
      hSigmaMQ,
      ?_
    ⟩

  intro g hMajorant n

  exact
    (hGap n).trans
      (
        hMajorant
          (σ (m (q n)))
          (hσ (m (q n)))
          (σ n)
          (hσ n)
          (q n)
      )

/--
Any scalar profile that majorizes every natural radial-tail increment fails
terminal interval-integral vanishing, witnessed by the canonical time pairs.
-/
theorem not_scalarIntervalIntegralVanishingAtEndpoint_of_canonicalIntervalIntegralObstructionSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hObs :
      H3TerminalPhysicalTopDissipationNaturalRadialTailCanonicalIntervalIntegralObstructionSubsequenceOf
        hH3 hClass σ)
    {g : ℝ → ℝ}
    (hMajorant :
      H3TerminalPhysicalTopDissipationNaturalRadialTailUniformIncrementMajorizedBy
        hH3 hClass g) :
    ¬ H3TerminalScalarIntervalIntegralVanishingAtEndpoint a T g := by

  intro hVanishing

  obtain
    ⟨
      δ,
      hδ,
      m,
      q,
      _hmTop,
      _hqTop,
      hσ,
      hSigma,
      hSigmaMQ,
      hLower
    ⟩ :=
    hObs

  obtain
    ⟨
      η,
      hη,
      hSmall
    ⟩ :=
    hVanishing
      δ
      hδ

  have hNearAnchor :
      ∀ᶠ n : ℕ in atTop,
        dist (σ n) T < η := by

    have hBall :
        Metric.ball T η ∈ 𝓝 T :=
      Metric.ball_mem_nhds
        T
        hη

    have hEventually :=
      hSigma.eventually
        hBall

    filter_upwards [hEventually] with n hn

    simpa only [
      Metric.mem_ball,
      dist_comm
    ] using hn

  have hNearEscape :
      ∀ᶠ n : ℕ in atTop,
        dist (σ (m (q n))) T < η := by

    have hBall :
        Metric.ball T η ∈ 𝓝 T :=
      Metric.ball_mem_nhds
        T
        hη

    have hEventually :=
      hSigmaMQ.eventually
        hBall

    filter_upwards [hEventually] with n hn

    simpa only [
      Metric.mem_ball,
      dist_comm
    ] using hn

  obtain
    ⟨
      n,
      hAnchorNear,
      hEscapeNear
    ⟩ :=
    (hNearAnchor.and hNearEscape).exists

  have hUpper :
      abs
          (
            ∫ r in
                σ (m (q n))..σ n,
              g r
          )
        <
      δ :=
    hSmall
      (σ (m (q n)))
      (hσ (m (q n)))
      (σ n)
      (hσ n)
      hEscapeNear
      hAnchorNear

  exact
    (not_lt_of_ge
      (hLower g hMajorant n))
      hUpper

/--
The final resolved-PDE canonical witness carries a fixed interval-integral
obstruction for every common scalar majorant of the natural top-dissipation
radial-tail increments.
-/
theorem exists_fixed_terminalSequence_with_canonicalTopDissipationIntervalIntegralObstruction_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ k : ℕ → ℕ,
      StrictMono k
        ∧
      Tendsto
        (
          fun n : ℕ =>
            (1 : ℝ) / (((k n : ℕ) : ℝ) + 1)
        )
        atTop
        (𝓝 0)
        ∧
      ∃ σ : ℕ → ℝ,
        ∃ hσ :
          ∀ n : ℕ,
            σ n ∈ Set.Ioo a T,
          Tendsto σ atTop (𝓝 T)
            ∧
          (
            ∀ n : ℕ,
              ENNReal.ofReal (ε ^ 2 / 64)
                <
              16 *
                h3TerminalPhysicalDissipationBadConeHighRadialMass
                  hH3
                  i
                  ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
                  1
                  (σ n)
                  ⟨
                    lt_trans hClass.terminal_start.1
                      (hσ n).1,
                    (hσ n).2
                  ⟩
          )
            ∧
          H3TerminalPhysicalTopDissipationNaturalRadialTailCanonicalIntervalIntegralObstructionSubsequenceOf
            hH3 hClass σ := by

  obtain
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hOsc
    ⟩ :=
    exists_fixed_terminalSequence_with_canonicalTopDissipationTemporalOscillation_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε

  have hObs :
      H3TerminalPhysicalTopDissipationNaturalRadialTailCanonicalIntervalIntegralObstructionSubsequenceOf
        hH3 hClass σ :=
    canonicalIntervalIntegralObstructionSubsequenceOf_of_temporalOscillationSubsequenceOf
      hH3
      hClass
      σ
      hOsc

  exact
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hObs
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
