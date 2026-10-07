import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Cauchy

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

def H3TerminalPhysicalTopDissipationNaturalRadialTailTemporalOscillationSubsequenceOf
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
        ∀ n : ℕ,
          δ
            ≤
          abs
            (
              h3TerminalPhysicalTopDissipationRadialTailMassAt
                  hH3 hClass
                  (σ (m (q n)))
                  (hσ (m (q n)))
                  (((q n : ℕ) : ℝ) + 1)
                -
              h3TerminalPhysicalTopDissipationRadialTailMassAt
                  hH3 hClass
                  (σ n)
                  (hσ n)
                  (((q n : ℕ) : ℝ) + 1)
            )

theorem topDissipationNaturalRadialTailTemporalOscillationSubsequenceOf_of_physicalDissipationRadialEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hσ :
      ∀ n : ℕ,
        σ n ∈ Set.Ioo a T)
    (hSigma :
      Tendsto σ atTop (𝓝 T))
    (hEscape :
      H3TerminalPhysicalDissipationRadialEscapeSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalTopDissipationNaturalRadialTailTemporalOscillationSubsequenceOf
      hH3 hClass σ := by

  obtain
    ⟨
      δ,
      hδ,
      m,
      hmTop,
      S,
      hData,
      _hSigmaM
    ⟩ :=
    hEscape

  let δTop : ℝ :=
    δ / 4

  let δOsc : ℝ :=
    δTop / 2

  have hδOsc :
      0 < δOsc := by
    dsimp only [δOsc, δTop]
    positivity

  have hTopTailLower :
      ∀ j : ℕ,
        δTop
          ≤
        h3TerminalPhysicalTopDissipationRadialTailMassAt
          hH3 hClass
          (σ (m j))
          (hData j).choose
          ((j : ℝ) + 1) := by

    intro j

    obtain
      ⟨
        ht,
        _hNear,
        hSMeas,
        hOutside,
        hMass
      ⟩ :=
      hData j

    have hOne :
        ∀ ξ ∈ S j,
          1 ≤ h3FourierGradientMagnitude ξ := by

      intro ξ hξ

      have hOutsideξ :=
        hOutside hξ

      have hRadial :
          (j : ℝ) + 1
            ≤
          h3FourierGradientMagnitude ξ := by

        change
          ¬
            h3FourierGradientMagnitude ξ
              <
            (j : ℝ) + 1
          at hOutsideξ

        exact
          le_of_not_gt
            hOutsideξ

      have hOneLe :
          1 ≤ (j : ℝ) + 1 := by

        have hj0 :
            0 ≤ (j : ℝ) := by
          exact_mod_cast Nat.zero_le j

        linarith

      exact
        hOneLe.trans
          hRadial

    have hCompare :
        h3TerminalPhysicalDissipationSetMassAt
            hH3 hClass (σ (m j)) ht (S j)
          ≤
        4 *
          h3TerminalPhysicalTopDissipationSetMassAt
            hH3 hClass (σ (m j)) ht (S j) :=
      physicalDissipationSetMass_le_four_mul_topDissipationSetMass_of_one_le_gradientMagnitude
        hH3
        hClass
        ht
        (S j)
        hSMeas
        hOne

    have hTopMass :
        δTop
          ≤
        h3TerminalPhysicalTopDissipationSetMassAt
          hH3 hClass (σ (m j)) ht (S j) := by

      dsimp only [δTop]

      linarith

    have hSetLeTail :
        h3TerminalPhysicalTopDissipationSetMassAt
            hH3 hClass (σ (m j)) ht (S j)
          ≤
        h3TerminalPhysicalTopDissipationRadialTailMassAt
          hH3 hClass (σ (m j)) ht ((j : ℝ) + 1) :=
      h3TerminalPhysicalTopDissipationSetMass_le_radialTailMass
        hH3
        hClass
        ht
        hOutside

    have hFinal :
        δTop
          ≤
        h3TerminalPhysicalTopDissipationRadialTailMassAt
          hH3 hClass (σ (m j)) ht ((j : ℝ) + 1) :=
      hTopMass.trans
        hSetLeTail

    simpa only using hFinal

  have hChoice :
      ∀ n : ℕ,
        ∃ qn : ℕ,
          n ≤ qn
            ∧
          h3TerminalPhysicalTopDissipationRadialTailMassAt
              hH3 hClass
              (σ n)
              (hσ n)
              ((qn : ℝ) + 1)
            <
          δOsc := by

    intro n

    have hFixed :=
      h3TerminalPhysicalTopDissipationRadialTailMass_tendsto_zero_at_fixed_time
        hH3
        hClass
        (hσ n)

    have hEventually :
        ∀ᶠ j : ℕ in atTop,
          h3TerminalPhysicalTopDissipationRadialTailMassAt
              hH3 hClass
              (σ n)
              (hσ n)
              ((j : ℝ) + 1)
            <
          δOsc :=
      hFixed.eventually
        (Iio_mem_nhds hδOsc)

    obtain
      ⟨N, hN⟩ :=
      eventually_atTop.1
        hEventually

    let qn : ℕ :=
      max n N

    refine
      ⟨
        qn,
        ?_,
        ?_
      ⟩

    · dsimp only [qn]
      exact
        le_max_left n N

    · exact
        hN
          qn
          (by
            dsimp only [qn]
            exact le_max_right n N)

  choose q hnq hAnchor using hChoice

  have hqTop :
      Tendsto q atTop atTop := by

    refine
      tendsto_atTop.2 ?_

    intro N

    filter_upwards
      [eventually_ge_atTop N]
      with n hn

    exact
      hn.trans
        (hnq n)

  have hmQTop :
      Tendsto
        (fun n : ℕ => m (q n))
        atTop
        atTop :=
    hmTop.comp
      hqTop

  have hSigmaMQ :
      Tendsto
        (fun n : ℕ => σ (m (q n)))
        atTop
        (𝓝 T) :=
    hSigma.comp
      hmQTop

  have hOsc :
      ∀ n : ℕ,
        δOsc
          ≤
        abs
          (
            h3TerminalPhysicalTopDissipationRadialTailMassAt
                hH3 hClass
                (σ (m (q n)))
                (hσ (m (q n)))
                (((q n : ℕ) : ℝ) + 1)
              -
            h3TerminalPhysicalTopDissipationRadialTailMassAt
                hH3 hClass
                (σ n)
                (hσ n)
                (((q n : ℕ) : ℝ) + 1)
          ) := by

    intro n

    have hEscapeLower :
        δTop
          ≤
        h3TerminalPhysicalTopDissipationRadialTailMassAt
          hH3 hClass
          (σ (m (q n)))
          (hσ (m (q n)))
          (((q n : ℕ) : ℝ) + 1) := by

      have hRaw :=
        hTopTailLower
          (q n)

      simpa only using hRaw

    have hDiff :
        δOsc
          <
        h3TerminalPhysicalTopDissipationRadialTailMassAt
              hH3 hClass
              (σ (m (q n)))
              (hσ (m (q n)))
              (((q n : ℕ) : ℝ) + 1)
          -
        h3TerminalPhysicalTopDissipationRadialTailMassAt
              hH3 hClass
              (σ n)
              (hσ n)
              (((q n : ℕ) : ℝ) + 1) := by

      have hAnchorN :=
        hAnchor n

      dsimp only [δOsc] at hAnchorN ⊢

      linarith [hEscapeLower, hAnchorN]

    exact
      (le_of_lt hDiff).trans
        (le_abs_self _)

  exact
    ⟨
      δOsc,
      hδOsc,
      m,
      q,
      hmTop,
      hqTop,
      hσ,
      hSigma,
      hSigmaMQ,
      hOsc
    ⟩

theorem not_naturalTopDissipationRadialTailUniformTemporalCauchy_of_temporalOscillationSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hOsc :
      H3TerminalPhysicalTopDissipationNaturalRadialTailTemporalOscillationSubsequenceOf
        hH3 hClass σ) :
    ¬
      H3TerminalPhysicalTopDissipationNaturalRadialTailUniformCauchyAtEndpoint
        hH3 hClass := by

  intro hCauchy

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
      hGap
    ⟩ :=
    hOsc

  obtain
    ⟨
      η,
      hη,
      hTemporal
    ⟩ :=
    hCauchy
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

  have hSmall :
      abs
          (
            h3TerminalPhysicalTopDissipationRadialTailMassAt
                hH3 hClass
                (σ (m (q n)))
                (hσ (m (q n)))
                (((q n : ℕ) : ℝ) + 1)
              -
            h3TerminalPhysicalTopDissipationRadialTailMassAt
                hH3 hClass
                (σ n)
                (hσ n)
                (((q n : ℕ) : ℝ) + 1)
          )
        <
      δ := by

    exact
      hTemporal
        (σ (m (q n)))
        (hσ (m (q n)))
        (σ n)
        (hσ n)
        hEscapeNear
        hAnchorNear
        (q n)

  exact
    (not_lt_of_ge (hGap n))
      hSmall

theorem exists_fixed_terminalSequence_with_canonicalTopDissipationTemporalOscillation_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
          H3TerminalPhysicalTopDissipationNaturalRadialTailTemporalOscillationSubsequenceOf
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
      hEscape
    ⟩ :=
    exists_fixed_terminalSequence_with_canonicalPhysicalDissipationRadialEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε

  have hOsc :
      H3TerminalPhysicalTopDissipationNaturalRadialTailTemporalOscillationSubsequenceOf
        hH3 hClass σ :=
    topDissipationNaturalRadialTailTemporalOscillationSubsequenceOf_of_physicalDissipationRadialEscapeSubsequenceOf
      hH3
      hClass
      σ
      hσ
      hSigma
      hEscape

  exact
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hOsc
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
