import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing.Pointwise.Component.Representative
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch

/-!
# Canonical adjacent-q forcing branch

The fixed raw third-radial forcing mass carries the canonical reciprocal-time
rate.  The interpolation inequality

    cubic₃ ≤ mass₂ + mass₄

therefore forces one adjacent square-gradient order to carry half of that
scale.  A finite two-channel extraction freezes the order while preserving the
canonical forcing coordinate, points, and shrinking time intervals.

The result is neutral: either the second-q mass or the fourth-q mass is the
persistent canonical escape channel.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalCanonicalAdjacentQ
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1800000

def H3TerminalPhysicalTopDissipationFixedThirdRadialForcingAdjacentQCanonicalRateEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ j₀ : Fin 3,
      ∃ m q φ ψ : ℕ → ℕ,
        Tendsto m atTop atTop
          ∧
        Tendsto q atTop atTop
          ∧
        StrictMono φ
          ∧
        StrictMono ψ
          ∧
        ∃ s r : ℕ → ℝ,
          ∃ hs :
            ∀ n : ℕ,
              s n ∈ Set.Ioo a T,
            ∃ hσ :
              ∀ n : ℕ,
                σ n ∈ Set.Ioo a T,
              Tendsto
                  (fun n : ℕ => s (φ (ψ n)))
                  atTop
                  (𝓝 T)
                ∧
              Tendsto
                  (fun n : ℕ => σ (m (q (φ (ψ n)))))
                  atTop
                  (𝓝 T)
                ∧
              (
                ∀ n : ℕ,
                  s (φ (ψ n))
                    <
                  σ (m (q (φ (ψ n))))
              )
                ∧
              (
                ∀ n : ℕ,
                  r (φ (ψ n)) ∈
                    Set.Icc
                      (s (φ (ψ n)))
                      (σ (m (q (φ (ψ n)))))
              )
                ∧
              Tendsto
                  (fun n : ℕ => r (φ (ψ n)))
                  atTop
                  (𝓝 T)
                ∧
              (
                (
                  (
                    ∀ n : ℕ,
                      δ
                          /
                        (
                          12
                            *
                          (
                            σ (m (q (φ (ψ n))))
                              -
                            s (φ (ψ n))
                          )
                        )
                        <
                      h3TerminalPhysicalTopDissipationForcingSecondQMassPath
                        hH3 hClass j₀ (r (φ (ψ n)))
                  )
                    ∧
                  Tendsto
                    (
                      fun n : ℕ =>
                        h3TerminalPhysicalTopDissipationForcingSecondQMassPath
                          hH3 hClass j₀ (r (φ (ψ n)))
                    )
                    atTop
                    atTop
                )
                  ∨
                (
                  (
                    ∀ n : ℕ,
                      δ
                          /
                        (
                          12
                            *
                          (
                            σ (m (q (φ (ψ n))))
                              -
                            s (φ (ψ n))
                          )
                        )
                        <
                      h3TerminalPhysicalTopDissipationForcingFourthQMassPath
                        hH3 hClass j₀ (r (φ (ψ n)))
                  )
                    ∧
                  Tendsto
                    (
                      fun n : ℕ =>
                        h3TerminalPhysicalTopDissipationForcingFourthQMassPath
                          hH3 hClass j₀ (r (φ (ψ n)))
                    )
                    atTop
                    atTop
                )
              )

theorem fixedThirdRadialForcingAdjacentQCanonicalRateEscapeSubsequenceOf_of_rawFourierMassCanonicalRateEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hRaw :
      H3TerminalPhysicalTopDissipationFixedThirdRadialForcingRawFourierMassCanonicalRateEscapeSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalTopDissipationFixedThirdRadialForcingAdjacentQCanonicalRateEscapeSubsequenceOf
      hH3 hClass σ := by

  obtain
    ⟨
      δ,
      hδ,
      j₀,
      m,
      q,
      φ,
      hmTop,
      hqTop,
      hPhiMono,
      s,
      r,
      hs,
      hσ,
      hsPhi,
      hSigmaPhi,
      hForward,
      hr,
      hrPhi,
      hRawRate,
      hRawTop
    ⟩ :=
    hRaw

  let C : ℝ :=
    (2 * Real.pi) ^ 6

  have hC :
      0 < C := by
    dsimp only [C]
    positivity

  have hrClass :
      ∀ n : ℕ,
        r (φ n) ∈ Set.Ioo a T := by

    intro n

    exact
      ⟨
        lt_of_lt_of_le
          (hs (φ n)).1
          (hr n).1,
        lt_of_le_of_lt
          (hr n).2
          (hσ (m (q (φ n)))).2
      ⟩

  let secondMass : ℕ → ℝ :=
    fun n =>
      h3TerminalPhysicalTopDissipationForcingSecondQMassPath
        hH3 hClass j₀ (r (φ n))

  let fourthMass : ℕ → ℝ :=
    fun n =>
      h3TerminalPhysicalTopDissipationForcingFourthQMassPath
        hH3 hClass j₀ (r (φ n))

  have hRateEither :
      ∀ n : ℕ,
        δ
            /
          (
            12
              *
            (
              σ (m (q (φ n)))
                -
              s (φ n)
            )
          )
          <
        secondMass n
        ∨
        δ
            /
          (
            12
              *
            (
              σ (m (q (φ n)))
                -
              s (φ n)
            )
          )
          <
        fourthMass n := by

    intro n

    have hGap :
        0 <
          σ (m (q (φ n)))
            -
          s (φ n) :=
      sub_pos.mpr
        (hForward n)

    have hGapNe :
        σ (m (q (φ n)))
            -
          s (φ n)
          ≠
        0 :=
      ne_of_gt hGap

    have hCNe :
        C ≠ 0 :=
      ne_of_gt hC

    have hRawN :=
      hRawRate n

    rw [
      h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath_eq
        hH3 hClass (hrClass n) j₀
    ] at hRawN

    have hScaled :
        δ
            /
          (
            6
              *
            (
              σ (m (q (φ n)))
                -
              s (φ n)
            )
          )
          <
        C
          *
        h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassAt
          hH3 hClass (hrClass n) j₀ := by

      have hMul :=
        mul_lt_mul_of_pos_left
          hRawN
          hC

      have hLeft :
          C
              *
            (
              δ
                /
              (
                6
                  *
                C
                  *
                (
                  σ (m (q (φ n)))
                    -
                  s (φ n)
                )
              )
            )
            =
          δ
            /
          (
            6
              *
            (
              σ (m (q (φ n)))
                -
              s (φ n)
            )
          ) := by

        field_simp [hGapNe, hCNe]

      calc
        δ
            /
          (
            6
              *
            (
              σ (m (q (φ n)))
                -
              s (φ n)
            )
          )
            =
          C
              *
            (
              δ
                /
              (
                6
                  *
                C
                  *
                (
                  σ (m (q (φ n)))
                    -
                  s (φ n)
                )
              )
            ) :=
          hLeft.symm

        _ <
          C
            *
          h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassAt
            hH3 hClass (hrClass n) j₀ :=
          hMul

    let M : ℝ :=
      δ
        /
      (
        12
          *
        (
          σ (m (q (φ n)))
            -
          s (φ n)
        )
      )

    have hTwoM :
        2 * M
          =
        δ
          /
        (
          6
            *
          (
            σ (m (q (φ n)))
              -
            s (φ n)
          )
        ) := by

      dsimp only [M]

      field_simp [hGapNe]
      ring

    have hCubicLarge :
        2 * M
          <
        ∫ ξ : H3FourierPoint3,
          h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
            hH3 hClass (hrClass n) j₀ ξ
          ∂(volume : Measure H3FourierPoint3) := by

      rw [
        integral_h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt_eq_two_pi_six_mul_rawThirdRadialMass
          hH3 hClass (hrClass n) j₀
      ]

      dsimp only [C] at hScaled

      rw [hTwoM]

      exact
        hScaled

    have hEither :=
      h3TerminalPhysicalTopDissipationForcingSecondQMassAt_or_fourthQMassAt_gt_of_two_mul_lt_cubic
        hH3
        hClass
        (hrClass n)
        j₀
        hCubicLarge

    rcases hEither with hSecond | hFourth

    · left

      dsimp only [secondMass]

      rw [
        h3TerminalPhysicalTopDissipationForcingSecondQMassPath_eq
          hH3 hClass (hrClass n) j₀
      ]

      simpa only [M] using
        hSecond

    · right

      dsimp only [fourthMass]

      rw [
        h3TerminalPhysicalTopDissipationForcingFourthQMassPath_eq
          hH3 hClass (hrClass n) j₀
      ]

      simpa only [M] using
        hFourth

  have hMaxTop :
      Tendsto
        (fun n : ℕ => max (secondMass n) (fourthMass n))
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    have hRawLarge :
        ∀ᶠ n : ℕ in atTop,
          (2 * M) / C
            <
          h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath
            hH3 hClass j₀ (r (φ n)) :=
      hRawTop.eventually
        (
          eventually_gt_atTop
            ((2 * M) / C)
        )

    filter_upwards [hRawLarge] with n hn

    rw [
      h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath_eq
        hH3 hClass (hrClass n) j₀
    ] at hn

    have hScaled :
        2 * M
          <
        C
          *
        h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassAt
          hH3 hClass (hrClass n) j₀ := by

      have h :=
        (div_lt_iff₀ hC).1
          hn

      simpa only [mul_comm] using
        h

    have hCubicLarge :
        2 * M
          <
        ∫ ξ : H3FourierPoint3,
          h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
            hH3 hClass (hrClass n) j₀ ξ
          ∂(volume : Measure H3FourierPoint3) := by

      rw [
        integral_h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt_eq_two_pi_six_mul_rawThirdRadialMass
          hH3 hClass (hrClass n) j₀
      ]

      simpa only [C] using
        hScaled

    have hEither :=
      h3TerminalPhysicalTopDissipationForcingSecondQMassAt_or_fourthQMassAt_gt_of_two_mul_lt_cubic
        hH3
        hClass
        (hrClass n)
        j₀
        hCubicLarge

    dsimp only [secondMass, fourthMass]

    rw [
      h3TerminalPhysicalTopDissipationForcingSecondQMassPath_eq
        hH3 hClass (hrClass n) j₀,
      h3TerminalPhysicalTopDissipationForcingFourthQMassPath_eq
        hH3 hClass (hrClass n) j₀
    ]

    rcases hEither with hSecond | hFourth

    · exact
        le_trans
          (le_of_lt hSecond)
          (le_max_left _ _)

    · exact
        le_trans
          (le_of_lt hFourth)
          (le_max_right _ _)

  let channel : ℕ → Bool :=
    fun n =>
      decide
        (fourthMass n ≤ secondMass n)

  let selected : ℕ → ℝ :=
    fun n =>
      if channel n = true then
        secondMass n
      else
        fourthMass n

  have hSelectedEqMax :
      ∀ n : ℕ,
        selected n
          =
        max (secondMass n) (fourthMass n) := by

    intro n

    by_cases h :
        fourthMass n ≤ secondMass n

    · have hc :
          channel n = true := by
        simp [channel, h]

      simp [
        selected,
        hc,
        max_eq_left h
      ]

    · have hle :
          secondMass n ≤ fourthMass n :=
        le_of_lt
          (lt_of_not_ge h)

      have hc :
          channel n = false := by
        simp [channel, h]

      simp [
        selected,
        hc,
        max_eq_right hle
      ]

  have hSelectedTop :
      Tendsto selected atTop atTop := by

    have hEq :
        selected
          =
        (fun n : ℕ =>
          max (secondMass n) (fourthMass n)) :=
      funext hSelectedEqMax

    rw [hEq]

    exact
      hMaxTop

  have hRateSelected :
      ∀ n : ℕ,
        δ
            /
          (
            12
              *
            (
              σ (m (q (φ n)))
                -
              s (φ n)
            )
          )
          <
        selected n := by

    intro n

    rw [hSelectedEqMax n]

    rcases hRateEither n with hSecond | hFourth

    · exact
        lt_of_lt_of_le
          hSecond
          (le_max_left _ _)

    · exact
        lt_of_lt_of_le
          hFourth
          (le_max_right _ _)

  have hFrequentlySomeChannel :
      ∃ᶠ n : ℕ in atTop,
        ∃ b : Bool,
          channel n = b :=
    Frequently.of_forall
      (
        fun n =>
          ⟨
            channel n,
            rfl
          ⟩
      )

  obtain
    ⟨b, hChannelFrequently⟩ :=
    (Filter.frequently_exists).1
      hFrequentlySomeChannel

  obtain
    ⟨ψ, hPsiMono, hChannel⟩ :=
    extraction_of_frequently_atTop
      hChannelFrequently

  have hPsiTop :
      Tendsto ψ atTop atTop :=
    hPsiMono.tendsto_atTop

  have hsPhiPsi :
      Tendsto
        (fun n : ℕ => s (φ (ψ n)))
        atTop
        (𝓝 T) :=
    hsPhi.comp
      hPsiTop

  have hSigmaPhiPsi :
      Tendsto
        (fun n : ℕ => σ (m (q (φ (ψ n)))))
        atTop
        (𝓝 T) :=
    hSigmaPhi.comp
      hPsiTop

  have hrPhiPsi :
      Tendsto
        (fun n : ℕ => r (φ (ψ n)))
        atTop
        (𝓝 T) :=
    hrPhi.comp
      hPsiTop

  have hSelectedSubTop :
      Tendsto
        (fun n : ℕ => selected (ψ n))
        atTop
        atTop := by

    change
      Tendsto
        (selected ∘ ψ)
        atTop
        atTop

    exact
      hSelectedTop.comp
        hPsiTop

  have hFixedBranch :
      (
        (
          ∀ n : ℕ,
            δ
                /
              (
                12
                  *
                (
                  σ (m (q (φ (ψ n))))
                    -
                  s (φ (ψ n))
                )
              )
              <
            h3TerminalPhysicalTopDissipationForcingSecondQMassPath
              hH3 hClass j₀ (r (φ (ψ n)))
        )
          ∧
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalPhysicalTopDissipationForcingSecondQMassPath
                hH3 hClass j₀ (r (φ (ψ n)))
          )
          atTop
          atTop
      )
        ∨
      (
        (
          ∀ n : ℕ,
            δ
                /
              (
                12
                  *
                (
                  σ (m (q (φ (ψ n))))
                    -
                  s (φ (ψ n))
                )
              )
              <
            h3TerminalPhysicalTopDissipationForcingFourthQMassPath
              hH3 hClass j₀ (r (φ (ψ n)))
        )
          ∧
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalPhysicalTopDissipationForcingFourthQMassPath
                hH3 hClass j₀ (r (φ (ψ n)))
          )
          atTop
          atTop
      ) := by

    cases b with

    | false =>

        right

        have hRateFourth :
            ∀ n : ℕ,
              δ
                  /
                (
                  12
                    *
                  (
                    σ (m (q (φ (ψ n))))
                      -
                    s (φ (ψ n))
                  )
                )
                <
              h3TerminalPhysicalTopDissipationForcingFourthQMassPath
                hH3 hClass j₀ (r (φ (ψ n))) := by

          intro n

          have hRateSub :=
            hRateSelected
              (ψ n)

          have hEq :
              selected (ψ n)
                =
              fourthMass (ψ n) := by

            simp [
              selected,
              hChannel n
            ]

          rw [hEq] at hRateSub

          simpa only [fourthMass] using
            hRateSub

        have hFourthTop :
            Tendsto
              (
                fun n : ℕ =>
                  h3TerminalPhysicalTopDissipationForcingFourthQMassPath
                    hH3 hClass j₀ (r (φ (ψ n)))
              )
              atTop
              atTop := by

          have hEq :
              (fun n : ℕ => selected (ψ n))
                =
              (fun n : ℕ => fourthMass (ψ n)) := by

            funext n

            simp [
              selected,
              hChannel n
            ]

          have hFourthSub :
              Tendsto
                (fun n : ℕ => fourthMass (ψ n))
                atTop
                atTop := by

            rw [← hEq]

            exact
              hSelectedSubTop

          simpa only [fourthMass] using
            hFourthSub

        exact
          ⟨
            hRateFourth,
            hFourthTop
          ⟩

    | true =>

        left

        have hRateSecond :
            ∀ n : ℕ,
              δ
                  /
                (
                  12
                    *
                  (
                    σ (m (q (φ (ψ n))))
                      -
                    s (φ (ψ n))
                  )
                )
                <
              h3TerminalPhysicalTopDissipationForcingSecondQMassPath
                hH3 hClass j₀ (r (φ (ψ n))) := by

          intro n

          have hRateSub :=
            hRateSelected
              (ψ n)

          have hEq :
              selected (ψ n)
                =
              secondMass (ψ n) := by

            simp [
              selected,
              hChannel n
            ]

          rw [hEq] at hRateSub

          simpa only [secondMass] using
            hRateSub

        have hSecondTop :
            Tendsto
              (
                fun n : ℕ =>
                  h3TerminalPhysicalTopDissipationForcingSecondQMassPath
                    hH3 hClass j₀ (r (φ (ψ n)))
              )
              atTop
              atTop := by

          have hEq :
              (fun n : ℕ => selected (ψ n))
                =
              (fun n : ℕ => secondMass (ψ n)) := by

            funext n

            simp [
              selected,
              hChannel n
            ]

          have hSecondSub :
              Tendsto
                (fun n : ℕ => secondMass (ψ n))
                atTop
                atTop := by

            rw [← hEq]

            exact
              hSelectedSubTop

          simpa only [secondMass] using
            hSecondSub

        exact
          ⟨
            hRateSecond,
            hSecondTop
          ⟩

  exact
    ⟨
      δ,
      hδ,
      j₀,
      m,
      q,
      φ,
      ψ,
      hmTop,
      hqTop,
      hPhiMono,
      hPsiMono,
      s,
      r,
      hs,
      hσ,
      hsPhiPsi,
      hSigmaPhiPsi,
      (fun n => hForward (ψ n)),
      (fun n => hr (ψ n)),
      hrPhiPsi,
      hFixedBranch
    ⟩

theorem exists_fixed_terminalSequence_with_canonicalAdjacentQForcingRateEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
          H3TerminalPhysicalTopDissipationFixedThirdRadialForcingAdjacentQCanonicalRateEscapeSubsequenceOf
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
      hRaw
    ⟩ :=
    exists_fixed_terminalSequence_with_canonicalFixedThirdRadialForcingRawFourierMassRateEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε

  have hAdjacent :
      H3TerminalPhysicalTopDissipationFixedThirdRadialForcingAdjacentQCanonicalRateEscapeSubsequenceOf
        hH3 hClass σ :=
    fixedThirdRadialForcingAdjacentQCanonicalRateEscapeSubsequenceOf_of_rawFourierMassCanonicalRateEscapeSubsequenceOf
      hH3
      hClass
      σ
      hRaw

  exact
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hAdjacent
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
