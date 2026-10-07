import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Local
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Integral.Integrable

/-!
# Full forcing cubic integral escape on the canonical witness

The canonical radial-escape sequence carries a fixed positive amount of
top-order physical dissipation beyond an increasing cutoff.

For each stage choose an explicit earlier anchor near `T`.  At that fixed
anchor the radial tail tends to zero as the cutoff tends to infinity.  Then
choose a sufficiently late canonical escape index so that

* the canonical escape time lies after the anchor, and
* the anchor tail at the selected cutoff is small.

The tail therefore makes a fixed positive forward increase.  The closed
localized PDE estimate

    d/dt tail_n(t) ≤ fullForcingCubicMassProfile(t)

together with local interval integrability forces a fixed positive lower bound
on the integral of the concrete full-forcing cubic profile over those shrinking
terminal intervals.

This is stronger than merely knowing that the profile is not terminal `L¹`:
the nonintegrability is witnessed on intervals whose right endpoint belongs to
the canonical PDE-selected physical-dissipation sequence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2400000

private theorem tendsto_terminal_of_one_div_natSucc_localization_canonicalForcing
    {T : ℝ}
    {s : ℕ → ℝ}
    (hs :
      ∀ n : ℕ,
        s n ∈
          Set.Ioo
            (T - (1 : ℝ) / ((n : ℝ) + 1))
            T) :
    Tendsto s atTop (𝓝 T) := by

  rw [Metric.tendsto_atTop]

  intro ε hε

  obtain
    ⟨N : ℕ, hN⟩ :=
    exists_nat_gt
      (1 / ε)

  refine
    ⟨
      N,
      ?_
    ⟩

  intro n hn

  have hDenN :
      0 < (N : ℝ) + 1 := by
    positivity

  have hInvN :
      (1 : ℝ) / ((n : ℝ) + 1)
        ≤
      1 / ((N : ℝ) + 1) := by

    exact
      one_div_le_one_div_of_le
        hDenN
        (by
          have hCast :
              (N : ℝ) ≤ n := by
            exact_mod_cast hn
          linarith)

  have hSmallN :
      1 / ((N : ℝ) + 1) < ε := by

    have hNPlus :
        1 / ε < (N : ℝ) + 1 := by
      linarith [hN]

    have hMulRaw :
        1 < ((N : ℝ) + 1) * ε :=
      (div_lt_iff₀ hε).1
        hNPlus

    exact
      (div_lt_iff₀ hDenN).2
        (by
          simpa only [mul_comm, one_mul] using hMulRaw)

  have hSmall :
      (1 : ℝ) / ((n : ℝ) + 1) < ε :=
    lt_of_le_of_lt
      hInvN
      hSmallN

  have hLower :=
    (hs n).1

  have hUpper :=
    (hs n).2

  rw [Real.dist_eq]

  have hDiffNonpos :
      s n - T ≤ 0 := by
    linarith

  rw [abs_of_nonpos hDiffNonpos]

  linarith

/--
A fixed positive amount of the concrete full-forcing cubic profile is consumed
on shrinking forward intervals ending at a subsequence of a prescribed
canonical terminal sequence.
-/
def H3TerminalPhysicalTopDissipationFullForcingCubicCanonicalForwardIntegralEscapeSubsequenceOf
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
      ∃ s : ℕ → ℝ,
        ∃ hs :
          ∀ n : ℕ,
            s n ∈ Set.Ioo a T,
          ∃ hσ :
            ∀ n : ℕ,
              σ n ∈ Set.Ioo a T,
            Tendsto s atTop (𝓝 T)
              ∧
            Tendsto
              (fun n : ℕ => σ (m (q n)))
              atTop
              (𝓝 T)
              ∧
            (
              ∀ n : ℕ,
                s n < σ (m (q n))
            )
              ∧
            (
              ∀ n : ℕ,
                δ
                  ≤
                ∫ r in s n..σ (m (q n)),
                  h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
                    hH3 hClass r
            )

/--
A same-witness physical-dissipation radial escape subsequence forces a
concrete full-forcing cubic integral escape on forward shrinking terminal
intervals ending on that canonical lineage.
-/
theorem fullForcingCubicCanonicalForwardIntegralEscapeSubsequenceOf_of_physicalDissipationRadialEscapeSubsequenceOf
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
    H3TerminalPhysicalTopDissipationFullForcingCubicCanonicalForwardIntegralEscapeSubsequenceOf
      hH3 hClass σ := by

  obtain
    ⟨
      δ,
      hδ,
      m,
      hmTop,
      S,
      hData,
      hSigmaM
    ⟩ :=
    hEscape

  have hChoiceData :
      ∀ j : ℕ,
        ∃ ht :
          σ (m j) ∈ Set.Ioo a T,
          dist (σ (m j)) T
              <
            (1 : ℝ) / ((j : ℝ) + 1)
            ∧
          MeasurableSet (S j)
            ∧
          S j
              ⊆
            (h3TerminalRadialFrequencyBelow
                ((j : ℝ) + 1))ᶜ
            ∧
          δ
              ≤
            h3TerminalPhysicalDissipationSetMassAt
              hH3 hClass (σ (m j)) ht (S j) := by

    intro j
    exact hData j

  choose
    ht
    hNear
    hSMeas
    hOutside
    hMass
    using hChoiceData

  let δTop : ℝ :=
    δ / 4

  let δForcing : ℝ :=
    δTop / 2

  have hδForcing :
      0 < δForcing := by
    dsimp only [δForcing, δTop]
    positivity

  have hTopTailLower :
      ∀ j : ℕ,
        δTop
          ≤
        h3TerminalPhysicalTopDissipationRadialTailMassAt
          hH3 hClass
          (σ (m j))
          (ht j)
          ((j : ℝ) + 1) := by

    intro j

    have hOne :
        ∀ ξ ∈ S j,
          1 ≤ h3FourierGradientMagnitude ξ := by

      intro ξ hξ

      have hOutsideξ :=
        hOutside j hξ

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

      have hj0 :
          0 ≤ (j : ℝ) := by
        exact_mod_cast Nat.zero_le j

      linarith

    have hCompare :
        h3TerminalPhysicalDissipationSetMassAt
            hH3 hClass (σ (m j)) (ht j) (S j)
          ≤
        4 *
          h3TerminalPhysicalTopDissipationSetMassAt
            hH3 hClass (σ (m j)) (ht j) (S j) :=
      physicalDissipationSetMass_le_four_mul_topDissipationSetMass_of_one_le_gradientMagnitude
        hH3
        hClass
        (ht j)
        (S j)
        (hSMeas j)
        hOne

    have hTopMass :
        δTop
          ≤
        h3TerminalPhysicalTopDissipationSetMassAt
          hH3 hClass (σ (m j)) (ht j) (S j) := by

      dsimp only [δTop]

      linarith [hMass j]

    have hSetLeTail :
        h3TerminalPhysicalTopDissipationSetMassAt
            hH3 hClass (σ (m j)) (ht j) (S j)
          ≤
        h3TerminalPhysicalTopDissipationRadialTailMassAt
          hH3 hClass
          (σ (m j))
          (ht j)
          ((j : ℝ) + 1) :=
      h3TerminalPhysicalTopDissipationSetMass_le_radialTailMass
        hH3
        hClass
        (ht j)
        (hOutside j)

    exact
      hTopMass.trans
        hSetLeTail

  let s : ℕ → ℝ :=
    fun n =>
      h3BKMKineticTailMidpoint
        (
          max
            a
            (
              T
                -
              (1 : ℝ) / ((n : ℝ) + 1)
            )
        )
        T

  have hsNear :
      ∀ n : ℕ,
        s n ∈
          Set.Ioo
            (T - (1 : ℝ) / ((n : ℝ) + 1))
            T := by

    intro n

    have hInv :
        0 < (1 : ℝ) / ((n : ℝ) + 1) := by
      positivity

    have hMax :
        max
            a
            (
              T
                -
              (1 : ℝ) / ((n : ℝ) + 1)
            )
          <
        T := by

      exact
        max_lt
          hClass.terminal_start.2
          (by linarith)

    have hMid :
        s n
          ∈
        Set.Ioo
          (
            max
              a
              (
                T
                  -
                (1 : ℝ) / ((n : ℝ) + 1)
              )
          )
          T := by

      dsimp only [s]

      exact
        h3BKMKineticTailMidpoint_mem_Ioo
          hMax

    exact
      ⟨
        lt_of_le_of_lt
          (
            le_max_right
              a
              (
                T
                  -
                (1 : ℝ) / ((n : ℝ) + 1)
              )
          )
          hMid.1,
        hMid.2
      ⟩

  have hs :
      ∀ n : ℕ,
        s n ∈ Set.Ioo a T := by

    intro n

    have hInv :
        0 < (1 : ℝ) / ((n : ℝ) + 1) := by
      positivity

    have hMax :
        max
            a
            (
              T
                -
              (1 : ℝ) / ((n : ℝ) + 1)
            )
          <
        T := by

      exact
        max_lt
          hClass.terminal_start.2
          (by linarith)

    have hMid :
        s n
          ∈
        Set.Ioo
          (
            max
              a
              (
                T
                  -
                (1 : ℝ) / ((n : ℝ) + 1)
              )
          )
          T := by

      dsimp only [s]

      exact
        h3BKMKineticTailMidpoint_mem_Ioo
          hMax

    exact
      ⟨
        lt_of_le_of_lt
          (
            le_max_left
              a
              (
                T
                  -
                (1 : ℝ) / ((n : ℝ) + 1)
              )
          )
          hMid.1,
        hMid.2
      ⟩

  have hsTendsto :
      Tendsto s atTop (𝓝 T) :=
    tendsto_terminal_of_one_div_natSucc_localization_canonicalForcing
      hsNear

  have hChoice :
      ∀ n : ℕ,
        ∃ j : ℕ,
          n ≤ j
            ∧
          s n < σ (m j)
            ∧
          h3TerminalPhysicalTopDissipationRadialTailMassAt
              hH3 hClass
              (s n)
              (hs n)
              ((j : ℝ) + 1)
            <
          δForcing := by

    intro n

    have hFixed :=
      h3TerminalPhysicalTopDissipationRadialTailMass_tendsto_zero_at_fixed_time
        hH3
        hClass
        (hs n)

    have hTailSmall :
        ∀ᶠ j : ℕ in atTop,
          h3TerminalPhysicalTopDissipationRadialTailMassAt
              hH3 hClass
              (s n)
              (hs n)
              ((j : ℝ) + 1)
            <
          δForcing :=
      hFixed.eventually
        (Iio_mem_nhds hδForcing)

    have hAfter :
        ∀ᶠ j : ℕ in atTop,
          s n < σ (m j) :=
      (tendsto_order.1 hSigmaM).1
        (s n)
        (hs n).2

    obtain
      ⟨
        j,
        hnj,
        hAfterJ,
        hSmallJ
      ⟩ :=
      (
        (eventually_ge_atTop n).and
          (hAfter.and hTailSmall)
      ).exists

    exact
      ⟨
        j,
        hnj,
        hAfterJ,
        hSmallJ
      ⟩

  choose q hnq hForward hAnchor using hChoice

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

  have hBalance :=
    h3TerminalPhysicalTopDissipationNaturalRadialTailLocalizedPDEBalanceAtEndpoint_closed
      hH3 hClass

  have hLocalDerivative :=
    h3TerminalPhysicalTopDissipationNaturalRadialTailDerivativeLocallyIntervalIntegrable_closed
      hH3 hClass

  have hForcingLower :
      ∀ n : ℕ,
        δForcing
          ≤
        ∫ r in s n..σ (m (q n)),
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass r := by

    intro n

    let j : ℕ :=
      q n

    let t : ℝ :=
      σ (m j)

    let F : ℝ → ℝ :=
      h3TerminalPhysicalTopDissipationNaturalRadialTailPath
        hH3 hClass j

    have htClass :
        t ∈ Set.Ioo a T := by

      dsimp only [t, j]

      exact
        hσ (m (q n))

    have hst :
        s n ≤ t := by

      dsimp only [t, j]

      exact
        (hForward n).le

    have hEscapeLower :
        δTop
          ≤
        h3TerminalPhysicalTopDissipationRadialTailMassAt
          hH3 hClass
          t
          htClass
          ((j : ℝ) + 1) := by

      have hRaw :=
        hTopTailLower
          j

      simpa only [t, j] using
        hRaw

    have hAnchorSmall :
        h3TerminalPhysicalTopDissipationRadialTailMassAt
            hH3 hClass
            (s n)
            (hs n)
            ((j : ℝ) + 1)
          <
        δForcing := by

      simpa only [j] using
        hAnchor n

    have hIncrease :
        δForcing
          <
        h3TerminalPhysicalTopDissipationRadialTailMassAt
              hH3 hClass
              t
              htClass
              ((j : ℝ) + 1)
          -
        h3TerminalPhysicalTopDissipationRadialTailMassAt
              hH3 hClass
              (s n)
              (hs n)
              ((j : ℝ) + 1) := by

      dsimp only [δForcing] at hAnchorSmall ⊢

      linarith [hEscapeLower, hAnchorSmall]

    have hUIccSubset :
        Set.uIcc (s n) t
          ⊆
        Set.Ioo a T := by

      intro r hr

      rw [uIcc_of_le hst] at hr

      exact
        ⟨
          lt_of_lt_of_le
            (hs n).1
            hr.1,
          lt_of_le_of_lt
            hr.2
            htClass.2
        ⟩

    have hDiff :
        ∀ r : ℝ,
          r ∈ Set.uIcc (s n) t
            →
          DifferentiableAt ℝ F r := by

      intro r hr

      dsimp only [F]

      exact
        (hBalance j r (hUIccSubset hr)).1

    have hDerivInterval :
        IntervalIntegrable
          (deriv F)
          volume
          (s n)
          t := by

      dsimp only [F]

      exact
        hLocalDerivative
          j
          (s n)
          (hs n)
          t
          htClass
          hst

    have hProfileInterval :
        IntervalIntegrable
          (
            h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
              hH3 hClass
          )
          volume
          (s n)
          t :=
      h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_intervalIntegrable
        hH3
        hClass
        (hs n)
        htClass

    have hFT :
        (∫ r in s n..t, deriv F r)
          =
        F t - F (s n) := by

      exact
        intervalIntegral.integral_deriv_eq_sub
          hDiff
          hDerivInterval

    have hIntegralUpper :
        (∫ r in s n..t, deriv F r)
          ≤
        ∫ r in s n..t,
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass r := by

      apply
        intervalIntegral.integral_mono_on
          hst
          hDerivInterval
          hProfileInterval

      intro r hr

      have hrClass :
          r ∈ Set.Ioo a T :=
        ⟨
          lt_of_lt_of_le
            (hs n).1
            hr.1,
          lt_of_le_of_lt
            hr.2
            htClass.2
        ⟩

      have hUpper :=
        deriv_h3TerminalPhysicalTopDissipationNaturalRadialTailPath_le_fullForcingCubicMass
          hH3
          hClass
          j
          hrClass

      dsimp only [F]

      calc
        deriv
            (h3TerminalPhysicalTopDissipationNaturalRadialTailPath
              hH3 hClass j)
            r
            ≤
          h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
            hH3 hClass hrClass :=
          hUpper

        _ =
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass r := by

          exact
            (
              h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_eq
                hH3 hClass hrClass
            ).symm

    have hFs :
        F (s n)
          =
        h3TerminalPhysicalTopDissipationRadialTailMassAt
          hH3 hClass
          (s n)
          (hs n)
          ((j : ℝ) + 1) := by

      dsimp only [F]

      exact
        h3TerminalPhysicalTopDissipationNaturalRadialTailPath_eq
          hH3
          hClass
          j
          (hs n)

    have hFt :
        F t
          =
        h3TerminalPhysicalTopDissipationRadialTailMassAt
          hH3 hClass
          t
          htClass
          ((j : ℝ) + 1) := by

      dsimp only [F]

      exact
        h3TerminalPhysicalTopDissipationNaturalRadialTailPath_eq
          hH3
          hClass
          j
          htClass

    rw [hFT] at hIntegralUpper
    rw [hFs, hFt] at hIntegralUpper

    have hStrict :
        δForcing
          <
        ∫ r in s n..t,
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass r :=
      lt_of_lt_of_le
        hIncrease
        hIntegralUpper

    simpa only [t] using
      hStrict.le

  exact
    ⟨
      δForcing,
      hδForcing,
      m,
      q,
      hmTop,
      hqTop,
      s,
      hs,
      hσ,
      hsTendsto,
      hSigmaMQ,
      hForward,
      hForcingLower
    ⟩

/--
The explicit canonical forcing-integral escape rules out terminal `L¹`
integrability of the full-forcing cubic profile directly.
-/
theorem not_integrableOn_fullForcingCubicMassProfile_of_canonicalForwardIntegralEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hEscape :
      H3TerminalPhysicalTopDissipationFullForcingCubicCanonicalForwardIntegralEscapeSubsequenceOf
        hH3 hClass σ) :
    ¬
      IntegrableOn
        (
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass
        )
        (Set.Ioo a T)
        volume := by

  intro hIntegrable

  obtain
    ⟨
      δ,
      hδ,
      m,
      q,
      _hmTop,
      _hqTop,
      s,
      hs,
      hσ,
      hsTendsto,
      hSigmaMQ,
      _hForward,
      hLower
    ⟩ :=
    hEscape

  have hVanishing :=
    scalarIntervalIntegralVanishingAtEndpoint_of_integrableOn
      hClass.terminal_start.2
      hIntegrable

  obtain
    ⟨
      η,
      hη,
      hSmall
    ⟩ :=
    hVanishing
      δ
      hδ

  have hNearS :
      ∀ᶠ n : ℕ in atTop,
        dist (s n) T < η := by

    have hBall :
        Metric.ball T η ∈ 𝓝 T :=
      Metric.ball_mem_nhds
        T
        hη

    have hEventually :=
      hsTendsto.eventually
        hBall

    filter_upwards [hEventually] with n hn

    simpa only [
      Metric.mem_ball,
      dist_comm
    ] using hn

  have hNearT :
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
      hNearSN,
      hNearTN
    ⟩ :=
    (hNearS.and hNearT).exists

  have hUpper :
      abs
          (
            ∫ r in s n..σ (m (q n)),
              h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
                hH3 hClass r
          )
        <
      δ :=
    hSmall
      (s n)
      (hs n)
      (σ (m (q n)))
      (hσ (m (q n)))
      hNearSN
      hNearTN

  have hAbsLower :
      δ
        ≤
      abs
        (
          ∫ r in s n..σ (m (q n)),
            h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
              hH3 hClass r
        ) :=
    (hLower n).trans
      (le_abs_self _)

  exact
    (not_lt_of_ge hAbsLower)
      hUpper

/--
The final resolved-PDE canonical witness has shrinking forward intervals ending
on its radial-escape subsequence where the concrete full-forcing cubic profile
carries one fixed positive integral.
-/
theorem exists_fixed_terminalSequence_with_canonicalFullForcingCubicForwardIntegralEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
          H3TerminalPhysicalTopDissipationFullForcingCubicCanonicalForwardIntegralEscapeSubsequenceOf
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
      hRadialEscape
    ⟩ :=
    exists_fixed_terminalSequence_with_canonicalPhysicalDissipationRadialEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε

  have hForcing :
      H3TerminalPhysicalTopDissipationFullForcingCubicCanonicalForwardIntegralEscapeSubsequenceOf
        hH3 hClass σ :=
    fullForcingCubicCanonicalForwardIntegralEscapeSubsequenceOf_of_physicalDissipationRadialEscapeSubsequenceOf
      hH3
      hClass
      σ
      hσ
      hSigma
      hRadialEscape

  exact
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hForcing
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
