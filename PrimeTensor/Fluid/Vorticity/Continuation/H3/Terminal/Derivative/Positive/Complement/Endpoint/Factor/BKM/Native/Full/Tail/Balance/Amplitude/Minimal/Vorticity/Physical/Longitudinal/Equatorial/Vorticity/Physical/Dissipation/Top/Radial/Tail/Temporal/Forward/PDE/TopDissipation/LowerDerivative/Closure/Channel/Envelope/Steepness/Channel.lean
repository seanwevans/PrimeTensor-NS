import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.Order.Group.MinMax

/-!
# Freeze one arbitrarily steep resolved physical PDE channel

The global resolved physical PDE envelope is a finite maximum: four named
physical amplitudes for each of three velocity coordinates.

The preceding checkpoint showed that hypothetical nonextension makes this
single global envelope arbitrarily steep on every strict terminal tail.

A maximum cannot create more temporal variation than its inputs.  Mathlib's

    abs_max_sub_max_le_max

makes this exact.  Therefore every steep global-envelope increment is carried
by at least one of the twelve underlying coordinate/channel amplitudes.

Choose increasingly late increments with slope threshold `n`.  The selected
coordinate/channel pair lies in a finite type, so infinite pigeonhole freezes
one pair on a cofinal set of indices.  The shrinking terminal localization and
the thresholds `n -> +∞` then upgrade recurrence to an intrinsic statement:

there is one fixed coordinate and one fixed resolved physical PDE channel whose
own scalar amplitude is arbitrarily steep on every strict terminal tail.

This reconnects the global scalar envelope obstruction to one concrete PDE
channel without adding a new analytic estimate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1200000

local instance resolvedPhysicalPDEChannelFintype :
    Fintype H3TerminalResolvedPhysicalPDEChannel where
  elems :=
    {
      H3TerminalResolvedPhysicalPDEChannel.lowerTemporal,
      H3TerminalResolvedPhysicalPDEChannel.topDissipation,
      H3TerminalResolvedPhysicalPDEChannel.fourthTemporal,
      H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion
    }
  complete := by
    intro channel
    cases channel <;> simp

/-! ## Finite-max increment lemmas -/

private theorem max3_abs_sub_large
    {L a0 a1 a2 b0 b1 b2 : ℝ}
    (h :
      L <
        abs
          (
            max a0 (max a1 a2)
              -
            max b0 (max b1 b2)
          )) :
    L < abs (a0 - b0)
      ∨
    L < abs (a1 - b1)
      ∨
    L < abs (a2 - b2) := by

  have hOuter :
      L <
        max
          (abs (a0 - b0))
          (abs (max a1 a2 - max b1 b2)) :=
    lt_of_lt_of_le
      h
      (abs_max_sub_max_le_max
        a0
        (max a1 a2)
        b0
        (max b1 b2))

  rcases
    (lt_max_iff.mp hOuter)
  with h0 | h12

  · exact
      Or.inl h0

  · have hInner :
        L <
          max
            (abs (a1 - b1))
            (abs (a2 - b2)) :=
      lt_of_lt_of_le
        h12
        (abs_max_sub_max_le_max
          a1 a2 b1 b2)

    rcases
      (lt_max_iff.mp hInner)
    with h1 | h2

    · exact
        Or.inr
          (Or.inl h1)

    · exact
        Or.inr
          (Or.inr h2)

private theorem max4_abs_sub_large
    {L a0 a1 a2 a3 b0 b1 b2 b3 : ℝ}
    (h :
      L <
        abs
          (
            max a0 (max a1 (max a2 a3))
              -
            max b0 (max b1 (max b2 b3))
          )) :
    L < abs (a0 - b0)
      ∨
    L < abs (a1 - b1)
      ∨
    L < abs (a2 - b2)
      ∨
    L < abs (a3 - b3) := by

  have hOuter :
      L <
        max
          (abs (a0 - b0))
          (abs
            (
              max a1 (max a2 a3)
                -
              max b1 (max b2 b3)
            )) :=
    lt_of_lt_of_le
      h
      (abs_max_sub_max_le_max
        a0
        (max a1 (max a2 a3))
        b0
        (max b1 (max b2 b3)))

  rcases
    (lt_max_iff.mp hOuter)
  with h0 | h123

  · exact
      Or.inl h0

  · have hMiddle :
        L <
          max
            (abs (a1 - b1))
            (abs (max a2 a3 - max b2 b3)) :=
      lt_of_lt_of_le
        h123
        (abs_max_sub_max_le_max
          a1
          (max a2 a3)
          b1
          (max b2 b3))

    rcases
      (lt_max_iff.mp hMiddle)
    with h1 | h23

    · exact
        Or.inr
          (Or.inl h1)

    · have hInner :
          L <
            max
              (abs (a2 - b2))
              (abs (a3 - b3)) :=
        lt_of_lt_of_le
          h23
          (abs_max_sub_max_le_max
            a2 a3 b2 b3)

      rcases
        (lt_max_iff.mp hInner)
      with h2 | h3

      · exact
          Or.inr
            (Or.inr
              (Or.inl h2))

      · exact
          Or.inr
            (Or.inr
              (Or.inr h3))

/--
If one increment of the global resolved physical PDE envelope is steeper than a
level `L`, then one of the twelve underlying coordinate/channel amplitudes has
an increment steeper than the same level.
-/
theorem exists_resolvedPhysicalPDEChannelAmplitude_steep_of_envelope_steep
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t L : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hSteep :
      L
        <
      abs
        (
          h3TerminalResolvedPhysicalPDEEnvelope
              hH3 hClass t
            -
          h3TerminalResolvedPhysicalPDEEnvelope
              hH3 hClass s
        )) :
    ∃ j : Fin 3,
      ∃ channel : H3TerminalResolvedPhysicalPDEChannel,
        L
          <
        abs
          (
            h3TerminalResolvedPhysicalPDEChannelAmplitude
                hH3 hClass j channel t
              -
            h3TerminalResolvedPhysicalPDEChannelAmplitude
                hH3 hClass j channel s
          ) := by

  unfold
    h3TerminalResolvedPhysicalPDEEnvelope
    at hSteep

  have hCoordinateCases :=
    max3_abs_sub_large
      hSteep

  rcases
    hCoordinateCases
  with h0 | h1 | h2

  · unfold
      h3TerminalResolvedPhysicalPDECoordinateEnvelope
      at h0

    have hChannelCases :=
      max4_abs_sub_large
        h0

    rcases
      hChannelCases
    with hLower | hTop | hFourth | hSixth

    · exact
        ⟨
          0,
          H3TerminalResolvedPhysicalPDEChannel.lowerTemporal,
          hLower
        ⟩

    · exact
        ⟨
          0,
          H3TerminalResolvedPhysicalPDEChannel.topDissipation,
          hTop
        ⟩

    · exact
        ⟨
          0,
          H3TerminalResolvedPhysicalPDEChannel.fourthTemporal,
          hFourth
        ⟩

    · exact
        ⟨
          0,
          H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion,
          hSixth
        ⟩

  · unfold
      h3TerminalResolvedPhysicalPDECoordinateEnvelope
      at h1

    have hChannelCases :=
      max4_abs_sub_large
        h1

    rcases
      hChannelCases
    with hLower | hTop | hFourth | hSixth

    · exact
        ⟨
          1,
          H3TerminalResolvedPhysicalPDEChannel.lowerTemporal,
          hLower
        ⟩

    · exact
        ⟨
          1,
          H3TerminalResolvedPhysicalPDEChannel.topDissipation,
          hTop
        ⟩

    · exact
        ⟨
          1,
          H3TerminalResolvedPhysicalPDEChannel.fourthTemporal,
          hFourth
        ⟩

    · exact
        ⟨
          1,
          H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion,
          hSixth
        ⟩

  · unfold
      h3TerminalResolvedPhysicalPDECoordinateEnvelope
      at h2

    have hChannelCases :=
      max4_abs_sub_large
        h2

    rcases
      hChannelCases
    with hLower | hTop | hFourth | hSixth

    · exact
        ⟨
          2,
          H3TerminalResolvedPhysicalPDEChannel.lowerTemporal,
          hLower
        ⟩

    · exact
        ⟨
          2,
          H3TerminalResolvedPhysicalPDEChannel.topDissipation,
          hTop
        ⟩

    · exact
        ⟨
          2,
          H3TerminalResolvedPhysicalPDEChannel.fourthTemporal,
          hFourth
        ⟩

    · exact
        ⟨
          2,
          H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion,
          hSixth
        ⟩

/-! ## Fixed-channel steepness -/

/--
One fixed resolved physical PDE channel is arbitrarily steep at `T`.
-/
def H3TerminalResolvedPhysicalPDEChannelArbitrarilySteep
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (channel : H3TerminalResolvedPhysicalPDEChannel) :
    Prop :=
  ∀ c : ℝ,
    c ∈ Set.Ioo a T →
    ∀ K : ℝ,
      0 ≤ K →
      ∃ s : ℝ,
        s ∈ Set.Ioo c T
          ∧
        ∃ t : ℝ,
          t ∈ Set.Ioo c T
            ∧
          K * abs (t - s)
            <
          abs
            (
              h3TerminalResolvedPhysicalPDEChannelAmplitude
                  hH3 hClass j channel t
                -
              h3TerminalResolvedPhysicalPDEChannelAmplitude
                  hH3 hClass j channel s
            )

/--
Under hypothetical nonextension, one fixed coordinate and one fixed resolved
physical PDE channel carry arbitrarily steep temporal increments on every
strict terminal tail.
-/
theorem exists_fixed_resolvedPhysicalPDEChannel_arbitrarilySteep_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
          SmoothContinuationExtension u v T) :
    ∃ j₀ : Fin 3,
      ∃ channel₀ : H3TerminalResolvedPhysicalPDEChannel,
        H3TerminalResolvedPhysicalPDEChannelArbitrarilySteep
          hH3 hClass j₀ channel₀ := by

  have hGlobal :=
    resolvedPhysicalPDEEnvelope_arbitrarilySteep_on_every_terminalTail_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3 hClass hPhysical hCauchy hNoExtension

  have haT :
      a < T :=
    hClass.terminal_start.2

  have hChoice :
      ∀ n : ℕ,
        ∃ j : Fin 3,
          ∃ channel : H3TerminalResolvedPhysicalPDEChannel,
            ∃ s : ℝ,
              ∃ t : ℝ,
                s ∈ Set.Ioo a T
                  ∧
                s ∈
                  Set.Ioo
                    (T - (1 : ℝ) / ((n : ℝ) + 1))
                    T
                  ∧
                t ∈ Set.Ioo a T
                  ∧
                t ∈
                  Set.Ioo
                    (T - (1 : ℝ) / ((n : ℝ) + 1))
                    T
                  ∧
                (n : ℝ) * abs (t - s)
                  <
                abs
                  (
                    h3TerminalResolvedPhysicalPDEChannelAmplitude
                        hH3 hClass j channel t
                      -
                    h3TerminalResolvedPhysicalPDEChannelAmplitude
                        hH3 hClass j channel s
                  ) := by

    intro n

    let ε : ℝ :=
      (1 : ℝ) / ((n : ℝ) + 1)

    have hε :
        0 < ε := by
      dsimp only [ε]
      positivity

    let c : ℝ :=
      max
        ((a + T) / 2)
        (T - ε)

    have hMidAbove :
        a < (a + T) / 2 := by
      linarith

    have hMidBelow :
        (a + T) / 2 < T := by
      linarith

    have hcAbove :
        a < c := by
      dsimp only [c]
      exact
        lt_of_lt_of_le
          hMidAbove
          (le_max_left _ _)

    have hcBelow :
        c < T := by
      dsimp only [c]
      exact
        max_lt
          hMidBelow
          (by linarith)

    have hc :
        c ∈ Set.Ioo a T :=
      ⟨hcAbove, hcBelow⟩

    obtain
      ⟨s, hs, t, ht, hEnvelopeSteep⟩ :=
      hGlobal
        c
        hc
        (n : ℝ)
        (by positivity)

    have hsClass :
        s ∈ Set.Ioo a T :=
      ⟨
        lt_trans hcAbove hs.1,
        hs.2
      ⟩

    have htClass :
        t ∈ Set.Ioo a T :=
      ⟨
        lt_trans hcAbove ht.1,
        ht.2
      ⟩

    have hNearBase :
        T - ε ≤ c := by
      dsimp only [c]
      exact
        le_max_right _ _

    have hsNear :
        s ∈ Set.Ioo (T - ε) T :=
      ⟨
        lt_of_le_of_lt
          hNearBase
          hs.1,
        hs.2
      ⟩

    have htNear :
        t ∈ Set.Ioo (T - ε) T :=
      ⟨
        lt_of_le_of_lt
          hNearBase
          ht.1,
        ht.2
      ⟩

    obtain
      ⟨j, channel, hChannelSteep⟩ :=
      exists_resolvedPhysicalPDEChannelAmplitude_steep_of_envelope_steep
        hH3 hClass hEnvelopeSteep

    refine
      ⟨
        j,
        channel,
        s,
        t,
        hsClass,
        ?_,
        htClass,
        ?_,
        hChannelSteep
      ⟩

    · simpa only [ε] using
        hsNear

    · simpa only [ε] using
        htNear

  choose j channel s t hData using
    hChoice

  let pair :
      ℕ →
        Fin 3 × H3TerminalResolvedPhysicalPDEChannel :=
    fun n =>
      (j n, channel n)

  obtain
    ⟨
      pairStar,
      hInfinite
    ⟩ :=
    Finite.exists_infinite_fiber
      pair

  rw [Set.infinite_coe_iff] at hInfinite

  refine
    ⟨
      pairStar.1,
      pairStar.2,
      ?_
    ⟩

  intro c hc K hK

  have hGap :
      0 < T - c := by
    linarith [hc.2]

  obtain
    ⟨NK : ℕ, hNK⟩ :=
    exists_nat_gt K

  obtain
    ⟨NT : ℕ, hNT⟩ :=
    exists_nat_gt
      (1 / (T - c))

  let N : ℕ :=
    max NK NT

  obtain
    ⟨
      n,
      hnFiber,
      hNn
    ⟩ :=
    Set.Infinite.exists_gt
      hInfinite
      N

  have hPairEq :
      (j n, channel n)
        =
      pairStar := by

    change pair n = pairStar at hnFiber

    simpa only [pair] using
      hnFiber

  have hj :
      j n = pairStar.1 := by

    exact
      congrArg Prod.fst
        hPairEq

  have hChannel :
      channel n = pairStar.2 := by

    exact
      congrArg Prod.snd
        hPairEq

  have hNKn :
      NK ≤ n := by

    exact
      le_trans
        (Nat.le_max_left NK NT)
        (Nat.le_of_lt hNn)

  have hNTn :
      NT ≤ n := by

    exact
      le_trans
        (Nat.le_max_right NK NT)
        (Nat.le_of_lt hNn)

  have hSlopeBase :
      K < (n : ℝ) := by

    exact
      lt_of_lt_of_le
        hNK
        (by exact_mod_cast hNKn)

  have hNTnReal :
      (NT : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hNTn

  have hDen :
      0 < (n : ℝ) + 1 := by
    positivity

  have hReciprocalDen :
      1 / (T - c)
        <
      (n : ℝ) + 1 := by

    exact
      lt_trans
        hNT
        (lt_of_le_of_lt
          hNTnReal
          (by linarith))

  have hMul :
      1
        <
      ((n : ℝ) + 1) * (T - c) :=
    (div_lt_iff₀ hGap).1
      hReciprocalDen

  have hSmall :
      (1 : ℝ) / ((n : ℝ) + 1)
        <
      T - c := by

    exact
      (div_lt_iff₀ hDen).2
        (by
          simpa only [mul_comm, one_mul] using
            hMul)

  have hTailStart :
      c
        <
      T - (1 : ℝ) / ((n : ℝ) + 1) := by
    linarith

  rcases
    hData n
  with
    ⟨
      hsClass,
      hsNear,
      htClass,
      htNear,
      hSteep
    ⟩

  have hsTail :
      s n ∈ Set.Ioo c T :=
    ⟨
      lt_trans
        hTailStart
        hsNear.1,
      hsNear.2
    ⟩

  have htTail :
      t n ∈ Set.Ioo c T :=
    ⟨
      lt_trans
        hTailStart
        htNear.1,
      htNear.2
    ⟩

  rw [
    hj,
    hChannel
  ] at hSteep

  have hScale :
      K * abs (t n - s n)
        ≤
      (n : ℝ) * abs (t n - s n) :=
    mul_le_mul_of_nonneg_right
      (le_of_lt hSlopeBase)
      (abs_nonneg (t n - s n))

  exact
    ⟨
      s n,
      hsTail,
      t n,
      htTail,
      lt_of_le_of_lt
        hScale
        hSteep
    ⟩

/--
Neutral fixed-channel steepness formulation.

Either the path extends smoothly through `T`, or one fixed coordinate and one
fixed resolved physical PDE channel is arbitrarily steep on every strict
terminal tail.
-/
theorem smoothContinuationExtension_or_fixed_resolvedPhysicalPDEChannel_arbitrarilySteep
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      ∃ j₀ : Fin 3,
        ∃ channel₀ : H3TerminalResolvedPhysicalPDEChannel,
          H3TerminalResolvedPhysicalPDEChannelArbitrarilySteep
            hH3 hClass j₀ channel₀
    ) := by

  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl hExtension

  · exact
      Or.inr
        (
          exists_fixed_resolvedPhysicalPDEChannel_arbitrarilySteep_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
            hH3 hClass hPhysical hCauchy hExtension
        )

end

end Euclidean
end Bridge
end PrimeTensor
