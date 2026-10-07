import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Radial.Temporal.Integral.Forcing
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Local

/-!
# Pointwise cubic-forcing rate on the canonical shrinking intervals

The preceding checkpoint gives a fixed `δ > 0` and shrinking forward
intervals

    [s n, σ (m (q n))]

on which the concrete full-forcing cubic profile has integral at least `δ`.

Because the interval width tends to zero, each such interval contains a point
where the forcing profile is at least on the reciprocal-width scale.  We use
the deliberately comfortable factor two

    δ / (2 * (σ (m (q n)) - s n)).

That threshold tends to `+∞`, so the selected forcing values tend to `+∞`.
The selected point remains inside the exact canonical forcing interval; no new
terminal branch is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

/--
One point inside every canonical forcing interval exceeds the reciprocal-width
forcing scale, and the selected forcing amplitudes tend to `+∞`.
-/
def H3TerminalPhysicalTopDissipationFullForcingCubicCanonicalPointwiseRateEscapeSubsequenceOf
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
      ∃ s r : ℕ → ℝ,
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
                r n ∈
                  Set.Icc
                    (s n)
                    (σ (m (q n)))
            )
              ∧
            Tendsto r atTop (𝓝 T)
              ∧
            (
              ∀ n : ℕ,
                δ
                    /
                  (
                    2
                      *
                    (
                      σ (m (q n))
                        -
                      s n
                    )
                  )
                  <
                h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
                  hH3 hClass (r n)
            )
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
                    hH3 hClass (r n)
              )
              atTop
              atTop

/--
A canonical fixed-positive forcing integral on shrinking intervals yields a
pointwise reciprocal-width forcing rate on those exact intervals.
-/
theorem fullForcingCubicCanonicalPointwiseRateEscapeSubsequenceOf_of_forwardIntegralEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hEscape :
      H3TerminalPhysicalTopDissipationFullForcingCubicCanonicalForwardIntegralEscapeSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalTopDissipationFullForcingCubicCanonicalPointwiseRateEscapeSubsequenceOf
      hH3 hClass σ := by

  obtain
    ⟨
      δ,
      hδ,
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
      hIntegralLower
    ⟩ :=
    hEscape

  let t : ℕ → ℝ :=
    fun n =>
      σ (m (q n))

  have ht :
      ∀ n : ℕ,
        t n ∈ Set.Ioo a T := by

    intro n

    dsimp only [t]

    exact
      hσ (m (q n))

  have htTendsto :
      Tendsto t atTop (𝓝 T) := by

    simpa only [t] using
      hSigmaMQ

  have hGapPos :
      ∀ n : ℕ,
        0 < t n - s n := by

    intro n

    exact
      sub_pos.mpr
        (by
          dsimp only [t]
          exact hForward n)

  have hPoint :
      ∀ n : ℕ,
        ∃ r : ℝ,
          r ∈ Set.Icc (s n) (t n)
            ∧
          δ / (2 * (t n - s n))
            <
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass r := by

    intro n

    let C : ℝ :=
      δ / (2 * (t n - s n))

    have hCInt :
        IntervalIntegrable
          (fun _ : ℝ => C)
          volume
          (s n)
          (t n) :=
      intervalIntegrable_const

    have hProfileInt :
        IntervalIntegrable
          (
            h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
              hH3 hClass
          )
          volume
          (s n)
          (t n) :=
      h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_intervalIntegrable
        hH3
        hClass
        (hs n)
        (ht n)

    by_contra hNoPoint

    have hPointwise :
        ∀ r ∈ Set.Icc (s n) (t n),
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
              hH3 hClass r
            ≤
          C := by

      intro r hr

      apply le_of_not_gt

      intro hGt

      exact
        hNoPoint
          ⟨
            r,
            hr,
            by
              simpa only [C] using hGt
          ⟩

    have hIntegralUpper :
        (∫ r in s n..t n,
            h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
              hH3 hClass r)
          ≤
        ∫ _r in s n..t n, C := by

      exact
        intervalIntegral.integral_mono_on
          (le_of_lt (sub_pos.mp (hGapPos n)))
          hProfileInt
          hCInt
          hPointwise

    have hConstIntegral :
        (∫ _r in s n..t n, C)
          =
        (t n - s n) * C := by

      simp

    have hCancel :
        (t n - s n) * C
          =
        δ / 2 := by

      dsimp only [C]

      have hGapNe :
          t n - s n ≠ 0 :=
        ne_of_gt
          (hGapPos n)

      field_simp [hGapNe]

    have hUpper :
        (∫ r in s n..t n,
            h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
              hH3 hClass r)
          ≤
        δ / 2 := by

      calc
        (∫ r in s n..t n,
            h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
              hH3 hClass r)
            ≤
          ∫ _r in s n..t n, C :=
          hIntegralUpper

        _ =
          (t n - s n) * C :=
          hConstIntegral

        _ =
          δ / 2 :=
          hCancel

    have hLower :
        δ
          ≤
        ∫ r in s n..t n,
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass r := by

      have hRaw :=
        hIntegralLower n

      simpa only [t] using
        hRaw

    linarith

  choose r hr hRate using hPoint

  have hrClass :
      ∀ n : ℕ,
        r n ∈ Set.Ioo a T := by

    intro n

    exact
      ⟨
        lt_of_lt_of_le
          (hs n).1
          (hr n).1,
        lt_of_le_of_lt
          (hr n).2
          (ht n).2
      ⟩

  have hrTendsto :
      Tendsto r atTop (𝓝 T) := by

    rw [Metric.tendsto_atTop]

    intro ε hε

    have hEventually :
        ∀ᶠ n : ℕ in atTop,
          dist (s n) T < ε :=

      hsTendsto.eventually
        (Metric.ball_mem_nhds T hε)

    obtain
      ⟨N, hN⟩ :=
      eventually_atTop.1
        hEventually

    refine
      ⟨
        N,
        ?_
      ⟩

    intro n hn

    have hsNear :
        dist (s n) T < ε :=
      hN n hn

    rw [Real.dist_eq] at hsNear ⊢

    have hsNonpos :
        s n - T ≤ 0 := by
      linarith [(hs n).2]

    have hrNonpos :
        r n - T ≤ 0 := by
      linarith [(hr n).2, (ht n).2]

    rw [abs_of_nonpos hsNonpos] at hsNear
    rw [abs_of_nonpos hrNonpos]

    linarith [(hr n).1]

  have hProfileTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
              hH3 hClass (r n)
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    let K : ℝ :=
      max M 0 + 1

    have hKPos :
        0 < K := by

      dsimp only [K]

      have hMax :
          0 ≤ max M 0 :=
        le_max_right
          M
          0

      linarith

    let c : ℝ :=
      δ / (2 * K)

    have hc :
        0 < c := by

      dsimp only [c]

      positivity

    have hsLate :
        ∀ᶠ n : ℕ in atTop,
          T - c < s n :=
      (tendsto_order.1 hsTendsto).1
        (T - c)
        (by linarith)

    filter_upwards [hsLate] with n hsLateN

    have hGapUpper :
        t n - s n < c := by

      have htUpper :
          t n < T :=
        (ht n).2

      linarith

    have hDenKPos :
        0 < 2 * K := by
      positivity

    have hGapScaled :
        (t n - s n) * (2 * K)
          <
        δ := by

      exact
        (lt_div_iff₀ hDenKPos).1
          (by
            simpa only [c] using hGapUpper)

    have hDenGapPos :
        0 < 2 * (t n - s n) := by

      positivity [hGapPos n]

    have hKThreshold :
        K
          <
        δ / (2 * (t n - s n)) := by

      apply
        (lt_div_iff₀ hDenGapPos).2

      nlinarith [hGapScaled]

    have hMK :
        M < K := by

      dsimp only [K]

      have hMMax :
          M ≤ max M 0 :=
        le_max_left
          M
          0

      linarith

    exact
      le_of_lt
        (
          lt_trans
            hMK
            (
              lt_trans
                hKThreshold
                (hRate n)
            )
        )

  exact
    ⟨
      δ,
      hδ,
      m,
      q,
      hmTop,
      hqTop,
      s,
      r,
      hs,
      hσ,
      hsTendsto,
      hSigmaMQ,
      hForward,
      hr,
      hrTendsto,
      (by
        intro n
        simpa only [t] using hRate n),
      hProfileTop
    ⟩

/--
The final resolved-PDE canonical witness therefore contains pointwise cubic
forcing blowup at the reciprocal width of its own shrinking forcing intervals.
-/
theorem exists_fixed_terminalSequence_with_canonicalFullForcingCubicPointwiseRateEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
          H3TerminalPhysicalTopDissipationFullForcingCubicCanonicalPointwiseRateEscapeSubsequenceOf
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
      hForcingIntegral
    ⟩ :=
    exists_fixed_terminalSequence_with_canonicalFullForcingCubicForwardIntegralEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε

  have hPointwise :
      H3TerminalPhysicalTopDissipationFullForcingCubicCanonicalPointwiseRateEscapeSubsequenceOf
        hH3 hClass σ :=
    fullForcingCubicCanonicalPointwiseRateEscapeSubsequenceOf_of_forwardIntegralEscapeSubsequenceOf
      hH3
      hClass
      σ
      hForcingIntegral

  exact
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hPointwise
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
