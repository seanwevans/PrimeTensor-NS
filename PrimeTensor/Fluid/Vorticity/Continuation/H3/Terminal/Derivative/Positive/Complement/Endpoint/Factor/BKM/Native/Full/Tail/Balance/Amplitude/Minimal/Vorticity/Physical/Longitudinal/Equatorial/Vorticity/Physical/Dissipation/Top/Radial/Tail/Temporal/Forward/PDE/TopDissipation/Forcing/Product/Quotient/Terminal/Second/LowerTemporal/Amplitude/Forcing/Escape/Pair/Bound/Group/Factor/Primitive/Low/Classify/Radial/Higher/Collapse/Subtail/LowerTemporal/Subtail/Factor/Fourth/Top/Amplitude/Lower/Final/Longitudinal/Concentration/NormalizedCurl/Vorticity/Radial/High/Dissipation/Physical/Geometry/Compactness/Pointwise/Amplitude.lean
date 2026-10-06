import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Pointwise
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Frequency.Amplitude.Dichotomy

/-!
# Frequency--amplitude split on the canonical final witness

The pointwise same-witness compactness theorem leaves two branches:

* radial frequency escape on a subsequence of the canonical physical witness;
* pointwise physical H³ dissipation-density blowup on such a subsequence.

The density is exactly

    |∇(ξ)|² * spectralStateSquareAmplitude.

Therefore density blowup has only two possibilities on that same witness:

* the frequency magnitude itself has a further cofinal escape subsequence; or
* the frequency magnitude is eventually bounded, in which case the weighted
  spectral-state square amplitude tends to infinity.

No unrelated terminal sequence is introduced.
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
Weighted spectral-state square-amplitude blowup realized on a subsequence of a
prescribed canonical terminal sequence.
-/
def H3TerminalPhysicalDissipationWeightedStateSquareAmplitudeBlowupPointSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ) : Prop :=
  ∃ m : ℕ → ℕ,
    Tendsto m atTop atTop
      ∧
    ∃ ξ : ℕ → H3FourierPoint3,
      ∃ hτ :
        ∀ n : ℕ,
          σ (m n) ∈ Set.Ioo a T,
        (
          ∀ n : ℕ,
            dist (σ (m n)) T
                <
              (1 : ℝ) / ((n : ℝ) + 1)
        )
          ∧
        Tendsto
          (fun n : ℕ => σ (m n))
          atTop
          (𝓝 T)
          ∧
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalSpectralStateSquareAmplitude
                (h3TerminalVelocitySpectralStateAt
                  hH3
                  (σ (m n))
                  ⟨
                    lt_trans hClass.terminal_start.1
                      (hτ n).1,
                    (hτ n).2
                  ⟩)
                (ξ n)
          )
          atTop
          atTop

private theorem eventuallyBounded_or_cofinal_natSucc_escape_finalWitness
    (q : ℕ → ℝ) :
    (
      ∃ C : ℝ,
        ∀ᶠ n : ℕ in atTop,
          q n ≤ C
    )
      ∨
    (
      ∃ k : ℕ → ℕ,
        (
          ∀ n : ℕ,
            n ≤ k n
              ∧
            (n : ℝ) + 1 < q (k n)
        )
          ∧
        Tendsto k atTop atTop
    ) := by

  classical

  by_cases hBound :
      ∃ C : ℝ,
        ∀ᶠ n : ℕ in atTop,
          q n ≤ C

  · exact Or.inl hBound

  · right

    have hCofinal :
        ∀ N : ℕ,
          ∀ M : ℝ,
            ∃ m : ℕ,
              N ≤ m
                ∧
              M < q m := by

      intro N M

      by_contra hNo

      apply hBound

      refine
        ⟨
          M,
          ?_
        ⟩

      filter_upwards
        [eventually_ge_atTop N]
        with n hn

      exact
        le_of_not_gt
          (fun hGreater =>
            hNo
              ⟨
                n,
                hn,
                hGreater
              ⟩)

    have hChoice :
        ∀ n : ℕ,
          ∃ m : ℕ,
            n ≤ m
              ∧
            (n : ℝ) + 1 < q m := by

      intro n

      exact
        hCofinal
          n
          ((n : ℝ) + 1)

    choose k hk using hChoice

    have hkTop :
        Tendsto k atTop atTop := by

      refine
        tendsto_atTop.2 ?_

      intro N

      filter_upwards
        [eventually_ge_atTop N]
        with n hn

      exact
        hn.trans
          (hk n).1

    exact
      ⟨
        k,
        hk,
        hkTop
      ⟩

private theorem tendsto_atTop_of_natSucc_lt_finalAmplitude
    {f : ℕ → ℝ}
    (hf :
      ∀ n : ℕ,
        (n : ℝ) + 1 < f n) :
    Tendsto f atTop atTop := by

  refine
    tendsto_atTop.2 ?_

  intro M

  obtain
    ⟨N : ℕ, hN⟩ :=
    exists_nat_gt M

  filter_upwards
    [eventually_ge_atTop N]
    with n hn

  have hCast :
      (N : ℝ) ≤ n := by
    exact_mod_cast hn

  have hM :
      M < (n : ℝ) + 1 := by
    linarith

  exact
    le_of_lt
      (lt_trans hM (hf n))

/--
Density blowup on a subsequence of `σ` forces either a further pointwise
frequency-escape subsequence of the same `σ`, or weighted spectral-state
square-amplitude blowup on the original density-blowup subsequence.
-/
theorem physicalDissipationFrequencyEscapePointSubsequenceOf_or_weightedStateSquareAmplitudeBlowupPointSubsequenceOf_of_densityBlowupPointSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ)
    (hDensity :
      H3TerminalPhysicalDissipationDensityBlowupPointSubsequenceOf
        hH3 hClass σ) :
    H3TerminalPhysicalDissipationFrequencyEscapePointSubsequenceOf
        hH3 hClass σ
      ∨
    H3TerminalPhysicalDissipationWeightedStateSquareAmplitudeBlowupPointSubsequenceOf
        hH3 hClass σ := by

  classical

  obtain
    ⟨
      δ,
      hδ,
      m,
      hmTop,
      ξ,
      hτ,
      hPoint,
      hSigmaM,
      hDensityTop
    ⟩ :=
    hDensity

  let q : ℕ → ℝ :=
    fun n =>
      h3FourierGradientMagnitude
        (ξ n)

  let A : ℕ → ℝ :=
    fun n =>
      h3TerminalSpectralStateSquareAmplitude
        (h3TerminalVelocitySpectralStateAt
          hH3
          (σ (m n))
          ⟨
            lt_trans hClass.terminal_start.1
              (hτ n).1,
            (hτ n).2
          ⟩)
        (ξ n)

  rcases
      eventuallyBounded_or_cofinal_natSucc_escape_finalWitness q
    with hQBound | hQEscape

  · right

    obtain
      ⟨C, hC⟩ :=
      hQBound

    let B : ℝ :=
      (max C 0) ^ 2 + 1

    have hBPos :
        0 < B := by

      dsimp only [B]

      positivity

    have hQNonneg :
        ∀ n : ℕ,
          0 ≤ q n := by

      intro n

      dsimp only [q]

      exact
        h3FourierGradientMagnitude_nonneg
          (ξ n)

    have hANonneg :
        ∀ n : ℕ,
          0 ≤ A n := by

      intro n

      dsimp only [A]

      exact
        h3TerminalSpectralStateSquareAmplitude_nonneg
          (h3TerminalVelocitySpectralStateAt
            hH3
            (σ (m n))
            ⟨
              lt_trans hClass.terminal_start.1
                (hτ n).1,
              (hτ n).2
            ⟩)
          (ξ n)

    have hQSqBound :
        ∀ᶠ n : ℕ in atTop,
          (q n) ^ 2 ≤ B := by

      filter_upwards [hC] with n hn

      have hQMax :
          q n ≤ max C 0 :=
        hn.trans
          (le_max_left C 0)

      have hMaxNonneg :
          0 ≤ max C 0 :=
        le_max_right C 0

      have hSq :
          (q n) ^ 2
            ≤
          (max C 0) ^ 2 := by

        nlinarith [hQNonneg n]

      dsimp only [B]

      linarith

    have hDensityEq :
        ∀ n : ℕ,
          h3TerminalSpectralDissipationSingleDensity
              (h3TerminalVelocitySpectralStateAt
                hH3
                (σ (m n))
                ⟨
                  lt_trans hClass.terminal_start.1
                    (hτ n).1,
                  (hτ n).2
                ⟩)
              (ξ n)
            =
          (q n) ^ 2 * A n := by

      intro n

      dsimp only [q, A]

      exact
        h3TerminalSpectralDissipationSingleDensity_eq_gradientMagnitude_sq_mul_stateSquareAmplitude
          (h3TerminalVelocitySpectralStateAt
            hH3
            (σ (m n))
            ⟨
              lt_trans hClass.terminal_start.1
                (hτ n).1,
              (hτ n).2
            ⟩)
          (ξ n)

    have hATop :
        Tendsto A atTop atTop := by

      refine
        tendsto_atTop.2 ?_

      intro M

      let M0 : ℝ :=
        max M 0

      have hMLe :
          M ≤ M0 := by

        dsimp only [M0]

        exact le_max_left M 0

      have hM0Nonneg :
          0 ≤ M0 := by

        dsimp only [M0]

        exact le_max_right M 0

      let D : ℝ :=
        B * M0 + 1

      have hDensityLarge :
          ∀ᶠ n : ℕ in atTop,
            D
              <
            h3TerminalSpectralDissipationSingleDensity
              (h3TerminalVelocitySpectralStateAt
                hH3
                (σ (m n))
                ⟨
                  lt_trans hClass.terminal_start.1
                    (hτ n).1,
                  (hτ n).2
                ⟩)
              (ξ n) :=
        hDensityTop.eventually
          (eventually_gt_atTop D)

      filter_upwards
        [hQSqBound, hDensityLarge]
        with n hQSq hLarge

      have hBNonneg :
          0 ≤ B :=
        hBPos.le

      by_contra hNot

      have hALt :
          A n < M :=
        lt_of_not_ge hNot

      have hALe :
          A n ≤ M0 :=
        hALt.le.trans
          hMLe

      have hProductLe :
          (q n) ^ 2 * A n
            ≤
          B * M0 := by

        exact
          mul_le_mul
            hQSq
            hALe
            (hANonneg n)
            hBNonneg

      rw [hDensityEq n] at hLarge

      have hDLe :
          D ≤ B * M0 :=
        (le_of_lt hLarge).trans
          hProductLe

      dsimp only [D] at hDLe

      linarith

    exact
      ⟨
        m,
        hmTop,
        ξ,
        hτ,
        (fun n => (hPoint n).1),
        hSigmaM,
        by
          simpa only [A] using hATop
      ⟩

  · left

    obtain
      ⟨
        k,
        hk,
        hkTop
      ⟩ :=
      hQEscape

    let m' : ℕ → ℕ :=
      fun n =>
        m (k n)

    let ξ' : ℕ → H3FourierPoint3 :=
      fun n =>
        ξ (k n)

    have hm'Top :
        Tendsto m' atTop atTop := by

      dsimp only [m']

      exact
        hmTop.comp
          hkTop

    have hτ' :
        ∀ n : ℕ,
          σ (m' n) ∈ Set.Ioo a T := by

      intro n

      dsimp only [m']

      exact
        hτ (k n)

    have hNear' :
        ∀ n : ℕ,
          dist (σ (m' n)) T
            <
          (1 : ℝ) / ((n : ℝ) + 1) := by

      intro n

      have hNearRaw :=
        (hPoint (k n)).1

      have hDen :
          0 < (n : ℝ) + 1 := by
        positivity

      have hInv :
          (1 : ℝ) / (((k n : ℕ) : ℝ) + 1)
            ≤
          (1 : ℝ) / ((n : ℝ) + 1) := by

        exact
          one_div_le_one_div_of_le
            hDen
            (by
              have hCast :
                  (n : ℝ) ≤ k n := by
                exact_mod_cast
                  (hk n).1
              linarith)

      dsimp only [m']

      exact
        (hNearRaw.trans_le hInv)

    have hRadial' :
        ∀ n : ℕ,
          (n : ℝ) + 1
            ≤
          h3FourierGradientMagnitude
            (ξ' n) := by

      intro n

      dsimp only [ξ', q]

      exact
        le_of_lt
          (hk n).2

    have hPositive' :
        ∀ n : ℕ,
          0
            <
          h3TerminalSpectralDissipationSingleDensity
            (h3TerminalVelocitySpectralStateAt
              hH3
              (σ (m' n))
              ⟨
                lt_trans hClass.terminal_start.1
                  (hτ' n).1,
                (hτ' n).2
              ⟩)
            (ξ' n) := by

      intro n

      have hLower :=
        (hPoint (k n)).2

      have hScalePos :
          0
            <
          δ * (((k n : ℕ) : ℝ) + 1) := by
        positivity

      dsimp only [m', ξ']

      exact
        hScalePos.trans
          hLower

    have hSigmaM' :
        Tendsto
          (fun n : ℕ => σ (m' n))
          atTop
          (𝓝 T) := by

      dsimp only [m']

      exact
        hSigmaM.comp
          hkTop

    have hRadialTop :
        Tendsto
          (
            fun n : ℕ =>
              h3FourierGradientMagnitude
                (ξ' n)
          )
          atTop
          atTop :=
      tendsto_atTop_of_natSucc_lt_finalAmplitude
        (fun n => by
          dsimp only [ξ', q]
          exact
            (hk n).2)

    exact
      ⟨
        δ,
        hδ,
        m',
        hm'Top,
        ξ',
        hτ',
        (fun n =>
          ⟨
            hNear' n,
            hRadial' n,
            hPositive' n
          ⟩),
        hSigmaM',
        hRadialTop
      ⟩

/--
The pointwise final compactness obstruction sharpens, on the same canonical
physical witness, to either radial frequency escape or weighted spectral-state
square-amplitude blowup.
-/
theorem exists_fixed_terminalSequence_with_frequencyEscape_or_weightedStateAmplitudeBlowup_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
          (
            H3TerminalPhysicalDissipationFrequencyEscapePointSubsequenceOf
                hH3 hClass σ
              ∨
            H3TerminalPhysicalDissipationWeightedStateSquareAmplitudeBlowupPointSubsequenceOf
                hH3 hClass σ
          ) := by

  obtain
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hPointwise
    ⟩ :=
    exists_fixed_terminalSequence_with_pointwisePhysicalDissipationConcentrationCompactnessDichotomy_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε

  have hFinal :
      H3TerminalPhysicalDissipationFrequencyEscapePointSubsequenceOf
          hH3 hClass σ
        ∨
      H3TerminalPhysicalDissipationWeightedStateSquareAmplitudeBlowupPointSubsequenceOf
          hH3 hClass σ := by

    rcases
        hPointwise
      with hEscape | hDensity

    · exact
        Or.inl
          hEscape

    · exact
        physicalDissipationFrequencyEscapePointSubsequenceOf_or_weightedStateSquareAmplitudeBlowupPointSubsequenceOf_of_densityBlowupPointSubsequenceOf
          hH3
          hClass
          σ
          hDensity

  exact
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hFinal
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
