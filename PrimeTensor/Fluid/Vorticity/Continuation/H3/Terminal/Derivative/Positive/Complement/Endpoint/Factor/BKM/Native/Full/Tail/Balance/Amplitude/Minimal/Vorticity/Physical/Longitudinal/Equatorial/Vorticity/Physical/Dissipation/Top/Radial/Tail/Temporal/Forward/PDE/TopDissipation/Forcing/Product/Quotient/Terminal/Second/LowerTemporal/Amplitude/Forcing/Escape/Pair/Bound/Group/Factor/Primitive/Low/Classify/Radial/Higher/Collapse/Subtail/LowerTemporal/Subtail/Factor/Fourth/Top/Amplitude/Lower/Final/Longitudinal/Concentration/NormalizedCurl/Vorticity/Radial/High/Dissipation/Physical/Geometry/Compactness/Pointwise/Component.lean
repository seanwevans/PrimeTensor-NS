import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness.Pointwise
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Bounded.Frequency.Fixed.Spectral.Component

/-!
# Freeze a spectral component on the canonical pointwise compactness witness

The canonical pointwise concentration--compactness theorem leaves either

* radial frequency escape on a subsequence of the canonical single-time
  physical witness `σ`, or
* pointwise physical H³ dissipation-density blowup on such a subsequence.

In the density branch, split the sampled radial frequencies into an eventually
bounded branch and a cofinal escape branch.  On the bounded branch the density
factorization

    density = |∇ξ|² * total spectral-state square amplitude

forces the total state square amplitude to diverge.  A finite-component
extraction then freezes one `Fin 3` coordinate whose square amplitude diverges.

Crucially, both reindexings are composed with the original density selector.
Thus the fixed-component branch is realized at times literally of the form

    σ (m (k n)),

and the canonical witness lineage is retained.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2400000

/--
One fixed spectral coordinate blows up pointwise at eventually bounded
frequencies on a subsequence of a prescribed canonical terminal sequence.
-/
def H3TerminalPhysicalDissipationBoundedFrequencyFixedSpectralComponentBlowupPointSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ) : Prop :=
  ∃ C : ℝ,
    0 ≤ C
      ∧
    ∃ j : Fin 3,
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
            (
              ∀ᶠ n : ℕ in atTop,
                h3FourierGradientMagnitude (ξ n) ≤ C
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
                  h3TerminalSpectralStateComponentSquareAmplitude
                    (h3TerminalVelocitySpectralStateAt
                      hH3
                      (σ (m n))
                      ⟨
                        lt_trans hClass.terminal_start.1
                          (hτ n).1,
                        (hτ n).2
                      ⟩)
                    j
                    (ξ n)
              )
              atTop
              atTop

/--
A density-blowup subsequence of `σ` either has a further frequency-escape
subsequence of that same `σ`, or a further eventually bounded-frequency
subsequence on which one fixed spectral component diverges.
-/
theorem physicalDissipationFrequencyEscapePointSubsequenceOf_or_boundedFrequencyFixedSpectralComponentBlowupPointSubsequenceOf_of_densityBlowupPointSubsequenceOf
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
    H3TerminalPhysicalDissipationBoundedFrequencyFixedSpectralComponentBlowupPointSubsequenceOf
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

  have hTail :
      H3TerminalRelativeTailAlternative
        (fun n : ℕ => q n - 1)
        q := by

    apply
      relativeTailAlternative_of_eventually_ratio_identity

    exact
      Eventually.of_forall
        (fun n => by
          ring)

  unfold
    H3TerminalRelativeTailAlternative
      at hTail

  rcases hTail with hBounded | hEscape

  · right

    obtain
      ⟨C, hC⟩ :=
      hBounded

    let C0 : ℝ :=
      max (1 + C) 0

    have hC0 :
        0 ≤ C0 := by

      dsimp only [C0]

      exact
        le_max_right (1 + C) 0

    have hQBound :
        ∀ᶠ n : ℕ in atTop,
          q n ≤ C0 := by

      filter_upwards [hC] with n hn

      exact
        hn.2.trans
          (le_max_left (1 + C) 0)

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

    let B : ℝ :=
      C0 ^ 2 + 1

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

      filter_upwards [hQBound] with n hn

      have hSq :
          (q n) ^ 2 ≤ C0 ^ 2 := by

        nlinarith [hQNonneg n, hC0]

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

      have hMLeM0 :
          M ≤ M0 := by

        dsimp only [M0]

        exact
          le_max_left M 0

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

      by_contra hNot

      have hALt :
          A n < M :=
        lt_of_not_ge hNot

      have hALeM0 :
          A n ≤ M0 :=
        hALt.le.trans
          hMLeM0

      have hProductLe :
          (q n) ^ 2 * A n
            ≤
          B * M0 := by

        exact
          mul_le_mul
            hQSq
            hALeM0
            (hANonneg n)
            hBPos.le

      rw [hDensityEq n] at hLarge

      have hDLe :
          D ≤ B * M0 :=
        (le_of_lt hLarge).trans
          hProductLe

      dsimp only [D] at hDLe

      linarith

    let G : ℕ → H3SpectralFinVectorState :=
      fun n =>
        h3TerminalVelocitySpectralStateAt
          hH3
          (σ (m n))
          ⟨
            lt_trans hClass.terminal_start.1
              (hτ n).1,
            (hτ n).2
          ⟩

    obtain
      ⟨
        j,
        k,
        hk,
        hkTop,
        hComponentTop
      ⟩ :=
      exists_fixed_spectralComponent_subsequence_of_stateSquareAmplitude_tendsto_atTop
        (G := G)
        (ξ := ξ)
        (by
          simpa only [G, A] using
            hATop)

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
          1 / ((n : ℝ) + 1) := by

        exact
          one_div_le_one_div_of_le
            hDen
            (by
              have hCast :
                  (n : ℝ) ≤ k n := by
                exact_mod_cast
                  hk n
              linarith)

      dsimp only [m']

      exact
        hNearRaw.trans_le
          hInv

    have hQBound' :
        ∀ᶠ n : ℕ in atTop,
          h3FourierGradientMagnitude (ξ' n) ≤ C0 := by

      have hComp :=
        hkTop.eventually
          hQBound

      simpa only [ξ', q] using
        hComp

    have hSigmaM' :
        Tendsto
          (fun n : ℕ => σ (m' n))
          atTop
          (𝓝 T) := by

      dsimp only [m']

      exact
        hSigmaM.comp
          hkTop

    have hComponentTop' :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalSpectralStateComponentSquareAmplitude
                (h3TerminalVelocitySpectralStateAt
                  hH3
                  (σ (m' n))
                  ⟨
                    lt_trans hClass.terminal_start.1
                      (hτ' n).1,
                    (hτ' n).2
                  ⟩)
                j
                (ξ' n)
          )
          atTop
          atTop := by

      simpa only [m', ξ', G] using
        hComponentTop

    exact
      ⟨
        C0,
        hC0,
        j,
        m',
        hm'Top,
        ξ',
        hτ',
        hNear',
        hQBound',
        hSigmaM',
        hComponentTop'
      ⟩

  · left

    obtain
      ⟨
        k,
        hk,
        hkTop,
        _hGapTop,
        hQTop
      ⟩ :=
      hEscape

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
          1 / ((n : ℝ) + 1) := by

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
        hNearRaw.trans_le
          hInv

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
          (hk n).2.2

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
          atTop := by

      simpa only [ξ', q] using
        hQTop

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
The canonical final physical witness sharpens pointwise to either frequency
escape or one fixed bounded-frequency spectral coordinate whose square
amplitude diverges.
-/
theorem exists_fixed_terminalSequence_with_frequencyEscape_or_boundedFrequencyFixedSpectralComponentBlowup_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
            H3TerminalPhysicalDissipationBoundedFrequencyFixedSpectralComponentBlowupPointSubsequenceOf
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
      H3TerminalPhysicalDissipationBoundedFrequencyFixedSpectralComponentBlowupPointSubsequenceOf
          hH3 hClass σ := by

    rcases
        hPointwise
      with hEscape | hDensity

    · exact
        Or.inl
          hEscape

    · exact
        physicalDissipationFrequencyEscapePointSubsequenceOf_or_boundedFrequencyFixedSpectralComponentBlowupPointSubsequenceOf_of_densityBlowupPointSubsequenceOf
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
