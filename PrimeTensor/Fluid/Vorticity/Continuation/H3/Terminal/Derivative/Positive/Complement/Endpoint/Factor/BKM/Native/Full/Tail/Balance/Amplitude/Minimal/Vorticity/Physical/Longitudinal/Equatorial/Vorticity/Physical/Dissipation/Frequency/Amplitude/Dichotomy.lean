import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Frequency.Escape.Density.Blowup

/-!
# Frequency escape versus weighted spectral-state amplitude blowup

The preceding checkpoint reduces the compactness obstruction to either

* pointwise radial frequency escape with positive physical H³ dissipation
  density, or
* pointwise blowup of the physical H³ dissipation density.

The latter density factors exactly as

    |D(ξ)|² * (|G₀(ξ)|² + |G₁(ξ)|² + |G₂(ξ)|²),

where `G` is the weighted H³ spectral state.

Therefore density blowup has only two possibilities.  If the radial factor is
not eventually bounded, a cofinal subsequence makes it tend to infinity.  If
the radial factor is eventually bounded, the weighted spectral-state square
amplitude must itself tend to infinity.

This file packages that elementary factor split and combines it with the
preceding concentration--compactness alternative.  No H⁴ or stronger
regularity hypothesis is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalDissipationFrequencyAmplitudeDichotomy
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalPhysicalDissipationFrequencyAmplitudeDichotomy :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Weighted spectral-state square amplitude -/

/--
Pointwise square amplitude of the three-component weighted H³ spectral state.
-/
def h3TerminalSpectralStateSquareAmplitude
    (G : H3SpectralFinVectorState)
    (ξ : H3FourierPoint3) : ℝ :=
  norm (G 0 ξ) ^ 2
    +
  norm (G 1 ξ) ^ 2
    +
  norm (G 2 ξ) ^ 2

theorem h3TerminalSpectralStateSquareAmplitude_nonneg
    (G : H3SpectralFinVectorState)
    (ξ : H3FourierPoint3) :
    0 ≤ h3TerminalSpectralStateSquareAmplitude G ξ := by
  unfold h3TerminalSpectralStateSquareAmplitude
  positivity

/--
The physical H³ dissipation density is exactly radial-frequency square times
weighted spectral-state square amplitude.
-/
theorem h3TerminalSpectralDissipationSingleDensity_eq_gradientMagnitude_sq_mul_stateSquareAmplitude
    (G : H3SpectralFinVectorState)
    (ξ : H3FourierPoint3) :
    h3TerminalSpectralDissipationSingleDensity G ξ
      =
    (h3FourierGradientMagnitude ξ) ^ 2
      *
    h3TerminalSpectralStateSquareAmplitude G ξ := by
  unfold
    h3TerminalSpectralDissipationSingleDensity
    h3TerminalSpectralStateSquareAmplitude
  rw [h3FourierGradientMagnitude_sq]

/-! ## Pointwise weighted-state amplitude blowup package -/

/--
A terminal point sequence on which the square amplitude of the weighted H³
spectral state tends to positive infinity.
-/
def H3TerminalPhysicalDissipationWeightedStateSquareAmplitudeBlowupPointSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∃ τ : ℕ → ℝ,
    ∃ ξ : ℕ → H3FourierPoint3,
      ∃ hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T,
        (
          ∀ n : ℕ,
            dist (τ n) T
                <
              (1 : ℝ) / ((n : ℝ) + 1)
        )
          ∧
        Tendsto τ atTop (𝓝 T)
          ∧
        Tendsto
          (fun n : ℕ =>
            h3TerminalSpectralStateSquareAmplitude
              (h3TerminalVelocitySpectralStateAt
                hH3
                (τ n)
                ⟨
                  lt_trans hClass.terminal_start.1 (hτ n).1,
                  (hτ n).2
                ⟩)
              (ξ n))
          atTop
          atTop

/-! ## Elementary tail split for a nonnegative real sequence -/

/--
Either a real sequence is eventually bounded above, or a cofinal extraction is
larger than `n+1` at extracted counter `n`.
-/
private theorem eventuallyBounded_or_cofinal_natSucc_escape
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
        tendsto_atTop.2
          ?_

      intro N

      filter_upwards
        [eventually_ge_atTop N]
        with n hn

      exact
        le_trans
          hn
          (hk n).1

    exact
      ⟨
        k,
        hk,
        hkTop
      ⟩

private theorem tendsto_atTop_of_natSucc_lt
    {f : ℕ → ℝ}
    (hf :
      ∀ n : ℕ,
        (n : ℝ) + 1 < f n) :
    Tendsto f atTop atTop := by

  refine
    tendsto_atTop.2
      ?_

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

/-! ## Density blowup splits into radial or weighted-state growth -/

/--
Pointwise dissipation-density blowup forces either a cofinal radial-frequency
escape subsequence or weighted spectral-state square-amplitude blowup.
-/
theorem physicalDissipationFrequencyEscapePointSequence_or_weightedStateSquareAmplitudeBlowupPointSequence_of_densityBlowupPointSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDensity :
      H3TerminalPhysicalDissipationDensityBlowupPointSequence
        hH3 hClass) :
    H3TerminalPhysicalDissipationFrequencyEscapePointSequence
        hH3 hClass
      ∨
    H3TerminalPhysicalDissipationWeightedStateSquareAmplitudeBlowupPointSequence
        hH3 hClass := by

  classical

  obtain
    ⟨
      δ,
      hδ,
      τ,
      ξ,
      hτ,
      hPoint,
      hτTendsto,
      hDensityTendsto
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
          (τ n)
          ⟨
            lt_trans hClass.terminal_start.1 (hτ n).1,
            (hτ n).2
          ⟩)
        (ξ n)

  rcases
      eventuallyBounded_or_cofinal_natSucc_escape q
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
            (τ n)
            ⟨
              lt_trans hClass.terminal_start.1 (hτ n).1,
              (hτ n).2
            ⟩)
          (ξ n)

    have hQSqBound :
        ∀ᶠ n : ℕ in atTop,
          (q n) ^ 2 ≤ B := by

      filter_upwards [hC] with n hn

      have hQMax :
          q n ≤ max C 0 :=
        hn.trans (le_max_left C 0)

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
                (τ n)
                ⟨
                  lt_trans hClass.terminal_start.1 (hτ n).1,
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
            (τ n)
            ⟨
              lt_trans hClass.terminal_start.1 (hτ n).1,
              (hτ n).2
            ⟩)
          (ξ n)

    have hATendsto :
        Tendsto A atTop atTop := by

      refine
        tendsto_atTop.2
          ?_

      intro M

      let M0 : ℝ :=
        max M 0

      have hMLeM0 :
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
                (τ n)
                ⟨
                  lt_trans hClass.terminal_start.1 (hτ n).1,
                  (hτ n).2
                ⟩)
              (ξ n) :=
        hDensityTendsto.eventually
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

      have hALeM0 :
          A n ≤ M0 :=
        le_trans
          hALt.le
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
            hBNonneg

      rw [hDensityEq n] at hLarge

      have hDLe :
          D ≤ B * M0 := by
        exact
          le_trans
            (le_of_lt hLarge)
            hProductLe

      dsimp only [D] at hDLe

      linarith

    refine
      ⟨
        τ,
        ξ,
        hτ,
        ?_,
        hτTendsto,
        ?_
      ⟩

    · intro n
      exact (hPoint n).1

    · simpa only [A] using hATendsto

  · left

    obtain
      ⟨
        k,
        hk,
        hkTop
      ⟩ :=
      hQEscape

    let τ' : ℕ → ℝ :=
      fun n =>
        τ (k n)

    let ξ' : ℕ → H3FourierPoint3 :=
      fun n =>
        ξ (k n)

    have hτ' :
        ∀ n : ℕ,
          τ' n ∈ Set.Ioo a T := by
      intro n
      dsimp only [τ']
      exact hτ (k n)

    have hNear' :
        ∀ n : ℕ,
          dist (τ' n) T
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
                exact_mod_cast (hk n).1
              linarith)

      dsimp only [τ']

      exact
        lt_of_lt_of_le
          hNearRaw
          hInv

    have hRadial' :
        ∀ n : ℕ,
          (n : ℝ) + 1
            ≤
          h3FourierGradientMagnitude
            (ξ' n) := by

      intro n

      dsimp only [ξ', q] at *

      exact
        le_of_lt
          (hk n).2

    have hDensityPositive' :
        ∀ n : ℕ,
          0
            <
          h3TerminalSpectralDissipationSingleDensity
            (h3TerminalVelocitySpectralStateAt
              hH3
              (τ' n)
              ⟨
                lt_trans hClass.terminal_start.1 (hτ' n).1,
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

      dsimp only [τ', ξ']

      exact
        lt_trans
          hScalePos
          hLower

    have hτ'Tendsto :
        Tendsto τ' atTop (𝓝 T) := by
      dsimp only [τ']
      exact
        hτTendsto.comp
          hkTop

    have hRadialTendsto :
        Tendsto
          (fun n : ℕ =>
            h3FourierGradientMagnitude
              (ξ' n))
          atTop
          atTop :=
      tendsto_atTop_of_natSucc_lt
        (fun n => by
          dsimp only [ξ', q]
          exact (hk n).2)

    refine
      ⟨
        δ,
        hδ,
        τ',
        ξ',
        hτ',
        ?_,
        hτ'Tendsto,
        hRadialTendsto
      ⟩

    intro n

    exact
      ⟨
        hNear' n,
        hRadial' n,
        hDensityPositive' n
      ⟩

/-! ## Refined compactness obstruction -/

/--
Under hypothetical nonextension, the physical H³ compactness obstruction can be
stated pointwise as either radial frequency escape or blowup of the weighted
H³ spectral-state square amplitude.
-/
theorem physicalDissipationFrequencyEscape_or_weightedStateSquareAmplitudeBlowup_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3) :
    H3TerminalPhysicalDissipationFrequencyEscapePointSequence
        hH3 hClass
      ∨
    H3TerminalPhysicalDissipationWeightedStateSquareAmplitudeBlowupPointSequence
        hH3 hClass := by

  rcases
      physicalDissipationFrequencyEscape_or_densityBlowup_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hPhysical
        hCauchy
    with hEscape | hDensity

  · exact Or.inl hEscape

  · exact
      physicalDissipationFrequencyEscapePointSequence_or_weightedStateSquareAmplitudeBlowupPointSequence_of_densityBlowupPointSequence
        hH3
        hClass
        hDensity

/--
Neutral formulation: under the retained endpoint hypotheses, either the path
extends smoothly through `T`, or physical H³ dissipation escapes to infinite
radial frequency, or the pointwise weighted H³ spectral-state square amplitude
diverges along a terminal sequence.
-/
theorem smoothContinuationExtension_or_physicalDissipationFrequencyEscape_or_weightedStateSquareAmplitudeBlowup
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
    H3TerminalPhysicalDissipationFrequencyEscapePointSequence
        hH3 hClass
      ∨
    H3TerminalPhysicalDissipationWeightedStateSquareAmplitudeBlowupPointSequence
        hH3 hClass := by

  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact Or.inl hExtension

  · exact
      Or.inr
        (physicalDissipationFrequencyEscape_or_weightedStateSquareAmplitudeBlowup_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical
          hCauchy)

end

end Euclidean
end Bridge
end PrimeTensor
