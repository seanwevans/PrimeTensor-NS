import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Frequency.Amplitude.Dichotomy
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Relative.Tail.Cascade

/-!
# Bounded-frequency fixed spectral component obstruction

The preceding frequency/amplitude dichotomy deliberately separated radial
frequency escape from blowup of the weighted H³ spectral-state square
amplitude.  Its amplitude package, however, no longer retained the bounded
radial-frequency information that produced that branch.

This file restores that information and then freezes one of the three spectral
coordinates.

Starting from the pointwise dissipation-density blowup sequence, apply the
standard eventual-bounded/cofinal-escape split to the radial gradient
magnitude.

* In the cofinal branch, radial frequency itself tends to infinity.
* In the eventually bounded branch, the dissipation factorization forces the
  three-component weighted spectral-state square amplitude to diverge.
  Since there are only three coordinates, a cofinal subsequence fixes one
  component whose pointwise square amplitude diverges while radial frequency
  remains eventually bounded.

This is still a concentration mechanism, not an `L²`-norm contradiction:
`H3SpectralScalarState` is an `L²` spectral state, and no fixed-frequency
evaluation continuity is assumed here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalDissipationBoundedFrequencyFixedSpectralComponent
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalPhysicalDissipationBoundedFrequencyFixedSpectralComponent :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## One weighted spectral coordinate -/

/-- Square amplitude of one fixed coordinate of a weighted H³ spectral state. -/
def h3TerminalSpectralStateComponentSquareAmplitude
    (G : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) : ℝ :=
  norm (G i ξ) ^ 2

theorem h3TerminalSpectralStateComponentSquareAmplitude_nonneg
    (G : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    0 ≤ h3TerminalSpectralStateComponentSquareAmplitude G i ξ := by
  unfold h3TerminalSpectralStateComponentSquareAmplitude
  positivity

/--
At every frequency, one of the three component squares carries at least one
third of the total three-component square amplitude.
-/
theorem exists_spectralComponent_stateSquareAmplitude_le_three_mul_componentSquare
    (G : H3SpectralFinVectorState)
    (ξ : H3FourierPoint3) :
    ∃ i : Fin 3,
      h3TerminalSpectralStateSquareAmplitude G ξ
        ≤
      3 * h3TerminalSpectralStateComponentSquareAmplitude G i ξ := by

  let x : ℝ := norm (G 0 ξ) ^ 2
  let y : ℝ := norm (G 1 ξ) ^ 2
  let z : ℝ := norm (G 2 ξ) ^ 2

  by_cases hyx : y ≤ x

  · by_cases hzx : z ≤ x

    · refine ⟨0, ?_⟩
      change x + y + z ≤ 3 * x
      linarith

    · have hxz : x < z :=
        lt_of_not_ge hzx
      refine ⟨2, ?_⟩
      change x + y + z ≤ 3 * z
      linarith

  · have hxy : x < y :=
      lt_of_not_ge hyx

    by_cases hzy : z ≤ y

    · refine ⟨1, ?_⟩
      change x + y + z ≤ 3 * y
      linarith

    · have hyz : y < z :=
        lt_of_not_ge hzy
      refine ⟨2, ?_⟩
      change x + y + z ≤ 3 * z
      linarith

/-! ## Bounded-frequency fixed-component package -/

/--
Terminal concentration at bounded radial frequency with one fixed weighted H³
spectral coordinate whose pointwise square amplitude tends to `+∞`.
-/
def H3TerminalPhysicalDissipationBoundedFrequencyFixedSpectralComponentBlowupPointSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) : Prop :=
  ∃ C : ℝ,
    0 ≤ C
      ∧
    ∃ i : Fin 3,
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
            (
              ∀ᶠ n : ℕ in atTop,
                h3FourierGradientMagnitude (ξ n) ≤ C
            )
              ∧
            Tendsto τ atTop (𝓝 T)
              ∧
            Tendsto
              (fun n : ℕ =>
                h3TerminalSpectralStateComponentSquareAmplitude
                  (h3TerminalVelocitySpectralStateAt
                    hH3
                    (τ n)
                    ⟨
                      lt_trans hClass.terminal_start.1 (hτ n).1,
                      (hτ n).2
                    ⟩)
                  i
                  (ξ n))
              atTop
              atTop

/-! ## Freeze a component from divergent total spectral amplitude -/

/--
If the total three-component square amplitude diverges, a cofinal subsequence
freezes one coordinate whose square amplitude also diverges.
-/
theorem exists_fixed_spectralComponent_subsequence_of_stateSquareAmplitude_tendsto_atTop
    {G : ℕ → H3SpectralFinVectorState}
    {ξ : ℕ → H3FourierPoint3}
    (hA :
      Tendsto
        (fun n : ℕ =>
          h3TerminalSpectralStateSquareAmplitude
            (G n)
            (ξ n))
        atTop
        atTop) :
    ∃ i : Fin 3,
      ∃ k : ℕ → ℕ,
        (∀ n : ℕ, n ≤ k n)
          ∧
        Tendsto k atTop atTop
          ∧
        Tendsto
          (fun n : ℕ =>
            h3TerminalSpectralStateComponentSquareAmplitude
              (G (k n))
              i
              (ξ (k n)))
          atTop
          atTop := by

  classical

  have hExists :
      ∀ n : ℕ,
        ∃ i : Fin 3,
          h3TerminalSpectralStateSquareAmplitude
              (G n)
              (ξ n)
            ≤
          3 *
            h3TerminalSpectralStateComponentSquareAmplitude
              (G n)
              i
              (ξ n) := by
    intro n
    exact
      exists_spectralComponent_stateSquareAmplitude_le_three_mul_componentSquare
        (G n)
        (ξ n)

  choose i hi using hExists

  have hFrequentlySome :
      ∃ᶠ n : ℕ in atTop,
        ∃ q : Fin 3,
          i n = q :=
    Frequently.of_forall
      (fun n =>
        ⟨
          i n,
          rfl
        ⟩)

  obtain
    ⟨q, hFrequently⟩ :=
    (Filter.frequently_exists).1
      hFrequentlySome

  obtain
    ⟨k, hMono, hFixed⟩ :=
    extraction_of_frequently_atTop
      hFrequently

  have hk :
      ∀ n : ℕ,
        n ≤ k n := by
    intro n
    exact hMono.le_apply

  have hkTop :
      Tendsto k atTop atTop :=
    hMono.tendsto_atTop

  have hLower :
      ∀ n : ℕ,
        h3TerminalSpectralStateSquareAmplitude
            (G (k n))
            (ξ (k n))
          ≤
        3 *
          h3TerminalSpectralStateComponentSquareAmplitude
            (G (k n))
            q
            (ξ (k n)) := by

    intro n

    have hAt :=
      hi (k n)

    rw [hFixed n] at hAt

    exact hAt

  have hATop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalSpectralStateSquareAmplitude
            (G (k n))
            (ξ (k n)))
        atTop
        atTop :=
    hA.comp hkTop

  have hComponentTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalSpectralStateComponentSquareAmplitude
            (G (k n))
            q
            (ξ (k n)))
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    let M0 : ℝ :=
      max M 0

    have hMLe :
        M ≤ M0 := by
      dsimp only [M0]
      exact le_max_left M 0

    have hLarge :
        ∀ᶠ n : ℕ in atTop,
          3 * M0
            <
          h3TerminalSpectralStateSquareAmplitude
            (G (k n))
            (ξ (k n)) :=
      hATop.eventually
        (eventually_gt_atTop (3 * M0))

    filter_upwards [hLarge] with n hn

    have hBound :=
      hLower n

    have hM0Lt :
        M0
          <
        h3TerminalSpectralStateComponentSquareAmplitude
          (G (k n))
          q
          (ξ (k n)) := by
      linarith

    exact
      le_of_lt
        (lt_of_le_of_lt
          hMLe
          hM0Lt)

  exact
    ⟨
      q,
      k,
      hk,
      hkTop,
      hComponentTop
    ⟩

/-! ## Density blowup: radial escape or bounded-frequency fixed component -/

/--
A pointwise dissipation-density blowup sequence either has a cofinal radial
frequency-escape subsequence, or has a bounded-frequency cofinal subsequence
on which one fixed weighted H³ spectral coordinate diverges pointwise.
-/
theorem physicalDissipationFrequencyEscapePointSequence_or_boundedFrequencyFixedSpectralComponentBlowupPointSequence_of_densityBlowupPointSequence
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
    H3TerminalPhysicalDissipationBoundedFrequencyFixedSpectralComponentBlowupPointSequence
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
      exact le_max_right (1 + C) 0

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
            (τ n)
            ⟨
              lt_trans hClass.terminal_start.1 (hτ n).1,
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
            (τ n)
            ⟨
              lt_trans hClass.terminal_start.1 (hτ n).1,
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
            hBPos.le

      rw [hDensityEq n] at hLarge

      have hDLe :
          D ≤ B * M0 := by
        exact
          le_trans
            (le_of_lt hLarge)
            hProductLe

      dsimp only [D] at hDLe

      linarith

    let G : ℕ → H3SpectralFinVectorState :=
      fun n =>
        h3TerminalVelocitySpectralStateAt
          hH3
          (τ n)
          ⟨
            lt_trans hClass.terminal_start.1 (hτ n).1,
            (hτ n).2
          ⟩

    obtain
      ⟨i, k, hk, hkTop, hComponentTop⟩ :=
      exists_fixed_spectralComponent_subsequence_of_stateSquareAmplitude_tendsto_atTop
        (G := G)
        (ξ := ξ)
        (by
          simpa only [G, A] using hATendsto)

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
                exact_mod_cast hk n
              linarith)

      dsimp only [τ']

      exact
        lt_of_lt_of_le
          hNearRaw
          hInv

    have hQBound' :
        ∀ᶠ n : ℕ in atTop,
          h3FourierGradientMagnitude (ξ' n) ≤ C0 := by

      have hComp :=
        hkTop.eventually hQBound

      simpa only [ξ', q] using hComp

    have hτ'Tendsto :
        Tendsto τ' atTop (𝓝 T) := by
      dsimp only [τ']
      exact
        hτTendsto.comp
          hkTop

    have hComponentTop' :
        Tendsto
          (fun n : ℕ =>
            h3TerminalSpectralStateComponentSquareAmplitude
              (h3TerminalVelocitySpectralStateAt
                hH3
                (τ' n)
                ⟨
                  lt_trans hClass.terminal_start.1 (hτ' n).1,
                  (hτ' n).2
                ⟩)
              i
              (ξ' n))
          atTop
          atTop := by

      simpa only [τ', ξ', G] using
        hComponentTop

    exact
      ⟨
        C0,
        hC0,
        i,
        τ',
        ξ',
        hτ',
        hNear',
        hQBound',
        hτ'Tendsto,
        hComponentTop'
      ⟩

  · left

    obtain
      ⟨
        k,
        hk,
        hkTop,
        _hGapTop,
        _hQTop
      ⟩ :=
      hEscape

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

      dsimp only [ξ', q]

      exact
        le_of_lt
          (hk n).2.2

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
          atTop := by

      simpa only [ξ', q] using
        _hQTop

    exact
      ⟨
        δ,
        hδ,
        τ',
        ξ',
        hτ',
        (fun n =>
          ⟨
            hNear' n,
            hRadial' n,
            hDensityPositive' n
          ⟩),
        hτ'Tendsto,
        hRadialTendsto
      ⟩

/-! ## Final refined endpoint obstruction -/

/--
Under the retained endpoint hypotheses and hypothetical nonextension, either
physical H³ dissipation escapes to arbitrarily large radial frequency, or one
fixed weighted spectral coordinate blows up pointwise along a terminal sequence
whose radial frequencies remain eventually bounded.
-/
theorem physicalDissipationFrequencyEscape_or_boundedFrequencyFixedSpectralComponentBlowup_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    H3TerminalPhysicalDissipationBoundedFrequencyFixedSpectralComponentBlowupPointSequence
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
      physicalDissipationFrequencyEscapePointSequence_or_boundedFrequencyFixedSpectralComponentBlowupPointSequence_of_densityBlowupPointSequence
        hH3
        hClass
        hDensity

/--
Neutral formulation: either the path extends smoothly through `T`, physical H³
dissipation escapes to infinite radial frequency, or one fixed weighted
spectral coordinate has pointwise square-amplitude blowup at eventually bounded
radial frequencies.
-/
theorem smoothContinuationExtension_or_physicalDissipationFrequencyEscape_or_boundedFrequencyFixedSpectralComponentBlowup
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
    H3TerminalPhysicalDissipationBoundedFrequencyFixedSpectralComponentBlowupPointSequence
        hH3 hClass := by

  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact Or.inl hExtension

  · exact
      Or.inr
        (physicalDissipationFrequencyEscape_or_boundedFrequencyFixedSpectralComponentBlowup_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical
          hCauchy)

end

end Euclidean
end Bridge
end PrimeTensor
