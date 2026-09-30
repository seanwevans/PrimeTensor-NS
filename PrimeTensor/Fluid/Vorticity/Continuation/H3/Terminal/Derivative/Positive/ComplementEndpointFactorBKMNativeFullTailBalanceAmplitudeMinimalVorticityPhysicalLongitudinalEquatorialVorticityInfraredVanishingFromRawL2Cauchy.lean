import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityInfraredVanishingFrontier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Round.Trip

/-!
# Infrared vanishing from terminal raw-velocity L² Cauchy control

The terminal spectral state used by the H³ endpoint analysis stores the weighted
Fourier amplitude

    G(ξ) = W₃(ξ) * û(ξ),

where

    W₃² = 1 + q + q² + q³,
    q = |D|².

The abstract infrared-vanishing frontier from the preceding file can therefore
be reduced to a zeroth-order statement.

On the fixed radial ball `|D| < 1` we have `q < 1`, hence

    W₃² ≤ 4.

The normalized-vorticity component multiplier is degree zero and its square is
already bounded by four times the total weighted spectral square difference.
Consequently,

    infrared normalized-vorticity defect
      ≤ 16 * raw velocity Fourier L² square defect.

Thus terminal Cauchy control of the deweighted/raw Fourier velocity implies the
infrared-vanishing property for every vorticity component.  Under hypothetical
nonextension, the diagonal infrared branch is then excluded and the radial
classification is forced into the positive-cutoff high-radial raw-vorticity
branch.

This file does not assert the terminal raw-velocity L² Cauchy property; it
identifies it as a concrete sufficient condition for closing the infrared
frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalLongitudinalEquatorialVorticityInfraredVanishingFromRawL2Cauchy
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Deweighted velocity defect -/

/-- Deweighted/raw Fourier velocity component of one weighted spectral state. -/
noncomputable def h3TerminalRawVelocityFourierComponent
    (G : H3SpectralFinVectorState)
    (j : Fin 3) :
    H3FourierComplexL2 :=
  h3SpectralScalarRawFourierL2
    (G j)

/-- Pointwise sum of the three raw Fourier velocity square differences. -/
def h3TerminalRawVelocityFourierTotalSquareDensity
    (G H : H3SpectralFinVectorState)
    (ξ : H3FourierPoint3) : ℝ :=
  norm
      (
        h3TerminalRawVelocityFourierComponent G 0 ξ
          -
        h3TerminalRawVelocityFourierComponent H 0 ξ
      ) ^ 2
    +
  norm
      (
        h3TerminalRawVelocityFourierComponent G 1 ξ
          -
        h3TerminalRawVelocityFourierComponent H 1 ξ
      ) ^ 2
    +
  norm
      (
        h3TerminalRawVelocityFourierComponent G 2 ξ
          -
        h3TerminalRawVelocityFourierComponent H 2 ξ
      ) ^ 2

/-- The raw velocity Fourier square density is globally integrable. -/
theorem rawVelocityFourierTotalSquareDensity_integrable
    (G H : H3SpectralFinVectorState) :
    Integrable
      (h3TerminalRawVelocityFourierTotalSquareDensity G H)
      volume := by

  have h0 :
      Integrable
        (
          fun ξ : H3FourierPoint3 =>
            norm
              (
                h3TerminalRawVelocityFourierComponent G 0 ξ
                  -
                h3TerminalRawVelocityFourierComponent H 0 ξ
              ) ^ 2
        )
        volume := by

    exact
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        (h3TerminalRawVelocityFourierComponent G 0)
        (h3TerminalRawVelocityFourierComponent H 0)

  have h1 :
      Integrable
        (
          fun ξ : H3FourierPoint3 =>
            norm
              (
                h3TerminalRawVelocityFourierComponent G 1 ξ
                  -
                h3TerminalRawVelocityFourierComponent H 1 ξ
              ) ^ 2
        )
        volume := by

    exact
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        (h3TerminalRawVelocityFourierComponent G 1)
        (h3TerminalRawVelocityFourierComponent H 1)

  have h2 :
      Integrable
        (
          fun ξ : H3FourierPoint3 =>
            norm
              (
                h3TerminalRawVelocityFourierComponent G 2 ξ
                  -
                h3TerminalRawVelocityFourierComponent H 2 ξ
              ) ^ 2
        )
        volume := by

    exact
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        (h3TerminalRawVelocityFourierComponent G 2)
        (h3TerminalRawVelocityFourierComponent H 2)

  unfold
    h3TerminalRawVelocityFourierTotalSquareDensity

  change
    Integrable
      (
        (
          fun ξ : H3FourierPoint3 =>
            norm
              (
                h3TerminalRawVelocityFourierComponent G 0 ξ
                  -
                h3TerminalRawVelocityFourierComponent H 0 ξ
              ) ^ 2
        )
          +
        (
          fun ξ : H3FourierPoint3 =>
            norm
              (
                h3TerminalRawVelocityFourierComponent G 1 ξ
                  -
                h3TerminalRawVelocityFourierComponent H 1 ξ
              ) ^ 2
        )
          +
        (
          fun ξ : H3FourierPoint3 =>
            norm
              (
                h3TerminalRawVelocityFourierComponent G 2 ξ
                  -
                h3TerminalRawVelocityFourierComponent H 2 ξ
              ) ^ 2
        )
      )
      volume

  exact
    (h0.add h1).add h2

/-- Global zeroth-order raw Fourier velocity square defect. -/
noncomputable def h3TerminalRawVelocityFourierTotalSquareDefect
    (G H : H3SpectralFinVectorState) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3TerminalRawVelocityFourierTotalSquareDensity G H ξ
    ∂volume

/-! ## Exact recovery of the weighted state -/

/--
A weighted spectral coordinate is recovered a.e. by multiplying its deweighted
raw Fourier coordinate by the exact H³ weight.
-/
private theorem spectralDifference_eq_weight_mul_rawDifference_ae
    (G H : H3SpectralFinVectorState)
    (j : Fin 3) :
    (
      fun ξ : H3FourierPoint3 =>
        h3TerminalSpectralDifferenceAt G H j ξ
    )
      =ᵐ[volume]
    (
      fun ξ : H3FourierPoint3 =>
        (h3SobolevFrequencyWeight ξ : ℂ)
          *
        (
          h3TerminalRawVelocityFourierComponent G j ξ
            -
          h3TerminalRawVelocityFourierComponent H j ξ
        )
    ) := by

  filter_upwards [
    h3SpectralScalarRawFourierL2_ae (G j),
    h3SpectralScalarRawFourierL2_ae (H j)
  ] with ξ hG hH

  have hCancel :
      (h3SobolevFrequencyWeight ξ : ℂ)
          *
        h3SobolevFrequencyWeightInvComplex ξ
        =
      1 := by

    rw [
      mul_comm,
      h3SobolevFrequencyWeightInvComplex_mul_weight
    ]

  unfold
    h3TerminalSpectralDifferenceAt
    h3TerminalRawVelocityFourierComponent

  calc
    (G j : H3FourierPoint3 → ℂ) ξ
          -
        (H j : H3FourierPoint3 → ℂ) ξ
        =
      1
        *
      (
        (G j : H3FourierPoint3 → ℂ) ξ
          -
        (H j : H3FourierPoint3 → ℂ) ξ
      ) := by
        rw [one_mul]

    _ =
      (
        (h3SobolevFrequencyWeight ξ : ℂ)
          *
        h3SobolevFrequencyWeightInvComplex ξ
      )
        *
      (
        (G j : H3FourierPoint3 → ℂ) ξ
          -
        (H j : H3FourierPoint3 → ℂ) ξ
      ) := by
        rw [hCancel]

    _ =
      (h3SobolevFrequencyWeight ξ : ℂ)
        *
      (
        h3SobolevFrequencyWeightInvComplex ξ
            *
          (G j : H3FourierPoint3 → ℂ) ξ
          -
        h3SobolevFrequencyWeightInvComplex ξ
            *
          (H j : H3FourierPoint3 → ℂ) ξ
      ) := by
        ring

    _ =
      (h3SobolevFrequencyWeight ξ : ℂ)
        *
      (
        h3SpectralScalarRawFourierL2 (G j) ξ
          -
        h3SpectralScalarRawFourierL2 (H j) ξ
      ) := by

        rw [hG, hH]

        rfl

/-! ## Unit-ball H³ weight control -/

/--
On the unit radial-gradient ball, the exact H³ Fourier weight-square is at most
four.
-/
theorem h3SobolevFrequencyWeight_sq_le_four_of_gradientMagnitude_lt_one
    {ξ : H3FourierPoint3}
    (hξ :
      h3FourierGradientMagnitude ξ < 1) :
    (h3SobolevFrequencyWeight ξ) ^ 2
      ≤
    4 := by

  let r : ℝ :=
    h3FourierGradientMagnitude ξ

  have hr0 :
      0 ≤ r := by

    dsimp only [r]

    exact
      h3FourierGradientMagnitude_nonneg ξ

  have hr1 :
      r ≤ 1 :=
    le_of_lt hξ

  have hq :
      r ^ 2 ≤ 1 := by

    simpa only [one_pow] using
      (
        (
          sq_le_sq₀
            hr0
            (by norm_num : (0 : ℝ) ≤ 1)
        ).2
          hr1
      )

  have hq0 :
      0 ≤ r ^ 2 :=
    sq_nonneg r

  have hq2le :
      (r ^ 2) ^ 2
        ≤
      r ^ 2 := by

    have h :=
      mul_nonneg
        hq0
        (sub_nonneg.mpr hq)

    nlinarith

  have hq2nonneg :
      0 ≤ (r ^ 2) ^ 2 :=
    sq_nonneg (r ^ 2)

  have hq3le :
      (r ^ 2) ^ 3
        ≤
      (r ^ 2) ^ 2 := by

    have h :=
      mul_nonneg
        hq2nonneg
        (sub_nonneg.mpr hq)

    nlinarith

  rw [
    h3SobolevFrequencyWeight_sq
  ]

  unfold
    h3SobolevFrequencyWeightSq

  rw [
    ← h3FourierGradientMagnitude_sq
  ]

  change
    1 + r ^ 2 + (r ^ 2) ^ 2 + (r ^ 2) ^ 3
      ≤
    4

  nlinarith

/-! ## Pointwise normalized-vorticity bound -/

/--
Every normalized-vorticity component square is controlled by four times the
total weighted spectral coordinate square.
-/
theorem normalizedVorticityComponentAmplitude_sq_le_four_mul_totalSquare
    (q : Fin 3)
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ) :
    norm
      (
        h3TerminalNormalizedVorticityComponentAmplitude
          q ξ g
      ) ^ 2
      ≤
    4
      *
    (
      norm (g 0) ^ 2
        +
      norm (g 1) ^ 2
        +
      norm (g 2) ^ 2
    ) := by

  fin_cases q

  · have hPair :=
      normalizedLongitudinalCurlPairSquareMagnitude_le_four_mul_totalSquare
        (1 : Fin 3) ξ g

    simp [
      h3TerminalNormalizedVorticityComponentAmplitude,
      h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude
    ] at hPair ⊢

    nlinarith [
      sq_nonneg
        (
          norm
            (
              h3TerminalNormalizedCurl01Amplitude
                ξ g
            )
        )
    ]

  · have hPair :=
      normalizedLongitudinalCurlPairSquareMagnitude_le_four_mul_totalSquare
        (0 : Fin 3) ξ g

    simp [
      h3TerminalNormalizedVorticityComponentAmplitude,
      h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude
    ] at hPair ⊢

    nlinarith [
      sq_nonneg
        (
          norm
            (
              h3TerminalNormalizedCurl01Amplitude
                ξ g
            )
        )
    ]

  · have hPair :=
      normalizedLongitudinalCurlPairSquareMagnitude_le_four_mul_totalSquare
        (0 : Fin 3) ξ g

    simp [
      h3TerminalNormalizedVorticityComponentAmplitude,
      h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude
    ] at hPair ⊢

    nlinarith [
      sq_nonneg
        (
          norm
            (
              h3TerminalNormalizedCurl02Amplitude
                ξ g
            )
        )
    ]

/-! ## Infrared defect controlled by raw velocity L² defect -/

/--
On radial cutoff `1`, the normalized-vorticity bad-cone low-radial square
defect is bounded by sixteen times the global raw Fourier velocity L² square
defect.
-/
theorem normalizedVorticityComponentBadConeLowRadialSquareDefect_one_le_sixteen_mul_rawVelocityFourierTotalSquareDefect
    (i q : Fin 3)
    (κ : ℝ)
    (G H : H3SpectralFinVectorState) :
    h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect
        i q κ 1 G H
      ≤
    16
      *
    h3TerminalRawVelocityFourierTotalSquareDefect
      G H := by

  let S : Set H3FourierPoint3 :=
    h3TerminalLongitudinalAngularBadCone i κ
      ∩
    h3TerminalRadialFrequencyBelow 1

  let f : H3FourierPoint3 → ℝ :=
    fun ξ =>
      norm
        (
          h3TerminalNormalizedVorticityComponentAmplitude
            q ξ
            (fun j =>
              h3TerminalSpectralDifferenceAt G H j ξ)
        ) ^ 2

  let raw : H3FourierPoint3 → ℝ :=
    h3TerminalRawVelocityFourierTotalSquareDensity
      G H

  let major : H3FourierPoint3 → ℝ :=
    fun ξ =>
      16 * raw ξ

  have hSMeas :
      MeasurableSet S := by

    exact
      (
        measurableSet_h3TerminalLongitudinalAngularBadCone
          i κ
      ).inter
        (
          measurableSet_h3TerminalRadialFrequencyBelow
            1
        )

  have hFInt :
      Integrable f volume := by

    simpa only [f] using
      normalizedVorticityComponentSquare_integrable
        q G H

  have hRawInt :
      Integrable raw volume := by

    simpa only [raw] using
      rawVelocityFourierTotalSquareDensity_integrable
        G H

  have hMajorInt :
      Integrable major volume := by

    simpa only [major] using
      hRawInt.const_mul 16

  have hRec0 :=
    spectralDifference_eq_weight_mul_rawDifference_ae
      G H (0 : Fin 3)

  have hRec1 :=
    spectralDifference_eq_weight_mul_rawDifference_ae
      G H (1 : Fin 3)

  have hRec2 :=
    spectralDifference_eq_weight_mul_rawDifference_ae
      G H (2 : Fin 3)

  have hPointGlobal :
      ∀ᵐ ξ : H3FourierPoint3 ∂volume,
        ξ ∈ S
          →
        f ξ
          ≤
        major ξ := by

    filter_upwards [
      hRec0,
      hRec1,
      hRec2
    ] with ξ h0 h1 h2

    intro hξ

    have hBelow :
        h3FourierGradientMagnitude ξ < 1 := by

      simpa only [
        S,
        h3TerminalRadialFrequencyBelow,
        Set.mem_inter_iff,
        Set.mem_ofPred_eq
      ] using
        hξ.2

    have hWeight :
        (h3SobolevFrequencyWeight ξ) ^ 2
          ≤
        4 :=
      h3SobolevFrequencyWeight_sq_le_four_of_gradientMagnitude_lt_one
        hBelow

    let r0 : ℝ :=
      norm
        (
          h3TerminalRawVelocityFourierComponent G 0 ξ
            -
          h3TerminalRawVelocityFourierComponent H 0 ξ
        ) ^ 2

    let r1 : ℝ :=
      norm
        (
          h3TerminalRawVelocityFourierComponent G 1 ξ
            -
          h3TerminalRawVelocityFourierComponent H 1 ξ
        ) ^ 2

    let r2 : ℝ :=
      norm
        (
          h3TerminalRawVelocityFourierComponent G 2 ξ
            -
          h3TerminalRawVelocityFourierComponent H 2 ξ
        ) ^ 2

    have hr0 :
        0 ≤ r0 := by
      dsimp only [r0]
      positivity

    have hr1 :
        0 ≤ r1 := by
      dsimp only [r1]
      positivity

    have hr2 :
        0 ≤ r2 := by
      dsimp only [r2]
      positivity

    have hG0 :
        norm
          (
            h3TerminalSpectralDifferenceAt
              G H 0 ξ
          ) ^ 2
          ≤
        4 * r0 := by

      rw [h0]

      dsimp only [r0]

      rw [
        norm_mul,
        mul_pow,
        Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg
          (le_of_lt
            (h3SobolevFrequencyWeight_pos ξ))
      ]

      exact
        mul_le_mul_of_nonneg_right
          hWeight
          (sq_nonneg _)

    have hG1 :
        norm
          (
            h3TerminalSpectralDifferenceAt
              G H 1 ξ
          ) ^ 2
          ≤
        4 * r1 := by

      rw [h1]

      dsimp only [r1]

      rw [
        norm_mul,
        mul_pow,
        Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg
          (le_of_lt
            (h3SobolevFrequencyWeight_pos ξ))
      ]

      exact
        mul_le_mul_of_nonneg_right
          hWeight
          (sq_nonneg _)

    have hG2 :
        norm
          (
            h3TerminalSpectralDifferenceAt
              G H 2 ξ
          ) ^ 2
          ≤
        4 * r2 := by

      rw [h2]

      dsimp only [r2]

      rw [
        norm_mul,
        mul_pow,
        Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg
          (le_of_lt
            (h3SobolevFrequencyWeight_pos ξ))
      ]

      exact
        mul_le_mul_of_nonneg_right
          hWeight
          (sq_nonneg _)

    have hVort :=
      normalizedVorticityComponentAmplitude_sq_le_four_mul_totalSquare
        q ξ
        (
          fun j =>
            h3TerminalSpectralDifferenceAt
              G H j ξ
        )

    dsimp only [f, major, raw]

    unfold
      h3TerminalRawVelocityFourierTotalSquareDensity

    dsimp only [r0, r1, r2] at hG0 hG1 hG2

    nlinarith

  have hPoint :
      f ≤ᵐ[volume.restrict S] major := by

    change
      ∀ᵐ ξ : H3FourierPoint3 ∂volume.restrict S,
        f ξ ≤ major ξ

    rw [
      ae_restrict_iff'
        hSMeas
    ]

    filter_upwards [hPointGlobal] with ξ hξ

    intro hξS

    exact
      hξ hξS

  have hIntegral :
      (∫ ξ in S, f ξ ∂volume)
        ≤
      ∫ ξ in S, major ξ ∂volume := by

    exact
      integral_mono_ae
        hFInt.integrableOn
        hMajorInt.integrableOn
        hPoint

  have hMajorNonneg :
      0 ≤ᵐ[volume] major := by

    filter_upwards with ξ

    dsimp only [major, raw]

    unfold
      h3TerminalRawVelocityFourierTotalSquareDensity

    positivity

  have hSetLe :
      (∫ ξ in S, major ξ ∂volume)
        ≤
      ∫ ξ : H3FourierPoint3,
        major ξ
        ∂volume := by

    exact
      integral_mono_measure
        Measure.restrict_le_self
        hMajorNonneg
        hMajorInt

  have hGlobal :
      (∫ ξ : H3FourierPoint3,
        major ξ
        ∂volume)
        =
      16
        *
      h3TerminalRawVelocityFourierTotalSquareDefect
        G H := by

    unfold
      h3TerminalRawVelocityFourierTotalSquareDefect

    dsimp only [major]

    rw [
      integral_const_mul
    ]

  unfold
    h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect

  change
    (∫ ξ in S, f ξ ∂volume)
      ≤
    16
      *
    h3TerminalRawVelocityFourierTotalSquareDefect
      G H

  exact
    hIntegral.trans
      (hSetLe.trans_eq hGlobal)

/-! ## Terminal raw Fourier L² Cauchy property -/

/--
Zeroth-order terminal Cauchy property for the deweighted/raw Fourier velocity.

The defect is exactly a sum of three ordinary Fourier `L²` square distances,
written as one integral.
-/
def H3TerminalVelocityRawFourierL2CauchyAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T) : Prop :=
  ∀ δ : ℝ,
    0 < δ
      →
    ∃ η : ℝ,
      0 < η
        ∧
      ∀ s t : ℝ,
        ∀ hs :
          s ∈ Set.Ioo (0 : ℝ) T,
          ∀ ht :
            t ∈ Set.Ioo (0 : ℝ) T,
            dist s T < η
              →
            dist t T < η
              →
            h3TerminalRawVelocityFourierTotalSquareDefect
                (h3TerminalVelocitySpectralStateAt
                  hH3 s hs)
                (h3TerminalVelocitySpectralStateAt
                  hH3 t ht)
              <
            δ

/--
Terminal raw Fourier `L²` Cauchy control implies the normalized-vorticity
infrared-vanishing property for every pair of component indices.
-/
theorem normalizedVorticityInfraredVanishingAtEndpoint_of_velocityRawFourierL2Cauchy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint
        hH3)
    (i q : Fin 3) :
    H3TerminalNormalizedVorticityInfraredVanishingAtEndpoint
      hH3 i q := by

  intro δ hδ

  obtain
    ⟨
      η,
      hη,
      hSmall
    ⟩ :=
    hCauchy
      (δ / 16)
      (by positivity)

  refine
    ⟨
      1,
      zero_lt_one,
      η,
      hη,
      ?_
    ⟩

  intro s t hs ht hsNear htNear κ hκ

  have hRaw :
      h3TerminalRawVelocityFourierTotalSquareDefect
          (h3TerminalVelocitySpectralStateAt
            hH3 s hs)
          (h3TerminalVelocitySpectralStateAt
            hH3 t ht)
        <
      δ / 16 :=
    hSmall
      s t hs ht
      hsNear htNear

  have hLow :
      h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect
          i q κ 1
          (h3TerminalVelocitySpectralStateAt
            hH3 s hs)
          (h3TerminalVelocitySpectralStateAt
            hH3 t ht)
        ≤
      16
        *
      h3TerminalRawVelocityFourierTotalSquareDefect
        (h3TerminalVelocitySpectralStateAt
          hH3 s hs)
        (h3TerminalVelocitySpectralStateAt
          hH3 t ht) :=
    normalizedVorticityComponentBadConeLowRadialSquareDefect_one_le_sixteen_mul_rawVelocityFourierTotalSquareDefect
      i q κ
      (h3TerminalVelocitySpectralStateAt
        hH3 s hs)
      (h3TerminalVelocitySpectralStateAt
        hH3 t ht)

  nlinarith

/-! ## Conditional branch closure from raw L² Cauchy -/

/--
If the strict-time raw Fourier velocity is terminal `L²` Cauchy, then under
hypothetical nonextension the infrared branch is impossible.  A failing
complementary vorticity component must therefore carry the positive-cutoff
high-radial raw-vorticity obstruction.
-/
theorem exists_failing_complementary_vorticityComponent_highRadialRaw_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hNoExtension :
      ¬
        ∃
          v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension
            u v T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint
        hH3)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ρ : ℝ,
      0 < ρ
        ∧
      ∃ q : Fin 3,
        q ≠ i
          ∧
        ¬
          H3TerminalActualVorticityStrongH3EndpointPath
            hH3 q
          ∧
        H3TerminalHighRadialRawVorticityBranchAtCutoff
          hH3 i q ε ρ := by

  apply
    exists_failing_complementary_vorticityComponent_highRadialRaw_of_normalizedVorticityInfraredVanishing_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical

  · intro q hq

    exact
      normalizedVorticityInfraredVanishingAtEndpoint_of_velocityRawFourierL2Cauchy
        hH3
        hCauchy
        i q

  · exact
      hε

end

end Euclidean
end Bridge
end PrimeTensor
