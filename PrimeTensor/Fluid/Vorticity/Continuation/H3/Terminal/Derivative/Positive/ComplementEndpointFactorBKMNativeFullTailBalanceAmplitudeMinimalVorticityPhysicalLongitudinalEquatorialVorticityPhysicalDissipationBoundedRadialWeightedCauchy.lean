import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityPhysicalDissipationBoundedFrequencyFixedSpectralComponent

/-!
# Raw Fourier Cauchy control implies bounded-radial weighted spectral Cauchy control

The current compactness frontier has isolated a bounded-frequency spectral
concentration mechanism.  Before using small-set compactness, we need the
quotient-safe invariant bridge from the assumed terminal raw Fourier `L²`
Cauchy property to the weighted H³ spectral state on every fixed bounded
frequency region.

On the radial region

    |D(ξ)| < ρ,

the exact H³ Sobolev weight has the explicit square ceiling

    1 + ρ² + ρ⁴ + ρ⁶.

Since the weighted spectral difference is exactly the Sobolev weight times the
deweighted/raw Fourier difference almost everywhere, the localized weighted
three-component square defect is bounded by this ceiling times the global raw
Fourier velocity square defect.

Consequently terminal raw Fourier `L²` Cauchy control implies terminal
weighted-spectral `L²` Cauchy control on every fixed radial cutoff.

This is the invariant bridge needed for the next compactness step; no
fixed-frequency evaluation continuity is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalDissipationBoundedRadialWeightedCauchy
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalPhysicalDissipationBoundedRadialWeightedCauchy :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Fixed-cutoff Sobolev-weight ceiling -/

/--
Explicit ceiling for the exact H³ Sobolev weight-square on the radial region
`|D| < ρ`.
-/
def h3TerminalRadialSobolevWeightSquareCeiling
    (ρ : ℝ) : ℝ :=
  1
    + ρ ^ 2
    + (ρ ^ 2) ^ 2
    + (ρ ^ 2) ^ 3

theorem h3TerminalRadialSobolevWeightSquareCeiling_pos
    (ρ : ℝ) :
    0 < h3TerminalRadialSobolevWeightSquareCeiling ρ := by
  unfold h3TerminalRadialSobolevWeightSquareCeiling
  positivity

/--
On `|D(ξ)| < ρ`, for nonnegative `ρ`, the exact H³ Sobolev weight-square is
bounded by the explicit radial ceiling.
-/
theorem h3SobolevFrequencyWeight_sq_le_radialCeiling_of_gradientMagnitude_lt
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {ξ : H3FourierPoint3}
    (hξ :
      h3FourierGradientMagnitude ξ < ρ) :
    (h3SobolevFrequencyWeight ξ) ^ 2
      ≤
    h3TerminalRadialSobolevWeightSquareCeiling ρ := by

  let r : ℝ :=
    h3FourierGradientMagnitude ξ

  have hr0 :
      0 ≤ r := by
    dsimp only [r]
    exact
      h3FourierGradientMagnitude_nonneg ξ

  have hrρ :
      r ≤ ρ :=
    le_of_lt hξ

  have hr2 :
      r ^ 2 ≤ ρ ^ 2 :=
    pow_le_pow_left₀
      hr0
      hrρ
      2

  have hr2nonneg :
      0 ≤ r ^ 2 := by
    positivity

  have hr4 :
      (r ^ 2) ^ 2
        ≤
      (ρ ^ 2) ^ 2 :=
    pow_le_pow_left₀
      hr2nonneg
      hr2
      2

  have hr6 :
      (r ^ 2) ^ 3
        ≤
      (ρ ^ 2) ^ 3 :=
    pow_le_pow_left₀
      hr2nonneg
      hr2
      3

  rw [
    h3SobolevFrequencyWeight_sq
  ]

  unfold
    h3SobolevFrequencyWeightSq
    h3TerminalRadialSobolevWeightSquareCeiling

  rw [
    ← h3FourierGradientMagnitude_sq
  ]

  change
    1 + r ^ 2 + (r ^ 2) ^ 2 + (r ^ 2) ^ 3
      ≤
    1 + ρ ^ 2 + (ρ ^ 2) ^ 2 + (ρ ^ 2) ^ 3

  linarith

/-! ## Localized weighted spectral square defect -/

/--
Pointwise total square difference of two weighted three-component H³ spectral
states.
-/
def h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity
    (G H : H3SpectralFinVectorState)
    (ξ : H3FourierPoint3) : ℝ :=
  norm (h3TerminalSpectralDifferenceAt G H 0 ξ) ^ 2
    +
  norm (h3TerminalSpectralDifferenceAt G H 1 ξ) ^ 2
    +
  norm (h3TerminalSpectralDifferenceAt G H 2 ξ) ^ 2

/--
Localized weighted spectral square defect below one radial cutoff.
-/
noncomputable def h3TerminalWeightedSpectralVelocityRadialSquareDefect
    (ρ : ℝ)
    (G H : H3SpectralFinVectorState) : ℝ :=
  ∫ ξ in h3TerminalRadialFrequencyBelow ρ,
    h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity
      G H ξ
    ∂volume

theorem h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity_nonneg
    (G H : H3SpectralFinVectorState)
    (ξ : H3FourierPoint3) :
    0 ≤
      h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity
        G H ξ := by
  unfold h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity
  positivity

theorem h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity_integrable
    (G H : H3SpectralFinVectorState) :
    Integrable
      (h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity
        G H)
      volume := by

  have h0 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          norm (h3TerminalSpectralDifferenceAt G H 0 ξ) ^ 2)
        volume := by
    exact
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        (G 0)
        (H 0)

  have h1 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          norm (h3TerminalSpectralDifferenceAt G H 1 ξ) ^ 2)
        volume := by
    exact
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        (G 1)
        (H 1)

  have h2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          norm (h3TerminalSpectralDifferenceAt G H 2 ξ) ^ 2)
        volume := by
    exact
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        (G 2)
        (H 2)

  unfold
    h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity

  exact
    (h0.add h1).add h2

/-! ## Exact a.e. reweighting of spectral differences -/

/--
A weighted spectral coordinate difference is exactly the H³ Sobolev weight
times the corresponding raw Fourier coordinate difference almost everywhere.
-/
theorem h3TerminalSpectralDifference_eq_weight_mul_rawDifference_ae
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

/-! ## Pointwise and integrated bounded-radial comparison -/

/--
On a fixed radial region, the total weighted spectral square difference is
bounded almost everywhere by the radial Sobolev ceiling times the raw Fourier
velocity square difference.
-/
theorem weightedSpectralVelocityTotalSquareDifferenceDensity_le_radialCeiling_mul_raw_ae
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (G H : H3SpectralFinVectorState) :
    ∀ᵐ ξ : H3FourierPoint3
      ∂(volume.restrict (h3TerminalRadialFrequencyBelow ρ)),
      h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity
          G H ξ
        ≤
      h3TerminalRadialSobolevWeightSquareCeiling ρ
        *
      h3TerminalRawVelocityFourierTotalSquareDensity
        G H ξ := by

  have hS :
      MeasurableSet
        (h3TerminalRadialFrequencyBelow ρ) :=
    measurableSet_h3TerminalRadialFrequencyBelow ρ

  rw [
    ae_restrict_iff' hS
  ]

  filter_upwards [
    h3TerminalSpectralDifference_eq_weight_mul_rawDifference_ae
      G H 0,
    h3TerminalSpectralDifference_eq_weight_mul_rawDifference_ae
      G H 1,
    h3TerminalSpectralDifference_eq_weight_mul_rawDifference_ae
      G H 2
  ] with ξ h0 h1 h2

  intro hξ

  have hW :
      (h3SobolevFrequencyWeight ξ) ^ 2
        ≤
      h3TerminalRadialSobolevWeightSquareCeiling ρ :=
    h3SobolevFrequencyWeight_sq_le_radialCeiling_of_gradientMagnitude_lt
      hρ
      hξ

  have hWNonneg :
      0 ≤ h3SobolevFrequencyWeight ξ :=
    (h3SobolevFrequencyWeight_pos ξ).le

  have hRaw0Nonneg :
      0 ≤
        norm
          (
            h3TerminalRawVelocityFourierComponent G 0 ξ
              -
            h3TerminalRawVelocityFourierComponent H 0 ξ
          ) ^ 2 := by
    positivity

  have hRaw1Nonneg :
      0 ≤
        norm
          (
            h3TerminalRawVelocityFourierComponent G 1 ξ
              -
            h3TerminalRawVelocityFourierComponent H 1 ξ
          ) ^ 2 := by
    positivity

  have hRaw2Nonneg :
      0 ≤
        norm
          (
            h3TerminalRawVelocityFourierComponent G 2 ξ
              -
            h3TerminalRawVelocityFourierComponent H 2 ξ
          ) ^ 2 := by
    positivity

  have hComp0 :
      norm (h3TerminalSpectralDifferenceAt G H 0 ξ) ^ 2
        =
      (h3SobolevFrequencyWeight ξ) ^ 2
        *
      norm
        (
          h3TerminalRawVelocityFourierComponent G 0 ξ
            -
          h3TerminalRawVelocityFourierComponent H 0 ξ
        ) ^ 2 := by

    rw [h0, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hWNonneg]
    ring

  have hComp1 :
      norm (h3TerminalSpectralDifferenceAt G H 1 ξ) ^ 2
        =
      (h3SobolevFrequencyWeight ξ) ^ 2
        *
      norm
        (
          h3TerminalRawVelocityFourierComponent G 1 ξ
            -
          h3TerminalRawVelocityFourierComponent H 1 ξ
        ) ^ 2 := by

    rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hWNonneg]
    ring

  have hComp2 :
      norm (h3TerminalSpectralDifferenceAt G H 2 ξ) ^ 2
        =
      (h3SobolevFrequencyWeight ξ) ^ 2
        *
      norm
        (
          h3TerminalRawVelocityFourierComponent G 2 ξ
            -
          h3TerminalRawVelocityFourierComponent H 2 ξ
        ) ^ 2 := by

    rw [h2, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hWNonneg]
    ring

  unfold
    h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity
    h3TerminalRawVelocityFourierTotalSquareDensity

  rw [
    hComp0,
    hComp1,
    hComp2
  ]

  have hSumNonneg :
      0 ≤
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
          ) ^ 2 := by
    positivity

  calc
    (h3SobolevFrequencyWeight ξ) ^ 2
          *
        norm
          (
            h3TerminalRawVelocityFourierComponent G 0 ξ
              -
            h3TerminalRawVelocityFourierComponent H 0 ξ
          ) ^ 2
      +
      (h3SobolevFrequencyWeight ξ) ^ 2
          *
        norm
          (
            h3TerminalRawVelocityFourierComponent G 1 ξ
              -
            h3TerminalRawVelocityFourierComponent H 1 ξ
          ) ^ 2
      +
      (h3SobolevFrequencyWeight ξ) ^ 2
          *
        norm
          (
            h3TerminalRawVelocityFourierComponent G 2 ξ
              -
            h3TerminalRawVelocityFourierComponent H 2 ξ
          ) ^ 2
        =
      (h3SobolevFrequencyWeight ξ) ^ 2
        *
      (
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
      ) := by
        ring

    _ ≤
      h3TerminalRadialSobolevWeightSquareCeiling ρ
        *
      (
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
      ) :=
        mul_le_mul_of_nonneg_right
          hW
          hSumNonneg

/--
Localized weighted spectral square difference is bounded by the explicit radial
Sobolev ceiling times the global raw Fourier square defect.
-/
theorem weightedSpectralVelocityRadialSquareDefect_le_ceiling_mul_rawVelocityFourierTotalSquareDefect
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (G H : H3SpectralFinVectorState) :
    h3TerminalWeightedSpectralVelocityRadialSquareDefect
        ρ G H
      ≤
    h3TerminalRadialSobolevWeightSquareCeiling ρ
      *
    h3TerminalRawVelocityFourierTotalSquareDefect
      G H := by

  let S : Set H3FourierPoint3 :=
    h3TerminalRadialFrequencyBelow ρ

  let f : H3FourierPoint3 → ℝ :=
    h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity
      G H

  let g : H3FourierPoint3 → ℝ :=
    h3TerminalRawVelocityFourierTotalSquareDensity
      G H

  let K : ℝ :=
    h3TerminalRadialSobolevWeightSquareCeiling ρ

  have hFInt :
      Integrable f volume := by
    dsimp only [f]
    exact
      h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity_integrable
        G H

  have hGInt :
      Integrable g volume := by
    dsimp only [g]
    exact
      rawVelocityFourierTotalSquareDensity_integrable
        G H

  have hKNonneg :
      0 ≤ K := by
    dsimp only [K]
    exact
      (h3TerminalRadialSobolevWeightSquareCeiling_pos ρ).le

  have hKGInt :
      Integrable
        (fun ξ : H3FourierPoint3 => K * g ξ)
        volume := by
    simpa only [Pi.mul_apply] using
      hGInt.const_mul K

  have hPoint :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume.restrict S),
        f ξ ≤ K * g ξ := by
    dsimp only [S, f, g, K]
    exact
      weightedSpectralVelocityTotalSquareDifferenceDensity_le_radialCeiling_mul_raw_ae
        hρ
        G H

  have hSetLe :
      (∫ ξ : H3FourierPoint3, f ξ ∂(volume.restrict S))
        ≤
      ∫ ξ : H3FourierPoint3, K * g ξ ∂(volume.restrict S) := by

    exact
      integral_mono_ae
        (hFInt.mono_measure Measure.restrict_le_self)
        (hKGInt.mono_measure Measure.restrict_le_self)
        hPoint

  have hGNonneg :
      0 ≤ᵐ[volume] g := by
    exact
      Eventually.of_forall
        (fun ξ => by
          dsimp only [g]
          unfold h3TerminalRawVelocityFourierTotalSquareDensity
          positivity)

  have hRestrictedRawLe :
      (∫ ξ : H3FourierPoint3, g ξ ∂(volume.restrict S))
        ≤
      ∫ ξ : H3FourierPoint3, g ξ ∂volume := by

    exact
      integral_mono_measure
        Measure.restrict_le_self
        hGNonneg
        hGInt

  unfold
    h3TerminalWeightedSpectralVelocityRadialSquareDefect
    h3TerminalRawVelocityFourierTotalSquareDefect

  change
    (∫ ξ : H3FourierPoint3, f ξ ∂(volume.restrict S))
      ≤
    K * ∫ ξ : H3FourierPoint3, g ξ ∂volume

  calc
    (∫ ξ : H3FourierPoint3, f ξ ∂(volume.restrict S))
        ≤
      ∫ ξ : H3FourierPoint3, K * g ξ ∂(volume.restrict S) :=
        hSetLe

    _ =
      K *
        ∫ ξ : H3FourierPoint3, g ξ ∂(volume.restrict S) := by
        rw [integral_const_mul]

    _ ≤
      K *
        ∫ ξ : H3FourierPoint3, g ξ ∂volume :=
        mul_le_mul_of_nonneg_left
          hRestrictedRawLe
          hKNonneg

/-! ## Terminal bounded-radial weighted Cauchy property -/

/--
Terminal Cauchy control for the weighted H³ spectral velocity after restricting
to one fixed bounded radial region.
-/
def H3TerminalVelocityWeightedSpectralL2CauchyBelowRadialCutoffAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ρ : ℝ) : Prop :=
  ∀ δ : ℝ,
    0 < δ
      →
    ∃ η : ℝ,
      0 < η
        ∧
      ∀ s t : ℝ,
        ∀ hs : s ∈ Set.Ioo (0 : ℝ) T,
          ∀ ht : t ∈ Set.Ioo (0 : ℝ) T,
            dist s T < η
              →
            dist t T < η
              →
            h3TerminalWeightedSpectralVelocityRadialSquareDefect
                ρ
                (h3TerminalVelocitySpectralStateAt
                  hH3 s hs)
                (h3TerminalVelocitySpectralStateAt
                  hH3 t ht)
              <
            δ

/--
Raw Fourier terminal `L²` Cauchy control implies weighted spectral terminal
`L²` Cauchy control on every fixed nonnegative radial cutoff.
-/
theorem weightedSpectralL2CauchyBelowRadialCutoffAtEndpoint_of_velocityRawFourierL2Cauchy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    H3TerminalVelocityWeightedSpectralL2CauchyBelowRadialCutoffAtEndpoint
      hH3 ρ := by

  intro δ hδ

  let K : ℝ :=
    h3TerminalRadialSobolevWeightSquareCeiling ρ

  have hK :
      0 < K := by
    dsimp only [K]
    exact
      h3TerminalRadialSobolevWeightSquareCeiling_pos ρ

  obtain
    ⟨η, hη, hRaw⟩ :=
    hCauchy
      (δ / K)
      (div_pos hδ hK)

  refine
    ⟨
      η,
      hη,
      ?_
    ⟩

  intro s t hs ht hsNear htNear

  have hRawSmall :
      h3TerminalRawVelocityFourierTotalSquareDefect
          (h3TerminalVelocitySpectralStateAt
            hH3 s hs)
          (h3TerminalVelocitySpectralStateAt
            hH3 t ht)
        <
      δ / K :=
    hRaw
      s t hs ht
      hsNear htNear

  have hLocal :
      h3TerminalWeightedSpectralVelocityRadialSquareDefect
          ρ
          (h3TerminalVelocitySpectralStateAt
            hH3 s hs)
          (h3TerminalVelocitySpectralStateAt
            hH3 t ht)
        ≤
      K
        *
      h3TerminalRawVelocityFourierTotalSquareDefect
          (h3TerminalVelocitySpectralStateAt
            hH3 s hs)
          (h3TerminalVelocitySpectralStateAt
            hH3 t ht) := by

    dsimp only [K]

    exact
      weightedSpectralVelocityRadialSquareDefect_le_ceiling_mul_rawVelocityFourierTotalSquareDefect
        hρ
        (h3TerminalVelocitySpectralStateAt
          hH3 s hs)
        (h3TerminalVelocitySpectralStateAt
          hH3 t ht)

  have hScaled :
      K
        *
      h3TerminalRawVelocityFourierTotalSquareDefect
          (h3TerminalVelocitySpectralStateAt
            hH3 s hs)
          (h3TerminalVelocitySpectralStateAt
            hH3 t ht)
        <
      K * (δ / K) :=
    mul_lt_mul_of_pos_left
      hRawSmall
      hK

  have hCancel :
      K * (δ / K) = δ := by
    field_simp [ne_of_gt hK]

  exact
    lt_of_le_of_lt
      hLocal
      (by
        simpa only [hCancel] using hScaled)

end

end Euclidean
end Bridge
end PrimeTensor
