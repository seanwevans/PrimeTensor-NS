import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialNormalizedCurl

/-!
# Integrated normalized-curl mass on the equatorial obstruction

The previous checkpoint proved the pointwise degree-zero estimate

    ((1 - κ²) / 2) |g_i|²
      - κ² |g_perp|²
      ≤
    normalizedCurlPair_i(g)²

on the longitudinal angular bad cone.

This file integrates that inequality and combines it with the two already
established terminal facts on the surviving physical-vorticity branch:

* the longitudinal bad-cone H³ defect carries a fixed positive amount of mass;
* the two transverse velocity components are pathwise strong-H³ Cauchy.

For every fixed `0 < κ ≤ 1/2` and every separation scale `ε > 0`,
arbitrarily close to the terminal time there are two strict times for which
the normalized curl pair involving the longitudinal coordinate carries more
than `ε² / 16` of square mass on the bad cone.

All multipliers are degree zero.  No fourth derivative or H⁴ estimate is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalLongitudinalEquatorialNormalizedCurlMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Measurability of the normalized multiplier -/

theorem measurable_h3TerminalNormalizedDerivativeSymbol
    (j : Fin 3) :
    Measurable
      (fun ξ : H3FourierPoint3 =>
        h3TerminalNormalizedDerivativeSymbol j ξ) := by

  unfold h3TerminalNormalizedDerivativeSymbol

  have hGrad :
      Measurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientMagnitude ξ) := by
    unfold h3FourierGradientMagnitude
    measurability

  have hDeriv :
      Measurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol j ξ) :=
    (h3FourierDerivativeSymbol_continuous j).measurable

  have hDen :
      Measurable
        (fun ξ : H3FourierPoint3 =>
          (h3FourierGradientMagnitude ξ : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      hGrad

  exact
    Measurable.ite
      (measurableSet_eq_fun hGrad measurable_const)
      measurable_const
      (hDeriv.div hDen)

/-! ## Raw difference measurability -/

private theorem terminalSpectralDifferenceAt_aestronglyMeasurable
    (G H : H3SpectralFinVectorState)
    (j : Fin 3) :
    AEStronglyMeasurable
      (fun ξ : H3FourierPoint3 =>
        h3TerminalSpectralDifferenceAt G H j ξ)
      volume := by

  unfold h3TerminalSpectralDifferenceAt

  exact
    (MeasureTheory.Lp.aestronglyMeasurable (G j)).sub
      (MeasureTheory.Lp.aestronglyMeasurable (H j))

private theorem terminalSpectralDifferenceAt_sq_integrable_normalizedCurlMass
    (G H : H3SpectralFinVectorState)
    (j : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖h3TerminalSpectralDifferenceAt G H j ξ‖ ^ 2)
      volume := by

  simpa [
    h3TerminalSpectralDifferenceAt
  ] using
    h3FourierComplexL2_pointwise_sub_norm_sq_integrable
      (G j)
      (H j)

/-! ## Pointwise coarse upper bound for normalized curl -/

private theorem normalizedDerivativeSymbol_mul_norm_le
    (j : Fin 3)
    (ξ : H3FourierPoint3)
    (z : ℂ) :
    ‖h3TerminalNormalizedDerivativeSymbol j ξ * z‖
      ≤
    ‖z‖ := by

  rw [norm_mul]

  calc
    ‖h3TerminalNormalizedDerivativeSymbol j ξ‖ * ‖z‖
        ≤
      1 * ‖z‖ :=
        mul_le_mul_of_nonneg_right
          (norm_h3TerminalNormalizedDerivativeSymbol_le_one j ξ)
          (norm_nonneg _)
    _ = ‖z‖ := one_mul _

private theorem norm_sub_sq_le_two_mul_sum_sq
    (a b : ℂ) :
    ‖a - b‖ ^ 2
      ≤
    2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by

  have hTri :
      ‖a - b‖
        ≤
      ‖a‖ + ‖b‖ :=
    norm_sub_le a b

  have hSq :
      ‖a - b‖ ^ 2
        ≤
      (‖a‖ + ‖b‖) ^ 2 :=
    (
      sq_le_sq₀
        (norm_nonneg _)
        (
          add_nonneg
            (norm_nonneg _)
            (norm_nonneg _)
        )
    ).2
      hTri

  nlinarith [
    sq_nonneg (‖a‖ - ‖b‖)
  ]

private theorem normalizedCurl01_sq_le
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ) :
    ‖h3TerminalNormalizedCurl01Amplitude ξ g‖ ^ 2
      ≤
    2 * (‖g 0‖ ^ 2 + ‖g 1‖ ^ 2) := by

  have hBase :=
    norm_sub_sq_le_two_mul_sum_sq
      (
        h3TerminalNormalizedDerivativeSymbol (1 : Fin 3) ξ
          *
        g 0
      )
      (
        h3TerminalNormalizedDerivativeSymbol (0 : Fin 3) ξ
          *
        g 1
      )

  have h0 :=
    normalizedDerivativeSymbol_mul_norm_le
      (1 : Fin 3) ξ (g 0)

  have h1 :=
    normalizedDerivativeSymbol_mul_norm_le
      (0 : Fin 3) ξ (g 1)

  have h0sq :
      ‖h3TerminalNormalizedDerivativeSymbol (1 : Fin 3) ξ * g 0‖ ^ 2
        ≤
      ‖g 0‖ ^ 2 :=
    (
      sq_le_sq₀
        (norm_nonneg _)
        (norm_nonneg _)
    ).2
      h0

  have h1sq :
      ‖h3TerminalNormalizedDerivativeSymbol (0 : Fin 3) ξ * g 1‖ ^ 2
        ≤
      ‖g 1‖ ^ 2 :=
    (
      sq_le_sq₀
        (norm_nonneg _)
        (norm_nonneg _)
    ).2
      h1

  unfold h3TerminalNormalizedCurl01Amplitude

  nlinarith

private theorem normalizedCurl02_sq_le
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ) :
    ‖h3TerminalNormalizedCurl02Amplitude ξ g‖ ^ 2
      ≤
    2 * (‖g 0‖ ^ 2 + ‖g 2‖ ^ 2) := by

  have hBase :=
    norm_sub_sq_le_two_mul_sum_sq
      (
        h3TerminalNormalizedDerivativeSymbol (2 : Fin 3) ξ
          *
        g 0
      )
      (
        h3TerminalNormalizedDerivativeSymbol (0 : Fin 3) ξ
          *
        g 2
      )

  have h0 :=
    normalizedDerivativeSymbol_mul_norm_le
      (2 : Fin 3) ξ (g 0)

  have h2 :=
    normalizedDerivativeSymbol_mul_norm_le
      (0 : Fin 3) ξ (g 2)

  have h0sq :
      ‖h3TerminalNormalizedDerivativeSymbol (2 : Fin 3) ξ * g 0‖ ^ 2
        ≤
      ‖g 0‖ ^ 2 :=
    (
      sq_le_sq₀
        (norm_nonneg _)
        (norm_nonneg _)
    ).2
      h0

  have h2sq :
      ‖h3TerminalNormalizedDerivativeSymbol (0 : Fin 3) ξ * g 2‖ ^ 2
        ≤
      ‖g 2‖ ^ 2 :=
    (
      sq_le_sq₀
        (norm_nonneg _)
        (norm_nonneg _)
    ).2
      h2

  unfold h3TerminalNormalizedCurl02Amplitude

  nlinarith

private theorem normalizedCurl12_sq_le
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ) :
    ‖h3TerminalNormalizedCurl12Amplitude ξ g‖ ^ 2
      ≤
    2 * (‖g 1‖ ^ 2 + ‖g 2‖ ^ 2) := by

  have hBase :=
    norm_sub_sq_le_two_mul_sum_sq
      (
        h3TerminalNormalizedDerivativeSymbol (2 : Fin 3) ξ
          *
        g 1
      )
      (
        h3TerminalNormalizedDerivativeSymbol (1 : Fin 3) ξ
          *
        g 2
      )

  have h1 :=
    normalizedDerivativeSymbol_mul_norm_le
      (2 : Fin 3) ξ (g 1)

  have h2 :=
    normalizedDerivativeSymbol_mul_norm_le
      (1 : Fin 3) ξ (g 2)

  have h1sq :
      ‖h3TerminalNormalizedDerivativeSymbol (2 : Fin 3) ξ * g 1‖ ^ 2
        ≤
      ‖g 1‖ ^ 2 :=
    (
      sq_le_sq₀
        (norm_nonneg _)
        (norm_nonneg _)
    ).2
      h1

  have h2sq :
      ‖h3TerminalNormalizedDerivativeSymbol (1 : Fin 3) ξ * g 2‖ ^ 2
        ≤
      ‖g 2‖ ^ 2 :=
    (
      sq_le_sq₀
        (norm_nonneg _)
        (norm_nonneg _)
    ).2
      h2

  unfold h3TerminalNormalizedCurl12Amplitude

  nlinarith

theorem normalizedLongitudinalCurlPairSquareMagnitude_le_four_mul_totalSquare
    (i : Fin 3)
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ) :
    h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude
        i ξ g
      ≤
    4 *
      (
        ‖g 0‖ ^ 2
          +
        ‖g 1‖ ^ 2
          +
        ‖g 2‖ ^ 2
      ) := by

  have h01 :=
    normalizedCurl01_sq_le ξ g

  have h02 :=
    normalizedCurl02_sq_le ξ g

  have h12 :=
    normalizedCurl12_sq_le ξ g

  fin_cases i <;>
    simp [
      h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude
    ] <;>
    nlinarith

/-! ## Integrability of normalized curl pair square -/

private theorem normalizedLongitudinalCurlPairSquare_aestronglyMeasurable
    (i : Fin 3)
    (G H : H3SpectralFinVectorState) :
    AEStronglyMeasurable
      (
        fun ξ : H3FourierPoint3 =>
          h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude
            i ξ
            (fun j =>
              h3TerminalSpectralDifferenceAt G H j ξ)
      )
      volume := by

  let μ :
      Measure[
        measureSpaceOfInnerProductSpace.toMeasurableSpace
      ] H3FourierPoint3 :=
    volume

  change
    AEStronglyMeasurable
      (
        fun ξ : H3FourierPoint3 =>
          h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude
            i ξ
            (fun j =>
              h3TerminalSpectralDifferenceAt G H j ξ)
      )
      μ

  have hD :
      ∀ j : Fin 3,
        AEStronglyMeasurable
          (fun ξ : H3FourierPoint3 =>
            h3TerminalNormalizedDerivativeSymbol j ξ)
          μ := by
    intro j

    exact
      (measurable_h3TerminalNormalizedDerivativeSymbol j).aestronglyMeasurable

  have hG :
      ∀ j : Fin 3,
        AEStronglyMeasurable
          (fun ξ : H3FourierPoint3 =>
            h3TerminalSpectralDifferenceAt G H j ξ)
          μ := by
    intro j

    unfold h3TerminalSpectralDifferenceAt

    exact
      (MeasureTheory.Lp.aestronglyMeasurable (G j)).sub
        (MeasureTheory.Lp.aestronglyMeasurable (H j))

  have h01 :
      AEStronglyMeasurable
        (
          fun ξ : H3FourierPoint3 =>
            h3TerminalNormalizedCurl01Amplitude
              ξ
              (fun j =>
                h3TerminalSpectralDifferenceAt G H j ξ)
        )
        μ := by
    unfold h3TerminalNormalizedCurl01Amplitude

    exact
      ((hD 1).mul (hG 0)).sub
        ((hD 0).mul (hG 1))

  have h02 :
      AEStronglyMeasurable
        (
          fun ξ : H3FourierPoint3 =>
            h3TerminalNormalizedCurl02Amplitude
              ξ
              (fun j =>
                h3TerminalSpectralDifferenceAt G H j ξ)
        )
        μ := by
    unfold h3TerminalNormalizedCurl02Amplitude

    exact
      ((hD 2).mul (hG 0)).sub
        ((hD 0).mul (hG 2))

  have h12 :
      AEStronglyMeasurable
        (
          fun ξ : H3FourierPoint3 =>
            h3TerminalNormalizedCurl12Amplitude
              ξ
              (fun j =>
                h3TerminalSpectralDifferenceAt G H j ξ)
        )
        μ := by
    unfold h3TerminalNormalizedCurl12Amplitude

    exact
      ((hD 2).mul (hG 1)).sub
        ((hD 1).mul (hG 2))

  have h01sq :
      AEStronglyMeasurable
        (
          fun ξ : H3FourierPoint3 =>
            norm
              (
                h3TerminalNormalizedCurl01Amplitude
                  ξ
                  (fun j =>
                    h3TerminalSpectralDifferenceAt G H j ξ)
              ) ^ 2
        )
        μ :=
    (
      h01.norm.aemeasurable.pow_const 2
    ).aestronglyMeasurable

  have h02sq :
      AEStronglyMeasurable
        (
          fun ξ : H3FourierPoint3 =>
            norm
              (
                h3TerminalNormalizedCurl02Amplitude
                  ξ
                  (fun j =>
                    h3TerminalSpectralDifferenceAt G H j ξ)
              ) ^ 2
        )
        μ :=
    (
      h02.norm.aemeasurable.pow_const 2
    ).aestronglyMeasurable

  have h12sq :
      AEStronglyMeasurable
        (
          fun ξ : H3FourierPoint3 =>
            norm
              (
                h3TerminalNormalizedCurl12Amplitude
                  ξ
                  (fun j =>
                    h3TerminalSpectralDifferenceAt G H j ξ)
              ) ^ 2
        )
        μ :=
    (
      h12.norm.aemeasurable.pow_const 2
    ).aestronglyMeasurable

  fin_cases i

  · change
      AEStronglyMeasurable
        (
          (fun ξ : H3FourierPoint3 =>
            norm
              (
                h3TerminalNormalizedCurl01Amplitude
                  ξ
                  (fun j =>
                    h3TerminalSpectralDifferenceAt G H j ξ)
              ) ^ 2)
            +
          (fun ξ : H3FourierPoint3 =>
            norm
              (
                h3TerminalNormalizedCurl02Amplitude
                  ξ
                  (fun j =>
                    h3TerminalSpectralDifferenceAt G H j ξ)
              ) ^ 2)
        )
        μ

    exact
      h01sq.add h02sq

  · change
      AEStronglyMeasurable
        (
          (fun ξ : H3FourierPoint3 =>
            norm
              (
                h3TerminalNormalizedCurl01Amplitude
                  ξ
                  (fun j =>
                    h3TerminalSpectralDifferenceAt G H j ξ)
              ) ^ 2)
            +
          (fun ξ : H3FourierPoint3 =>
            norm
              (
                h3TerminalNormalizedCurl12Amplitude
                  ξ
                  (fun j =>
                    h3TerminalSpectralDifferenceAt G H j ξ)
              ) ^ 2)
        )
        μ

    exact
      h01sq.add h12sq

  · change
      AEStronglyMeasurable
        (
          (fun ξ : H3FourierPoint3 =>
            norm
              (
                h3TerminalNormalizedCurl02Amplitude
                  ξ
                  (fun j =>
                    h3TerminalSpectralDifferenceAt G H j ξ)
              ) ^ 2)
            +
          (fun ξ : H3FourierPoint3 =>
            norm
              (
                h3TerminalNormalizedCurl12Amplitude
                  ξ
                  (fun j =>
                    h3TerminalSpectralDifferenceAt G H j ξ)
              ) ^ 2)
        )
        μ

    exact
      h02sq.add h12sq

private theorem normalizedLongitudinalCurlPairSquare_integrable
    (i : Fin 3)
    (G H : H3SpectralFinVectorState) :
    Integrable
      (
        fun ξ : H3FourierPoint3 =>
          h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude
            i ξ
            (fun j =>
              h3TerminalSpectralDifferenceAt G H j ξ)
      )
      volume := by

  have h0 :=
    terminalSpectralDifferenceAt_sq_integrable_normalizedCurlMass
      G H (0 : Fin 3)

  have h1 :=
    terminalSpectralDifferenceAt_sq_integrable_normalizedCurlMass
      G H (1 : Fin 3)

  have h2 :=
    terminalSpectralDifferenceAt_sq_integrable_normalizedCurlMass
      G H (2 : Fin 3)

  have hMajor :
      Integrable
        (
          fun ξ : H3FourierPoint3 =>
            4 *
              (
                ‖h3TerminalSpectralDifferenceAt G H 0 ξ‖ ^ 2
                  +
                ‖h3TerminalSpectralDifferenceAt G H 1 ξ‖ ^ 2
                  +
                ‖h3TerminalSpectralDifferenceAt G H 2 ξ‖ ^ 2
              )
        )
        volume :=
    ((h0.add h1).add h2).const_mul 4

  apply
    Integrable.mono'
      hMajor
      (
        normalizedLongitudinalCurlPairSquare_aestronglyMeasurable
          i G H
      )

  filter_upwards with ξ

  have hNonneg :
      0
        ≤
      h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude
        i ξ
        (fun j =>
          h3TerminalSpectralDifferenceAt G H j ξ) := by

    fin_cases i <;>
      simp [
        h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude
      ] <;>
      positivity

  rw [
    Real.norm_eq_abs,
    abs_of_nonneg hNonneg
  ]

  exact
    normalizedLongitudinalCurlPairSquareMagnitude_le_four_mul_totalSquare
      i ξ
      (fun j =>
        h3TerminalSpectralDifferenceAt G H j ξ)

/-! ## Bad-cone masses -/

/--
Transverse velocity square defect restricted to the longitudinal bad cone.
-/
noncomputable def h3TerminalTransverseBadConeSquareDefect
    (i : Fin 3)
    (κ : ℝ)
    (G H : H3SpectralFinVectorState) : ℝ :=
  ∫ ξ in h3TerminalLongitudinalAngularBadCone i κ,
    h3TerminalTransverseSpectralSquareMagnitude
      i
      (fun j =>
        h3TerminalSpectralDifferenceAt G H j ξ)

/--
Normalized curl-pair square defect restricted to the longitudinal bad cone.
-/
noncomputable def h3TerminalNormalizedLongitudinalCurlPairBadConeSquareDefect
    (i : Fin 3)
    (κ : ℝ)
    (G H : H3SpectralFinVectorState) : ℝ :=
  ∫ ξ in h3TerminalLongitudinalAngularBadCone i κ,
    h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude
      i ξ
      (fun j =>
        h3TerminalSpectralDifferenceAt G H j ξ)

/--
Bad-cone transverse square defect is bounded by the corresponding global
transverse H³ norm-square defect.
-/
theorem transverseBadConeSquareDefect_le_globalNormSquare
    (i : Fin 3)
    (κ : ℝ)
    (G H : H3SpectralFinVectorState) :
    h3TerminalTransverseBadConeSquareDefect
        i κ G H
      ≤
    h3TerminalTransverseSpectralNormSquareMagnitude
        i G H := by

  fin_cases i

  · have h1 :=
      terminalSpectralDifferenceAt_sq_integrable_normalizedCurlMass
        G H (1 : Fin 3)

    have h2 :=
      terminalSpectralDifferenceAt_sq_integrable_normalizedCurlMass
        G H (2 : Fin 3)

    have hInt :=
      h1.add h2

    have hNonneg :
        ∀ᵐ ξ : H3FourierPoint3 ∂volume,
          0
            ≤
          ‖h3TerminalSpectralDifferenceAt G H 1 ξ‖ ^ 2
            +
          ‖h3TerminalSpectralDifferenceAt G H 2 ξ‖ ^ 2 := by
      filter_upwards with ξ
      positivity

    calc
      h3TerminalTransverseBadConeSquareDefect
          (0 : Fin 3) κ G H
          =
        ∫ ξ in h3TerminalLongitudinalAngularBadCone (0 : Fin 3) κ,
          (
            ‖h3TerminalSpectralDifferenceAt G H 1 ξ‖ ^ 2
              +
            ‖h3TerminalSpectralDifferenceAt G H 2 ξ‖ ^ 2
          ) := by
            simp [
              h3TerminalTransverseBadConeSquareDefect,
              h3TerminalTransverseSpectralSquareMagnitude
            ]
      _ ≤
        ∫ ξ : H3FourierPoint3,
          (
            ‖h3TerminalSpectralDifferenceAt G H 1 ξ‖ ^ 2
              +
            ‖h3TerminalSpectralDifferenceAt G H 2 ξ‖ ^ 2
          ) := by
            exact
              integral_mono_measure
                Measure.restrict_le_self
                hNonneg
                hInt
      _ =
        ‖G 1 - H 1‖ ^ 2
          +
        ‖G 2 - H 2‖ ^ 2 := by
            rw [integral_add h1 h2]
            simp only [h3TerminalSpectralDifferenceAt]
            rw [
              ←
                h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq
                  (G 1) (H 1)
            ]
            rw [
              ←
                h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq
                  (G 2) (H 2)
            ]
      _ =
        h3TerminalTransverseSpectralNormSquareMagnitude
          (0 : Fin 3) G H := by
            simp [
              h3TerminalTransverseSpectralNormSquareMagnitude
            ]

  · have h0 :=
      terminalSpectralDifferenceAt_sq_integrable_normalizedCurlMass
        G H (0 : Fin 3)

    have h2 :=
      terminalSpectralDifferenceAt_sq_integrable_normalizedCurlMass
        G H (2 : Fin 3)

    have hInt :=
      h0.add h2

    have hNonneg :
        ∀ᵐ ξ : H3FourierPoint3 ∂volume,
          0
            ≤
          ‖h3TerminalSpectralDifferenceAt G H 0 ξ‖ ^ 2
            +
          ‖h3TerminalSpectralDifferenceAt G H 2 ξ‖ ^ 2 := by
      filter_upwards with ξ
      positivity

    calc
      h3TerminalTransverseBadConeSquareDefect
          (1 : Fin 3) κ G H
          =
        ∫ ξ in h3TerminalLongitudinalAngularBadCone (1 : Fin 3) κ,
          (
            ‖h3TerminalSpectralDifferenceAt G H 0 ξ‖ ^ 2
              +
            ‖h3TerminalSpectralDifferenceAt G H 2 ξ‖ ^ 2
          ) := by
            simp [
              h3TerminalTransverseBadConeSquareDefect,
              h3TerminalTransverseSpectralSquareMagnitude
            ]
      _ ≤
        ∫ ξ : H3FourierPoint3,
          (
            ‖h3TerminalSpectralDifferenceAt G H 0 ξ‖ ^ 2
              +
            ‖h3TerminalSpectralDifferenceAt G H 2 ξ‖ ^ 2
          ) := by
            exact
              integral_mono_measure
                Measure.restrict_le_self
                hNonneg
                hInt
      _ =
        ‖G 0 - H 0‖ ^ 2
          +
        ‖G 2 - H 2‖ ^ 2 := by
            rw [integral_add h0 h2]
            simp only [h3TerminalSpectralDifferenceAt]
            rw [
              ←
                h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq
                  (G 0) (H 0)
            ]
            rw [
              ←
                h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq
                  (G 2) (H 2)
            ]
      _ =
        h3TerminalTransverseSpectralNormSquareMagnitude
          (1 : Fin 3) G H := by
            simp [
              h3TerminalTransverseSpectralNormSquareMagnitude
            ]

  · have h0 :=
      terminalSpectralDifferenceAt_sq_integrable_normalizedCurlMass
        G H (0 : Fin 3)

    have h1 :=
      terminalSpectralDifferenceAt_sq_integrable_normalizedCurlMass
        G H (1 : Fin 3)

    have hInt :=
      h0.add h1

    have hNonneg :
        ∀ᵐ ξ : H3FourierPoint3 ∂volume,
          0
            ≤
          ‖h3TerminalSpectralDifferenceAt G H 0 ξ‖ ^ 2
            +
          ‖h3TerminalSpectralDifferenceAt G H 1 ξ‖ ^ 2 := by
      filter_upwards with ξ
      positivity

    calc
      h3TerminalTransverseBadConeSquareDefect
          (2 : Fin 3) κ G H
          =
        ∫ ξ in h3TerminalLongitudinalAngularBadCone (2 : Fin 3) κ,
          (
            ‖h3TerminalSpectralDifferenceAt G H 0 ξ‖ ^ 2
              +
            ‖h3TerminalSpectralDifferenceAt G H 1 ξ‖ ^ 2
          ) := by
            simp [
              h3TerminalTransverseBadConeSquareDefect,
              h3TerminalTransverseSpectralSquareMagnitude
            ]
      _ ≤
        ∫ ξ : H3FourierPoint3,
          (
            ‖h3TerminalSpectralDifferenceAt G H 0 ξ‖ ^ 2
              +
            ‖h3TerminalSpectralDifferenceAt G H 1 ξ‖ ^ 2
          ) := by
            exact
              integral_mono_measure
                Measure.restrict_le_self
                hNonneg
                hInt
      _ =
        ‖G 0 - H 0‖ ^ 2
          +
        ‖G 1 - H 1‖ ^ 2 := by
            rw [integral_add h0 h1]
            simp only [h3TerminalSpectralDifferenceAt]
            rw [
              ←
                h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq
                  (G 0) (H 0)
            ]
            rw [
              ←
                h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq
                  (G 1) (H 1)
            ]
      _ =
        h3TerminalTransverseSpectralNormSquareMagnitude
          (2 : Fin 3) G H := by
            simp [
              h3TerminalTransverseSpectralNormSquareMagnitude
            ]

/-! ## Integrated normalized-curl inequality -/

/--
Integrated bad-cone form of the pointwise normalized-curl lower bound.
-/
theorem half_one_sub_sq_mul_longitudinalBadCone_le_normalizedCurlPairBadCone_add_sq_mul_transverseBadCone
    {i : Fin 3}
    {κ : ℝ}
    (hκ : 0 < κ)
    (G H : H3SpectralFinVectorState) :
    (1 / 2 : ℝ)
        *
      (1 - κ ^ 2)
        *
      h3TerminalLongitudinalBadConeSquareDefect
        i κ G H
      ≤
    h3TerminalNormalizedLongitudinalCurlPairBadConeSquareDefect
        i κ G H
      +
    κ ^ 2
        *
      h3TerminalTransverseBadConeSquareDefect
        i κ G H := by

  let S : Set H3FourierPoint3 :=
    h3TerminalLongitudinalAngularBadCone i κ

  let g :
      H3FourierPoint3 → Fin 3 → ℂ :=
    fun ξ j =>
      h3TerminalSpectralDifferenceAt G H j ξ

  let c : ℝ :=
    (1 / 2 : ℝ) * (1 - κ ^ 2)

  have hLongBase :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖g ξ i‖ ^ 2)
        (volume.restrict S) :=
    (
      terminalSpectralDifferenceAt_sq_integrable_normalizedCurlMass
        G H i
    ).mono_measure
      Measure.restrict_le_self

  have hLongInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          c * ‖g ξ i‖ ^ 2)
        (volume.restrict S) :=
    hLongBase.const_mul c

  have hTransInt :
      Integrable
        (
          fun ξ : H3FourierPoint3 =>
            h3TerminalTransverseSpectralSquareMagnitude
              i
              (g ξ)
        )
        (volume.restrict S) := by

    have hJ :
        ∀ j : Fin 3,
          Integrable
            (fun ξ : H3FourierPoint3 =>
              ‖g ξ j‖ ^ 2)
            (volume.restrict S) := by
      intro j
      exact
        (
          terminalSpectralDifferenceAt_sq_integrable_normalizedCurlMass
            G H j
        ).mono_measure
          Measure.restrict_le_self

    fin_cases i

    · apply
        ((hJ 1).add
          (hJ 2)).congr

      filter_upwards with ξ

      simp [
        g,
        h3TerminalTransverseSpectralSquareMagnitude
      ]

    · apply
        ((hJ 0).add
          (hJ 2)).congr

      filter_upwards with ξ

      simp [
        g,
        h3TerminalTransverseSpectralSquareMagnitude
      ]

    · apply
        ((hJ 0).add
          (hJ 1)).congr

      filter_upwards with ξ

      simp [
        g,
        h3TerminalTransverseSpectralSquareMagnitude
      ]

  have hErrInt :
      Integrable
        (
          fun ξ : H3FourierPoint3 =>
            κ ^ 2
              *
            h3TerminalTransverseSpectralSquareMagnitude
              i
              (g ξ)
        )
        (volume.restrict S) :=
    hTransInt.const_mul
      (κ ^ 2)

  have hCurlInt :
      Integrable
        (
          fun ξ : H3FourierPoint3 =>
            h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude
              i ξ
              (g ξ)
        )
        (volume.restrict S) :=
    (
      normalizedLongitudinalCurlPairSquare_integrable
        i G H
    ).mono_measure
      Measure.restrict_le_self

  have hPoint :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume.restrict S),
        c * ‖g ξ i‖ ^ 2
          ≤
        h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude
            i ξ
            (g ξ)
          +
        κ ^ 2
            *
          h3TerminalTransverseSpectralSquareMagnitude
            i
            (g ξ) := by

    filter_upwards
      [
        ae_restrict_mem
          (measurableSet_h3TerminalLongitudinalAngularBadCone i κ)
      ]
      with ξ hξ

    have hBase :=
      half_one_sub_sq_mul_longitudinal_sub_sq_mul_transverse_le_normalizedCurlPair_of_mem_badCone
        hκ
        hξ
        (g ξ)

    dsimp only [c]

    linarith

  have hIntegral :
      ∫ ξ : H3FourierPoint3, c * ‖g ξ i‖ ^ 2
          ∂(volume.restrict S)
        ≤
      ∫ ξ : H3FourierPoint3,
          (
            h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude
                i ξ
                (g ξ)
              +
            κ ^ 2
                *
              h3TerminalTransverseSpectralSquareMagnitude
                i
                (g ξ)
          )
          ∂(volume.restrict S) :=
    integral_mono_ae
      hLongInt
      (hCurlInt.add hErrInt)
      hPoint

  dsimp only [S, g, c] at hIntegral

  calc
    (1 / 2 : ℝ)
          *
        (1 - κ ^ 2)
          *
        h3TerminalLongitudinalBadConeSquareDefect
          i κ G H
        =
      ∫ ξ in h3TerminalLongitudinalAngularBadCone i κ,
        (
          (1 / 2 : ℝ)
            *
          (1 - κ ^ 2)
        )
          *
        ‖h3TerminalSpectralDifferenceAt G H i ξ‖ ^ 2 := by
            unfold h3TerminalLongitudinalBadConeSquareDefect
            rw [integral_const_mul]

    _ ≤
      ∫ ξ in h3TerminalLongitudinalAngularBadCone i κ,
        (
          h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude
              i ξ
              (fun j =>
                h3TerminalSpectralDifferenceAt G H j ξ)
            +
          κ ^ 2
              *
            h3TerminalTransverseSpectralSquareMagnitude
              i
              (fun j =>
                h3TerminalSpectralDifferenceAt G H j ξ)
        ) :=
          hIntegral

    _ =
      h3TerminalNormalizedLongitudinalCurlPairBadConeSquareDefect
          i κ G H
        +
      κ ^ 2
          *
        h3TerminalTransverseBadConeSquareDefect
          i κ G H := by

            unfold
              h3TerminalNormalizedLongitudinalCurlPairBadConeSquareDefect
              h3TerminalTransverseBadConeSquareDefect

            rw [integral_add hCurlInt hErrInt]
            rw [integral_const_mul]

/-! ## Transverse pathwise Cauchy square bound -/

/--
One surviving physical-vorticity strong-H³ endpoint makes the global
transverse velocity H³ square defect smaller than `ε²/2` near `T`.
-/
theorem transverseSpectralNormSquareMagnitude_lt_half_sq_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ η : ℝ,
      0 < η
        ∧
      ∀
        (s : ℝ)
        (hs : s ∈ Set.Ioo (0 : ℝ) T)
        (t : ℝ)
        (ht : t ∈ Set.Ioo (0 : ℝ) T),
        dist s T < η →
        dist t T < η →
          h3TerminalTransverseSpectralNormSquareMagnitude
              i
              (h3TerminalVelocitySpectralStateAt hH3 s hs)
              (h3TerminalVelocitySpectralStateAt hH3 t ht)
            <
          ε ^ 2 / 2 := by

  have hHalf :
      0 < ε / 2 := by
    linarith

  fin_cases i

  · have hEndpoint1 :=
      velocityComponentStrongH3EndpointPath_of_actualVorticityStrongH3EndpointPath
        hH3
        (i := (0 : Fin 3))
        (j := (1 : Fin 3))
        (by decide)
        hPhysical

    have hEndpoint2 :=
      velocityComponentStrongH3EndpointPath_of_actualVorticityStrongH3EndpointPath
        hH3
        (i := (0 : Fin 3))
        (j := (2 : Fin 3))
        (by decide)
        hPhysical

    obtain ⟨η1, hη1, hC1⟩ :=
      velocityComponentSpectralState_pairwiseCauchy_of_strongH3EndpointPath
        hH3 hEndpoint1
        (ε / 2)
        hHalf

    obtain ⟨η2, hη2, hC2⟩ :=
      velocityComponentSpectralState_pairwiseCauchy_of_strongH3EndpointPath
        hH3 hEndpoint2
        (ε / 2)
        hHalf

    refine
      ⟨
        min η1 η2,
        lt_min hη1 hη2,
        ?_
      ⟩

    intro s hs t ht hsT htT

    have h1 :=
      hC1
        s hs t ht
        (lt_of_lt_of_le hsT (min_le_left _ _))
        (lt_of_lt_of_le htT (min_le_left _ _))

    have h2 :=
      hC2
        s hs t ht
        (lt_of_lt_of_le hsT (min_le_right _ _))
        (lt_of_lt_of_le htT (min_le_right _ _))

    have h1sq :
        ‖h3TerminalVelocityComponentSpectralStateAt
            hH3 (1 : Fin 3) s hs
          -
          h3TerminalVelocityComponentSpectralStateAt
            hH3 (1 : Fin 3) t ht‖ ^ 2
          <
        (ε / 2) ^ 2 :=
      (
        sq_lt_sq₀
          (norm_nonneg _)
          hHalf.le
      ).2
        h1

    have h2sq :
        ‖h3TerminalVelocityComponentSpectralStateAt
            hH3 (2 : Fin 3) s hs
          -
          h3TerminalVelocityComponentSpectralStateAt
            hH3 (2 : Fin 3) t ht‖ ^ 2
          <
        (ε / 2) ^ 2 :=
      (
        sq_lt_sq₀
          (norm_nonneg _)
          hHalf.le
      ).2
        h2

    simp [
      h3TerminalTransverseSpectralNormSquareMagnitude,
      h3TerminalVelocitySpectralStateAt_apply
    ]

    nlinarith

  · have hEndpoint0 :=
      velocityComponentStrongH3EndpointPath_of_actualVorticityStrongH3EndpointPath
        hH3
        (i := (1 : Fin 3))
        (j := (0 : Fin 3))
        (by decide)
        hPhysical

    have hEndpoint2 :=
      velocityComponentStrongH3EndpointPath_of_actualVorticityStrongH3EndpointPath
        hH3
        (i := (1 : Fin 3))
        (j := (2 : Fin 3))
        (by decide)
        hPhysical

    obtain ⟨η0, hη0, hC0⟩ :=
      velocityComponentSpectralState_pairwiseCauchy_of_strongH3EndpointPath
        hH3 hEndpoint0
        (ε / 2)
        hHalf

    obtain ⟨η2, hη2, hC2⟩ :=
      velocityComponentSpectralState_pairwiseCauchy_of_strongH3EndpointPath
        hH3 hEndpoint2
        (ε / 2)
        hHalf

    refine
      ⟨
        min η0 η2,
        lt_min hη0 hη2,
        ?_
      ⟩

    intro s hs t ht hsT htT

    have h0 :=
      hC0
        s hs t ht
        (lt_of_lt_of_le hsT (min_le_left _ _))
        (lt_of_lt_of_le htT (min_le_left _ _))

    have h2 :=
      hC2
        s hs t ht
        (lt_of_lt_of_le hsT (min_le_right _ _))
        (lt_of_lt_of_le htT (min_le_right _ _))

    have h0sq :
        ‖h3TerminalVelocityComponentSpectralStateAt
            hH3 (0 : Fin 3) s hs
          -
          h3TerminalVelocityComponentSpectralStateAt
            hH3 (0 : Fin 3) t ht‖ ^ 2
          <
        (ε / 2) ^ 2 :=
      (
        sq_lt_sq₀
          (norm_nonneg _)
          hHalf.le
      ).2
        h0

    have h2sq :
        ‖h3TerminalVelocityComponentSpectralStateAt
            hH3 (2 : Fin 3) s hs
          -
          h3TerminalVelocityComponentSpectralStateAt
            hH3 (2 : Fin 3) t ht‖ ^ 2
          <
        (ε / 2) ^ 2 :=
      (
        sq_lt_sq₀
          (norm_nonneg _)
          hHalf.le
      ).2
        h2

    simp [
      h3TerminalTransverseSpectralNormSquareMagnitude,
      h3TerminalVelocitySpectralStateAt_apply
    ]

    nlinarith

  · have hEndpoint0 :=
      velocityComponentStrongH3EndpointPath_of_actualVorticityStrongH3EndpointPath
        hH3
        (i := (2 : Fin 3))
        (j := (0 : Fin 3))
        (by decide)
        hPhysical

    have hEndpoint1 :=
      velocityComponentStrongH3EndpointPath_of_actualVorticityStrongH3EndpointPath
        hH3
        (i := (2 : Fin 3))
        (j := (1 : Fin 3))
        (by decide)
        hPhysical

    obtain ⟨η0, hη0, hC0⟩ :=
      velocityComponentSpectralState_pairwiseCauchy_of_strongH3EndpointPath
        hH3 hEndpoint0
        (ε / 2)
        hHalf

    obtain ⟨η1, hη1, hC1⟩ :=
      velocityComponentSpectralState_pairwiseCauchy_of_strongH3EndpointPath
        hH3 hEndpoint1
        (ε / 2)
        hHalf

    refine
      ⟨
        min η0 η1,
        lt_min hη0 hη1,
        ?_
      ⟩

    intro s hs t ht hsT htT

    have h0 :=
      hC0
        s hs t ht
        (lt_of_lt_of_le hsT (min_le_left _ _))
        (lt_of_lt_of_le htT (min_le_left _ _))

    have h1 :=
      hC1
        s hs t ht
        (lt_of_lt_of_le hsT (min_le_right _ _))
        (lt_of_lt_of_le htT (min_le_right _ _))

    have h0sq :
        ‖h3TerminalVelocityComponentSpectralStateAt
            hH3 (0 : Fin 3) s hs
          -
          h3TerminalVelocityComponentSpectralStateAt
            hH3 (0 : Fin 3) t ht‖ ^ 2
          <
        (ε / 2) ^ 2 :=
      (
        sq_lt_sq₀
          (norm_nonneg _)
          hHalf.le
      ).2
        h0

    have h1sq :
        ‖h3TerminalVelocityComponentSpectralStateAt
            hH3 (1 : Fin 3) s hs
          -
          h3TerminalVelocityComponentSpectralStateAt
            hH3 (1 : Fin 3) t ht‖ ^ 2
          <
        (ε / 2) ^ 2 :=
      (
        sq_lt_sq₀
          (norm_nonneg _)
          hHalf.le
      ).2
        h1

    simp [
      h3TerminalTransverseSpectralNormSquareMagnitude,
      h3TerminalVelocitySpectralStateAt_apply
    ]

    nlinarith

/-! ## Arbitrarily late positive normalized-curl mass -/

/--
Under hypothetical nonextension and one surviving physical-vorticity endpoint,
for every fixed aperture `0 < κ ≤ 1/2` and every `ε > 0`, arbitrarily close to
`T` there are two strict times whose normalized longitudinal curl-pair square
mass on the bad cone exceeds `ε² / 16`.
-/
theorem exists_arbitrarilyLate_normalizedLongitudinalCurlPairBadConeSquareDefect_gt_sixteenth_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    {κ ε : ℝ}
    (hκ : 0 < κ)
    (hκHalf : κ ≤ 1 / 2)
    (hε : 0 < ε) :
    ∀ η : ℝ,
      0 < η →
      ∃
        s : ℝ,
        ∃ hs : s ∈ Set.Ioo (0 : ℝ) T,
        ∃
          t : ℝ,
          ∃ ht : t ∈ Set.Ioo (0 : ℝ) T,
            dist s T < η
              ∧
            dist t T < η
              ∧
            ε ^ 2 / 16
              <
            h3TerminalNormalizedLongitudinalCurlPairBadConeSquareDefect
              i κ
              (h3TerminalVelocitySpectralStateAt hH3 s hs)
              (h3TerminalVelocitySpectralStateAt hH3 t ht) := by

  obtain
    ⟨
      ηTrans,
      hηTrans,
      hTransNear
    ⟩ :=
    transverseSpectralNormSquareMagnitude_lt_half_sq_of_actualVorticityStrongH3EndpointPath
      hH3
      hPhysical
      hε

  intro η hη

  let ρ : ℝ :=
    min η ηTrans

  have hρ :
      0 < ρ := by
    dsimp only [ρ]
    exact
      lt_min
        hη
        hηTrans

  obtain
    ⟨
      s,
      hs,
      t,
      ht,
      hsρ,
      htρ,
      hLong
    ⟩ :=
    exists_arbitrarilyLate_longitudinalBadConeSquareDefect_gt_half_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hκ
      hε
      ρ
      hρ

  have hsη :
      dist s T < η :=
    lt_of_lt_of_le
      hsρ
      (min_le_left _ _)

  have htη :
      dist t T < η :=
    lt_of_lt_of_le
      htρ
      (min_le_left _ _)

  have hsTrans :
      dist s T < ηTrans :=
    lt_of_lt_of_le
      hsρ
      (min_le_right _ _)

  have htTrans :
      dist t T < ηTrans :=
    lt_of_lt_of_le
      htρ
      (min_le_right _ _)

  let Gs :=
    h3TerminalVelocitySpectralStateAt
      hH3 s hs

  let Gt :=
    h3TerminalVelocitySpectralStateAt
      hH3 t ht

  have hGlobalTrans :
      h3TerminalTransverseSpectralNormSquareMagnitude
          i Gs Gt
        <
      ε ^ 2 / 2 := by

    dsimp only [Gs, Gt]

    exact
      hTransNear
        s hs t ht
        hsTrans
        htTrans

  have hTransBad :
      h3TerminalTransverseBadConeSquareDefect
          i κ Gs Gt
        <
      ε ^ 2 / 2 := by

    have hLe :=
      transverseBadConeSquareDefect_le_globalNormSquare
        i κ Gs Gt

    exact
      lt_of_le_of_lt
        hLe
        hGlobalTrans

  have hTransBadNonneg :
      0
        ≤
      h3TerminalTransverseBadConeSquareDefect
        i κ Gs Gt := by

    unfold h3TerminalTransverseBadConeSquareDefect

    apply integral_nonneg

    intro ξ

    fin_cases i <;>
      simp [
        h3TerminalTransverseSpectralSquareMagnitude
      ] <;>
      positivity

  have hIntegrated :=
    half_one_sub_sq_mul_longitudinalBadCone_le_normalizedCurlPairBadCone_add_sq_mul_transverseBadCone
      (i := i)
      hκ
      Gs Gt

  have hκsq :
      κ ^ 2
        ≤
      1 / 4 := by
    nlinarith [
      sq_nonneg κ
    ]

  have hCoef :
      3 / 8
        ≤
      (1 / 2 : ℝ) * (1 - κ ^ 2) := by
    nlinarith

  have hCoefPos :
      0
        <
      (1 / 2 : ℝ) * (1 - κ ^ 2) := by
    nlinarith

  have hMainLower :
      3 * ε ^ 2 / 16
        <
      (1 / 2 : ℝ)
          *
        (1 - κ ^ 2)
          *
        h3TerminalLongitudinalBadConeSquareDefect
          i κ Gs Gt := by

    have hFirst :
        3 * ε ^ 2 / 16
          ≤
        (
          (1 / 2 : ℝ) * (1 - κ ^ 2)
        )
          *
        (ε ^ 2 / 2) := by
      nlinarith [
        sq_nonneg ε
      ]

    have hSecond :
        (
          (1 / 2 : ℝ) * (1 - κ ^ 2)
        )
          *
        (ε ^ 2 / 2)
          <
        (
          (1 / 2 : ℝ) * (1 - κ ^ 2)
        )
          *
        h3TerminalLongitudinalBadConeSquareDefect
          i κ Gs Gt := by

      apply
        mul_lt_mul_of_pos_left
          ?_
          hCoefPos

      dsimp only [Gs, Gt]

      exact
        hLong

    exact
      lt_of_le_of_lt
        hFirst
        hSecond

  have hErrUpper :
      κ ^ 2
          *
        h3TerminalTransverseBadConeSquareDefect
          i κ Gs Gt
        <
      ε ^ 2 / 8 := by

    calc
      κ ^ 2
            *
          h3TerminalTransverseBadConeSquareDefect
            i κ Gs Gt
          ≤
        (1 / 4 : ℝ)
            *
          h3TerminalTransverseBadConeSquareDefect
            i κ Gs Gt :=
              mul_le_mul_of_nonneg_right
                hκsq
                hTransBadNonneg

      _ <
        (1 / 4 : ℝ) * (ε ^ 2 / 2) :=
          mul_lt_mul_of_pos_left
            hTransBad
            (by norm_num)

      _ =
        ε ^ 2 / 8 := by
          ring

  have hCurl :
      ε ^ 2 / 16
        <
      h3TerminalNormalizedLongitudinalCurlPairBadConeSquareDefect
        i κ Gs Gt := by

    linarith

  dsimp only [Gs, Gt] at hCurl

  exact
    ⟨
      s,
      hs,
      t,
      ht,
      hsη,
      htη,
      hCurl
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
