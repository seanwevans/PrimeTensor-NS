import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialPolarization

/-!
# Degree-zero normalized curl on the shrinking equatorial obstruction

The shrinking equatorial concentration mechanism should be coupled back to
vorticity without spending one additional Fourier derivative.

For that purpose normalize each coordinate derivative symbol by the radial
gradient magnitude

    a_j(ξ) = d_j(ξ) / |D(ξ)|,

with value zero at the origin.  Each `a_j` is a bounded degree-zero multiplier.

Define normalized curl amplitudes

    C01~ = a₁ g₀ - a₀ g₁,
    C02~ = a₂ g₀ - a₀ g₂,
    C12~ = a₂ g₁ - a₁ g₂.

For a longitudinal coordinate `i`, take the two normalized curl channels that
contain `g_i`.

On the angular bad cone

    |a_i| < κ,

while the transverse-frequency polarization gives

    1 - κ² < sum_{j ≠ i} |a_j|².

A two-term square estimate then yields the pointwise lower bound

    ((1 - κ²) / 2) |g_i|²
      - κ² |g_perp|²
      ≤
    normalized-curl-pair square.

This is the degree-zero bridge needed for the next integrated checkpoint.
No H⁴ estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalLongitudinalEquatorialNormalizedCurl
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Normalized coordinate derivative symbols -/

/--
Coordinate derivative symbol normalized by the radial derivative magnitude.

At zero radial frequency the value is set to zero.
-/
noncomputable def h3TerminalNormalizedDerivativeSymbol
    (j : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  if hGrad :
      h3FourierGradientMagnitude ξ = 0
  then
    0
  else
    h3FourierDerivativeSymbol j ξ
      /
    (h3FourierGradientMagnitude ξ : ℂ)

/--
Away from zero radial frequency, the normalized-symbol norm is the coordinate
symbol norm divided by the radial magnitude.
-/
theorem norm_h3TerminalNormalizedDerivativeSymbol_eq_div
    (j : Fin 3)
    (ξ : H3FourierPoint3)
    (hGrad :
      0 < h3FourierGradientMagnitude ξ) :
    ‖h3TerminalNormalizedDerivativeSymbol j ξ‖
      =
    ‖h3FourierDerivativeSymbol j ξ‖
      /
    h3FourierGradientMagnitude ξ := by

  rw [
    h3TerminalNormalizedDerivativeSymbol,
    dif_neg hGrad.ne',
    norm_div,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_pos hGrad
  ]

/--
Every normalized coordinate derivative multiplier has norm at most one.
-/
theorem norm_h3TerminalNormalizedDerivativeSymbol_le_one
    (j : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3TerminalNormalizedDerivativeSymbol j ξ‖
      ≤
    1 := by

  by_cases hZero :
      h3FourierGradientMagnitude ξ = 0

  · simp [
      h3TerminalNormalizedDerivativeSymbol,
      hZero
    ]

  · have hNonneg :
        0 ≤ h3FourierGradientMagnitude ξ :=
      h3FourierGradientMagnitude_nonneg ξ

    have hGrad :
        0 < h3FourierGradientMagnitude ξ :=
      lt_of_le_of_ne
        hNonneg
        (Ne.symm hZero)

    rw [
      norm_h3TerminalNormalizedDerivativeSymbol_eq_div
        j ξ hGrad
    ]

    exact
      (div_le_iff₀ hGrad).2
        (
          by
            simpa only [one_mul] using
              norm_h3FourierDerivativeSymbol_le_gradientMagnitude
                j ξ
        )

/--
The three normalized coordinate-symbol norm squares sum to one away from zero
radial frequency.
-/
theorem sum_norm_h3TerminalNormalizedDerivativeSymbol_sq_eq_one
    (ξ : H3FourierPoint3)
    (hGrad :
      0 < h3FourierGradientMagnitude ξ) :
    (
      ∑ j : Fin 3,
        ‖h3TerminalNormalizedDerivativeSymbol j ξ‖ ^ 2
    )
      =
    1 := by

  simp_rw [
    norm_h3TerminalNormalizedDerivativeSymbol_eq_div
      _ ξ hGrad,
    div_pow
  ]

  rw [
    ← Finset.sum_div,
    sum_norm_h3FourierDerivativeSymbol_sq,
    ← h3FourierGradientMagnitude_sq
  ]

  have hGradNe :
      h3FourierGradientMagnitude ξ ≠ 0 :=
    hGrad.ne'

  field_simp [hGradNe]

/-! ## Transverse normalized-symbol square -/

/--
Sum of the two normalized derivative-symbol norm squares transverse to
coordinate `i`.
-/
def h3TerminalNormalizedTransverseDerivativeSymbolSquareMagnitude
    (i : Fin 3)
    (ξ : H3FourierPoint3) : ℝ :=
  if i = 0 then
    ‖h3TerminalNormalizedDerivativeSymbol (1 : Fin 3) ξ‖ ^ 2
      +
    ‖h3TerminalNormalizedDerivativeSymbol (2 : Fin 3) ξ‖ ^ 2
  else if i = 1 then
    ‖h3TerminalNormalizedDerivativeSymbol (0 : Fin 3) ξ‖ ^ 2
      +
    ‖h3TerminalNormalizedDerivativeSymbol (2 : Fin 3) ξ‖ ^ 2
  else
    ‖h3TerminalNormalizedDerivativeSymbol (0 : Fin 3) ξ‖ ^ 2
      +
    ‖h3TerminalNormalizedDerivativeSymbol (1 : Fin 3) ξ‖ ^ 2

/--
Away from zero radial frequency, transverse normalized-symbol square plus the
longitudinal normalized-symbol square is exactly one.
-/
theorem normalizedTransverseDerivativeSymbolSquareMagnitude_add_longitudinal_eq_one
    (i : Fin 3)
    (ξ : H3FourierPoint3)
    (hGrad :
      0 < h3FourierGradientMagnitude ξ) :
    h3TerminalNormalizedTransverseDerivativeSymbolSquareMagnitude
        i ξ
      +
    ‖h3TerminalNormalizedDerivativeSymbol i ξ‖ ^ 2
      =
    1 := by

  have hSum :=
    sum_norm_h3TerminalNormalizedDerivativeSymbol_sq_eq_one
      ξ hGrad

  fin_cases i <;>
    simp [
      h3TerminalNormalizedTransverseDerivativeSymbolSquareMagnitude,
      Fin.sum_univ_three
    ] at hSum ⊢ <;>
    nlinarith

/-! ## Bad-cone normalized-symbol polarization -/

/--
A bad-cone frequency is necessarily nonzero in radial derivative magnitude.
-/
theorem gradientMagnitude_pos_of_mem_longitudinalAngularBadCone
    {i : Fin 3}
    {κ : ℝ}
    {ξ : H3FourierPoint3}
    (hBad :
      ξ ∈ h3TerminalLongitudinalAngularBadCone i κ) :
    0 < h3FourierGradientMagnitude ξ := by

  change
    ‖h3FourierDerivativeSymbol i ξ‖
      <
    κ * h3FourierGradientMagnitude ξ
    at hBad

  have hGradNonneg :
      0 ≤ h3FourierGradientMagnitude ξ :=
    h3FourierGradientMagnitude_nonneg ξ

  by_contra hNot

  have hGradZero :
      h3FourierGradientMagnitude ξ = 0 :=
    le_antisymm
      (le_of_not_gt hNot)
      hGradNonneg

  rw [hGradZero] at hBad

  simp only [mul_zero] at hBad

  exact
    (not_lt_of_ge
      (norm_nonneg _))
      hBad

/--
On the bad cone the normalized longitudinal derivative coefficient has norm
strictly below the aperture.
-/
theorem norm_normalizedLongitudinalDerivativeSymbol_lt_of_mem_badCone
    {i : Fin 3}
    {κ : ℝ}
    {ξ : H3FourierPoint3}
    (hBad :
      ξ ∈ h3TerminalLongitudinalAngularBadCone i κ) :
    ‖h3TerminalNormalizedDerivativeSymbol i ξ‖
      <
    κ := by

  have hGrad :
      0 < h3FourierGradientMagnitude ξ :=
    gradientMagnitude_pos_of_mem_longitudinalAngularBadCone
      hBad

  change
    ‖h3FourierDerivativeSymbol i ξ‖
      <
    κ * h3FourierGradientMagnitude ξ
    at hBad

  rw [
    norm_h3TerminalNormalizedDerivativeSymbol_eq_div
      i ξ hGrad
  ]

  exact
    (div_lt_iff₀ hGrad).2
      hBad

/--
On the bad cone the normalized transverse coordinate-symbol square exceeds
`1 - κ²`.
-/
theorem one_sub_sq_lt_normalizedTransverseDerivativeSymbolSquareMagnitude_of_mem_badCone
    {i : Fin 3}
    {κ : ℝ}
    (hκ : 0 ≤ κ)
    {ξ : H3FourierPoint3}
    (hBad :
      ξ ∈ h3TerminalLongitudinalAngularBadCone i κ) :
    1 - κ ^ 2
      <
    h3TerminalNormalizedTransverseDerivativeSymbolSquareMagnitude
      i ξ := by

  have hGrad :
      0 < h3FourierGradientMagnitude ξ :=
    gradientMagnitude_pos_of_mem_longitudinalAngularBadCone
      hBad

  have hLong :
      ‖h3TerminalNormalizedDerivativeSymbol i ξ‖
        <
      κ :=
    norm_normalizedLongitudinalDerivativeSymbol_lt_of_mem_badCone
      hBad

  have hLongSq :
      ‖h3TerminalNormalizedDerivativeSymbol i ξ‖ ^ 2
        <
      κ ^ 2 :=
    (
      sq_lt_sq₀
        (norm_nonneg _)
        hκ
    ).2
      hLong

  have hSplit :=
    normalizedTransverseDerivativeSymbolSquareMagnitude_add_longitudinal_eq_one
      i ξ hGrad

  nlinarith

/-! ## Normalized curl amplitudes -/

/-- Normalized `01` curl amplitude. -/
def h3TerminalNormalizedCurl01Amplitude
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ) : ℂ :=
  h3TerminalNormalizedDerivativeSymbol (1 : Fin 3) ξ * g 0
    -
  h3TerminalNormalizedDerivativeSymbol (0 : Fin 3) ξ * g 1

/-- Normalized `02` curl amplitude. -/
def h3TerminalNormalizedCurl02Amplitude
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ) : ℂ :=
  h3TerminalNormalizedDerivativeSymbol (2 : Fin 3) ξ * g 0
    -
  h3TerminalNormalizedDerivativeSymbol (0 : Fin 3) ξ * g 2

/-- Normalized `12` curl amplitude. -/
def h3TerminalNormalizedCurl12Amplitude
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ) : ℂ :=
  h3TerminalNormalizedDerivativeSymbol (2 : Fin 3) ξ * g 1
    -
  h3TerminalNormalizedDerivativeSymbol (1 : Fin 3) ξ * g 2

/--
Square magnitude of the two normalized curl channels containing longitudinal
velocity coordinate `i`.
-/
def h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude
    (i : Fin 3)
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ) : ℝ :=
  if i = 0 then
    ‖h3TerminalNormalizedCurl01Amplitude ξ g‖ ^ 2
      +
    ‖h3TerminalNormalizedCurl02Amplitude ξ g‖ ^ 2
  else if i = 1 then
    ‖h3TerminalNormalizedCurl01Amplitude ξ g‖ ^ 2
      +
    ‖h3TerminalNormalizedCurl12Amplitude ξ g‖ ^ 2
  else
    ‖h3TerminalNormalizedCurl02Amplitude ξ g‖ ^ 2
      +
    ‖h3TerminalNormalizedCurl12Amplitude ξ g‖ ^ 2

/-! ## Elementary two-term square estimate -/

private theorem half_norm_sq_sub_norm_sq_le_norm_sub_sq
    (a b : ℂ) :
    (1 / 2 : ℝ) * ‖a‖ ^ 2
        -
      ‖b‖ ^ 2
      ≤
    ‖a - b‖ ^ 2 := by

  have hTriangle :
      ‖a‖
        ≤
      ‖a - b‖ + ‖b‖ := by

    calc
      ‖a‖
          =
        ‖(a - b) + b‖ := by
          rw [sub_add_cancel]
      _ ≤
        ‖a - b‖ + ‖b‖ :=
          norm_add_le _ _

  have hSquare :
      ‖a‖ ^ 2
        ≤
      (‖a - b‖ + ‖b‖) ^ 2 :=
    (
      sq_le_sq₀
        (norm_nonneg _)
        (
          add_nonneg
            (norm_nonneg _)
            (norm_nonneg _)
        )
    ).2
      hTriangle

  nlinarith [
    sq_nonneg
      (‖a - b‖ - ‖b‖)
  ]

/-! ## Pointwise normalized-curl lower bound -/

/--
Before using the angular bad-cone inequalities, the two normalized curl
channels control half of the longitudinal contribution, up to the transverse
velocity contribution weighted by the longitudinal normalized symbol.
-/
theorem normalizedLongitudinalCurlPairSquareMagnitude_lower
    (i : Fin 3)
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ) :
    (1 / 2 : ℝ)
        *
      h3TerminalNormalizedTransverseDerivativeSymbolSquareMagnitude
        i ξ
        *
      ‖g i‖ ^ 2
      -
    ‖h3TerminalNormalizedDerivativeSymbol i ξ‖ ^ 2
        *
      h3TerminalTransverseSpectralSquareMagnitude
        i g
      ≤
    h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude
      i ξ g := by

  fin_cases i

  · have h01 :=
      half_norm_sq_sub_norm_sq_le_norm_sub_sq
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

    have h02 :=
      half_norm_sq_sub_norm_sq_le_norm_sub_sq
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

    simp only [norm_mul] at h01 h02

    simp [
      h3TerminalNormalizedTransverseDerivativeSymbolSquareMagnitude,
      h3TerminalTransverseSpectralSquareMagnitude,
      h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude,
      h3TerminalNormalizedCurl01Amplitude,
      h3TerminalNormalizedCurl02Amplitude
    ]

    nlinarith [h01, h02]

  · have h01 :=
      half_norm_sq_sub_norm_sq_le_norm_sub_sq
        (
          h3TerminalNormalizedDerivativeSymbol (0 : Fin 3) ξ
            *
          g 1
        )
        (
          h3TerminalNormalizedDerivativeSymbol (1 : Fin 3) ξ
            *
          g 0
        )

    have h12 :=
      half_norm_sq_sub_norm_sq_le_norm_sub_sq
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

    rw [norm_sub_rev] at h01

    simp only [norm_mul] at h01 h12

    simp [
      h3TerminalNormalizedTransverseDerivativeSymbolSquareMagnitude,
      h3TerminalTransverseSpectralSquareMagnitude,
      h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude,
      h3TerminalNormalizedCurl01Amplitude,
      h3TerminalNormalizedCurl12Amplitude
    ]

    nlinarith [h01, h12]

  · have h02 :=
      half_norm_sq_sub_norm_sq_le_norm_sub_sq
        (
          h3TerminalNormalizedDerivativeSymbol (0 : Fin 3) ξ
            *
          g 2
        )
        (
          h3TerminalNormalizedDerivativeSymbol (2 : Fin 3) ξ
            *
          g 0
        )

    have h12 :=
      half_norm_sq_sub_norm_sq_le_norm_sub_sq
        (
          h3TerminalNormalizedDerivativeSymbol (1 : Fin 3) ξ
            *
          g 2
        )
        (
          h3TerminalNormalizedDerivativeSymbol (2 : Fin 3) ξ
            *
          g 1
        )

    rw [norm_sub_rev] at h02
    rw [norm_sub_rev] at h12

    simp only [norm_mul] at h02 h12

    simp [
      h3TerminalNormalizedTransverseDerivativeSymbolSquareMagnitude,
      h3TerminalTransverseSpectralSquareMagnitude,
      h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude,
      h3TerminalNormalizedCurl02Amplitude,
      h3TerminalNormalizedCurl12Amplitude
    ]

    nlinarith [h02, h12]

/--
On the angular bad cone, the two normalized curl channels involving the
longitudinal coordinate retain a definite portion of longitudinal velocity
mass, up to a `κ²`-weighted transverse velocity error.
-/
theorem half_one_sub_sq_mul_longitudinal_sub_sq_mul_transverse_le_normalizedCurlPair_of_mem_badCone
    {i : Fin 3}
    {κ : ℝ}
    (hκ : 0 < κ)
    {ξ : H3FourierPoint3}
    (hBad :
      ξ ∈ h3TerminalLongitudinalAngularBadCone i κ)
    (g : Fin 3 → ℂ) :
    (1 / 2 : ℝ)
        *
      (1 - κ ^ 2)
        *
      ‖g i‖ ^ 2
      -
    κ ^ 2
        *
      h3TerminalTransverseSpectralSquareMagnitude
        i g
      ≤
    h3TerminalNormalizedLongitudinalCurlPairSquareMagnitude
      i ξ g := by

  have hTrans :
      1 - κ ^ 2
        ≤
      h3TerminalNormalizedTransverseDerivativeSymbolSquareMagnitude
        i ξ :=
    le_of_lt
      (
        one_sub_sq_lt_normalizedTransverseDerivativeSymbolSquareMagnitude_of_mem_badCone
          hκ.le
          hBad
      )

  have hLong :
      ‖h3TerminalNormalizedDerivativeSymbol i ξ‖
        <
      κ :=
    norm_normalizedLongitudinalDerivativeSymbol_lt_of_mem_badCone
      hBad

  have hLongSq :
      ‖h3TerminalNormalizedDerivativeSymbol i ξ‖ ^ 2
        ≤
      κ ^ 2 :=
    le_of_lt
      (
        (
          sq_lt_sq₀
            (norm_nonneg _)
            hκ.le
        ).2
          hLong
      )

  have hMain :
      (1 - κ ^ 2) * ‖g i‖ ^ 2
        ≤
      h3TerminalNormalizedTransverseDerivativeSymbolSquareMagnitude
          i ξ
        *
      ‖g i‖ ^ 2 :=
    mul_le_mul_of_nonneg_right
      hTrans
      (sq_nonneg _)

  have hErr :
      ‖h3TerminalNormalizedDerivativeSymbol i ξ‖ ^ 2
          *
        h3TerminalTransverseSpectralSquareMagnitude i g
        ≤
      κ ^ 2
          *
        h3TerminalTransverseSpectralSquareMagnitude i g := by

    apply
      mul_le_mul_of_nonneg_right
        hLongSq

    fin_cases i <;>
      simp [
        h3TerminalTransverseSpectralSquareMagnitude
      ] <;>
      positivity

  have hBase :=
    normalizedLongitudinalCurlPairSquareMagnitude_lower
      i ξ g

  linarith

end

end Euclidean
end Bridge
end PrimeTensor
