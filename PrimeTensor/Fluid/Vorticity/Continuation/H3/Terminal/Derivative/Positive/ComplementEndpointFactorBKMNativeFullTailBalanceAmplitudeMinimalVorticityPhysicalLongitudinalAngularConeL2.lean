import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalAngularCone
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spectral.Difference.Energy

/-!
# L² localization of the longitudinal angular-cone defect

The previous file proved the pointwise good-cone estimate

    κ ‖gᵢ - hᵢ‖ ≤ transverse difference.

This file integrates the squared form.  To keep the measure argument stable,
all densities are written through one raw representative

    Gⱼ(ξ) - Hⱼ(ξ),

rather than through a bundled `Lp` subtraction coerced back to a function.

For two divergence-free weighted H³ spectral states,

    good-cone longitudinal square defect
      ≤
    twice the transverse square defect.

Specializing to two strict preterminal times gives the exact Cauchy estimate
needed for the terminal path.  Thus any surviving longitudinal non-Cauchy
mass must lie in the complementary equatorial cone.

The standard fact that the origin is negligible is left explicit as an
a.e.-nonzero helper hypothesis so that this checkpoint stays focused on the
angular localization itself.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalLongitudinalAngularConeL2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Measurability of the angular good cone -/

theorem measurableSet_h3TerminalLongitudinalAngularGoodCone
    (i : Fin 3)
    (κ : ℝ) :
    MeasurableSet
      (h3TerminalLongitudinalAngularGoodCone i κ) := by

  have hGrad :
      Continuous
        h3FourierGradientMagnitude := by
    unfold h3FourierGradientMagnitude
    exact
      continuous_const.mul
        continuous_norm

  have hLeft :
      Continuous
        (fun ξ : H3FourierPoint3 =>
          κ * h3FourierGradientMagnitude ξ) :=
    continuous_const.mul
      hGrad

  have hRight :
      Continuous
        (fun ξ : H3FourierPoint3 =>
          ‖h3FourierDerivativeSymbol i ξ‖) :=
    (h3FourierDerivativeSymbol_continuous i).norm

  exact
    (
      isClosed_le
        hLeft
        hRight
    ).measurableSet

/-! ## Raw spectral difference and transverse square density -/

/--
Pointwise raw difference of two weighted H³ spectral vector states.
-/
def h3TerminalSpectralDifferenceAt
    (G H : H3SpectralFinVectorState)
    (j : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  (G j : H3FourierPoint3 → ℂ) ξ
    -
  (H j : H3FourierPoint3 → ℂ) ξ

/--
Sum of the two transverse component square magnitudes.
-/
def h3TerminalTransverseSpectralSquareMagnitude
    (i : Fin 3)
    (g : Fin 3 → ℂ) : ℝ :=
  if i = 0 then
    ‖g 1‖ ^ 2 + ‖g 2‖ ^ 2
  else if i = 1 then
    ‖g 0‖ ^ 2 + ‖g 2‖ ^ 2
  else
    ‖g 0‖ ^ 2 + ‖g 1‖ ^ 2

/--
The square of the transverse `ℓ¹` magnitude is controlled by twice the
transverse square magnitude.
-/
theorem transverseSpectralMagnitude_sq_le_two_mul_squareMagnitude
    (i : Fin 3)
    (g : Fin 3 → ℂ) :
    (
      h3TerminalTransverseSpectralMagnitude
        i g
    ) ^ 2
      ≤
    2 *
      h3TerminalTransverseSpectralSquareMagnitude
        i g := by

  fin_cases i

  · simp [
      h3TerminalTransverseSpectralMagnitude,
      h3TerminalTransverseSpectralSquareMagnitude
    ]

    nlinarith [
      sq_nonneg
        (‖g 1‖ - ‖g 2‖)
    ]

  · simp [
      h3TerminalTransverseSpectralMagnitude,
      h3TerminalTransverseSpectralSquareMagnitude
    ]

    nlinarith [
      sq_nonneg
        (‖g 0‖ - ‖g 2‖)
    ]

  · simp [
      h3TerminalTransverseSpectralMagnitude,
      h3TerminalTransverseSpectralSquareMagnitude
    ]

    nlinarith [
      sq_nonneg
        (‖g 0‖ - ‖g 1‖)
    ]

/-! ## Good-cone square defect masses -/

/--
Scaled longitudinal square defect on the angular good cone.
-/
noncomputable def h3TerminalLongitudinalGoodConeScaledSquareDefect
    (i : Fin 3)
    (κ : ℝ)
    (G H : H3SpectralFinVectorState) : ℝ :=
  ∫ ξ in h3TerminalLongitudinalAngularGoodCone i κ,
    (
      κ *
        ‖h3TerminalSpectralDifferenceAt G H i ξ‖
    ) ^ 2

/--
Twice the transverse square defect on the same angular good cone.
-/
noncomputable def h3TerminalTransverseGoodConeSquareDefect
    (i : Fin 3)
    (κ : ℝ)
    (G H : H3SpectralFinVectorState) : ℝ :=
  ∫ ξ in h3TerminalLongitudinalAngularGoodCone i κ,
    2 *
      h3TerminalTransverseSpectralSquareMagnitude
        i
        (fun j =>
          h3TerminalSpectralDifferenceAt
            G H j ξ)

/-! ## Integrability helpers -/

/--
The raw square difference of one component is integrable.
-/
private theorem spectralDifferenceAt_sq_integrable
    (G H : H3SpectralFinVectorState)
    (j : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖h3TerminalSpectralDifferenceAt G H j ξ‖ ^ 2)
      volume := by

  exact
    h3FourierComplexL2_pointwise_sub_norm_sq_integrable
      (G j)
      (H j)

/--
The scaled longitudinal square density is integrable on the good cone.
-/
private theorem longitudinalGoodConeScaledSquare_integrable
    (i : Fin 3)
    (κ : ℝ)
    (G H : H3SpectralFinVectorState) :
    Integrable
      (
        fun ξ : H3FourierPoint3 =>
          (
            κ *
              ‖h3TerminalSpectralDifferenceAt
                G H i ξ‖
          ) ^ 2
      )
      (
        volume.restrict
          (h3TerminalLongitudinalAngularGoodCone i κ)
      ) := by

  have hBase :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3TerminalSpectralDifferenceAt
            G H i ξ‖ ^ 2)
        volume :=
    spectralDifferenceAt_sq_integrable
      G H i

  have hRestricted :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3TerminalSpectralDifferenceAt
            G H i ξ‖ ^ 2)
        (
          volume.restrict
            (h3TerminalLongitudinalAngularGoodCone i κ)
        ) :=
    hBase.mono_measure
      Measure.restrict_le_self

  have hScaled :=
    hRestricted.const_mul
      (κ ^ 2)

  refine
    hScaled.congr
      ?_

  filter_upwards with ξ

  ring

/--
The transverse square density is integrable on the good cone.
-/
private theorem transverseGoodConeSquare_integrable
    (i : Fin 3)
    (κ : ℝ)
    (G H : H3SpectralFinVectorState) :
    Integrable
      (
        fun ξ : H3FourierPoint3 =>
          2 *
            h3TerminalTransverseSpectralSquareMagnitude
              i
              (fun j =>
                h3TerminalSpectralDifferenceAt
                  G H j ξ)
      )
      (
        volume.restrict
          (h3TerminalLongitudinalAngularGoodCone i κ)
      ) := by

  have hInt :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖h3TerminalSpectralDifferenceAt
              G H j ξ‖ ^ 2)
          (
            volume.restrict
              (h3TerminalLongitudinalAngularGoodCone i κ)
          ) := by

    intro j

    exact
      (
        spectralDifferenceAt_sq_integrable
          G H j
      ).mono_measure
        Measure.restrict_le_self

  fin_cases i

  · simpa [
      h3TerminalTransverseSpectralSquareMagnitude
    ] using
      (
        (hInt 1).add
          (hInt 2)
      ).const_mul
        2

  · simpa [
      h3TerminalTransverseSpectralSquareMagnitude
    ] using
      (
        (hInt 0).add
          (hInt 2)
      ).const_mul
        2

  · simpa [
      h3TerminalTransverseSpectralSquareMagnitude
    ] using
      (
        (hInt 0).add
          (hInt 1)
      ).const_mul
        2

/-! ## Integrated good-cone recovery -/

/--
For two divergence-free weighted H³ spectral states, the scaled longitudinal
square defect on the angular good cone is controlled by the transverse square
defect.
-/
theorem longitudinalGoodConeScaledSquareDefect_le_transverse
    {i : Fin 3}
    {κ : ℝ}
    (hκ : 0 < κ)
    {G H : H3SpectralFinVectorState}
    (hDivG :
      H3SpectralFinDivergenceFree
        G)
    (hDivH :
      H3SpectralFinDivergenceFree
        H)
    (hNonzero :
      ∀ᵐ ξ : H3FourierPoint3 ∂volume,
        ξ ≠ 0) :
    h3TerminalLongitudinalGoodConeScaledSquareDefect
        i κ G H
      ≤
    h3TerminalTransverseGoodConeSquareDefect
        i κ G H := by

  let S : Set H3FourierPoint3 :=
    h3TerminalLongitudinalAngularGoodCone
      i κ

  have hS :
      MeasurableSet S := by
    dsimp only [S]
    exact
      measurableSet_h3TerminalLongitudinalAngularGoodCone
        i κ

  have hPointwise :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume.restrict S),
        (
          κ *
            ‖h3TerminalSpectralDifferenceAt
              G H i ξ‖
        ) ^ 2
          ≤
        2 *
          h3TerminalTransverseSpectralSquareMagnitude
            i
            (fun j =>
              h3TerminalSpectralDifferenceAt
                G H j ξ) := by

    rw [ae_restrict_iff' hS]

    filter_upwards [
      hDivG,
      hDivH,
      hNonzero
    ] with ξ hDG hDH hξ0

    intro hξS

    have hRaw :=
      mul_norm_longitudinal_sub_le_transverse_of_divergenceFree_of_mem_goodCone
        hκ
        hξ0
        hDG
        hDH
        hξS

    have hRaw' :
        κ *
            ‖h3TerminalSpectralDifferenceAt
              G H i ξ‖
          ≤
        h3TerminalTransverseSpectralMagnitude
          i
          (fun j =>
            h3TerminalSpectralDifferenceAt
              G H j ξ) := by

      simpa [
        h3TerminalSpectralDifferenceAt
      ] using
        hRaw

    have hLeftNonneg :
        0
          ≤
        κ *
          ‖h3TerminalSpectralDifferenceAt
            G H i ξ‖ :=
      mul_nonneg
        hκ.le
        (norm_nonneg _)

    have hSquare :=
      mul_self_le_mul_self
        hLeftNonneg
        hRaw'

    have hSquare' :
        (
          κ *
            ‖h3TerminalSpectralDifferenceAt
              G H i ξ‖
        ) ^ 2
          ≤
        (
          h3TerminalTransverseSpectralMagnitude
            i
            (fun j =>
              h3TerminalSpectralDifferenceAt
                G H j ξ)
        ) ^ 2 := by

      simpa [pow_two] using
        hSquare

    exact
      hSquare'.trans
        (
          transverseSpectralMagnitude_sq_le_two_mul_squareMagnitude
            i
            (fun j =>
              h3TerminalSpectralDifferenceAt
                G H j ξ)
        )

  unfold
    h3TerminalLongitudinalGoodConeScaledSquareDefect
    h3TerminalTransverseGoodConeSquareDefect

  change
    (∫ ξ : H3FourierPoint3,
        (
          κ *
            ‖h3TerminalSpectralDifferenceAt
              G H i ξ‖
        ) ^ 2
      ∂(volume.restrict S))
      ≤
    (∫ ξ : H3FourierPoint3,
        2 *
          h3TerminalTransverseSpectralSquareMagnitude
            i
            (fun j =>
              h3TerminalSpectralDifferenceAt
                G H j ξ)
      ∂(volume.restrict S))

  exact
    integral_mono_ae
      (
        longitudinalGoodConeScaledSquare_integrable
          i κ G H
      )
      (
        transverseGoodConeSquare_integrable
          i κ G H
      )
      hPointwise

/-! ## Strict-time path specialization -/

/--
For two strict preterminal times, the canonical divergence-free H³ spectral
states satisfy the good-cone square-defect estimate.
-/
theorem terminalVelocitySpectralState_longitudinalGoodConeScaledSquareDefect_le_transverse
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    {i : Fin 3}
    {κ : ℝ}
    (hκ : 0 < κ)
    {s t : ℝ}
    (hs :
      s ∈ Set.Ioo (0 : ℝ) T)
    (ht :
      t ∈ Set.Ioo (0 : ℝ) T)
    (hNonzero :
      ∀ᵐ ξ : H3FourierPoint3 ∂volume,
        ξ ≠ 0) :
    h3TerminalLongitudinalGoodConeScaledSquareDefect
        i κ
        (h3TerminalVelocitySpectralStateAt hH3 s hs)
        (h3TerminalVelocitySpectralStateAt hH3 t ht)
      ≤
    h3TerminalTransverseGoodConeSquareDefect
        i κ
        (h3TerminalVelocitySpectralStateAt hH3 s hs)
        (h3TerminalVelocitySpectralStateAt hH3 t ht) := by

  exact
    longitudinalGoodConeScaledSquareDefect_le_transverse
      hκ
      (
        h3TerminalVelocitySpectralStateAt_divergenceFree
          hH3 s hs
      )
      (
        h3TerminalVelocitySpectralStateAt_divergenceFree
          hH3 t ht
      )
      hNonzero

end

end Euclidean
end Bridge
end PrimeTensor
