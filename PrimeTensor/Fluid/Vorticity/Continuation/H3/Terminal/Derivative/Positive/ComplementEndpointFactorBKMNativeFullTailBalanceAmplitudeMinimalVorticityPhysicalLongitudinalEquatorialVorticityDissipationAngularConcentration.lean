import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityHighRadialAngularVanishingFrontier

/-!
# Reduce terminal raw-vorticity concentration to H³ dissipation concentration

The surviving high-radial obstruction from the preceding checkpoint is an
extended raw-vorticity square mass on shrinking equatorial cones.

The key observation is that the raw vorticity symbol applies exactly one
Fourier derivative to the already weighted H³ spectral difference.  Therefore
its square is controlled pointwise by the radial gradient square times the
weighted spectral difference square.

For a weighted H³ state `G = W₃ û`,

    q |G|²
      = q W₃² |û|²
      = (q + q² + q³ + q⁴) |û|²,

where `q = |D|²`.  This is precisely the symbol of the full H³ viscous
dissipation: derivative orders one through four.

We package the corresponding pair-difference density and its bad-cone
high-radial control mass.  Every raw-vorticity component mass is bounded by
that control mass with the universal constant four already available from the
normalized-vorticity estimate.

Consequently, angular vanishing of the spectral dissipation difference implies
angular vanishing of every raw-vorticity component.  Combined with terminal raw
Fourier velocity L² Cauchy control, hypothetical nonextension therefore forces
failure of angular vanishing in the full H³ dissipation channel itself.

This file does not yet identify the pair-difference control mass with the
single-time physical quantity `velocityH3DissipationAt`.  That is the next
bridge: the exact orderwise Fourier dissipation identities already present in
the repository should convert this spectral concentration statement into a
physical dissipation statement.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalLongitudinalEquatorialVorticityDissipationAngularConcentration
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Full H³ dissipation symbol -/

/--
Multiplying the exact H³ weight square by one radial gradient square gives the
sum of the four viscous radial symbols.
-/
theorem h3FourierGradientSquare_mul_h3SobolevFrequencyWeight_sq
    (ξ : H3FourierPoint3) :
    h3FourierGradientSquare ξ
        *
      (h3SobolevFrequencyWeight ξ) ^ 2
      =
    h3FourierGradientSquare ξ
      +
    h3FourierGradientSquare ξ ^ 2
      +
    h3FourierGradientSquare ξ ^ 3
      +
    h3FourierGradientSquare ξ ^ 4 := by

  rw [
    h3SobolevFrequencyWeight_sq
  ]

  unfold
    h3SobolevFrequencyWeightSq

  ring

/-! ## Pair-difference dissipation density -/

/--
Full H³ spectral dissipation density of the difference of two weighted
three-component spectral states.
-/
def h3TerminalSpectralDissipationDifferenceDensity
    (G H : H3SpectralFinVectorState)
    (ξ : H3FourierPoint3) : ℝ :=
  h3FourierGradientSquare ξ
    *
  (
    norm
        (
          h3TerminalSpectralDifferenceAt
            G H 0 ξ
        ) ^ 2
      +
    norm
        (
          h3TerminalSpectralDifferenceAt
            G H 1 ξ
        ) ^ 2
      +
    norm
        (
          h3TerminalSpectralDifferenceAt
            G H 2 ξ
        ) ^ 2
  )

/-- The pair-difference dissipation density is pointwise nonnegative. -/
theorem h3TerminalSpectralDissipationDifferenceDensity_nonneg
    (G H : H3SpectralFinVectorState)
    (ξ : H3FourierPoint3) :
    0
      ≤
    h3TerminalSpectralDissipationDifferenceDensity
      G H ξ := by

  unfold
    h3TerminalSpectralDissipationDifferenceDensity

  have hq :
      0 ≤ h3FourierGradientSquare ξ := by

    rw [
      ← h3FourierGradientMagnitude_sq
    ]

    positivity

  exact
    mul_nonneg
      hq
      (by positivity)

/-! ## Pointwise raw-vorticity domination -/

/--
One raw-vorticity component square is bounded by four times the full H³
spectral dissipation density of the underlying weighted vector amplitude.
-/
theorem rawVorticityComponentAmplitude_sq_le_four_mul_gradientSquare_mul_totalSquare
    (q : Fin 3)
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ) :
    norm
      (
        h3TerminalRawVorticityComponentAmplitude
          q ξ g
      ) ^ 2
      ≤
    4
      *
    h3FourierGradientSquare ξ
      *
    (
      norm (g 0) ^ 2
        +
      norm (g 1) ^ 2
        +
      norm (g 2) ^ 2
    ) := by

  by_cases hGradZero :
      h3FourierGradientMagnitude ξ = 0

  · have hSymbolZero :
        ∀ j : Fin 3,
          h3FourierDerivativeSymbol j ξ = 0 := by

      intro j

      have hLe :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          j ξ

      have hNormZero :
          norm
              (h3FourierDerivativeSymbol j ξ)
            =
          0 := by

        apply le_antisymm

        · simpa only [hGradZero] using hLe

        · exact
            norm_nonneg _

      exact
        norm_eq_zero.mp
          hNormZero

    have hSquareZero :
        h3FourierGradientSquare ξ = 0 := by

      rw [
        ← h3FourierGradientMagnitude_sq,
        hGradZero
      ]

      norm_num

    fin_cases q <;>
      simp [
        h3TerminalRawVorticityComponentAmplitude,
        hSymbolZero,
        hSquareZero
      ]

  · have hGradNonneg :
        0 ≤ h3FourierGradientMagnitude ξ :=
      h3FourierGradientMagnitude_nonneg ξ

    have hGrad :
        0 < h3FourierGradientMagnitude ξ :=
      lt_of_le_of_ne
        hGradNonneg
        (Ne.symm hGradZero)

    have hRawNorm :=
      norm_rawVorticityComponentAmplitude_eq_gradientMagnitude_mul_normalized
        q ξ g hGrad

    have hNormalized :=
      normalizedVorticityComponentAmplitude_sq_le_four_mul_totalSquare
        q ξ g

    have hSquareNonneg :
        0 ≤ h3FourierGradientSquare ξ := by

      rw [
        ← h3FourierGradientMagnitude_sq
      ]

      positivity

    calc
      norm
          (
            h3TerminalRawVorticityComponentAmplitude
              q ξ g
          ) ^ 2
          =
        h3FourierGradientSquare ξ
          *
        norm
          (
            h3TerminalNormalizedVorticityComponentAmplitude
              q ξ g
          ) ^ 2 := by

            rw [
              hRawNorm,
              mul_pow,
              h3FourierGradientMagnitude_sq
            ]

      _ ≤
        h3FourierGradientSquare ξ
          *
        (
          4
            *
          (
            norm (g 0) ^ 2
              +
            norm (g 1) ^ 2
              +
            norm (g 2) ^ 2
          )
        ) :=
          mul_le_mul_of_nonneg_left
            hNormalized
            hSquareNonneg

      _ =
        4
          *
        h3FourierGradientSquare ξ
          *
        (
          norm (g 0) ^ 2
            +
          norm (g 1) ^ 2
            +
          norm (g 2) ^ 2
        ) := by
          ring

/--
Specialization of the pointwise raw-vorticity bound to the difference of two
terminal weighted spectral states.
-/
theorem rawVorticityComponentAmplitude_spectralDifference_sq_le_four_mul_dissipationDifferenceDensity
    (q : Fin 3)
    (ξ : H3FourierPoint3)
    (G H : H3SpectralFinVectorState) :
    norm
      (
        h3TerminalRawVorticityComponentAmplitude
          q ξ
          (fun j =>
            h3TerminalSpectralDifferenceAt
              G H j ξ)
      ) ^ 2
      ≤
    4
      *
    h3TerminalSpectralDissipationDifferenceDensity
      G H ξ := by

  simpa only [
    h3TerminalSpectralDissipationDifferenceDensity,
    mul_assoc
  ] using
    rawVorticityComponentAmplitude_sq_le_four_mul_gradientSquare_mul_totalSquare
      q
      ξ
      (fun j =>
        h3TerminalSpectralDifferenceAt
          G H j ξ)

/-! ## High-radial bad-cone dissipation control mass -/

/--
Fourfold full-H³ dissipation difference mass on the same equatorial bad-cone
high-radial region used by the raw-vorticity obstruction.

The factor four is included so that raw-vorticity domination is literal, with
no scalar manipulation required at the `ℝ≥0∞` level.
-/
noncomputable def h3TerminalSpectralDissipationDifferenceBadConeHighRadialControlMass
    (i : Fin 3)
    (κ ρ : ℝ)
    (G H : H3SpectralFinVectorState) : ℝ≥0∞ :=
  ∫⁻ ξ in
      h3TerminalLongitudinalAngularBadCone i κ
        \
      h3TerminalRadialFrequencyBelow ρ,
    ENNReal.ofReal
      (
        4
          *
        h3TerminalSpectralDissipationDifferenceDensity
          G H ξ
      )

/--
The extended raw-vorticity high-radial mass is bounded by the fourfold full-H³
spectral dissipation difference mass on the same set.
-/
theorem rawVorticityComponentBadConeHighRadialSquareMass_le_spectralDissipationDifferenceControlMass
    (i q : Fin 3)
    (κ ρ : ℝ)
    (G H : H3SpectralFinVectorState) :
    h3TerminalRawVorticityComponentBadConeHighRadialSquareMass
        i q κ ρ G H
      ≤
    h3TerminalSpectralDissipationDifferenceBadConeHighRadialControlMass
      i κ ρ G H := by

  let S : Set H3FourierPoint3 :=
    h3TerminalLongitudinalAngularBadCone i κ
      \
    h3TerminalRadialFrequencyBelow ρ

  have hSMeas :
      MeasurableSet S := by

    exact
      (
        measurableSet_h3TerminalLongitudinalAngularBadCone
          i κ
      ).diff
        (
          measurableSet_h3TerminalRadialFrequencyBelow
            ρ
        )

  unfold
    h3TerminalRawVorticityComponentBadConeHighRadialSquareMass
    h3TerminalSpectralDissipationDifferenceBadConeHighRadialControlMass

  change
    (∫⁻ ξ in S,
      ENNReal.ofReal
        (
          norm
            (
              h3TerminalRawVorticityComponentAmplitude
                q ξ
                (fun j =>
                  h3TerminalSpectralDifferenceAt
                    G H j ξ)
            ) ^ 2
        )
      ∂volume)
      ≤
    ∫⁻ ξ in S,
      ENNReal.ofReal
        (
          4
            *
          h3TerminalSpectralDissipationDifferenceDensity
            G H ξ
        )
      ∂volume

  apply
    setLIntegral_mono'
      hSMeas

  intro ξ hξ

  exact
    ENNReal.ofReal_le_ofReal
      (
        rawVorticityComponentAmplitude_spectralDifference_sq_le_four_mul_dissipationDifferenceDensity
          q ξ G H
      )

/-! ## Dissipation angular vanishing -/

/--
Terminal angular vanishing for the full H³ spectral dissipation difference at
one fixed positive radial cutoff.

The property is component-free: it controls the complete three-component
weighted velocity difference, hence every raw-vorticity component at once.
-/
def H3TerminalSpectralDissipationDifferenceAngularVanishingAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (i : Fin 3)
    (ρ : ℝ) : Prop :=
  ∀ δ : ℝ,
    0 < δ
      →
    ∃ κ₀ : ℝ,
      0 < κ₀
        ∧
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
              ∀ κ : ℝ,
                0 < κ
                  →
                κ < κ₀
                  →
                h3TerminalSpectralDissipationDifferenceBadConeHighRadialControlMass
                    i κ ρ
                    (h3TerminalVelocitySpectralStateAt
                      hH3 s hs)
                    (h3TerminalVelocitySpectralStateAt
                      hH3 t ht)
                  <
                ENNReal.ofReal δ

/--
Full-H³ spectral dissipation angular vanishing implies high-radial angular
vanishing for every raw-vorticity component.
-/
theorem rawVorticityHighRadialAngularVanishingAtEndpoint_of_spectralDissipationDifferenceAngularVanishingAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (i q : Fin 3)
    (ρ : ℝ)
    (hDissipation :
      H3TerminalSpectralDissipationDifferenceAngularVanishingAtEndpoint
        hH3 i ρ) :
    H3TerminalRawVorticityHighRadialAngularVanishingAtEndpoint
      hH3 i q ρ := by

  intro δ hδ

  obtain
    ⟨
      κ₀,
      hκ₀,
      η,
      hη,
      hSmall
    ⟩ :=
    hDissipation
      δ hδ

  refine
    ⟨
      κ₀,
      hκ₀,
      η,
      hη,
      ?_
    ⟩

  intro s t hs ht hsNear htNear κ hκ hκSmall

  have hRawLe :
      h3TerminalRawVorticityComponentBadConeHighRadialSquareMass
          i q κ ρ
          (h3TerminalVelocitySpectralStateAt
            hH3 s hs)
          (h3TerminalVelocitySpectralStateAt
            hH3 t ht)
        ≤
      h3TerminalSpectralDissipationDifferenceBadConeHighRadialControlMass
          i κ ρ
          (h3TerminalVelocitySpectralStateAt
            hH3 s hs)
          (h3TerminalVelocitySpectralStateAt
            hH3 t ht) :=
    rawVorticityComponentBadConeHighRadialSquareMass_le_spectralDissipationDifferenceControlMass
      i q κ ρ
      (h3TerminalVelocitySpectralStateAt
        hH3 s hs)
      (h3TerminalVelocitySpectralStateAt
        hH3 t ht)

  exact
    hRawLe.trans_lt
      (
        hSmall
          s t hs ht
          hsNear htNear
          κ hκ hκSmall
      )

/-! ## Necessary dissipation concentration under hypothetical nonextension -/

/--
Once raw Fourier velocity L² Cauchy control has removed the infrared branch,
hypothetical nonextension forces failure of angular vanishing in the full H³
spectral dissipation difference channel at one positive radial cutoff.
-/
theorem exists_failing_complementary_vorticityComponent_highRadialRaw_and_not_spectralDissipationAngularVanishing_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
          hH3 i q ε ρ
          ∧
        ¬
          H3TerminalSpectralDissipationDifferenceAngularVanishingAtEndpoint
            hH3 i ρ := by

  obtain
    ⟨
      ρ,
      hρ,
      q,
      hqNe,
      hqFail,
      hBranch,
      hNotRawAngular
    ⟩ :=
    exists_failing_complementary_vorticityComponent_highRadialRaw_and_not_angularVanishing_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hCauchy
      hε

  refine
    ⟨
      ρ,
      hρ,
      q,
      hqNe,
      hqFail,
      hBranch,
      ?_
    ⟩

  intro hDissipationAngular

  exact
    hNotRawAngular
      (
        rawVorticityHighRadialAngularVanishingAtEndpoint_of_spectralDissipationDifferenceAngularVanishingAtEndpoint
          hH3
          i
          q
          ρ
          hDissipationAngular
      )

/-! ## Conditional continuation at the dissipation frontier -/

/--
If terminal raw Fourier velocity is L² Cauchy and the full H³ spectral
dissipation difference is angularly vanishing at every positive radial cutoff,
then one surviving physical-vorticity strong H³ endpoint forces smooth
continuation.

The remaining analytic task is now entirely in the dissipation channel.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_spectralDissipationDifferenceAngularVanishing_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
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
    (hDissipationAngular :
      ∀ ρ : ℝ,
        0 < ρ
          →
        H3TerminalSpectralDissipationDifferenceAngularVanishingAtEndpoint
          hH3 i ρ) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension
        u v T := by

  apply
    smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_rawVorticityHighRadialAngularVanishing_of_actualVorticityStrongH3EndpointPath
      hH3
      hClass
      hPhysical
      hCauchy

  intro q hq ρ hρ

  exact
    rawVorticityHighRadialAngularVanishingAtEndpoint_of_spectralDissipationDifferenceAngularVanishingAtEndpoint
      hH3
      i
      q
      ρ
      (hDissipationAngular ρ hρ)

end

end Euclidean
end Bridge
end PrimeTensor
