import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Raw.Vorticity.Radial

/-!
# Radial split of the fixed normalized-vorticity obstruction

The fixed complementary normalized-vorticity component carries a uniform
positive amount of square mass on shrinking equatorial cones.

For any fixed radial cutoff `ρ`, split that cone into

* the infrared region `|D| < ρ`; and
* its radial complement `|D| ≥ ρ`.

Because normalized vorticity is a degree-zero multiplier of the weighted H³
velocity state, its square amplitude is globally integrable.  Therefore the
bad-cone mass decomposes exactly into the two radial pieces.

Consequently, at every index of the previously extracted shrinking-cone
subsequence, at least one radial piece carries more than `ε² / 64`.

This checkpoint deliberately keeps both branches.  It does not assume that
the obstruction is infrared, nor that it escapes away from zero frequency.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalLongitudinalEquatorialNormalizedVorticityRadialSplit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Integrability of one normalized-vorticity component -/

private theorem normalizedVorticityComponentSquare_aestronglyMeasurable
    (q : Fin 3)
    (G H : H3SpectralFinVectorState) :
    AEStronglyMeasurable
      (
        fun ξ : H3FourierPoint3 =>
          norm
            (
              h3TerminalNormalizedVorticityComponentAmplitude
                q ξ
                (fun j =>
                  h3TerminalSpectralDifferenceAt G H j ξ)
            ) ^ 2
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
          norm
            (
              h3TerminalNormalizedVorticityComponentAmplitude
                q ξ
                (fun j =>
                  h3TerminalSpectralDifferenceAt G H j ξ)
            ) ^ 2
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

  have hAmp :
      AEStronglyMeasurable
        (
          fun ξ : H3FourierPoint3 =>
            h3TerminalNormalizedVorticityComponentAmplitude
              q ξ
              (fun j =>
                h3TerminalSpectralDifferenceAt G H j ξ)
        )
        μ := by

    fin_cases q

    · change
        AEStronglyMeasurable
          (
            fun ξ : H3FourierPoint3 =>
              -
                h3TerminalNormalizedCurl12Amplitude
                  ξ
                  (fun j =>
                    h3TerminalSpectralDifferenceAt G H j ξ)
          )
          μ

      apply h12.neg.congr

      filter_upwards with ξ

      rfl

    · simpa [
        h3TerminalNormalizedVorticityComponentAmplitude
      ] using
        h02

    · change
        AEStronglyMeasurable
          (
            fun ξ : H3FourierPoint3 =>
              -
                h3TerminalNormalizedCurl01Amplitude
                  ξ
                  (fun j =>
                    h3TerminalSpectralDifferenceAt G H j ξ)
          )
          μ

      apply h01.neg.congr

      filter_upwards with ξ

      rfl

  exact
    (
      hAmp.norm.aemeasurable.pow_const 2
    ).aestronglyMeasurable

/--
A normalized-vorticity component square is globally integrable for every pair
of weighted H³ spectral states.
-/
theorem normalizedVorticityComponentSquare_integrable
    (q : Fin 3)
    (G H : H3SpectralFinVectorState) :
    Integrable
      (
        fun ξ : H3FourierPoint3 =>
          norm
            (
              h3TerminalNormalizedVorticityComponentAmplitude
                q ξ
                (fun j =>
                  h3TerminalSpectralDifferenceAt G H j ξ)
            ) ^ 2
      )
      volume := by

  have h0 :
      Integrable
        (
          fun ξ : H3FourierPoint3 =>
            ‖h3TerminalSpectralDifferenceAt G H 0 ξ‖ ^ 2
        )
        volume := by
    simpa [h3TerminalSpectralDifferenceAt] using
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        (G 0) (H 0)

  have h1 :
      Integrable
        (
          fun ξ : H3FourierPoint3 =>
            ‖h3TerminalSpectralDifferenceAt G H 1 ξ‖ ^ 2
        )
        volume := by
    simpa [h3TerminalSpectralDifferenceAt] using
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        (G 1) (H 1)

  have h2 :
      Integrable
        (
          fun ξ : H3FourierPoint3 =>
            ‖h3TerminalSpectralDifferenceAt G H 2 ξ‖ ^ 2
        )
        volume := by
    simpa [h3TerminalSpectralDifferenceAt] using
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        (G 2) (H 2)

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
        normalizedVorticityComponentSquare_aestronglyMeasurable
          q G H
      )

  filter_upwards with ξ

  let g : Fin 3 → ℂ :=
    fun j =>
      h3TerminalSpectralDifferenceAt G H j ξ

  have hBound :
      norm
        (
          h3TerminalNormalizedVorticityComponentAmplitude
            q ξ g
        ) ^ 2
        ≤
      4 *
        (
          ‖g 0‖ ^ 2
            +
          ‖g 1‖ ^ 2
            +
          ‖g 2‖ ^ 2
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
          (norm
            (h3TerminalNormalizedCurl01Amplitude ξ g))
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
          (norm
            (h3TerminalNormalizedCurl01Amplitude ξ g))
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
          (norm
            (h3TerminalNormalizedCurl02Amplitude ξ g))
      ]

  have hNonneg :
      0
        ≤
      norm
        (
          h3TerminalNormalizedVorticityComponentAmplitude
            q ξ g
        ) ^ 2 :=
    sq_nonneg _

  rw [
    Real.norm_eq_abs,
    abs_of_nonneg hNonneg
  ]

  simpa only [g] using
    hBound

/-! ## Radial localization -/

/--
Strict infrared radial region.
-/
def h3TerminalRadialFrequencyBelow
    (ρ : ℝ) :
    Set H3FourierPoint3 :=
  {
    ξ |
      h3FourierGradientMagnitude ξ
        <
      ρ
  }

theorem measurableSet_h3TerminalRadialFrequencyBelow
    (ρ : ℝ) :
    MeasurableSet
      (h3TerminalRadialFrequencyBelow ρ) := by

  unfold
    h3TerminalRadialFrequencyBelow
    h3FourierGradientMagnitude

  exact
    measurableSet_lt
      (by fun_prop)
      measurable_const

/--
Normalized-vorticity bad-cone mass below radial cutoff `ρ`.
-/
noncomputable def h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect
    (i q : Fin 3)
    (κ ρ : ℝ)
    (G H : H3SpectralFinVectorState) : ℝ :=
  ∫ ξ in
      h3TerminalLongitudinalAngularBadCone i κ
        ∩
      h3TerminalRadialFrequencyBelow ρ,
    norm
      (
        h3TerminalNormalizedVorticityComponentAmplitude
          q ξ
          (fun j =>
            h3TerminalSpectralDifferenceAt G H j ξ)
      ) ^ 2

/--
Normalized-vorticity bad-cone mass on the complementary radial region.
-/
noncomputable def h3TerminalNormalizedVorticityComponentBadConeHighRadialSquareDefect
    (i q : Fin 3)
    (κ ρ : ℝ)
    (G H : H3SpectralFinVectorState) : ℝ :=
  ∫ ξ in
      h3TerminalLongitudinalAngularBadCone i κ
        \
      h3TerminalRadialFrequencyBelow ρ,
    norm
      (
        h3TerminalNormalizedVorticityComponentAmplitude
          q ξ
          (fun j =>
            h3TerminalSpectralDifferenceAt G H j ξ)
      ) ^ 2

/--
Exact low/high radial decomposition of one normalized-vorticity bad-cone mass.
-/
theorem normalizedVorticityComponentBadConeSquareDefect_eq_lowRadial_add_highRadial
    (i q : Fin 3)
    (κ ρ : ℝ)
    (G H : H3SpectralFinVectorState) :
    h3TerminalNormalizedVorticityComponentBadConeSquareDefect
        i q κ G H
      =
    h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect
        i q κ ρ G H
      +
    h3TerminalNormalizedVorticityComponentBadConeHighRadialSquareDefect
        i q κ ρ G H := by

  let f : H3FourierPoint3 → ℝ :=
    fun ξ =>
      norm
        (
          h3TerminalNormalizedVorticityComponentAmplitude
            q ξ
            (fun j =>
              h3TerminalSpectralDifferenceAt G H j ξ)
        ) ^ 2

  have hInt :
      Integrable f volume := by
    simpa only [f] using
      normalizedVorticityComponentSquare_integrable
        q G H

  have hLowMeas :
      MeasurableSet
        (h3TerminalRadialFrequencyBelow ρ) :=
    measurableSet_h3TerminalRadialFrequencyBelow ρ

  have hSplit :=
    integral_inter_add_sdiff₀
      (μ := volume)
      (s := h3TerminalLongitudinalAngularBadCone i κ)
      hLowMeas.nullMeasurableSet
      hInt.integrableOn

  unfold
    h3TerminalNormalizedVorticityComponentBadConeSquareDefect
    h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect
    h3TerminalNormalizedVorticityComponentBadConeHighRadialSquareDefect

  change
    (∫ ξ in h3TerminalLongitudinalAngularBadCone i κ, f ξ)
      =
    (∫ ξ in
        h3TerminalLongitudinalAngularBadCone i κ
          ∩
        h3TerminalRadialFrequencyBelow ρ,
        f ξ)
      +
    (∫ ξ in
        h3TerminalLongitudinalAngularBadCone i κ
          \
        h3TerminalRadialFrequencyBelow ρ,
        f ξ)

  exact
    hSplit.symm

/--
If the total normalized-vorticity bad-cone mass is larger than `C`, then at
least one radial side carries more than `C/2`.
-/
theorem normalizedVorticityComponentBadCone_lowRadial_or_highRadial_gt_half
    (i q : Fin 3)
    (κ ρ C : ℝ)
    (G H : H3SpectralFinVectorState)
    (hTotal :
      C
        <
      h3TerminalNormalizedVorticityComponentBadConeSquareDefect
        i q κ G H) :
    C / 2
        <
      h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect
        i q κ ρ G H
      ∨
    C / 2
        <
      h3TerminalNormalizedVorticityComponentBadConeHighRadialSquareDefect
        i q κ ρ G H := by

  rw [
    normalizedVorticityComponentBadConeSquareDefect_eq_lowRadial_add_highRadial
  ] at hTotal

  by_contra hNo

  push_neg at hNo

  linarith

/-! ## Radial dichotomy along the fixed shrinking-cone subsequence -/

/--
For every fixed positive radial cutoff, each index of the fixed complementary
normalized-vorticity shrinking-cone subsequence carries more than `ε²/64`
either below that cutoff or on its radial complement.
-/
theorem exists_fixed_complementary_normalizedVorticityComponent_shrinkingEquatorialCone_radialSplit_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    {ε ρ : ℝ}
    (hε : 0 < ε)
    (hρ : 0 < ρ) :
    ∃ s t : ℕ → ℝ,
      ∃ hs :
        ∀ n : ℕ,
          s n ∈ Set.Ioo (0 : ℝ) T,
        ∃ ht :
          ∀ n : ℕ,
            t n ∈ Set.Ioo (0 : ℝ) T,
          ∃ q : Fin 3,
            q ≠ i
              ∧
            ∃ m : ℕ → ℕ,
              StrictMono m
                ∧
              Tendsto
                (fun n : ℕ => s (m n))
                atTop
                (𝓝 T)
                ∧
              Tendsto
                (fun n : ℕ => t (m n))
                atTop
                (𝓝 T)
                ∧
              Tendsto
                (
                  fun n : ℕ =>
                    (1 : ℝ) / (((m n : ℕ) : ℝ) + 2)
                )
                atTop
                (𝓝 0)
                ∧
              (
                ∀ n : ℕ,
                  ε ^ 2 / 64
                      <
                    h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect
                      i q
                      ((1 : ℝ) / (((m n : ℕ) : ℝ) + 2))
                      ρ
                      (h3TerminalVelocitySpectralStateAt
                        hH3
                        (s (m n))
                        (hs (m n)))
                      (h3TerminalVelocitySpectralStateAt
                        hH3
                        (t (m n))
                        (ht (m n)))
                    ∨
                  ε ^ 2 / 64
                      <
                    h3TerminalNormalizedVorticityComponentBadConeHighRadialSquareDefect
                      i q
                      ((1 : ℝ) / (((m n : ℕ) : ℝ) + 2))
                      ρ
                      (h3TerminalVelocitySpectralStateAt
                        hH3
                        (s (m n))
                        (hs (m n)))
                      (h3TerminalVelocitySpectralStateAt
                        hH3
                        (t (m n))
                        (ht (m n)))
              ) := by

  obtain
    ⟨
      s,
      t,
      hs,
      ht,
      q,
      hqNe,
      m,
      hMMono,
      hSTendsto,
      hTTendsto,
      hApertureTendsto,
      hMass
    ⟩ :=
    exists_fixed_complementary_normalizedVorticityComponent_shrinkingEquatorialCone_subsequence_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hε

  have hSplit :
      ∀ n : ℕ,
        ε ^ 2 / 64
            <
          h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect
            i q
            ((1 : ℝ) / (((m n : ℕ) : ℝ) + 2))
            ρ
            (h3TerminalVelocitySpectralStateAt
              hH3
              (s (m n))
              (hs (m n)))
            (h3TerminalVelocitySpectralStateAt
              hH3
              (t (m n))
              (ht (m n)))
          ∨
        ε ^ 2 / 64
            <
          h3TerminalNormalizedVorticityComponentBadConeHighRadialSquareDefect
            i q
            ((1 : ℝ) / (((m n : ℕ) : ℝ) + 2))
            ρ
            (h3TerminalVelocitySpectralStateAt
              hH3
              (s (m n))
              (hs (m n)))
            (h3TerminalVelocitySpectralStateAt
              hH3
              (t (m n))
              (ht (m n))) := by

    intro n

    have hOne :=
      normalizedVorticityComponentBadCone_lowRadial_or_highRadial_gt_half
        i q
        ((1 : ℝ) / (((m n : ℕ) : ℝ) + 2))
        ρ
        (ε ^ 2 / 32)
        (h3TerminalVelocitySpectralStateAt
          hH3
          (s (m n))
          (hs (m n)))
        (h3TerminalVelocitySpectralStateAt
          hH3
          (t (m n))
          (ht (m n)))
        (hMass n)

    convert hOne using 1 <;> ring_nf

  exact
    ⟨
      s,
      t,
      hs,
      ht,
      q,
      hqNe,
      m,
      hMMono,
      hSTendsto,
      hTTendsto,
      hApertureTendsto,
      hSplit
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
