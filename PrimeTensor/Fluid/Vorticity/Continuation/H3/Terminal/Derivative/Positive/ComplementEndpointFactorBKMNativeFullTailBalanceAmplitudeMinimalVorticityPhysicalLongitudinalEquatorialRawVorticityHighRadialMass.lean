import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialNormalizedVorticityFixedRadialBranch

/-!
# Raw vorticity mass on the frozen high-radial branch

The preceding radial classification freezes, for every fixed `ρ > 0`, either

* an infrared normalized-vorticity branch below `ρ`, or
* a normalized-vorticity branch on the complementary region `|D| ≥ ρ`.

On the second branch the pointwise raw/normalized identity gives

    ρ² |ω̃_q|² ≤ |ω_q^raw|².

The raw square need not be integrable at H³, because it spends one additional
radial Fourier derivative.  Therefore the correct H³-level raw mass is an
extended nonnegative integral in `ℝ≥0∞`, not a real Bochner integral.

This file defines that extended raw mass, proves that it dominates `ρ²` times
the finite normalized mass, and upgrades the frozen radial dichotomy
accordingly.

No H⁴ assumption is introduced, and the infrared branch is retained.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalLongitudinalEquatorialRawVorticityHighRadialMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Extended raw-vorticity mass -/

/--
Extended raw-vorticity square mass on the equatorial bad cone and on the
radial complement `|D| ≥ ρ`.

The codomain is `ℝ≥0∞` intentionally: H³ does not provide global integrability
of one additional raw radial derivative.
-/
noncomputable def h3TerminalRawVorticityComponentBadConeHighRadialSquareMass
    (i q : Fin 3)
    (κ ρ : ℝ)
    (G H : H3SpectralFinVectorState) : ℝ≥0∞ :=
  ∫⁻ ξ in
      h3TerminalLongitudinalAngularBadCone i κ
        \
      h3TerminalRadialFrequencyBelow ρ,
    ENNReal.ofReal
      (
        norm
          (
            h3TerminalRawVorticityComponentAmplitude
              q ξ
              (fun j =>
                h3TerminalSpectralDifferenceAt G H j ξ)
          ) ^ 2
      )

/--
On the high-radial bad-cone region, extended raw-vorticity mass dominates
`ρ²` times the finite normalized-vorticity mass.
-/
theorem ofReal_sq_mul_normalizedVorticityComponentBadConeHighRadialSquareDefect_le_rawVorticityComponentBadConeHighRadialSquareMass
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (i q : Fin 3)
    (κ : ℝ)
    (G H : H3SpectralFinVectorState) :
    ENNReal.ofReal
      (
        ρ ^ 2
          *
        h3TerminalNormalizedVorticityComponentBadConeHighRadialSquareDefect
          i q κ ρ G H
      )
      ≤
    h3TerminalRawVorticityComponentBadConeHighRadialSquareMass
      i q κ ρ G H := by

  let S : Set H3FourierPoint3 :=
    h3TerminalLongitudinalAngularBadCone i κ
      \
    h3TerminalRadialFrequencyBelow ρ

  let f : H3FourierPoint3 → ℝ :=
    fun ξ =>
      norm
        (
          h3TerminalNormalizedVorticityComponentAmplitude
            q ξ
            (fun j =>
              h3TerminalSpectralDifferenceAt G H j ξ)
        ) ^ 2

  let g : H3FourierPoint3 → ℝ :=
    fun ξ =>
      norm
        (
          h3TerminalRawVorticityComponentAmplitude
            q ξ
            (fun j =>
              h3TerminalSpectralDifferenceAt G H j ξ)
        ) ^ 2

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

  have hFInt :
      IntegrableOn f S volume := by

    exact
      (
        normalizedVorticityComponentSquare_integrable
          q G H
      ).integrableOn

  have hFNonneg :
      0 ≤ᵐ[volume.restrict S] f := by

    filter_upwards with ξ

    exact
      sq_nonneg _

  have hIntegralBridge :
      ENNReal.ofReal
        (∫ ξ in S, f ξ ∂volume)
        =
      ∫⁻ ξ in S,
        ENNReal.ofReal (f ξ)
        ∂volume := by

    exact
      ofReal_integral_eq_lintegral_ofReal
        hFInt
        hFNonneg

  have hPointwise :
      ∀ ξ ∈ S,
        ρ ^ 2 * f ξ
          ≤
        g ξ := by

    intro ξ hξ

    have hHigh :
        ξ ∈ h3TerminalRadialFrequencyAbove ρ := by

      change
        ρ
          ≤
        h3FourierGradientMagnitude ξ

      have hNotLow :=
        hξ.2

      change
        ¬
          h3FourierGradientMagnitude ξ
            <
          ρ
        at hNotLow

      exact
        le_of_not_gt
          hNotLow

    exact
      sq_mul_normalizedVorticity_le_rawVorticity_sq_of_mem_radialFrequencyAbove
        hρ
        hHigh
        q
        (fun j =>
          h3TerminalSpectralDifferenceAt G H j ξ)

  have hLIntegral :
      (∫⁻ ξ in S,
        ENNReal.ofReal
          (ρ ^ 2 * f ξ)
        ∂volume)
        ≤
      ∫⁻ ξ in S,
        ENNReal.ofReal
          (g ξ)
        ∂volume := by

    apply
      setLIntegral_mono'
        hSMeas

    intro ξ hξ

    exact
      ENNReal.ofReal_le_ofReal
        (hPointwise ξ hξ)

  unfold
    h3TerminalNormalizedVorticityComponentBadConeHighRadialSquareDefect
    h3TerminalRawVorticityComponentBadConeHighRadialSquareMass

  change
    ENNReal.ofReal
      (
        ρ ^ 2
          *
        (∫ ξ in S, f ξ ∂volume)
      )
      ≤
    ∫⁻ ξ in S,
      ENNReal.ofReal (g ξ)
      ∂volume

  calc
    ENNReal.ofReal
        (
          ρ ^ 2
            *
          (∫ ξ in S, f ξ ∂volume)
        )
        =
      ENNReal.ofReal (ρ ^ 2)
        *
      ENNReal.ofReal
        (∫ ξ in S, f ξ ∂volume) := by

          rw [
            ENNReal.ofReal_mul
              (sq_nonneg ρ)
          ]

    _ =
      ENNReal.ofReal (ρ ^ 2)
        *
      (∫⁻ ξ in S,
        ENNReal.ofReal (f ξ)
        ∂volume) := by

          rw [
            hIntegralBridge
          ]

    _ =
      ∫⁻ ξ in S,
        ENNReal.ofReal (ρ ^ 2)
          *
        ENNReal.ofReal (f ξ)
        ∂volume := by

          symm

          exact
            lintegral_const_mul'
              (ENNReal.ofReal (ρ ^ 2))
              (fun ξ =>
                ENNReal.ofReal (f ξ))
              ENNReal.ofReal_lt_top.ne

    _ =
      ∫⁻ ξ in S,
        ENNReal.ofReal
          (ρ ^ 2 * f ξ)
        ∂volume := by

          apply
            setLIntegral_congr_fun
              hSMeas

          intro ξ hξ

          change
            ENNReal.ofReal (ρ ^ 2)
                *
              ENNReal.ofReal (f ξ)
              =
            ENNReal.ofReal
              (ρ ^ 2 * f ξ)

          exact
            (
              ENNReal.ofReal_mul
                (sq_nonneg ρ)
            ).symm

    _ ≤
      ∫⁻ ξ in S,
        ENNReal.ofReal (g ξ)
        ∂volume :=
          hLIntegral

/--
A strict lower bound on normalized high-radial mass yields a strict extended
raw-vorticity lower bound with the quantitative `ρ²` factor.
-/
theorem rawVorticityComponentBadConeHighRadialSquareMass_gt_of_normalizedVorticityComponentBadConeHighRadialSquareDefect_gt
    {ρ C : ℝ}
    (hρ : 0 < ρ)
    (hC : 0 ≤ C)
    (i q : Fin 3)
    (κ : ℝ)
    (G H : H3SpectralFinVectorState)
    (hHigh :
      C
        <
      h3TerminalNormalizedVorticityComponentBadConeHighRadialSquareDefect
        i q κ ρ G H) :
    ENNReal.ofReal
      (ρ ^ 2 * C)
      <
    h3TerminalRawVorticityComponentBadConeHighRadialSquareMass
      i q κ ρ G H := by

  have hNormPos :
      0
        <
      h3TerminalNormalizedVorticityComponentBadConeHighRadialSquareDefect
        i q κ ρ G H :=
    lt_of_le_of_lt
      hC
      hHigh

  have hScaled :
      ρ ^ 2 * C
        <
      ρ ^ 2
        *
      h3TerminalNormalizedVorticityComponentBadConeHighRadialSquareDefect
        i q κ ρ G H := by

    have hρsq :
        0 < ρ ^ 2 := by
      positivity

    exact
      mul_lt_mul_of_pos_left
        hHigh
        hρsq

  have hOfReal :
      ENNReal.ofReal
          (ρ ^ 2 * C)
        <
      ENNReal.ofReal
          (
            ρ ^ 2
              *
            h3TerminalNormalizedVorticityComponentBadConeHighRadialSquareDefect
              i q κ ρ G H
          ) := by

    apply
      (
        ENNReal.ofReal_lt_ofReal_iff
          (by positivity :
            0
              <
            ρ ^ 2
              *
            h3TerminalNormalizedVorticityComponentBadConeHighRadialSquareDefect
              i q κ ρ G H)
      ).2

    exact
      hScaled

  exact
    hOfReal.trans_le
      (
        ofReal_sq_mul_normalizedVorticityComponentBadConeHighRadialSquareDefect_le_rawVorticityComponentBadConeHighRadialSquareMass
          hρ
          i q κ G H
      )

/-! ## Upgrade the frozen radial classification -/

/--
For each fixed `ρ > 0`, the frozen terminal radial classification can be
stated directly as:

* persistent infrared normalized-vorticity mass below `ρ`, or
* persistent extended raw-vorticity mass above `ρ`, bounded below by the
  quantitative threshold `ρ² ε² / 64`.

This is the H³-compatible raw-vorticity form of the high-radial branch.
-/
theorem exists_fixed_complementary_vorticityComponent_shrinkingEquatorialCone_infraredNormalized_or_highRadialRaw_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
            ∃ p : ℕ → ℕ,
              StrictMono p
                ∧
              Tendsto
                (fun n : ℕ => s (p n))
                atTop
                (𝓝 T)
                ∧
              Tendsto
                (fun n : ℕ => t (p n))
                atTop
                (𝓝 T)
                ∧
              Tendsto
                (
                  fun n : ℕ =>
                    (1 : ℝ) / (((p n : ℕ) : ℝ) + 2)
                )
                atTop
                (𝓝 0)
                ∧
              (
                (
                  ∀ n : ℕ,
                    ε ^ 2 / 64
                        <
                      h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect
                        i q
                        ((1 : ℝ) / (((p n : ℕ) : ℝ) + 2))
                        ρ
                        (h3TerminalVelocitySpectralStateAt
                          hH3
                          (s (p n))
                          (hs (p n)))
                        (h3TerminalVelocitySpectralStateAt
                          hH3
                          (t (p n))
                          (ht (p n)))
                )
                  ∨
                (
                  ∀ n : ℕ,
                    ENNReal.ofReal
                        (ρ ^ 2 * (ε ^ 2 / 64))
                      <
                    h3TerminalRawVorticityComponentBadConeHighRadialSquareMass
                      i q
                      ((1 : ℝ) / (((p n : ℕ) : ℝ) + 2))
                      ρ
                      (h3TerminalVelocitySpectralStateAt
                        hH3
                        (s (p n))
                        (hs (p n)))
                      (h3TerminalVelocitySpectralStateAt
                        hH3
                        (t (p n))
                        (ht (p n)))
                )
              ) := by

  obtain
    ⟨
      s,
      t,
      hs,
      ht,
      q,
      hqNe,
      p,
      hPMono,
      hSTendsto,
      hTTendsto,
      hApertureTendsto,
      hBranch
    ⟩ :=
    exists_fixed_complementary_normalizedVorticityComponent_shrinkingEquatorialCone_fixedRadialBranch_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hε
      hρ

  refine
    ⟨
      s,
      t,
      hs,
      ht,
      q,
      hqNe,
      p,
      hPMono,
      hSTendsto,
      hTTendsto,
      hApertureTendsto,
      ?_
    ⟩

  rcases hBranch with hLow | hHigh

  · exact
      Or.inl
        hLow

  · right

    intro n

    exact
      rawVorticityComponentBadConeHighRadialSquareMass_gt_of_normalizedVorticityComponentBadConeHighRadialSquareDefect_gt
        hρ
        (by positivity)
        i q
        ((1 : ℝ) / (((p n : ℕ) : ℝ) + 2))
        (h3TerminalVelocitySpectralStateAt
          hH3
          (s (p n))
          (hs (p n)))
        (h3TerminalVelocitySpectralStateAt
          hH3
          (t (p n))
          (ht (p n)))
        (hHigh n)

end

end Euclidean
end Bridge
end PrimeTensor
