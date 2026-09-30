import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialNormalizedCurlChannelSubsequence

/-!
# Identify the frozen normalized curl channel with normalized vorticity

The three normalized pairwise curl amplitudes are, with the physical vorticity
sign convention used by `realVorticityX/Y/Z`,

    C01 = - ω₂ / |D|
    C02 = + ω₁ / |D|
    C12 = - ω₀ / |D|.

Hence every normalized longitudinal curl channel is exactly one complementary
normalized-vorticity component up to sign.  Since the concentration statement
is in square norm, the sign disappears.

This file packages that identification and upgrades the fixed-channel
subsequence to one fixed complementary normalized-vorticity component.

No new physical Fourier-transform identification is asserted here: the object
below is the degree-zero normalized vorticity symbol built from the terminal
velocity spectral state.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalLongitudinalEquatorialNormalizedVorticityChannel
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Normalized vorticity-symbol components -/

/--
Degree-zero normalized vorticity-symbol amplitude.

With coordinate labels `0=x`, `1=y`, `2=z`,

* component `0` is `ωₓ / |D| = - C12`,
* component `1` is `ωᵧ / |D| =   C02`,
* component `2` is `ω_z / |D| = - C01`.
-/
def h3TerminalNormalizedVorticityComponentAmplitude
    (q : Fin 3)
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ) : ℂ :=
  if q = 0 then
    - h3TerminalNormalizedCurl12Amplitude ξ g
  else if q = 1 then
    h3TerminalNormalizedCurl02Amplitude ξ g
  else
    - h3TerminalNormalizedCurl01Amplitude ξ g

/--
The physical-vorticity coordinate represented by longitudinal curl channel
`(i,k)`.
-/
def h3TerminalNormalizedLongitudinalCurlChannelVorticityIndex
    (i : Fin 3)
    (k : Fin 2) : Fin 3 :=
  if i = 0 then
    if k = 0 then
      2
    else
      1
  else if i = 1 then
    if k = 0 then
      2
    else
      0
  else
    if k = 0 then
      1
    else
      0

/--
A longitudinal curl channel always corresponds to a complementary vorticity
coordinate.
-/
theorem normalizedLongitudinalCurlChannelVorticityIndex_ne_longitudinal
    (i : Fin 3)
    (k : Fin 2) :
    h3TerminalNormalizedLongitudinalCurlChannelVorticityIndex i k
      ≠
    i := by

  fin_cases i <;>
    fin_cases k <;>
    simp [
      h3TerminalNormalizedLongitudinalCurlChannelVorticityIndex
    ]

/--
The frozen longitudinal curl channel and its corresponding normalized
vorticity-symbol component have identical magnitude.
-/
theorem norm_normalizedLongitudinalCurlChannelAmplitude_eq_normalizedVorticityComponentAmplitude
    (i : Fin 3)
    (k : Fin 2)
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ) :
    ‖h3TerminalNormalizedLongitudinalCurlChannelAmplitude i k ξ g‖
      =
    norm
      (
        h3TerminalNormalizedVorticityComponentAmplitude
          (h3TerminalNormalizedLongitudinalCurlChannelVorticityIndex i k)
          ξ g
      ) := by

  fin_cases i <;>
    fin_cases k <;>
    simp [
      h3TerminalNormalizedLongitudinalCurlChannelAmplitude,
      h3TerminalNormalizedLongitudinalCurlChannelVorticityIndex,
      h3TerminalNormalizedVorticityComponentAmplitude
    ]

/-! ## Bad-cone mass for one normalized vorticity component -/

/--
Square mass of normalized vorticity-symbol component `q` on the bad cone
associated with longitudinal velocity coordinate `i`.
-/
noncomputable def h3TerminalNormalizedVorticityComponentBadConeSquareDefect
    (i q : Fin 3)
    (κ : ℝ)
    (G H : H3SpectralFinVectorState) : ℝ :=
  ∫ ξ in h3TerminalLongitudinalAngularBadCone i κ,
    norm
      (
        h3TerminalNormalizedVorticityComponentAmplitude
          q ξ
          (fun j =>
            h3TerminalSpectralDifferenceAt G H j ξ)
      ) ^ 2

/--
The individual longitudinal curl-channel bad-cone mass is exactly the bad-cone
mass of its corresponding normalized vorticity component.
-/
theorem normalizedLongitudinalCurlChannelBadConeSquareDefect_eq_normalizedVorticityComponentBadConeSquareDefect
    (i : Fin 3)
    (k : Fin 2)
    (κ : ℝ)
    (G H : H3SpectralFinVectorState) :
    h3TerminalNormalizedLongitudinalCurlChannelBadConeSquareDefect
        i k κ G H
      =
    h3TerminalNormalizedVorticityComponentBadConeSquareDefect
        i
        (h3TerminalNormalizedLongitudinalCurlChannelVorticityIndex i k)
        κ G H := by

  unfold
    h3TerminalNormalizedLongitudinalCurlChannelBadConeSquareDefect
    h3TerminalNormalizedVorticityComponentBadConeSquareDefect

  apply integral_congr_ae

  filter_upwards with ξ

  rw [
    norm_normalizedLongitudinalCurlChannelAmplitude_eq_normalizedVorticityComponentAmplitude
  ]

/-! ## Fixed complementary normalized-vorticity component -/

/--
Under hypothetical nonextension and one surviving physical-vorticity
strong-H³ endpoint, one fixed complementary normalized-vorticity component
carries more than `ε²/32` square mass along an explicit shrinking-equatorial
subsequence.
-/
theorem exists_fixed_complementary_normalizedVorticityComponent_shrinkingEquatorialCone_subsequence_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    {ε : ℝ}
    (hε : 0 < ε) :
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
                  ε ^ 2 / 32
                    <
                  h3TerminalNormalizedVorticityComponentBadConeSquareDefect
                    i q
                    ((1 : ℝ) / (((m n : ℕ) : ℝ) + 2))
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
      k,
      m,
      hMMono,
      hSTendsto,
      hTTendsto,
      hApertureTendsto,
      hChannelMass
    ⟩ :=
    exists_fixed_normalizedLongitudinalCurlChannel_shrinkingEquatorialCone_subsequence_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hε

  let q : Fin 3 :=
    h3TerminalNormalizedLongitudinalCurlChannelVorticityIndex i k

  have hqNe :
      q ≠ i := by
    dsimp only [q]
    exact
      normalizedLongitudinalCurlChannelVorticityIndex_ne_longitudinal
        i k

  have hVorticityMass :
      ∀ n : ℕ,
        ε ^ 2 / 32
          <
        h3TerminalNormalizedVorticityComponentBadConeSquareDefect
          i q
          ((1 : ℝ) / (((m n : ℕ) : ℝ) + 2))
          (h3TerminalVelocitySpectralStateAt
            hH3
            (s (m n))
            (hs (m n)))
          (h3TerminalVelocitySpectralStateAt
            hH3
            (t (m n))
            (ht (m n))) := by

    intro n

    have hMass :=
      hChannelMass n

    rw [
      normalizedLongitudinalCurlChannelBadConeSquareDefect_eq_normalizedVorticityComponentBadConeSquareDefect
    ] at hMass

    simpa only [q] using
      hMass

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
      hVorticityMass
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
