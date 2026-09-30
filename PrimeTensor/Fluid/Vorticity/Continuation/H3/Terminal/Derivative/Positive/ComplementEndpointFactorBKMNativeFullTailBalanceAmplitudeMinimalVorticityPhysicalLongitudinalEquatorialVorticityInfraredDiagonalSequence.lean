import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityFixedInfraredComponent

/-!
# Diagonal infrared vorticity concentration sequence

The preceding checkpoint froze one complementary vorticity component `q ≠ i`
across all canonical radial cutoffs

    ρ_N = 1 / (N + 1).

The terminal time sequences and angular subsequences inside each cutoff branch
could still depend on `N`.

This file performs the next diagonal selection.  For each radial cutoff `ρ_N`,
choose one sufficiently late pair from that cutoff's branch so that both times
lie in `(T - ρ_N, T)`, and choose the inner angular index at least `N`.
The resulting diagonal sequences have

* one fixed complementary vorticity component `q`;
* two strict times converging to `T`;
* radial cutoff `ρ_N → 0`;
* angular aperture `κ_N → 0`, with `κ_N ≤ ρ_N`;
* normalized-vorticity square mass `> ε² / 64` inside both the shrinking
  equatorial cone and the shrinking radial ball.

This remains the infrared alternative only.  The separate positive-cutoff
high-radial raw-vorticity branch is retained unchanged.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalLongitudinalEquatorialVorticityInfraredDiagonalSequence
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
Either some positive radial cutoff carries the high-radial raw-vorticity
obstruction, or there is one fixed complementary vorticity component and one
explicit diagonal sequence whose times, radial cutoff, and angular aperture all
converge simultaneously while the infrared normalized-vorticity mass stays
above `ε² / 64`.
-/
theorem exists_positive_highRadialRaw_cutoff_or_fixed_complementary_infraredNormalized_diagonalSequence_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    (
      ∃ ρ : ℝ,
        0 < ρ
          ∧
        ∃ q : Fin 3,
          q ≠ i
            ∧
          H3TerminalHighRadialRawVorticityBranchAtCutoff
            hH3 i q ε ρ
    )
      ∨
    (
      ∃ q : Fin 3,
        q ≠ i
          ∧
        ∃ σ τ κ : ℕ → ℝ,
          ∃ hσ :
            ∀ N : ℕ,
              σ N ∈ Set.Ioo (0 : ℝ) T,
            ∃ hτ :
              ∀ N : ℕ,
                τ N ∈ Set.Ioo (0 : ℝ) T,
              Tendsto
                σ
                atTop
                (𝓝 T)
                ∧
              Tendsto
                τ
                atTop
                (𝓝 T)
                ∧
              Tendsto
                (
                  fun N : ℕ =>
                    (1 : ℝ) / ((N : ℝ) + 1)
                )
                atTop
                (𝓝 0)
                ∧
              Tendsto
                κ
                atTop
                (𝓝 0)
                ∧
              (
                ∀ N : ℕ,
                  0 < κ N
                    ∧
                  κ N
                    ≤
                  (1 : ℝ) / ((N : ℝ) + 1)
                    ∧
                  ε ^ 2 / 64
                    <
                  h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect
                    i q
                    (κ N)
                    ((1 : ℝ) / ((N : ℝ) + 1))
                    (h3TerminalVelocitySpectralStateAt
                      hH3
                      (σ N)
                      (hσ N))
                    (h3TerminalVelocitySpectralStateAt
                      hH3
                      (τ N)
                      (hτ N))
              )
    ) := by

  classical

  have hFixed :=
    exists_positive_highRadialRaw_cutoff_or_fixed_complementary_infraredNormalized_on_all_vanishing_radial_scales_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hε

  rcases hFixed with hHigh | hInfra

  · exact
      Or.inl
        hHigh

  · right

    obtain
      ⟨
        q,
        hqNe,
        hRhoTendsto,
        hEvery
      ⟩ :=
      hInfra

    have hPoint :
        ∀ N : ℕ,
          ∃ σN τN κN : ℝ,
            ∃ hσN :
              σN ∈ Set.Ioo (0 : ℝ) T,
              ∃ hτN :
                τN ∈ Set.Ioo (0 : ℝ) T,
                T - (1 : ℝ) / ((N : ℝ) + 1)
                    <
                  σN
                  ∧
                T - (1 : ℝ) / ((N : ℝ) + 1)
                    <
                  τN
                  ∧
                0 < κN
                  ∧
                κN
                    ≤
                  (1 : ℝ) / ((N : ℝ) + 1)
                  ∧
                ε ^ 2 / 64
                    <
                  h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect
                    i q
                    κN
                    ((1 : ℝ) / ((N : ℝ) + 1))
                    (h3TerminalVelocitySpectralStateAt
                      hH3
                      σN
                      hσN)
                    (h3TerminalVelocitySpectralStateAt
                      hH3
                      τN
                      hτN) := by

      intro N

      have hBranch :=
        hEvery N

      unfold
        H3TerminalInfraredNormalizedVorticityBranchAtCutoff
      at hBranch

      obtain
        ⟨
          s,
          t,
          hs,
          ht,
          p,
          hPMono,
          hSTendsto,
          hTTendsto,
          hApertureTendsto,
          hMass
        ⟩ :=
        hBranch

      have hRhoPos :
          0
            <
          (1 : ℝ) / ((N : ℝ) + 1) := by
        positivity

      have hSLate :
          ∀ᶠ n : ℕ in atTop,
            T - (1 : ℝ) / ((N : ℝ) + 1)
              <
            s (p n) := by

        exact
          (tendsto_order.1 hSTendsto).1
            (T - (1 : ℝ) / ((N : ℝ) + 1))
            (by linarith)

      have hTLate :
          ∀ᶠ n : ℕ in atTop,
            T - (1 : ℝ) / ((N : ℝ) + 1)
              <
            t (p n) := by

        exact
          (tendsto_order.1 hTTendsto).1
            (T - (1 : ℝ) / ((N : ℝ) + 1))
            (by linarith)

      obtain
        ⟨
          n,
          hnS,
          hnT,
          hnN
        ⟩ :=
        (
          hSLate.and
            (
              hTLate.and
                (eventually_ge_atTop N)
            )
        ).exists

      have hNp :
          N ≤ p n := by

        exact
          hnN.trans
            hPMono.le_apply

      have hDenPos :
          0 < (N : ℝ) + 1 := by
        positivity

      have hDenLe :
          (N : ℝ) + 1
            ≤
          (p n : ℝ) + 2 := by

        have hCast :
            (N : ℝ)
              ≤
            (p n : ℝ) := by
          exact_mod_cast
            hNp

        linarith

      have hKappaLe :
          (1 : ℝ) / ((p n : ℝ) + 2)
            ≤
          (1 : ℝ) / ((N : ℝ) + 1) := by

        exact
          one_div_le_one_div_of_le
            hDenPos
            hDenLe

      exact
        ⟨
          s (p n),
          t (p n),
          (1 : ℝ) / ((p n : ℝ) + 2),
          hs (p n),
          ht (p n),
          hnS,
          hnT,
          by positivity,
          hKappaLe,
          hMass n
        ⟩

    choose
      σ τ κ hσ hτ
      hσNear hτNear
      hκPos hκBound hMass
    using
      hPoint

    have hSigmaNormBound :
        ∀ N : ℕ,
          ‖σ N - T‖
            ≤
          (1 : ℝ) / ((N : ℝ) + 1) := by

      intro N

      rw [
        Real.norm_eq_abs,
        abs_of_nonpos
          (
            sub_nonpos.mpr
              (le_of_lt (hσ N).2)
          )
      ]

      linarith [
        hσNear N
      ]

    have hTauNormBound :
        ∀ N : ℕ,
          ‖τ N - T‖
            ≤
          (1 : ℝ) / ((N : ℝ) + 1) := by

      intro N

      rw [
        Real.norm_eq_abs,
        abs_of_nonpos
          (
            sub_nonpos.mpr
              (le_of_lt (hτ N).2)
          )
      ]

      linarith [
        hτNear N
      ]

    have hSigmaTendsto :
        Tendsto
          σ
          atTop
          (𝓝 T) := by

      exact
        (tendsto_iff_norm_sub_tendsto_zero).2
          (
            squeeze_zero'
              (
                Filter.Eventually.of_forall
                  (fun N =>
                    norm_nonneg (σ N - T))
              )
              (
                Filter.Eventually.of_forall
                  hSigmaNormBound
              )
              hRhoTendsto
          )

    have hTauTendsto :
        Tendsto
          τ
          atTop
          (𝓝 T) := by

      exact
        (tendsto_iff_norm_sub_tendsto_zero).2
          (
            squeeze_zero'
              (
                Filter.Eventually.of_forall
                  (fun N =>
                    norm_nonneg (τ N - T))
              )
              (
                Filter.Eventually.of_forall
                  hTauNormBound
              )
              hRhoTendsto
          )

    have hKappaTendsto :
        Tendsto
          κ
          atTop
          (𝓝 0) := by

      exact
        squeeze_zero'
          (
            Filter.Eventually.of_forall
              (fun N =>
                le_of_lt
                  (hκPos N))
          )
          (
            Filter.Eventually.of_forall
              hκBound
          )
          hRhoTendsto

    exact
      ⟨
        q,
        hqNe,
        σ,
        τ,
        κ,
        hσ,
        hτ,
        hSigmaTendsto,
        hTauTendsto,
        hRhoTendsto,
        hKappaTendsto,
        fun N =>
          ⟨
            hκPos N,
            hκBound N,
            hMass N
          ⟩
      ⟩

end

end Euclidean
end Bridge
end PrimeTensor
