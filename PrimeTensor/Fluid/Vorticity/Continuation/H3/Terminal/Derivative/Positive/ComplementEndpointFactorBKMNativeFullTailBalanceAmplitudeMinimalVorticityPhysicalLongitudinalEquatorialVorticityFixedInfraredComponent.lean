import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityRadialScaleAlternative

/-!
# Freeze the infrared vorticity component across vanishing radial scales

The preceding checkpoint showed that hypothetical nonextension forces either

* a high-radial raw-vorticity obstruction at some positive cutoff; or
* an infrared normalized-vorticity obstruction at every positive cutoff.

On the canonical cutoffs

    ρ_N = 1 / (N + 1),

the complementary vorticity component in the infrared alternative was still
allowed to depend on `N`.

This file removes that finite component drift.

The key extra fact is radial monotonicity: normalized-vorticity mass below a
smaller cutoff is also mass below every larger cutoff.  Since there are only
three vorticity coordinates, one complementary component occurs at arbitrarily
large cutoff indices.  Its recurrent arbitrarily-small-cutoff witnesses then
propagate by monotonicity to every canonical cutoff.

The terminal time sequences and angular subsequences inside the branch
predicate may still depend on the radial cutoff.  No diagonal synchronization
of those witnesses is asserted here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalLongitudinalEquatorialVorticityFixedInfraredComponent
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Radial monotonicity -/

/--
The low-radial normalized-vorticity bad-cone square defect is monotone in the
radial cutoff.
-/
theorem normalizedVorticityComponentBadConeLowRadialSquareDefect_mono
    (i q : Fin 3)
    (κ : ℝ)
    {ρ₁ ρ₂ : ℝ}
    (hρ :
      ρ₁ ≤ ρ₂)
    (G H : H3SpectralFinVectorState) :
    h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect
        i q κ ρ₁ G H
      ≤
    h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect
        i q κ ρ₂ G H := by

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

  have hSubset :
      h3TerminalLongitudinalAngularBadCone i κ
          ∩
        h3TerminalRadialFrequencyBelow ρ₁
        ⊆
      h3TerminalLongitudinalAngularBadCone i κ
          ∩
        h3TerminalRadialFrequencyBelow ρ₂ := by

    intro ξ hξ

    refine
      ⟨
        hξ.1,
        ?_
      ⟩

    have hBelow :
        h3FourierGradientMagnitude ξ
          <
        ρ₁ := by

      simpa only [
        h3TerminalRadialFrequencyBelow,
        Set.mem_ofPred_eq
      ] using
        hξ.2

    have hBelow' :
        h3FourierGradientMagnitude ξ
          <
        ρ₂ :=
      lt_of_lt_of_le
        hBelow
        hρ

    simpa only [
      h3TerminalRadialFrequencyBelow,
      Set.mem_ofPred_eq
    ] using
      hBelow'

  unfold
    h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect

  change
    (∫ ξ in
        h3TerminalLongitudinalAngularBadCone i κ
            ∩
          h3TerminalRadialFrequencyBelow ρ₁,
        f ξ)
      ≤
    ∫ ξ in
        h3TerminalLongitudinalAngularBadCone i κ
            ∩
          h3TerminalRadialFrequencyBelow ρ₂,
        f ξ

  apply
    setIntegral_mono_set
      hInt.integrableOn

  · filter_upwards with ξ

    exact
      sq_nonneg _

  · filter_upwards with ξ

    intro hξ

    exact
      hSubset hξ

/--
An infrared branch at a smaller radial cutoff remains an infrared branch at
every larger radial cutoff, using the same terminal witnesses.
-/
theorem H3TerminalInfraredNormalizedVorticityBranchAtCutoff_mono
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (i q : Fin 3)
    (ε : ℝ)
    {ρ₁ ρ₂ : ℝ}
    (hρ :
      ρ₁ ≤ ρ₂)
    (hBranch :
      H3TerminalInfraredNormalizedVorticityBranchAtCutoff
        hH3 i q ε ρ₁) :
    H3TerminalInfraredNormalizedVorticityBranchAtCutoff
      hH3 i q ε ρ₂ := by

  unfold
    H3TerminalInfraredNormalizedVorticityBranchAtCutoff
    at hBranch ⊢

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

  refine
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
      ?_
    ⟩

  intro n

  exact
    (hMass n).trans_le
      (
        normalizedVorticityComponentBadConeLowRadialSquareDefect_mono
          i q
          ((1 : ℝ) / (((p n : ℕ) : ℝ) + 2))
          hρ
          (h3TerminalVelocitySpectralStateAt
            hH3
            (s (p n))
            (hs (p n)))
          (h3TerminalVelocitySpectralStateAt
            hH3
            (t (p n))
            (ht (p n)))
      )

/-! ## Freeze one complementary component across all canonical cutoffs -/

/--
Either some positive radial cutoff already carries the high-radial raw
obstruction, or one fixed complementary vorticity component carries an
infrared normalized-vorticity branch at every canonical cutoff

    `1 / (N + 1)`.

The branch witnesses themselves may still depend on `N`.
-/
theorem exists_positive_highRadialRaw_cutoff_or_fixed_complementary_infraredNormalized_on_all_vanishing_radial_scales_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
        Tendsto
          (fun N : ℕ =>
            (1 : ℝ) / ((N : ℝ) + 1))
          atTop
          (𝓝 0)
          ∧
        ∀ N : ℕ,
          H3TerminalInfraredNormalizedVorticityBranchAtCutoff
            hH3 i q ε
            ((1 : ℝ) / ((N : ℝ) + 1))
    ) := by

  classical

  have hScale :=
    exists_positive_highRadialRaw_cutoff_or_infraredNormalized_on_vanishing_radial_scales_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hε

  rcases hScale with hHigh | hLow

  · exact
      Or.inl
        hHigh

  · right

    obtain
      ⟨
        hRhoTendsto,
        hEach
      ⟩ :=
      hLow

    let qAt : ℕ → Fin 3 :=
      fun N =>
        Classical.choose
          (hEach N)

    have hqAtSpec :
        ∀ N : ℕ,
          qAt N ≠ i
            ∧
          H3TerminalInfraredNormalizedVorticityBranchAtCutoff
            hH3 i (qAt N) ε
            ((1 : ℝ) / ((N : ℝ) + 1)) := by

      intro N

      exact
        Classical.choose_spec
          (hEach N)

    obtain
      ⟨
        qStar,
        hInfinite
      ⟩ :=
      Finite.exists_infinite_fiber
        qAt

    rw [Set.infinite_coe_iff] at hInfinite

    have hqStarNe :
        qStar ≠ i := by

      obtain
        ⟨
          N,
          hNFiber,
          hN
        ⟩ :=
        Set.Infinite.exists_gt
          hInfinite
          0

      change
        qAt N = qStar
      at hNFiber

      have hNe :=
        (hqAtSpec N).1

      rw [hNFiber] at hNe

      exact
        hNe

    have hEvery :
        ∀ M : ℕ,
          H3TerminalInfraredNormalizedVorticityBranchAtCutoff
            hH3 i qStar ε
            ((1 : ℝ) / ((M : ℝ) + 1)) := by

      intro M

      obtain
        ⟨
          N,
          hNFiber,
          hMN
        ⟩ :=
        Set.Infinite.exists_gt
          hInfinite
          M

      change
        qAt N = qStar
      at hNFiber

      have hBranchN :=
        (hqAtSpec N).2

      rw [hNFiber] at hBranchN

      have hDenM :
          0 < (M : ℝ) + 1 := by
        positivity

      have hDenLe :
          (M : ℝ) + 1
            ≤
          (N : ℝ) + 1 := by

        have hCast :
            (M : ℝ)
              ≤
            (N : ℝ) := by
          exact_mod_cast
            (Nat.le_of_lt hMN)

        linarith

      have hRhoLe :
          (1 : ℝ) / ((N : ℝ) + 1)
            ≤
          (1 : ℝ) / ((M : ℝ) + 1) := by

        exact
          one_div_le_one_div_of_le
            hDenM
            hDenLe

      exact
        H3TerminalInfraredNormalizedVorticityBranchAtCutoff_mono
          hH3
          i qStar ε
          hRhoLe
          hBranchN

    exact
      ⟨
        qStar,
        hqStarNe,
        hRhoTendsto,
        hEvery
      ⟩

end

end Euclidean
end Bridge
end PrimeTensor
