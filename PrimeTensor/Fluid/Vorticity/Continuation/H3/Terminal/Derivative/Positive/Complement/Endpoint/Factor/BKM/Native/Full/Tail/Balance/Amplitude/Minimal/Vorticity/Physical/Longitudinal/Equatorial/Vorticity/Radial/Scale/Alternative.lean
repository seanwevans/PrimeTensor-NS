import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Raw.Vorticity.High.Radial.Mass

/-!
# Global radial-scale alternative for the equatorial vorticity obstruction

For each fixed positive radial cutoff `ρ`, the preceding checkpoint gives a
terminal shrinking-cone alternative for one complementary vorticity component:

* persistent normalized-vorticity mass below `ρ`; or
* persistent extended raw-vorticity mass on `|D| ≥ ρ`.

This file packages those two branches as reusable predicates and moves the
quantifier over `ρ` outside the fixed-cutoff statement.

The resulting neutral classification is:

* either some positive radial cutoff supports the high-radial raw-vorticity
  branch; or
* every positive radial cutoff supports an infrared normalized-vorticity
  branch.

The second alternative is then specialized to the explicit vanishing cutoffs

    ρ_N = 1 / (N + 1) → 0.

The complementary component and terminal subsequence are still allowed to
depend on the cutoff.  No diagonal synchronization across radial scales is
asserted here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalLongitudinalEquatorialVorticityRadialScaleAlternative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Reusable fixed-cutoff branch predicates -/

/--
At radial cutoff `ρ`, component `q` has a terminal shrinking-equatorial
subsequence whose normalized-vorticity square mass below `ρ` stays above
`ε²/64`.
-/
def H3TerminalInfraredNormalizedVorticityBranchAtCutoff
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (i q : Fin 3)
    (ε ρ : ℝ) :
    Prop :=
  ∃ s t : ℕ → ℝ,
    ∃ hs :
      ∀ n : ℕ,
        s n ∈ Set.Ioo (0 : ℝ) T,
      ∃ ht :
        ∀ n : ℕ,
          t n ∈ Set.Ioo (0 : ℝ) T,
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

/--
At radial cutoff `ρ`, component `q` has a terminal shrinking-equatorial
subsequence whose extended raw-vorticity square mass on `|D| ≥ ρ` stays above
the quantitative threshold `ρ² ε² / 64`.
-/
def H3TerminalHighRadialRawVorticityBranchAtCutoff
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (i q : Fin 3)
    (ε ρ : ℝ) :
    Prop :=
  ∃ s t : ℕ → ℝ,
    ∃ hs :
      ∀ n : ℕ,
        s n ∈ Set.Ioo (0 : ℝ) T,
      ∃ ht :
        ∀ n : ℕ,
          t n ∈ Set.Ioo (0 : ℝ) T,
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

/-! ## Fixed-cutoff branch packaging -/

/--
At every fixed positive radial cutoff, hypothetical nonextension produces one
complementary vorticity component in either the infrared normalized branch or
the high-radial raw branch.
-/
theorem exists_complementary_vorticityComponent_infraredNormalized_or_highRadialRaw_branchAtCutoff_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    ∃ q : Fin 3,
      q ≠ i
        ∧
      (
        H3TerminalInfraredNormalizedVorticityBranchAtCutoff
          hH3 i q ε ρ
          ∨
        H3TerminalHighRadialRawVorticityBranchAtCutoff
          hH3 i q ε ρ
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
    exists_fixed_complementary_vorticityComponent_shrinkingEquatorialCone_infraredNormalized_or_highRadialRaw_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hε
      hρ

  refine
    ⟨
      q,
      hqNe,
      ?_
    ⟩

  rcases hBranch with hLow | hHigh

  · left

    unfold
      H3TerminalInfraredNormalizedVorticityBranchAtCutoff

    exact
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
        hLow
      ⟩

  · right

    unfold
      H3TerminalHighRadialRawVorticityBranchAtCutoff

    exact
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
        hHigh
      ⟩

/-! ## Global radial-scale classification -/

/--
Global radial-scale alternative.

Either there exists some positive cutoff carrying a high-radial raw-vorticity
terminal obstruction, or every positive cutoff carries an infrared
normalized-vorticity terminal obstruction.
-/
theorem exists_positive_highRadialRaw_cutoff_or_infraredNormalized_every_positive_cutoff_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
      ∀ ρ : ℝ,
        0 < ρ
          →
        ∃ q : Fin 3,
          q ≠ i
            ∧
          H3TerminalInfraredNormalizedVorticityBranchAtCutoff
            hH3 i q ε ρ
    ) := by

  classical

  by_cases hHighGlobal :
      ∃ ρ : ℝ,
        0 < ρ
          ∧
        ∃ q : Fin 3,
          q ≠ i
            ∧
          H3TerminalHighRadialRawVorticityBranchAtCutoff
            hH3 i q ε ρ

  · exact
      Or.inl
        hHighGlobal

  · right

    intro ρ hρ

    obtain
      ⟨
        q,
        hqNe,
        hBranch
      ⟩ :=
      exists_complementary_vorticityComponent_infraredNormalized_or_highRadialRaw_branchAtCutoff_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hPhysical
        hε
        hρ

    rcases hBranch with hLow | hHigh

    · exact
        ⟨
          q,
          hqNe,
          hLow
        ⟩

    · exfalso

      apply
        hHighGlobal

      exact
        ⟨
          ρ,
          hρ,
          q,
          hqNe,
          hHigh
        ⟩

/-! ## Explicit vanishing radial cutoffs -/

/--
The global alternative specialized to the canonical vanishing radial scales

    `ρ_N = 1 / (N + 1)`.

If no positive high-radial raw cutoff exists, then for every `N` there is a
complementary component and terminal shrinking-cone subsequence carrying the
infrared normalized obstruction below `ρ_N`, while `ρ_N → 0`.
-/
theorem exists_positive_highRadialRaw_cutoff_or_infraredNormalized_on_vanishing_radial_scales_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
      Tendsto
        (fun N : ℕ =>
          (1 : ℝ) / ((N : ℝ) + 1))
        atTop
        (𝓝 0)
        ∧
      ∀ N : ℕ,
        ∃ q : Fin 3,
          q ≠ i
            ∧
          H3TerminalInfraredNormalizedVorticityBranchAtCutoff
            hH3 i q ε
            ((1 : ℝ) / ((N : ℝ) + 1))
    ) := by

  have hGlobal :=
    exists_positive_highRadialRaw_cutoff_or_infraredNormalized_every_positive_cutoff_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hε

  rcases hGlobal with hHigh | hEveryLow

  · exact
      Or.inl
        hHigh

  · right

    constructor

    · simpa only [
        Nat.cast_add,
        Nat.cast_one
      ] using
        tendsto_one_div_add_atTop_nhds_zero_nat

    · intro N

      have hρ :
          0
            <
          (1 : ℝ) / ((N : ℝ) + 1) := by
        positivity

      exact
        hEveryLow
          ((1 : ℝ) / ((N : ℝ) + 1))
          hρ

end

end Euclidean
end Bridge
end PrimeTensor
