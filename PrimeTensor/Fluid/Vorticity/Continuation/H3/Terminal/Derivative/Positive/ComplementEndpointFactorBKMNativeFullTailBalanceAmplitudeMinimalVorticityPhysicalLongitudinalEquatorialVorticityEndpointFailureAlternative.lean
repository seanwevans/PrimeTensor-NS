import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityInfraredDiagonalSequence

/-!
# Attach the radial obstruction to a failing physical vorticity component

The preceding checkpoints produced the neutral terminal radial alternative:

* some positive radial cutoff supports a high-radial raw-vorticity obstruction;
  or
* one fixed complementary normalized-vorticity component supports a diagonal
  infrared concentration sequence whose time, angular, and radial scales all
  converge to the terminal regime.

In either branch the extracted component `q` is complementary to the surviving
physical endpoint component `i`, so `q ≠ i`.

The already established two-component continuation criterion says that two
distinct physical vorticity components cannot both possess pathwise strong H³
endpoint control under hypothetical nonextension.

This file records that consequence explicitly: whichever complementary
component carries the radial obstruction must itself fail the physical
strong-H³ endpoint property.

No branch is excluded here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalLongitudinalEquatorialVorticityEndpointFailureAlternative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Distinct complementary physical component must fail -/

/--
Under hypothetical nonextension, once physical component `i` has the actual
vorticity strong-H³ endpoint property, every distinct component `q` fails that
same endpoint property.
-/
theorem not_actualVorticityStrongH3EndpointPath_of_distinct_of_noH3PathExtension
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
    {i q : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i)
    (hqi :
      q ≠ i) :
    ¬
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 q := by

  intro hq

  have hiq :
      i = q :=
    actualVorticityStrongH3EndpointPath_eq_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hq

  exact
    hqi
      hiq.symm

/-! ## Final radial obstruction with physical endpoint failure attached -/

/--
Under hypothetical nonextension, if one physical vorticity component `i`
survives with pathwise strong H³ endpoint control, then one complementary
component `q ≠ i` that necessarily fails that endpoint property carries one of
two radial obstruction mechanisms:

1. a positive-cutoff high-radial raw-vorticity branch; or
2. a simultaneous diagonal infrared normalized-vorticity concentration
   sequence with both times approaching `T` and both angular and radial scales
   approaching zero.

This theorem only classifies necessary failure mechanisms under the
nonextension hypothesis; it does not assert that nonextension actually occurs.
-/
theorem exists_failing_complementary_vorticityComponent_highRadialRaw_or_infraredDiagonal_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
          ¬
            H3TerminalActualVorticityStrongH3EndpointPath
              hH3 q
            ∧
          H3TerminalHighRadialRawVorticityBranchAtCutoff
            hH3 i q ε ρ
    )
      ∨
    (
      ∃ q : Fin 3,
        q ≠ i
          ∧
        ¬
          H3TerminalActualVorticityStrongH3EndpointPath
            hH3 q
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

  have hRadial :=
    exists_positive_highRadialRaw_cutoff_or_fixed_complementary_infraredNormalized_diagonalSequence_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hε

  rcases hRadial with hHigh | hInfra

  · left

    obtain
      ⟨
        ρ,
        hρ,
        q,
        hqNe,
        hBranch
      ⟩ :=
      hHigh

    have hqFail :
        ¬
          H3TerminalActualVorticityStrongH3EndpointPath
            hH3 q :=
      not_actualVorticityStrongH3EndpointPath_of_distinct_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hPhysical
        hqNe

    exact
      ⟨
        ρ,
        hρ,
        q,
        hqNe,
        hqFail,
        hBranch
      ⟩

  · right

    obtain
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
        hMass
      ⟩ :=
      hInfra

    have hqFail :
        ¬
          H3TerminalActualVorticityStrongH3EndpointPath
            hH3 q :=
      not_actualVorticityStrongH3EndpointPath_of_distinct_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hPhysical
        hqNe

    exact
      ⟨
        q,
        hqNe,
        hqFail,
        σ,
        τ,
        κ,
        hσ,
        hτ,
        hSigmaTendsto,
        hTauTendsto,
        hRhoTendsto,
        hKappaTendsto,
        hMass
      ⟩

end

end Euclidean
end Bridge
end PrimeTensor
