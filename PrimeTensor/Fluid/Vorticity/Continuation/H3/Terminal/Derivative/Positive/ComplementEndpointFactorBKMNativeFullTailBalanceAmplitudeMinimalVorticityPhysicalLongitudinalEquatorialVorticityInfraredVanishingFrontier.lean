import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityEndpointFailureAlternative

/-!
# Infrared vanishing frontier for the terminal vorticity obstruction

The preceding radial classification is now fully explicit under hypothetical
nonextension with one surviving physical vorticity endpoint component `i`:

* either a complementary component carries a positive-cutoff high-radial
  raw-vorticity obstruction; or
* a complementary component `q ≠ i`, which itself fails the physical
  strong-H³ endpoint property, carries a diagonal normalized-vorticity
  concentration sequence with both time variables approaching `T` and both
  radial and angular scales approaching zero.

Uniform zeroth-order L² control alone does not rule out the second mechanism:
an L²-bounded family can concentrate on shrinking Fourier sets.

This file isolates the exact additional compactness statement needed to close
the infrared branch.  The `infrared vanishing` property says that, for one
fixed component, sufficiently terminal differences have arbitrarily small
normalized-vorticity mass in a sufficiently small radial ball, uniformly in
the positive angular aperture.

If every complementary component has this property, the diagonal infrared
branch contradicts its fixed positive mass lower bound.  Hence only the
positive-cutoff high-radial raw-vorticity branch remains.

No proof of the infrared-vanishing property itself is asserted here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalLongitudinalEquatorialVorticityInfraredVanishingFrontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Infrared vanishing modulus -/

/--
Terminal normalized-vorticity infrared vanishing for one complementary
component.

For every positive mass threshold `δ`, there are a positive radial cutoff `ρ`
and a positive terminal time modulus `η` such that every pair of strict times
within `η` of `T` has low-radial normalized-vorticity square defect below `δ`,
uniformly in every positive angular aperture `κ`.
-/
def H3TerminalNormalizedVorticityInfraredVanishingAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (i q : Fin 3) : Prop :=
  ∀ δ : ℝ,
    0 < δ
      →
    ∃ ρ : ℝ,
      0 < ρ
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
                h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect
                    i q κ ρ
                    (h3TerminalVelocitySpectralStateAt
                      hH3 s hs)
                    (h3TerminalVelocitySpectralStateAt
                      hH3 t ht)
                  <
                δ

/--
A diagonal infrared concentration sequence with fixed positive mass is
incompatible with infrared vanishing for the same component.
-/
theorem false_of_infraredDiagonal_of_normalizedVorticityInfraredVanishingAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (i q : Fin 3)
    {ε : ℝ}
    (hε : 0 < ε)
    (hVanishing :
      H3TerminalNormalizedVorticityInfraredVanishingAtEndpoint
        hH3 i q)
    (σ τ κ : ℕ → ℝ)
    (hσ :
      ∀ N : ℕ,
        σ N ∈ Set.Ioo (0 : ℝ) T)
    (hτ :
      ∀ N : ℕ,
        τ N ∈ Set.Ioo (0 : ℝ) T)
    (hSigmaTendsto :
      Tendsto
        σ
        atTop
        (𝓝 T))
    (hTauTendsto :
      Tendsto
        τ
        atTop
        (𝓝 T))
    (hRhoTendsto :
      Tendsto
        (
          fun N : ℕ =>
            (1 : ℝ) / ((N : ℝ) + 1)
        )
        atTop
        (𝓝 0))
    (hKappaTendsto :
      Tendsto
        κ
        atTop
        (𝓝 0))
    (hMass :
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
            (hτ N))) :
    False := by

  have hThresholdPos :
      0 < ε ^ 2 / 64 := by
    positivity

  obtain
    ⟨
      ρ,
      hρ,
      η,
      hη,
      hSmall
    ⟩ :=
    hVanishing
      (ε ^ 2 / 64)
      hThresholdPos

  have hRhoSmall :
      ∀ᶠ N : ℕ in atTop,
        (1 : ℝ) / ((N : ℝ) + 1)
          <
        ρ := by

    exact
      (tendsto_order.1 hRhoTendsto).2
        ρ
        hρ

  have hSigmaNear :
      ∀ᶠ N : ℕ in atTop,
        dist (σ N) T < η := by

    have hBall :
        Metric.ball T η ∈ 𝓝 T :=
      Metric.ball_mem_nhds
        T
        hη

    have hEventually :=
      hSigmaTendsto.eventually
        hBall

    filter_upwards [hEventually] with N hN

    simpa only [
      Metric.mem_ball,
      dist_comm
    ] using
      hN

  have hTauNear :
      ∀ᶠ N : ℕ in atTop,
        dist (τ N) T < η := by

    have hBall :
        Metric.ball T η ∈ 𝓝 T :=
      Metric.ball_mem_nhds
        T
        hη

    have hEventually :=
      hTauTendsto.eventually
        hBall

    filter_upwards [hEventually] with N hN

    simpa only [
      Metric.mem_ball,
      dist_comm
    ] using
      hN

  obtain
    ⟨
      N,
      hNRho,
      hNSigma,
      hNTau
    ⟩ :=
    (
      hRhoSmall.and
        (
          hSigmaNear.and
            hTauNear
        )
    ).exists

  have hAtFixedRadius :
      h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect
          i q
          (κ N)
          ρ
          (h3TerminalVelocitySpectralStateAt
            hH3
            (σ N)
            (hσ N))
          (h3TerminalVelocitySpectralStateAt
            hH3
            (τ N)
            (hτ N))
        <
      ε ^ 2 / 64 := by

    exact
      hSmall
        (σ N)
        (τ N)
        (hσ N)
        (hτ N)
        hNSigma
        hNTau
        (κ N)
        (hMass N).1

  have hRadialMono :
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
        ≤
      h3TerminalNormalizedVorticityComponentBadConeLowRadialSquareDefect
          i q
          (κ N)
          ρ
          (h3TerminalVelocitySpectralStateAt
            hH3
            (σ N)
            (hσ N))
          (h3TerminalVelocitySpectralStateAt
            hH3
            (τ N)
            (hτ N)) := by

    exact
      normalizedVorticityComponentBadConeLowRadialSquareDefect_mono
        i q
        (κ N)
        (le_of_lt hNRho)
        (h3TerminalVelocitySpectralStateAt
          hH3
          (σ N)
          (hσ N))
        (h3TerminalVelocitySpectralStateAt
          hH3
          (τ N)
          (hτ N))

  have hContradiction :
      ε ^ 2 / 64
        <
      ε ^ 2 / 64 := by

    exact
      ((hMass N).2.2).trans_le hRadialMono
        |>.trans hAtFixedRadius

  exact
    (lt_irrefl _)
      hContradiction

/-! ## Conditional closure of the infrared branch -/

/--
If every component distinct from the surviving physical endpoint component
has terminal normalized-vorticity infrared vanishing, then hypothetical
nonextension cannot use the diagonal infrared mechanism.  Therefore one
failing complementary component must carry a positive-cutoff high-radial
raw-vorticity obstruction.
-/
theorem exists_failing_complementary_vorticityComponent_highRadialRaw_of_normalizedVorticityInfraredVanishing_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    (hInfraredVanishing :
      ∀ q : Fin 3,
        q ≠ i
          →
        H3TerminalNormalizedVorticityInfraredVanishingAtEndpoint
          hH3 i q)
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
          hH3 i q ε ρ := by

  have hAlternative :=
    exists_failing_complementary_vorticityComponent_highRadialRaw_or_infraredDiagonal_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hε

  rcases hAlternative with hHigh | hInfra

  · exact
      hHigh

  · obtain
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
      ⟩ :=
      hInfra

    exact
      False.elim
        (
          false_of_infraredDiagonal_of_normalizedVorticityInfraredVanishingAtEndpoint
            hH3
            i q
            hε
            (hInfraredVanishing q hqNe)
            σ τ κ
            hσ
            hτ
            hSigmaTendsto
            hTauTendsto
            hRhoTendsto
            hKappaTendsto
            hMass
        )

end

end Euclidean
end Bridge
end PrimeTensor
