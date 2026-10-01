import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityPhysicalDissipationAngularVanishingCriterion

/-!
# Equatorial polarization of the physical dissipation concentration branch

The single-time physical dissipation obstruction already carries a positive
amount of full H³ dissipation on shrinking longitudinal bad cones.  This file
records the corresponding degree-zero Fourier geometry explicitly.

If a frequency sequence remains inside those mass-carrying bad cones, then the
normalized longitudinal derivative symbol is bounded by the cone aperture.
Since the aperture tends to zero, the normalized longitudinal symbol tends to
zero along every such frequency selection.

Thus the surviving physical-dissipation concentration is not merely localized
in a family of sets whose names contain “equatorial”: it is asymptotically
polarized toward the coordinate plane orthogonal to the surviving physical
vorticity direction.

This remains a necessary-condition statement under hypothetical nonextension.
It does not assert that a nonextendible solution exists.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Polarized single-time concentration branch -/

/--
A single-time physical dissipation concentration branch together with its
explicit asymptotic equatorial polarization.

The final clause says that every frequency selection staying in the localized
bad-cone/high-radial support has normalized longitudinal derivative symbol
converging to zero.
-/
def H3TerminalPhysicalDissipationSingleTimeEquatorialPolarizationBranchAtCutoff
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (ε ρ : ℝ) : Prop :=
  ∃ τ κ : ℕ → ℝ,
    ∃ hτ : ∀ n, τ n ∈ Set.Ioo a T,
      (∀ n, 0 < κ n)
        ∧
      Tendsto τ atTop (𝓝 T)
        ∧
      Tendsto κ atTop (𝓝 0)
        ∧
      (∀ n,
        ENNReal.ofReal (ρ ^ 2 * (ε ^ 2 / 64))
          <
        16 *
          h3TerminalPhysicalDissipationBadConeHighRadialMass
            hH3 i (κ n) ρ (τ n)
            ⟨lt_trans hClass.terminal_start.1 (hτ n).1,
              (hτ n).2⟩)
        ∧
      ∀ ξ : ℕ → H3FourierPoint3,
        (∀ n,
          ξ n ∈
            h3TerminalLongitudinalAngularBadCone i (κ n)
              \
            h3TerminalRadialFrequencyBelow ρ)
          →
        Tendsto
          (fun n =>
            ‖h3TerminalNormalizedDerivativeSymbol i (ξ n)‖)
          atTop
          (𝓝 0)

/--
Every single-time physical dissipation concentration branch is automatically
asymptotically equatorially polarized.
-/
theorem physicalDissipationSingleTimeEquatorialPolarizationBranchAtCutoff_of_singleTimeBranch
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    {ε ρ : ℝ}
    (hBranch :
      H3TerminalPhysicalDissipationSingleTimeAngularConcentrationBranchAtCutoff
        hH3 hClass i ε ρ) :
    H3TerminalPhysicalDissipationSingleTimeEquatorialPolarizationBranchAtCutoff
      hH3 hClass i ε ρ := by

  unfold
    H3TerminalPhysicalDissipationSingleTimeAngularConcentrationBranchAtCutoff
      at hBranch

  obtain
    ⟨τ, κ, hτ,
      hκPos,
      hτTendsto,
      hκTendsto,
      hMass⟩ :=
    hBranch

  refine
    ⟨τ, κ, hτ,
      hκPos,
      hτTendsto,
      hκTendsto,
      hMass,
      ?_⟩

  intro ξ hξ

  apply
    squeeze_zero'

  · exact
      Filter.Eventually.of_forall
        (fun n =>
          norm_nonneg
            (h3TerminalNormalizedDerivativeSymbol i (ξ n)))

  · exact
      Filter.Eventually.of_forall
        (fun n =>
          le_of_lt
            (norm_normalizedLongitudinalDerivativeSymbol_lt_of_mem_badCone
              ((hξ n).1)))

  · exact hκTendsto

/-! ## Necessary polarized concentration under hypothetical nonextension -/

/--
Under the retained raw-Fourier `L²` Cauchy hypothesis, hypothetical
nonextension and one surviving physical-vorticity strong H³ endpoint force a
single-time physical H³ dissipation concentration branch whose mass-carrying
frequency regions are asymptotically equatorially polarized.
-/
theorem exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationEquatorialPolarization_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ρ : ℝ,
      0 < ρ
        ∧
      ∃ q : Fin 3,
        q ≠ i
          ∧
        ¬ H3TerminalActualVorticityStrongH3EndpointPath hH3 q
          ∧
        H3TerminalHighRadialRawVorticityBranchAtCutoff
          hH3 i q ε ρ
          ∧
        H3TerminalPhysicalDissipationSingleTimeEquatorialPolarizationBranchAtCutoff
          hH3 hClass i ε ρ := by

  obtain
    ⟨ρ, hρ, q, hqNe, hqFail, hRawBranch, hSingle⟩ :=
    exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationAngularConcentration_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hCauchy
      hε

  refine
    ⟨ρ, hρ, q, hqNe, hqFail, hRawBranch, ?_⟩

  exact
    physicalDissipationSingleTimeEquatorialPolarizationBranchAtCutoff_of_singleTimeBranch
      hH3
      hClass
      i
      hSingle

end

end Euclidean
end Bridge
end PrimeTensor
