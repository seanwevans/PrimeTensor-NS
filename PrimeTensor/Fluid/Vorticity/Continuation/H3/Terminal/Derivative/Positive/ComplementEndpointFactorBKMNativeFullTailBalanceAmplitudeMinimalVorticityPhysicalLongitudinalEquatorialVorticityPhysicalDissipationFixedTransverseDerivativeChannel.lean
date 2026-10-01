import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityPhysicalDissipationFixedTransverseChannel

/-!
# Freeze one absolute transverse derivative channel in the physical dissipation branch

The preceding checkpoint freezes, along every frequency selection in the
mass-carrying high-radial shrinking cones, one transverse coordinate whose
normalized derivative-symbol square is recurrently larger than `1/4`.

On the same support the radial derivative magnitude is at least the fixed
positive cutoff `ρ`.  Hence normalized square share `> 1/4` implies normalized
norm `> 1/2`, and therefore the corresponding unnormalized coordinate
derivative symbol has norm strictly larger than `ρ / 2`.

Thus the surviving physical H³ dissipation concentration has one fixed
transverse coordinate direction that recurs arbitrarily late with a genuine
positive absolute Fourier derivative scale.  This is still only a conditional
necessary mechanism under hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Remove the normalized symbol on the high-radial support -/

/--
On the radial complement of `|D(ξ)| < ρ`, normalized coordinate-symbol square
above `1/4` forces the corresponding raw derivative-symbol norm above `ρ/2`.
-/
theorem norm_h3FourierDerivativeSymbol_gt_half_cutoff_of_not_mem_radialBelow_of_normalized_sq_gt_quarter
    (j : Fin 3)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    {ξ : H3FourierPoint3}
    (hHigh : ξ ∉ h3TerminalRadialFrequencyBelow ρ)
    (hShare :
      (1 / 4 : ℝ)
        <
      ‖h3TerminalNormalizedDerivativeSymbol j ξ‖ ^ 2) :
    ρ / 2
      <
    ‖h3FourierDerivativeSymbol j ξ‖ := by

  have hRadial :
      ρ ≤ h3FourierGradientMagnitude ξ := by
    unfold h3TerminalRadialFrequencyBelow at hHigh
    simp only [Set.mem_setOf_eq, not_lt] at hHigh
    exact hHigh

  have hGradPos :
      0 < h3FourierGradientMagnitude ξ :=
    lt_of_lt_of_le hρ hRadial

  have hNormNonneg :
      0 ≤ ‖h3TerminalNormalizedDerivativeSymbol j ξ‖ :=
    norm_nonneg _

  have hNormHalf :
      (1 / 2 : ℝ)
        <
      ‖h3TerminalNormalizedDerivativeSymbol j ξ‖ := by
    by_contra hNot
    have hLe :
        ‖h3TerminalNormalizedDerivativeSymbol j ξ‖
          ≤
        (1 / 2 : ℝ) :=
      le_of_not_gt hNot
    nlinarith

  rw [
    norm_h3TerminalNormalizedDerivativeSymbol_eq_div
      j ξ hGradPos
  ] at hNormHalf

  have hDerivativeHalf :
      (1 / 2 : ℝ) * h3FourierGradientMagnitude ξ
        <
      ‖h3FourierDerivativeSymbol j ξ‖ :=
    (lt_div_iff₀ hGradPos).1 hNormHalf

  have hCutoffHalf :
      ρ / 2
        ≤
      (1 / 2 : ℝ) * h3FourierGradientMagnitude ξ := by
    nlinarith

  exact
    lt_of_le_of_lt
      hCutoffHalf
      hDerivativeHalf

/-! ## Physical branch with one absolute transverse derivative channel -/

/--
A single-time physical H³ dissipation concentration branch whose every
mass-carrying high-radial bad-cone frequency selection has one fixed actual
transverse coordinate `j ≠ i` recurring cofinally with

    `ρ / 2 < ‖d_j(ξ_n)‖`.
-/
def H3TerminalPhysicalDissipationSingleTimeFixedTransverseDerivativeChannelBranchAtCutoff
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
          ∧
        Tendsto
            (fun n =>
              h3TerminalNormalizedTransverseDerivativeSymbolSquareMagnitude
                i (ξ n))
            atTop
            (𝓝 1)
          ∧
        ∃ j : Fin 3,
          j ≠ i
            ∧
          ∀ N : ℕ,
            ∃ n : ℕ,
              N ≤ n
                ∧
              ρ / 2
                <
              ‖h3FourierDerivativeSymbol j (ξ n)‖

/--
At positive radial cutoff, the recurrent fixed normalized transverse channel
from the preceding checkpoint yields a recurrent fixed absolute transverse
derivative-symbol channel on exactly the same concentration witnesses.
-/
theorem physicalDissipationSingleTimeFixedTransverseDerivativeChannelBranchAtCutoff_of_fixedTransverseChannelBranch
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    {ε ρ : ℝ}
    (hρ : 0 < ρ)
    (hBranch :
      H3TerminalPhysicalDissipationSingleTimeFixedTransverseChannelBranchAtCutoff
        hH3 hClass i ε ρ) :
    H3TerminalPhysicalDissipationSingleTimeFixedTransverseDerivativeChannelBranchAtCutoff
      hH3 hClass i ε ρ := by

  unfold
    H3TerminalPhysicalDissipationSingleTimeFixedTransverseChannelBranchAtCutoff
      at hBranch

  obtain
    ⟨τ, κ, hτ,
      hκPos,
      hτTendsto,
      hκTendsto,
      hMass,
      hSelection⟩ :=
    hBranch

  refine
    ⟨τ, κ, hτ,
      hκPos,
      hτTendsto,
      hκTendsto,
      hMass,
      ?_⟩

  intro ξ hξ

  have hSelected :=
    hSelection ξ hξ

  refine
    ⟨hSelected.1, hSelected.2.1, ?_⟩

  obtain ⟨k, hk⟩ :=
    hSelected.2.2

  let j : Fin 3 :=
    h3TerminalTransverseCoordinate i k

  have hjNe :
      j ≠ i := by
    dsimp only [j]
    exact
      h3TerminalTransverseCoordinate_ne
        i k

  refine
    ⟨j, hjNe, ?_⟩

  intro N

  obtain ⟨n, hnN, hnShare⟩ :=
    hk N

  refine
    ⟨n, hnN, ?_⟩

  dsimp only [j]

  exact
    norm_h3FourierDerivativeSymbol_gt_half_cutoff_of_not_mem_radialBelow_of_normalized_sq_gt_quarter
      (h3TerminalTransverseCoordinate i k)
      hρ
      (hξ n).2
      hnShare

/-! ## Necessary absolute transverse channel under nonextension -/

/--
Under the retained raw-Fourier `L²` Cauchy hypothesis, hypothetical
nonextension and one surviving physical-vorticity strong H³ endpoint force a
single-time physical H³ dissipation concentration branch with one recurrent
fixed transverse coordinate whose actual Fourier derivative symbol remains
above the positive scale `ρ/2` arbitrarily late along every supported
frequency selection.
-/
theorem exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationFixedTransverseDerivativeChannel_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
        H3TerminalPhysicalDissipationSingleTimeFixedTransverseDerivativeChannelBranchAtCutoff
          hH3 hClass i ε ρ := by

  obtain
    ⟨ρ, hρ, q, hqNe, hqFail, hRawBranch, hFixed⟩ :=
    exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationFixedTransverseChannel_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hCauchy
      hε

  refine
    ⟨ρ, hρ, q, hqNe, hqFail, hRawBranch, ?_⟩

  exact
    physicalDissipationSingleTimeFixedTransverseDerivativeChannelBranchAtCutoff_of_fixedTransverseChannelBranch
      hH3
      hClass
      i
      hρ
      hFixed

end

end Euclidean
end Bridge
end PrimeTensor
