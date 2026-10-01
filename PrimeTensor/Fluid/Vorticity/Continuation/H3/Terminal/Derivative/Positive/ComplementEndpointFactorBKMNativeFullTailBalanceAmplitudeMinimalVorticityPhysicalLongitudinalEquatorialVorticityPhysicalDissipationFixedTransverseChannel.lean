import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityPhysicalDissipationTransversePolarization

/-!
# Freeze one transverse frequency channel in the physical dissipation branch

The preceding checkpoint proves that every frequency selection remaining in the
shrinking equatorial bad cones has normalized transverse derivative-symbol
square tending to one.

There are only two transverse coordinate directions.  If neither coordinate
carried normalized-symbol square above `1/4` cofinally often, then both would
be eventually bounded by `1/4`, forcing their sum to be at most `1/2`.  This
contradicts convergence of the transverse square to one.

Thus every such frequency selection has one fixed transverse coordinate that
recurs arbitrarily late with normalized derivative-symbol square strictly above
`1/4`.  This removes finite directional drift inside the asymptotically
transverse geometry.

This is still a conditional necessary mechanism under hypothetical
nonextension; it does not assert existence of a singular solution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## The two transverse coordinate channels -/

/-- Enumerate the two coordinate directions transverse to `i`. -/
def h3TerminalTransverseCoordinate
    (i : Fin 3)
    (k : Fin 2) : Fin 3 :=
  if i = 0 then
    if k = 0 then 1 else 2
  else if i = 1 then
    if k = 0 then 0 else 2
  else
    if k = 0 then 0 else 1

/-- Every enumerated transverse coordinate differs from the longitudinal one. -/
theorem h3TerminalTransverseCoordinate_ne
    (i : Fin 3)
    (k : Fin 2) :
    h3TerminalTransverseCoordinate i k ≠ i := by
  fin_cases i <;>
    fin_cases k <;>
    simp [h3TerminalTransverseCoordinate]

/-- The transverse normalized-symbol square is exactly the sum of the two
named transverse coordinate squares. -/
theorem normalizedTransverseDerivativeSymbolSquareMagnitude_eq_coordinate_zero_add_one
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3TerminalNormalizedTransverseDerivativeSymbolSquareMagnitude i ξ
      =
    ‖h3TerminalNormalizedDerivativeSymbol
        (h3TerminalTransverseCoordinate i (0 : Fin 2)) ξ‖ ^ 2
      +
    ‖h3TerminalNormalizedDerivativeSymbol
        (h3TerminalTransverseCoordinate i (1 : Fin 2)) ξ‖ ^ 2 := by
  fin_cases i <;>
    simp [
      h3TerminalNormalizedTransverseDerivativeSymbolSquareMagnitude,
      h3TerminalTransverseCoordinate
    ]

/-! ## Freeze a recurrent transverse channel -/

/--
If the transverse normalized-symbol square tends to one, then one fixed
transverse coordinate has square share above `1/4` arbitrarily far out.
-/
theorem exists_cofinally_recurrent_transverseCoordinate_of_transversePolarization
    (i : Fin 3)
    (ξ : ℕ → H3FourierPoint3)
    (hTransverse :
      Tendsto
        (fun n =>
          h3TerminalNormalizedTransverseDerivativeSymbolSquareMagnitude
            i (ξ n))
        atTop
        (𝓝 1)) :
    ∃ k : Fin 2,
      ∀ N : ℕ,
        ∃ n : ℕ,
          N ≤ n
            ∧
          (1 / 4 : ℝ)
            <
          ‖h3TerminalNormalizedDerivativeSymbol
              (h3TerminalTransverseCoordinate i k)
              (ξ n)‖ ^ 2 := by
  by_contra hNo
  push_neg at hNo

  obtain ⟨N0, h0⟩ := hNo (0 : Fin 2)
  obtain ⟨N1, h1⟩ := hNo (1 : Fin 2)

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        (1 / 2 : ℝ)
          <
        h3TerminalNormalizedTransverseDerivativeSymbolSquareMagnitude
          i (ξ n) :=
    (tendsto_order.1 hTransverse).1
      (1 / 2 : ℝ)
      (by norm_num)

  obtain ⟨n, hn0, hn1, hnLarge⟩ :=
    ((eventually_ge_atTop N0).and
      ((eventually_ge_atTop N1).and hLarge)).exists

  have h0Le := h0 n hn0
  have h1Le := h1 n hn1

  rw [
    normalizedTransverseDerivativeSymbolSquareMagnitude_eq_coordinate_zero_add_one
  ] at hnLarge

  linarith

/-! ## Physical branch with a frozen recurrent transverse channel -/

/--
A single-time physical dissipation concentration branch whose every
mass-carrying bad-cone frequency selection has one fixed transverse coordinate
recurring cofinally with normalized-symbol square above `1/4`.
-/
def H3TerminalPhysicalDissipationSingleTimeFixedTransverseChannelBranchAtCutoff
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
        ∃ k : Fin 2,
          ∀ N : ℕ,
            ∃ n : ℕ,
              N ≤ n
                ∧
              (1 / 4 : ℝ)
                <
              ‖h3TerminalNormalizedDerivativeSymbol
                  (h3TerminalTransverseCoordinate i k)
                  (ξ n)‖ ^ 2

/-- Every fully transverse physical dissipation branch has a fixed recurrent
transverse coordinate along each admissible frequency selection. -/
theorem physicalDissipationSingleTimeFixedTransverseChannelBranchAtCutoff_of_transverseBranch
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    {ε ρ : ℝ}
    (hBranch :
      H3TerminalPhysicalDissipationSingleTimeTransversePolarizationBranchAtCutoff
        hH3 hClass i ε ρ) :
    H3TerminalPhysicalDissipationSingleTimeFixedTransverseChannelBranchAtCutoff
      hH3 hClass i ε ρ := by
  unfold
    H3TerminalPhysicalDissipationSingleTimeTransversePolarizationBranchAtCutoff
      at hBranch

  obtain
    ⟨τ, κ, hτ,
      hκPos,
      hτTendsto,
      hκTendsto,
      hMass,
      hPolarization⟩ :=
    hBranch

  refine
    ⟨τ, κ, hτ,
      hκPos,
      hτTendsto,
      hκTendsto,
      hMass,
      ?_⟩

  intro ξ hξ

  have hPol := hPolarization ξ hξ

  refine
    ⟨hPol.1, hPol.2, ?_⟩

  exact
    exists_cofinally_recurrent_transverseCoordinate_of_transversePolarization
      i
      ξ
      hPol.2

/-! ## Necessary fixed transverse channel under nonextension -/

/--
Under the retained raw-Fourier `L²` Cauchy hypothesis, hypothetical
nonextension and one surviving physical-vorticity strong H³ endpoint force a
single-time physical H³ dissipation concentration branch with a recurrent
fixed transverse normalized-symbol channel along every admissible frequency
selection.
-/
theorem exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationFixedTransverseChannel_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
        H3TerminalPhysicalDissipationSingleTimeFixedTransverseChannelBranchAtCutoff
          hH3 hClass i ε ρ := by
  obtain
    ⟨ρ, hρ, q, hqNe, hqFail, hRawBranch, hTransverse⟩ :=
    exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationTransversePolarization_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hCauchy
      hε

  refine
    ⟨ρ, hρ, q, hqNe, hqFail, hRawBranch, ?_⟩

  exact
    physicalDissipationSingleTimeFixedTransverseChannelBranchAtCutoff_of_transverseBranch
      hH3
      hClass
      i
      hTransverse

end

end Euclidean
end Bridge
end PrimeTensor
