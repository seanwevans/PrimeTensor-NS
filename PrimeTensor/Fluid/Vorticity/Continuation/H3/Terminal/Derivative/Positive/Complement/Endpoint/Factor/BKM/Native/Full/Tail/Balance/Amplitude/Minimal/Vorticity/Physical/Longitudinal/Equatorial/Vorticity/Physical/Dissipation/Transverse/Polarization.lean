import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Equatorial.Polarization

/-!
# Transverse polarization of the physical dissipation concentration branch

The preceding checkpoint shows that every frequency selection staying in the
mass-carrying shrinking bad cones has normalized longitudinal derivative
symbol tending to zero.

Away from zero radial frequency the three normalized coordinate-symbol squares
sum to one.  Every bad-cone frequency has strictly positive radial derivative
magnitude, so along the same selected frequencies

    transverse normalized-symbol square
      = 1 - longitudinal normalized-symbol square.

Consequently the transverse share tends to one.  Thus the surviving physical
H³ dissipation concentration is asymptotically fully polarized into the two
frequency directions transverse to the distinguished longitudinal axis.

This remains a necessary-condition statement under hypothetical nonextension.
It does not assert existence of a nonextendible solution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Pure shrinking-cone transverse polarization -/

/--
If positive apertures tend to zero and a frequency sequence remains in the
corresponding longitudinal bad cones, then the normalized longitudinal symbol
tends to zero and the normalized transverse-symbol square tends to one.
-/
theorem normalizedDerivativeSymbol_transversePolarization_of_badCone_selection
    (i : Fin 3)
    {κ : ℕ → ℝ}
    (hκPos : ∀ n, 0 < κ n)
    (hκTendsto : Tendsto κ atTop (𝓝 0))
    (ξ : ℕ → H3FourierPoint3)
    (hξ : ∀ n, ξ n ∈ h3TerminalLongitudinalAngularBadCone i (κ n)) :
    Tendsto
        (fun n => ‖h3TerminalNormalizedDerivativeSymbol i (ξ n)‖)
        atTop
        (𝓝 0)
      ∧
    Tendsto
        (fun n =>
          h3TerminalNormalizedTransverseDerivativeSymbolSquareMagnitude
            i (ξ n))
        atTop
        (𝓝 1) := by

  have hLong :
      Tendsto
        (fun n => ‖h3TerminalNormalizedDerivativeSymbol i (ξ n)‖)
        atTop
        (𝓝 0) := by
    apply squeeze_zero'
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
                (hξ n)))
    · exact hκTendsto

  have hLongSq :
      Tendsto
        (fun n =>
          ‖h3TerminalNormalizedDerivativeSymbol i (ξ n)‖ ^ 2)
        atTop
        (𝓝 0) := by
    have hMul := hLong.mul hLong
    simpa only [pow_two, zero_mul] using hMul

  have hOneSub :
      Tendsto
        (fun n =>
          (1 : ℝ)
            -
          ‖h3TerminalNormalizedDerivativeSymbol i (ξ n)‖ ^ 2)
        atTop
        (𝓝 1) := by
    have hConst :
        Tendsto
          (fun _ : ℕ => (1 : ℝ))
          atTop
          (𝓝 1) :=
      tendsto_const_nhds
    have hSub := hConst.sub hLongSq
    simpa only [sub_zero] using hSub

  have hEq :
      (fun n =>
        h3TerminalNormalizedTransverseDerivativeSymbolSquareMagnitude
          i (ξ n))
        =ᶠ[atTop]
      (fun n =>
        (1 : ℝ)
          -
        ‖h3TerminalNormalizedDerivativeSymbol i (ξ n)‖ ^ 2) := by
    filter_upwards with n

    have hGrad :
        0 < h3FourierGradientMagnitude (ξ n) :=
      gradientMagnitude_pos_of_mem_longitudinalAngularBadCone
        (hξ n)

    have hSplit :=
      normalizedTransverseDerivativeSymbolSquareMagnitude_add_longitudinal_eq_one
        i
        (ξ n)
        hGrad

    linarith

  exact
    ⟨
      hLong,
      hOneSub.congr' hEq.symm
    ⟩

/-! ## Physical dissipation branch with transverse polarization -/

/--
A single-time physical H³ dissipation concentration branch whose mass-carrying
frequency regions are asymptotically fully transverse in normalized Fourier
symbol geometry.
-/
def H3TerminalPhysicalDissipationSingleTimeTransversePolarizationBranchAtCutoff
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

/--
Every equatorially polarized single-time physical dissipation branch is in fact
asymptotically fully transverse in normalized derivative-symbol square.
-/
theorem physicalDissipationSingleTimeTransversePolarizationBranchAtCutoff_of_equatorialBranch
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    {ε ρ : ℝ}
    (hBranch :
      H3TerminalPhysicalDissipationSingleTimeEquatorialPolarizationBranchAtCutoff
        hH3 hClass i ε ρ) :
    H3TerminalPhysicalDissipationSingleTimeTransversePolarizationBranchAtCutoff
      hH3 hClass i ε ρ := by

  unfold
    H3TerminalPhysicalDissipationSingleTimeEquatorialPolarizationBranchAtCutoff
      at hBranch

  obtain
    ⟨τ, κ, hτ,
      hκPos,
      hτTendsto,
      hκTendsto,
      hMass,
      hLongitudinal⟩ :=
    hBranch

  refine
    ⟨τ, κ, hτ,
      hκPos,
      hτTendsto,
      hκTendsto,
      hMass,
      ?_⟩

  intro ξ hξ

  have hPure :=
    normalizedDerivativeSymbol_transversePolarization_of_badCone_selection
      i
      hκPos
      hκTendsto
      ξ
      (fun n => (hξ n).1)

  exact
    ⟨
      hLongitudinal ξ hξ,
      hPure.2
    ⟩

/-! ## Necessary fully transverse concentration under nonextension -/

/--
Under the retained raw-Fourier `L²` Cauchy hypothesis, hypothetical
nonextension and one surviving physical-vorticity strong H³ endpoint force a
single-time physical H³ dissipation concentration branch that is asymptotically
fully transverse in normalized Fourier symbol geometry.
-/
theorem exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationTransversePolarization_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
        H3TerminalPhysicalDissipationSingleTimeTransversePolarizationBranchAtCutoff
          hH3 hClass i ε ρ := by

  obtain
    ⟨ρ, hρ, q, hqNe, hqFail, hRawBranch, hEquatorial⟩ :=
    exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationEquatorialPolarization_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hCauchy
      hε

  refine
    ⟨ρ, hρ, q, hqNe, hqFail, hRawBranch, ?_⟩

  exact
    physicalDissipationSingleTimeTransversePolarizationBranchAtCutoff_of_equatorialBranch
      hH3
      hClass
      i
      hEquatorial

end

end Euclidean
end Bridge
end PrimeTensor
