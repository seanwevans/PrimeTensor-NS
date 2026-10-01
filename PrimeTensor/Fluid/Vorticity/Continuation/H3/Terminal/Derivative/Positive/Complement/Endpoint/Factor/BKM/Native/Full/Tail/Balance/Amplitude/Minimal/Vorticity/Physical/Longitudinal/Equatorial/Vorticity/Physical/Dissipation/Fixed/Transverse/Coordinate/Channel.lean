import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Fixed.Transverse.Derivative.Channel

/-!
# Freeze one literal transverse Fourier-coordinate channel

The preceding checkpoint removes the normalized multiplier and freezes one
transverse derivative-symbol channel with recurrent absolute lower bound

    rho / 2 < ||d_j(xi_n)||.

Since the coordinate derivative symbol is exactly

    d_j(xi) = 2 pi i xi_j,

this file removes the remaining symbol wrapper.  The same fixed transverse
coordinate satisfies

    rho / (4 pi) < |xi_{n,j}|

arbitrarily far out along every supported frequency selection.

Thus the surviving physical H3 dissipation concentration is localized not
only to shrinking equatorial cones and a positive radial region, but also has
one recurrent literal transverse Fourier coordinate bounded away from zero.
This remains a conditional necessary mechanism under hypothetical
nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Derivative symbol to literal Fourier coordinate -/

/-- The norm of one coordinate derivative symbol is exactly `2*pi` times the
absolute value of the corresponding Fourier coordinate. -/
theorem norm_h3FourierDerivativeSymbol_eq_two_pi_mul_abs_coordinate
    (j : Fin 3)
    (xi : H3FourierPoint3) :
    ‖h3FourierDerivativeSymbol j xi‖
      =
    (2 * Real.pi) * |xi (h3AxisOfFin3 j)| := by
  unfold h3FourierDerivativeSymbol
  simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- A raw derivative-symbol lower bound at scale `rho/2` is exactly a literal
Fourier-coordinate lower bound at scale `rho/(4*pi)`. -/
theorem abs_fourierCoordinate_gt_cutoff_div_four_pi_of_derivativeSymbol_gt_half_cutoff
    (j : Fin 3)
    {rho : ℝ}
    {xi : H3FourierPoint3}
    (hDerivative :
      rho / 2
        <
      ‖h3FourierDerivativeSymbol j xi‖) :
    rho / (4 * Real.pi)
      <
    |xi (h3AxisOfFin3 j)| := by

  rw [
    norm_h3FourierDerivativeSymbol_eq_two_pi_mul_abs_coordinate
  ] at hDerivative

  have hTwoPiPos :
      0 < 2 * Real.pi := by
    positivity

  have hDerivative' :
      rho / 2
        <
      |xi (h3AxisOfFin3 j)| * (2 * Real.pi) := by
    simpa only [mul_comm] using hDerivative

  have hDiv :
      (rho / 2) / (2 * Real.pi)
        <
      |xi (h3AxisOfFin3 j)| :=
    (div_lt_iff₀ hTwoPiPos).2
      hDerivative'

  have hScale :
      (rho / 2) / (2 * Real.pi)
        =
      rho / (4 * Real.pi) := by
    field_simp [ne_of_gt Real.pi_pos]
    <;> ring

  rw [hScale] at hDiv
  exact hDiv

/-! ## Physical branch with one literal transverse coordinate -/

/--
A single-time physical H3 dissipation concentration branch whose every
mass-carrying high-radial bad-cone frequency selection has one fixed actual
transverse coordinate `j != i` recurring cofinally with

    `rho / (4*pi) < |xi_{n,j}|`.
-/
def H3TerminalPhysicalDissipationSingleTimeFixedTransverseCoordinateChannelBranchAtCutoff
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (epsilon rho : ℝ) : Prop :=
  ∃ tau kappa : ℕ → ℝ,
    ∃ htau : ∀ n, tau n ∈ Set.Ioo a T,
      (∀ n, 0 < kappa n)
        ∧
      Tendsto tau atTop (𝓝 T)
        ∧
      Tendsto kappa atTop (𝓝 0)
        ∧
      (∀ n,
        ENNReal.ofReal (rho ^ 2 * (epsilon ^ 2 / 64))
          <
        16 *
          h3TerminalPhysicalDissipationBadConeHighRadialMass
            hH3 i (kappa n) rho (tau n)
            ⟨lt_trans hClass.terminal_start.1 (htau n).1,
              (htau n).2⟩)
        ∧
      ∀ xi : ℕ → H3FourierPoint3,
        (∀ n,
          xi n ∈
            h3TerminalLongitudinalAngularBadCone i (kappa n)
              \
            h3TerminalRadialFrequencyBelow rho)
          →
        Tendsto
            (fun n =>
              ‖h3TerminalNormalizedDerivativeSymbol i (xi n)‖)
            atTop
            (𝓝 0)
          ∧
        Tendsto
            (fun n =>
              h3TerminalNormalizedTransverseDerivativeSymbolSquareMagnitude
                i (xi n))
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
              rho / (4 * Real.pi)
                <
              |(xi n) (h3AxisOfFin3 j)|

/-- The frozen absolute transverse derivative channel from the previous
checkpoint gives a frozen literal Fourier-coordinate channel on the same
concentration witnesses. -/
theorem physicalDissipationSingleTimeFixedTransverseCoordinateChannelBranchAtCutoff_of_fixedTransverseDerivativeChannelBranch
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    {epsilon rho : ℝ}
    (hBranch :
      H3TerminalPhysicalDissipationSingleTimeFixedTransverseDerivativeChannelBranchAtCutoff
        hH3 hClass i epsilon rho) :
    H3TerminalPhysicalDissipationSingleTimeFixedTransverseCoordinateChannelBranchAtCutoff
      hH3 hClass i epsilon rho := by

  unfold
    H3TerminalPhysicalDissipationSingleTimeFixedTransverseDerivativeChannelBranchAtCutoff
      at hBranch

  obtain
    ⟨tau, kappa, htau,
      hkappaPos,
      htauTendsto,
      hkappaTendsto,
      hMass,
      hSelection⟩ :=
    hBranch

  refine
    ⟨tau, kappa, htau,
      hkappaPos,
      htauTendsto,
      hkappaTendsto,
      hMass,
      ?_⟩

  intro xi hxi

  have hSelected :=
    hSelection xi hxi

  refine
    ⟨hSelected.1, hSelected.2.1, ?_⟩

  obtain ⟨j, hjNe, hj⟩ :=
    hSelected.2.2

  refine
    ⟨j, hjNe, ?_⟩

  intro N

  obtain ⟨n, hnN, hnDerivative⟩ :=
    hj N

  refine
    ⟨n, hnN, ?_⟩

  exact
    abs_fourierCoordinate_gt_cutoff_div_four_pi_of_derivativeSymbol_gt_half_cutoff
      j
      hnDerivative

/-! ## Necessary literal transverse coordinate under nonextension -/

/--
Under the retained raw-Fourier L2 Cauchy hypothesis, hypothetical nonextension
and one surviving physical-vorticity strong H3 endpoint force a single-time
physical H3 dissipation concentration branch with one recurrent fixed
transverse Fourier coordinate bounded below by the positive physical scale
`rho/(4*pi)` along every supported frequency selection.
-/
theorem exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationFixedTransverseCoordinateChannel_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ rho : ℝ,
      0 < rho
        ∧
      ∃ q : Fin 3,
        q ≠ i
          ∧
        ¬ H3TerminalActualVorticityStrongH3EndpointPath hH3 q
          ∧
        H3TerminalHighRadialRawVorticityBranchAtCutoff
          hH3 i q epsilon rho
          ∧
        H3TerminalPhysicalDissipationSingleTimeFixedTransverseCoordinateChannelBranchAtCutoff
          hH3 hClass i epsilon rho := by

  obtain
    ⟨rho, hrho, q, hqNe, hqFail, hRawBranch, hFixed⟩ :=
    exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationFixedTransverseDerivativeChannel_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hCauchy
      hepsilon

  refine
    ⟨rho, hrho, q, hqNe, hqFail, hRawBranch, ?_⟩

  exact
    physicalDissipationSingleTimeFixedTransverseCoordinateChannelBranchAtCutoff_of_fixedTransverseDerivativeChannelBranch
      hH3
      hClass
      i
      hFixed

end

end Euclidean
end Bridge
end PrimeTensor
