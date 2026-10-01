import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityPhysicalDissipationTransverseShareDichotomy

/-!
# Quantify the two-transverse-channel dissipation regime

The preceding checkpoint classifies the transverse polarization by a parameter

    theta ∈ [1/2, 1].

If `theta = 1`, the complementary transverse normalized square share tends to
zero.  If `theta < 1`, that complementary square share tends to the positive
number `1 - theta`.

This file turns the latter statement into an absolute Fourier-frequency scale.
Because every normalized coordinate norm is at most one, a normalized square
share above `delta > 0` forces the normalized norm itself above `delta`.  On
the fixed high-radial support `|D(xi)| >= rho`, this gives

    delta * rho / (2*pi) < |xi_r|.

Taking `delta = (1 - theta)/2`, the two-channel branch therefore carries both
transverse literal coordinates at positive scales on the same strict
subsequence:

* the selected coordinate `j` stays above `rho/(4*pi)`;
* the complementary coordinate `r` eventually stays above
  `rho*(1-theta)/(4*pi)`.

The axial branch is retained unchanged.  This remains a conditional necessary
mechanism under hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Positive normalized square share gives an absolute coordinate scale -/

/--
On the radial complement of `|D(xi)| < rho`, any positive lower bound `delta`
on a normalized coordinate-symbol square gives the literal coordinate lower
bound `delta*rho/(2*pi)`.
-/
theorem abs_fourierCoordinate_gt_scaled_cutoff_of_not_mem_radialBelow_of_normalized_sq_gt
    (j : Fin 3)
    {rho delta : ℝ}
    (hrho : 0 < rho)
    (hdelta : 0 < delta)
    {xi : H3FourierPoint3}
    (hHigh : xi ∉ h3TerminalRadialFrequencyBelow rho)
    (hShare :
      delta
        <
      ‖h3TerminalNormalizedDerivativeSymbol j xi‖ ^ 2) :
    (delta * rho) / (2 * Real.pi)
      <
    |xi (h3AxisOfFin3 j)| := by

  have hRadial :
      rho ≤ h3FourierGradientMagnitude xi := by
    unfold h3TerminalRadialFrequencyBelow at hHigh
    simp only [Set.mem_setOf_eq, not_lt] at hHigh
    exact hHigh

  have hGradPos :
      0 < h3FourierGradientMagnitude xi :=
    lt_of_lt_of_le hrho hRadial

  let x : ℝ :=
    ‖h3TerminalNormalizedDerivativeSymbol j xi‖

  have hx0 : 0 ≤ x := by
    dsimp only [x]
    exact norm_nonneg _

  have hx1 : x ≤ 1 := by
    dsimp only [x]
    exact
      norm_h3TerminalNormalizedDerivativeSymbol_le_one
        j xi

  have hxSqLe : x ^ 2 ≤ x := by
    nlinarith

  have hdeltaNorm : delta < x := by
    exact
      hShare.trans_le hxSqLe

  dsimp only [x] at hdeltaNorm

  rw [
    norm_h3TerminalNormalizedDerivativeSymbol_eq_div
      j xi hGradPos
  ] at hdeltaNorm

  have hRaw :
      delta * h3FourierGradientMagnitude xi
        <
      ‖h3FourierDerivativeSymbol j xi‖ :=
    (lt_div_iff₀ hGradPos).1
      hdeltaNorm

  have hScaledLe :
      delta * rho
        ≤
      delta * h3FourierGradientMagnitude xi :=
    mul_le_mul_of_nonneg_left
      hRadial
      hdelta.le

  have hRawScaled :
      delta * rho
        <
      ‖h3FourierDerivativeSymbol j xi‖ :=
    lt_of_le_of_lt
      hScaledLe
      hRaw

  rw [
    norm_h3FourierDerivativeSymbol_eq_two_pi_mul_abs_coordinate
  ] at hRawScaled

  have hTwoPiPos :
      0 < 2 * Real.pi := by
    positivity

  have hRawScaled' :
      delta * rho
        <
      |xi (h3AxisOfFin3 j)| * (2 * Real.pi) := by
    simpa only [mul_comm] using hRawScaled

  exact
    (div_lt_iff₀ hTwoPiPos).2
      hRawScaled'

/-! ## Physical branch with quantitative two-transverse scale -/

/--
A single-time physical H3 dissipation concentration branch with the exact
transverse-share dichotomy and a quantitative literal scale for the second
transverse coordinate in the genuine two-channel regime.
-/
def H3TerminalPhysicalDissipationSingleTimeTransverseTwoScaleDichotomyBranchAtCutoff
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
        ∃ j r : Fin 3,
          j ≠ i
            ∧
          r ≠ i
            ∧
          r ≠ j
            ∧
          ∃ theta : ℝ,
            theta ∈ Set.Icc ((1 : ℝ) / 2) 1
              ∧
            ∃ m : ℕ → ℕ,
              StrictMono m
                ∧
              Tendsto
                (fun n =>
                  ‖h3TerminalNormalizedDerivativeSymbol j (xi (m n))‖ ^ 2)
                atTop
                (𝓝 theta)
                ∧
              Tendsto
                (fun n =>
                  ‖h3TerminalNormalizedDerivativeSymbol r (xi (m n))‖ ^ 2)
                atTop
                (𝓝 (1 - theta))
                ∧
              (∀ᶠ n : ℕ in atTop,
                rho / (4 * Real.pi)
                  <
                |(xi (m n)) (h3AxisOfFin3 j)|)
                ∧
              Tendsto
                (fun n =>
                  |(xi (m n)) (h3AxisOfFin3 i)|
                    /
                  |(xi (m n)) (h3AxisOfFin3 j)|)
                atTop
                (𝓝 0)
                ∧
              (
                (theta = 1
                  ∧
                Tendsto
                  (fun n =>
                    ‖h3TerminalNormalizedDerivativeSymbol r (xi (m n))‖ ^ 2)
                  atTop
                  (𝓝 0))
                  ∨
                (theta < 1
                  ∧
                0 < 1 - theta
                  ∧
                ∀ᶠ n : ℕ in atTop,
                  rho * (1 - theta) / (4 * Real.pi)
                    <
                  |(xi (m n)) (h3AxisOfFin3 r)|)
              )

/--
The transverse-share dichotomy from the preceding checkpoint upgrades to a
literal second transverse coordinate scale in the `theta < 1` branch.
-/
theorem physicalDissipationSingleTimeTransverseTwoScaleDichotomyBranchAtCutoff_of_shareDichotomyBranch
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    {epsilon rho : ℝ}
    (hrho : 0 < rho)
    (hBranch :
      H3TerminalPhysicalDissipationSingleTimeTransverseShareDichotomyBranchAtCutoff
        hH3 hClass i epsilon rho) :
    H3TerminalPhysicalDissipationSingleTimeTransverseTwoScaleDichotomyBranchAtCutoff
      hH3 hClass i epsilon rho := by

  unfold
    H3TerminalPhysicalDissipationSingleTimeTransverseShareDichotomyBranchAtCutoff
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

  obtain
    ⟨hLongitudinal,
      hTransverse,
      j, r,
      hjNe, hrNe, hrjNe,
      theta, htheta,
      m, hmMono,
      hJShare,
      hRShare,
      hRegime,
      hJCoordinate,
      hRatio⟩ :=
    hSelection xi hxi

  refine
    ⟨hLongitudinal,
      hTransverse,
      j, r,
      hjNe, hrNe, hrjNe,
      theta, htheta,
      m, hmMono,
      hJShare,
      hRShare,
      hJCoordinate,
      hRatio,
      ?_⟩

  rcases hRegime with hAxial | hTwo

  · left
    exact hAxial

  · right

    have hdeltaPos :
        0 < (1 - theta) / 2 := by
      linarith [hTwo.2]

    have hdeltaLt :
        (1 - theta) / 2
          <
        1 - theta := by
      linarith [hTwo.2]

    have hRShareEventually :
        ∀ᶠ n : ℕ in atTop,
          (1 - theta) / 2
            <
          ‖h3TerminalNormalizedDerivativeSymbol r (xi (m n))‖ ^ 2 :=
      (tendsto_order.1 hRShare).1
        ((1 - theta) / 2)
        hdeltaLt

    have hRCoordinate :
        ∀ᶠ n : ℕ in atTop,
          rho * (1 - theta) / (4 * Real.pi)
            <
          |(xi (m n)) (h3AxisOfFin3 r)| := by
      filter_upwards [hRShareEventually] with n hnShare

      have hCoordinate :=
        abs_fourierCoordinate_gt_scaled_cutoff_of_not_mem_radialBelow_of_normalized_sq_gt
          r
          hrho
          hdeltaPos
          (hxi (m n)).2
          hnShare

      have hScale :
          (((1 - theta) / 2) * rho) / (2 * Real.pi)
            =
          rho * (1 - theta) / (4 * Real.pi) := by
        field_simp [ne_of_gt Real.pi_pos]
        <;> ring

      rw [hScale] at hCoordinate
      exact hCoordinate

    exact
      ⟨hTwo.1, hTwo.2, hRCoordinate⟩

/-! ## Necessary quantified transverse geometry under nonextension -/

/--
Under the retained raw-Fourier L2 Cauchy hypothesis, hypothetical nonextension
and one surviving physical-vorticity strong H3 endpoint force either an axial
transverse polarization limit or a genuine two-transverse-channel branch in
which both literal transverse Fourier coordinates remain at positive scales on
the same strict subsequence.
-/
theorem exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationTransverseTwoScaleDichotomy_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
        H3TerminalPhysicalDissipationSingleTimeTransverseTwoScaleDichotomyBranchAtCutoff
          hH3 hClass i epsilon rho := by

  obtain
    ⟨rho, hrho, q, hqNe, hqFail, hRawBranch, hDichotomy⟩ :=
    exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationTransverseShareDichotomy_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hCauchy
      hepsilon

  refine
    ⟨rho, hrho, q, hqNe, hqFail, hRawBranch, ?_⟩

  exact
    physicalDissipationSingleTimeTransverseTwoScaleDichotomyBranchAtCutoff_of_shareDichotomyBranch
      hH3
      hClass
      i
      hrho
      hDichotomy

end

end Euclidean
end Bridge
end PrimeTensor
