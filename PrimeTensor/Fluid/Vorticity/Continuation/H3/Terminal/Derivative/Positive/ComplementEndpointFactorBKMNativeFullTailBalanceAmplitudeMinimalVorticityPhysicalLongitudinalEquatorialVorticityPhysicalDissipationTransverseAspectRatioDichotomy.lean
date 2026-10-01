import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityPhysicalDissipationTransverseTwoScaleDichotomy

/-!
# Transverse Fourier aspect-ratio classification

The preceding checkpoint classifies the asymptotic transverse square shares by

    theta in [1/2,1],   1-theta in [0,1/2].

Both normalized derivative symbols use the same radial denominator, and both
raw coordinate derivative symbols carry the same factor `2*pi`.  Therefore the
quotient of transverse normalized square shares is exactly the squared literal
Fourier-coordinate ratio.

Along the same strict subsequence this gives

    (|xi_r| / |xi_j|)^2 -> (1-theta)/theta.

Hence the axial branch `theta = 1` has transverse aspect ratio tending to zero,
while the genuine two-channel branch `theta < 1` has a finite strictly positive
squared aspect-ratio limit.  The positive literal coordinate scales and the
longitudinal/transverse ratio collapse from the preceding checkpoint are
retained unchanged.

This remains a conditional necessary mechanism under hypothetical
nonextension; it does not assert existence of a singular solution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Exact cancellation of common Fourier scales -/

/--
Away from zero radial frequency, if the denominator transverse Fourier
coordinate is nonzero, the squared literal transverse-coordinate ratio is
exactly the quotient of the corresponding normalized derivative-symbol square
shares.
-/
theorem sq_abs_fourierCoordinate_ratio_eq_normalizedDerivativeSymbol_sq_ratio
    (j r : Fin 3)
    {xi : H3FourierPoint3}
    (hGrad : 0 < h3FourierGradientMagnitude xi)
    (hJPos : 0 < |xi (h3AxisOfFin3 j)|) :
    (|xi (h3AxisOfFin3 r)| / |xi (h3AxisOfFin3 j)|) ^ 2
      =
    ‖h3TerminalNormalizedDerivativeSymbol r xi‖ ^ 2
      /
    ‖h3TerminalNormalizedDerivativeSymbol j xi‖ ^ 2 := by

  rw [
    norm_h3TerminalNormalizedDerivativeSymbol_eq_div
      r xi hGrad,
    norm_h3TerminalNormalizedDerivativeSymbol_eq_div
      j xi hGrad,
    norm_h3FourierDerivativeSymbol_eq_two_pi_mul_abs_coordinate,
    norm_h3FourierDerivativeSymbol_eq_two_pi_mul_abs_coordinate
  ]

  have hTwoPiPos :
      0 < 2 * Real.pi := by
    positivity

  field_simp [
    ne_of_gt hTwoPiPos,
    hGrad.ne',
    hJPos.ne'
  ]
  <;> ring

/-! ## Physical branch with a classified transverse aspect ratio -/

/--
A single-time physical H3 dissipation concentration branch with two fixed
transverse coordinates `j` and `r`, square-share parameter `theta`, and exact
literal squared transverse aspect-ratio limit

    `(|xi_r| / |xi_j|)^2 -> (1-theta)/theta`.

The axial branch has ratio-square limit zero.  The genuine two-channel branch
has a strictly positive finite ratio-square limit and retains the quantitative
second transverse coordinate scale from the preceding checkpoint.
-/
def H3TerminalPhysicalDissipationSingleTimeTransverseAspectRatioDichotomyBranchAtCutoff
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
              Tendsto
                (fun n =>
                  (|(xi (m n)) (h3AxisOfFin3 r)|
                      /
                    |(xi (m n)) (h3AxisOfFin3 j)|) ^ 2)
                atTop
                (𝓝 ((1 - theta) / theta))
                ∧
              (
                (theta = 1
                  ∧
                Tendsto
                  (fun n =>
                    (|(xi (m n)) (h3AxisOfFin3 r)|
                        /
                      |(xi (m n)) (h3AxisOfFin3 j)|) ^ 2)
                  atTop
                  (𝓝 0))
                  ∨
                (theta < 1
                  ∧
                0 < (1 - theta) / theta
                  ∧
                ∀ᶠ n : ℕ in atTop,
                  rho * (1 - theta) / (4 * Real.pi)
                    <
                  |(xi (m n)) (h3AxisOfFin3 r)|)
              )

/--
The quantitative two-scale transverse dichotomy upgrades to an exact literal
transverse aspect-ratio limit on the same concentration witnesses.
-/
theorem physicalDissipationSingleTimeTransverseAspectRatioDichotomyBranchAtCutoff_of_twoScaleDichotomyBranch
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    {epsilon rho : ℝ}
    (hrho : 0 < rho)
    (hBranch :
      H3TerminalPhysicalDissipationSingleTimeTransverseTwoScaleDichotomyBranchAtCutoff
        hH3 hClass i epsilon rho) :
    H3TerminalPhysicalDissipationSingleTimeTransverseAspectRatioDichotomyBranchAtCutoff
      hH3 hClass i epsilon rho := by

  unfold
    H3TerminalPhysicalDissipationSingleTimeTransverseTwoScaleDichotomyBranchAtCutoff
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
      hJCoordinate,
      hLongRatio,
      hRegime⟩ :=
    hSelection xi hxi

  have hthetaPos :
      0 < theta := by
    linarith [htheta.1]

  have hShareRatio :
      Tendsto
        (fun n =>
          ‖h3TerminalNormalizedDerivativeSymbol r (xi (m n))‖ ^ 2
            /
          ‖h3TerminalNormalizedDerivativeSymbol j (xi (m n))‖ ^ 2)
        atTop
        (𝓝 ((1 - theta) / theta)) := by
    exact
      hRShare.div
        hJShare
        (ne_of_gt hthetaPos)

  have hJCutoffPos :
      0 < rho / (4 * Real.pi) := by
    positivity

  have hAspectEq :
      (fun n =>
        (|(xi (m n)) (h3AxisOfFin3 r)|
            /
          |(xi (m n)) (h3AxisOfFin3 j)|) ^ 2)
        =ᶠ[atTop]
      (fun n =>
        ‖h3TerminalNormalizedDerivativeSymbol r (xi (m n))‖ ^ 2
          /
        ‖h3TerminalNormalizedDerivativeSymbol j (xi (m n))‖ ^ 2) := by
    filter_upwards [hJCoordinate] with n hnJ

    have hJPos :
        0 < |(xi (m n)) (h3AxisOfFin3 j)| :=
      lt_trans hJCutoffPos hnJ

    have hGrad :
        0 < h3FourierGradientMagnitude (xi (m n)) :=
      gradientMagnitude_pos_of_mem_longitudinalAngularBadCone
        (hxi (m n)).1

    exact
      sq_abs_fourierCoordinate_ratio_eq_normalizedDerivativeSymbol_sq_ratio
        j r hGrad hJPos

  have hAspect :
      Tendsto
        (fun n =>
          (|(xi (m n)) (h3AxisOfFin3 r)|
              /
            |(xi (m n)) (h3AxisOfFin3 j)|) ^ 2)
        atTop
        (𝓝 ((1 - theta) / theta)) :=
    hShareRatio.congr'
      hAspectEq.symm

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
      hLongRatio,
      hAspect,
      ?_⟩

  rcases hRegime with hAxial | hTwo

  · left
    refine ⟨hAxial.1, ?_⟩
    simpa only [hAxial.1, sub_self, zero_div] using hAspect

  · right
    refine
      ⟨hTwo.1,
        div_pos hTwo.2.1 hthetaPos,
        hTwo.2.2⟩

/-! ## Necessary aspect-ratio classification under nonextension -/

/--
Under the retained raw-Fourier L2 Cauchy hypothesis, hypothetical nonextension
and one surviving physical-vorticity strong H3 endpoint force a transverse
frequency aspect-ratio classification: axial collapse with ratio-square limit
zero, or a genuine two-channel branch with a finite strictly positive
ratio-square limit `(1-theta)/theta`.
-/
theorem exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationTransverseAspectRatioDichotomy_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
        H3TerminalPhysicalDissipationSingleTimeTransverseAspectRatioDichotomyBranchAtCutoff
          hH3 hClass i epsilon rho := by

  obtain
    ⟨rho, hrho, q, hqNe, hqFail, hRawBranch, hTwoScale⟩ :=
    exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationTransverseTwoScaleDichotomy_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hCauchy
      hepsilon

  refine
    ⟨rho, hrho, q, hqNe, hqFail, hRawBranch, ?_⟩

  exact
    physicalDissipationSingleTimeTransverseAspectRatioDichotomyBranchAtCutoff_of_twoScaleDichotomyBranch
      hH3
      hClass
      i
      hrho
      hTwoScale

end

end Euclidean
end Bridge
end PrimeTensor
