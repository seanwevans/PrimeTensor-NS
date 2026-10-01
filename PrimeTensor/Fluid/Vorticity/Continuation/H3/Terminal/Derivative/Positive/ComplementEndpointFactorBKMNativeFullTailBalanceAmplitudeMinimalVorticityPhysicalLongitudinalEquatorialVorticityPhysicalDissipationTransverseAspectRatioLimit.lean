import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityPhysicalDissipationTransverseAspectRatioDichotomy

/-!
# Unsquared transverse Fourier aspect-ratio limit

The preceding checkpoint identifies the squared transverse aspect ratio

    (|xi_r| / |xi_j|)^2 -> (1 - theta) / theta,

with `theta ∈ [1/2,1]`.

The literal aspect ratio is nonnegative.  Continuity of the real square root
therefore removes the final square:

    |xi_r| / |xi_j|
      -> sqrt ((1 - theta) / theta).

This gives a direct geometric classification on the same strict subsequence:

* `theta = 1`: the transverse aspect ratio tends to zero;
* `theta < 1`: the aspect ratio tends to the strictly positive finite number
  `sqrt ((1 - theta) / theta)`.

All positive literal coordinate scales and the longitudinal/transverse ratio
collapse are retained.  This remains a conditional necessary mechanism under
hypothetical nonextension and does not assert existence of a singular solution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Remove a square from a nonnegative sequence limit -/

/--
A nonnegative real sequence whose square tends to `L >= 0` tends to
`sqrt L`.
-/
theorem tendsto_sqrt_limit_of_nonnegative_sq_tendsto
    (f : ℕ → ℝ)
    {L : ℝ}
    (hf : ∀ n, 0 ≤ f n)
    (hL : 0 ≤ L)
    (hSq :
      Tendsto
        (fun n => (f n) ^ 2)
        atTop
        (𝓝 L)) :
    Tendsto
      f
      atTop
      (𝓝 (Real.sqrt L)) := by

  have hSqrt :=
    (Real.continuous_sqrt.tendsto L).comp
      hSq

  change
    Tendsto
      (fun n => Real.sqrt ((f n) ^ 2))
      atTop
      (𝓝 (Real.sqrt L))
    at hSqrt

  simpa only [
    Real.sqrt_sq (hf _)
  ] using hSqrt

/-! ## Physical branch with the literal transverse aspect-ratio limit -/

/--
A single-time physical H3 dissipation concentration branch with exact squared
and unsquared literal transverse aspect-ratio limits

    (|xi_r| / |xi_j|)^2 -> (1-theta)/theta,

    |xi_r| / |xi_j| -> sqrt ((1-theta)/theta).

The axial regime has aspect-ratio limit zero.  The genuine two-channel regime
has a strictly positive finite aspect-ratio limit.
-/
def H3TerminalPhysicalDissipationSingleTimeTransverseAspectRatioLimitBranchAtCutoff
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
              Tendsto
                (fun n =>
                  |(xi (m n)) (h3AxisOfFin3 r)|
                    /
                  |(xi (m n)) (h3AxisOfFin3 j)|)
                atTop
                (𝓝 (Real.sqrt ((1 - theta) / theta)))
                ∧
              (
                (theta = 1
                  ∧
                Tendsto
                  (fun n =>
                    |(xi (m n)) (h3AxisOfFin3 r)|
                      /
                    |(xi (m n)) (h3AxisOfFin3 j)|)
                  atTop
                  (𝓝 0))
                  ∨
                (theta < 1
                  ∧
                0 < Real.sqrt ((1 - theta) / theta)
                  ∧
                ∀ᶠ n : ℕ in atTop,
                  rho * (1 - theta) / (4 * Real.pi)
                    <
                  |(xi (m n)) (h3AxisOfFin3 r)|)
              )

/--
The squared transverse aspect-ratio classification upgrades to the exact
unsquared nonnegative aspect-ratio limit on the same concentration witnesses.
-/
theorem physicalDissipationSingleTimeTransverseAspectRatioLimitBranchAtCutoff_of_aspectRatioDichotomyBranch
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    {epsilon rho : ℝ}
    (hBranch :
      H3TerminalPhysicalDissipationSingleTimeTransverseAspectRatioDichotomyBranchAtCutoff
        hH3 hClass i epsilon rho) :
    H3TerminalPhysicalDissipationSingleTimeTransverseAspectRatioLimitBranchAtCutoff
      hH3 hClass i epsilon rho := by

  unfold
    H3TerminalPhysicalDissipationSingleTimeTransverseAspectRatioDichotomyBranchAtCutoff
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
      hAspectSq,
      hRegime⟩ :=
    hSelection xi hxi

  have hthetaPos :
      0 < theta := by
    linarith [htheta.1]

  have hLimitNonneg :
      0 ≤ (1 - theta) / theta := by
    exact
      div_nonneg
        (by linarith [htheta.2])
        hthetaPos.le

  have hAspectNonneg :
      ∀ n : ℕ,
        0 ≤
          |(xi (m n)) (h3AxisOfFin3 r)|
            /
          |(xi (m n)) (h3AxisOfFin3 j)| := by
    intro n
    exact
      div_nonneg
        (abs_nonneg _)
        (abs_nonneg _)

  have hAspect :
      Tendsto
        (fun n =>
          |(xi (m n)) (h3AxisOfFin3 r)|
            /
          |(xi (m n)) (h3AxisOfFin3 j)|)
        atTop
        (𝓝 (Real.sqrt ((1 - theta) / theta))) := by
    exact
      tendsto_sqrt_limit_of_nonnegative_sq_tendsto
        (fun n =>
          |(xi (m n)) (h3AxisOfFin3 r)|
            /
          |(xi (m n)) (h3AxisOfFin3 j)|)
        hAspectNonneg
        hLimitNonneg
        hAspectSq

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
      hAspectSq,
      hAspect,
      ?_⟩

  rcases hRegime with hAxial | hTwo

  · left
    refine ⟨hAxial.1, ?_⟩
    simpa only [
      hAxial.1,
      sub_self,
      zero_div,
      Real.sqrt_zero
    ] using hAspect

  · right
    exact
      ⟨
        hTwo.1,
        Real.sqrt_pos.2 hTwo.2.1,
        hTwo.2.2
      ⟩

/-! ## Necessary literal aspect-ratio classification under nonextension -/

/--
Under the retained raw-Fourier L2 Cauchy hypothesis, hypothetical nonextension
and one surviving physical-vorticity strong H3 endpoint force a literal
transverse Fourier aspect-ratio limit.  The axial branch converges to zero; the
genuine two-channel branch converges to the strictly positive finite value
`sqrt ((1-theta)/theta)`.
-/
theorem exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationTransverseAspectRatioLimit_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
        H3TerminalPhysicalDissipationSingleTimeTransverseAspectRatioLimitBranchAtCutoff
          hH3 hClass i epsilon rho := by

  obtain
    ⟨rho, hrho, q, hqNe, hqFail, hRawBranch, hAspect⟩ :=
    exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationTransverseAspectRatioDichotomy_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hCauchy
      hepsilon

  refine
    ⟨rho, hrho, q, hqNe, hqFail, hRawBranch, ?_⟩

  exact
    physicalDissipationSingleTimeTransverseAspectRatioLimitBranchAtCutoff_of_aspectRatioDichotomyBranch
      hH3
      hClass
      i
      hAspect

end

end Euclidean
end Bridge
end PrimeTensor
