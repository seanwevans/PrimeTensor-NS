import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityPhysicalDissipationTransverseAspectRatioLimit

/-!
# Extract an actual frequency sequence from positive localized dissipation mass

The preceding geometric checkpoints are formulated universally over every
frequency selection lying in the shrinking high-radial bad-cone sets.  Such a
universal statement would be vacuous if one of those sets were empty.

The single-time physical dissipation branch already carries a strict positive
localized-mass inequality at every index.  Since that mass is literally a
`lintegral` restricted to the corresponding high-radial bad cone, an empty
localized set would force the mass to be zero and contradict the strict lower
bound.

Hence every localized set is nonempty.  Choosing one point from each set gives
an actual frequency sequence.  The entire transverse aspect-ratio
classification from the preceding checkpoint then applies to this concrete
sequence.

This does not say that any chosen point carries positive atomic mass; the
conclusion is only nonemptiness of the positive-mass localization region.
The result remains a conditional necessary mechanism under hypothetical
nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Positive localized mass rules out an empty support region -/

/--
A strict lower bound against the localized dissipation mass forces the
high-radial bad-cone localization set to be nonempty.
-/
theorem physicalDissipationBadConeHighRadial_nonempty_of_strict_mass_lower
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (i : Fin 3)
    {kappa rho t threshold : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hLower :
      ENNReal.ofReal threshold
        <
      16 *
        h3TerminalPhysicalDissipationBadConeHighRadialMass
          hH3 i kappa rho t ht) :
    (
      h3TerminalLongitudinalAngularBadCone i kappa
        \
      h3TerminalRadialFrequencyBelow rho
    ).Nonempty := by

  by_contra hEmpty

  have hEqEmpty :
      h3TerminalLongitudinalAngularBadCone i kappa
          \
        h3TerminalRadialFrequencyBelow rho
        =
      ∅ :=
    Set.not_nonempty_iff_eq_empty.mp
      hEmpty

  have hContradiction :=
    hLower

  unfold
    h3TerminalPhysicalDissipationBadConeHighRadialMass
    at hContradiction

  rw [hEqEmpty] at hContradiction

  simpa using hContradiction

/-! ## Nonvacuous branch with one actual frequency sequence -/

/--
A single-time physical H3 dissipation branch with one actual frequency
selection `xi_n` in every shrinking high-radial bad-cone localization region,
together with the full literal transverse aspect-ratio classification on that
chosen sequence.
-/
def H3TerminalPhysicalDissipationSingleTimeActualFrequencyAspectRatioLimitBranchAtCutoff
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (epsilon rho : ℝ) : Prop :=
  ∃ tau kappa : ℕ → ℝ,
    ∃ xi : ℕ → H3FourierPoint3,
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
        (∀ n,
          xi n ∈
            h3TerminalLongitudinalAngularBadCone i (kappa n)
              \
            h3TerminalRadialFrequencyBelow rho)
          ∧
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
The universal transverse aspect-ratio branch is nonvacuous: its strict
localized-mass lower bound produces an actual frequency point in every
localized set, and the existing universal classification applies to the
resulting chosen frequency sequence.
-/
theorem physicalDissipationSingleTimeActualFrequencyAspectRatioLimitBranchAtCutoff_of_aspectRatioLimitBranch
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    {epsilon rho : ℝ}
    (hBranch :
      H3TerminalPhysicalDissipationSingleTimeTransverseAspectRatioLimitBranchAtCutoff
        hH3 hClass i epsilon rho) :
    H3TerminalPhysicalDissipationSingleTimeActualFrequencyAspectRatioLimitBranchAtCutoff
      hH3 hClass i epsilon rho := by

  classical

  unfold
    H3TerminalPhysicalDissipationSingleTimeTransverseAspectRatioLimitBranchAtCutoff
      at hBranch

  obtain
    ⟨tau, kappa, htau,
      hkappaPos,
      htauTendsto,
      hkappaTendsto,
      hMass,
      hSelection⟩ :=
    hBranch

  have hSupportNonempty :
      ∀ n : ℕ,
        (
          h3TerminalLongitudinalAngularBadCone i (kappa n)
            \
          h3TerminalRadialFrequencyBelow rho
        ).Nonempty := by
    intro n

    exact
      physicalDissipationBadConeHighRadial_nonempty_of_strict_mass_lower
        hH3
        i
        ⟨lt_trans hClass.terminal_start.1 (htau n).1,
          (htau n).2⟩
        (hMass n)

  choose xi hxi using hSupportNonempty

  have hSelected :=
    hSelection xi hxi

  refine
    ⟨
      tau,
      kappa,
      xi,
      htau,
      hkappaPos,
      htauTendsto,
      hkappaTendsto,
      hMass,
      hxi,
      ?_
    ⟩

  exact hSelected

/-! ## Necessary actual frequency sequence under hypothetical nonextension -/

/--
Under the retained raw-Fourier L2 Cauchy hypothesis, hypothetical nonextension
and one surviving physical-vorticity strong H3 endpoint force an actual
frequency sequence lying in every shrinking high-radial bad-cone localization
set.  Along a strict subsequence of that concrete sequence, the literal
transverse aspect-ratio classification holds.
-/
theorem exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationActualFrequencyAspectRatioLimit_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
        H3TerminalPhysicalDissipationSingleTimeActualFrequencyAspectRatioLimitBranchAtCutoff
          hH3 hClass i epsilon rho := by

  obtain
    ⟨rho, hrho, q, hqNe, hqFail, hRawBranch, hAspect⟩ :=
    exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationTransverseAspectRatioLimit_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hCauchy
      hepsilon

  refine
    ⟨rho, hrho, q, hqNe, hqFail, hRawBranch, ?_⟩

  exact
    physicalDissipationSingleTimeActualFrequencyAspectRatioLimitBranchAtCutoff_of_aspectRatioLimitBranch
      hH3
      hClass
      i
      hAspect

end

end Euclidean
end Bridge
end PrimeTensor
