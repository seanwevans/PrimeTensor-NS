import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Actual.Frequency.Aspect.Ratio.Limit

/-!
# Extract a positive-density frequency sequence from dissipation concentration

The preceding checkpoint removes the vacuity of the universal frequency
geometry by choosing one point from every nonempty localized high-radial bad
cone.

The strict localized dissipation-mass lower bound gives more.  If the
single-time spectral dissipation density were zero at every point of one
localized set, then its restricted `lintegral` would vanish.  This contradicts
the same strict mass lower bound.  Since the density is everywhere
nonnegative, every localized set therefore contains a point where the density
is strictly positive.

Choosing such a point at every index gives an actual frequency sequence with

    0 < spectral dissipation density at xi_n,

and the full transverse aspect-ratio classification applies to that same
sequence.

This is a pointwise positive-density statement, not a claim that a singleton
frequency carries positive measure or atomic dissipation mass.  The result
remains a conditional necessary mechanism under hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalDissipationPositiveDensityFrequencyAspectRatioLimit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalPhysicalDissipationPositiveDensityFrequencyAspectRatioLimit :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Strict localized mass produces a positive-density point -/

/--
A strict lower bound against the localized physical H3 dissipation mass forces
the localized high-radial bad cone to contain a point where the canonical
single-time dissipation density is strictly positive.
-/
theorem exists_positive_spectralDissipationDensity_of_strict_localized_mass_lower
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
    ∃ xi : H3FourierPoint3,
      xi ∈
        h3TerminalLongitudinalAngularBadCone i kappa
          \
        h3TerminalRadialFrequencyBelow rho
        ∧
      0 <
        h3TerminalSpectralDissipationSingleDensity
          (h3TerminalVelocitySpectralStateAt hH3 t ht)
          xi := by

  let S : Set H3FourierPoint3 :=
    h3TerminalLongitudinalAngularBadCone i kappa
      \
    h3TerminalRadialFrequencyBelow rho

  by_contra hNo

  have hZeroOn :
      Set.EqOn
        (fun xi : H3FourierPoint3 =>
          ENNReal.ofReal
            (h3TerminalSpectralDissipationSingleDensity
              (h3TerminalVelocitySpectralStateAt hH3 t ht)
              xi))
        (0 : H3FourierPoint3 → ℝ≥0∞)
        S := by
    intro xi hxi

    have hNotPos :
        ¬ 0 <
          h3TerminalSpectralDissipationSingleDensity
            (h3TerminalVelocitySpectralStateAt hH3 t ht)
            xi := by
      intro hPos
      apply hNo
      exact
        ⟨xi, hxi, hPos⟩

    have hNonpos :
        h3TerminalSpectralDissipationSingleDensity
            (h3TerminalVelocitySpectralStateAt hH3 t ht)
            xi
          ≤
        0 :=
      le_of_not_gt hNotPos

    have hNonneg :
        0 ≤
          h3TerminalSpectralDissipationSingleDensity
            (h3TerminalVelocitySpectralStateAt hH3 t ht)
            xi :=
      h3TerminalSpectralDissipationSingleDensity_nonneg
        (h3TerminalVelocitySpectralStateAt hH3 t ht)
        xi

    have hZero :
        h3TerminalSpectralDissipationSingleDensity
            (h3TerminalVelocitySpectralStateAt hH3 t ht)
            xi
          =
        0 :=
      le_antisymm hNonpos hNonneg

    simp only [Pi.zero_apply, hZero, ENNReal.ofReal_zero]

  have hSMeas :
      MeasurableSet S :=
    (measurableSet_h3TerminalLongitudinalAngularBadCone i kappa).diff
      (measurableSet_h3TerminalRadialFrequencyBelow rho)

  have hMassZero :
      h3TerminalPhysicalDissipationBadConeHighRadialMass
          hH3 i kappa rho t ht
        =
      0 := by
    unfold
      h3TerminalPhysicalDissipationBadConeHighRadialMass
    change
      (∫⁻ xi in S,
        ENNReal.ofReal
          (h3TerminalSpectralDissipationSingleDensity
            (h3TerminalVelocitySpectralStateAt hH3 t ht)
            xi)
        ∂volume)
        =
      0
    exact
      setLIntegral_eq_zero
        (μ := volume)
        hSMeas
        hZeroOn

  have hContradiction :=
    hLower

  rw [hMassZero] at hContradiction
  simpa using hContradiction

/-! ## Actual positive-density sequence with classified geometry -/

/--
A single-time physical H3 dissipation concentration branch carrying an actual
frequency `xi_n` of strictly positive canonical dissipation density at every
index, together with the full transverse aspect-ratio classification on that
same sequence.
-/
def H3TerminalPhysicalDissipationSingleTimePositiveDensityFrequencyAspectRatioLimitBranchAtCutoff
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
        (∀ n,
          0 <
            h3TerminalSpectralDissipationSingleDensity
              (h3TerminalVelocitySpectralStateAt
                hH3
                (tau n)
                ⟨lt_trans hClass.terminal_start.1 (htau n).1,
                  (htau n).2⟩)
              (xi n))
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
The universal aspect-ratio branch contains an actual positive-density frequency
sequence.  The existing universal geometric classification then applies to
that same chosen sequence.
-/
theorem physicalDissipationSingleTimePositiveDensityFrequencyAspectRatioLimitBranchAtCutoff_of_aspectRatioLimitBranch
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    {epsilon rho : ℝ}
    (hBranch :
      H3TerminalPhysicalDissipationSingleTimeTransverseAspectRatioLimitBranchAtCutoff
        hH3 hClass i epsilon rho) :
    H3TerminalPhysicalDissipationSingleTimePositiveDensityFrequencyAspectRatioLimitBranchAtCutoff
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

  have hPositivePoint :
      ∀ n : ℕ,
        ∃ xi : H3FourierPoint3,
          xi ∈
            h3TerminalLongitudinalAngularBadCone i (kappa n)
              \
            h3TerminalRadialFrequencyBelow rho
            ∧
          0 <
            h3TerminalSpectralDissipationSingleDensity
              (h3TerminalVelocitySpectralStateAt
                hH3
                (tau n)
                ⟨lt_trans hClass.terminal_start.1 (htau n).1,
                  (htau n).2⟩)
              xi := by
    intro n

    exact
      exists_positive_spectralDissipationDensity_of_strict_localized_mass_lower
        hH3
        i
        ⟨lt_trans hClass.terminal_start.1 (htau n).1,
          (htau n).2⟩
        (hMass n)

  choose xi hxi using hPositivePoint

  have hxiMem :
      ∀ n,
        xi n ∈
          h3TerminalLongitudinalAngularBadCone i (kappa n)
            \
          h3TerminalRadialFrequencyBelow rho :=
    fun n => (hxi n).1

  have hxiPositive :
      ∀ n,
        0 <
          h3TerminalSpectralDissipationSingleDensity
            (h3TerminalVelocitySpectralStateAt
              hH3
              (tau n)
              ⟨lt_trans hClass.terminal_start.1 (htau n).1,
                (htau n).2⟩)
            (xi n) :=
    fun n => (hxi n).2

  have hSelected :=
    hSelection xi hxiMem

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
      hxiMem,
      hxiPositive,
      ?_
    ⟩

  exact hSelected

/-! ## Necessary positive-density frequency sequence under nonextension -/

/--
Under the retained raw-Fourier L2 Cauchy hypothesis, hypothetical nonextension
and one surviving physical-vorticity strong H3 endpoint force an actual
frequency sequence of strictly positive canonical dissipation density inside
every shrinking high-radial bad-cone localization.  The full literal
transverse aspect-ratio classification holds along a strict subsequence of
those same positive-density points.
-/
theorem exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationPositiveDensityFrequencyAspectRatioLimit_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
        H3TerminalPhysicalDissipationSingleTimePositiveDensityFrequencyAspectRatioLimitBranchAtCutoff
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
    physicalDissipationSingleTimePositiveDensityFrequencyAspectRatioLimitBranchAtCutoff_of_aspectRatioLimitBranch
      hH3
      hClass
      i
      hAspect

end

end Euclidean
end Bridge
end PrimeTensor
