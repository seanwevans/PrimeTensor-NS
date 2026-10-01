import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityPhysicalDissipationFixedTransverseCoordinateChannel

/-!
# Transverse coordinate ratio collapse in the physical dissipation branch

The fixed-transverse-channel checkpoint retains more information than the
absolute coordinate lower bound alone: on a cofinal family of indices, one
fixed transverse normalized derivative symbol has square strictly above
`1/4`.

On the same shrinking bad cone the normalized longitudinal symbol is below the
aperture `κ`.  Hence, along those recurrent indices,

    |ξ_i| / |ξ_j| < 2 κ.

Selecting one recurrent index at or beyond every original index produces a
cofinal reindexing.  Since `κ -> 0`, the literal Fourier-coordinate aspect
ratio tends to zero along that reindexing, while the fixed transverse
coordinate remains bounded away from zero by the positive radial cutoff.

This is a conditional necessary geometric mechanism under hypothetical
nonextension.  It does not assert existence of a singular solution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Pointwise coordinate-ratio estimate -/

/--
On a longitudinal bad cone, if one transverse normalized derivative-symbol
square exceeds `1/4`, then the literal longitudinal/transverse Fourier
coordinate ratio is below twice the cone aperture.
-/
theorem abs_fourierCoordinate_ratio_lt_two_mul_aperture_of_badCone_of_normalized_transverse_sq_gt_quarter
    (i j : Fin 3)
    {κ : ℝ}
    (hκ : 0 < κ)
    {ξ : H3FourierPoint3}
    (hBad :
      ξ ∈ h3TerminalLongitudinalAngularBadCone i κ)
    (hShare :
      (1 / 4 : ℝ)
        <
      ‖h3TerminalNormalizedDerivativeSymbol j ξ‖ ^ 2) :
    |ξ (h3AxisOfFin3 i)| / |ξ (h3AxisOfFin3 j)|
      <
    2 * κ := by

  have hGrad :
      0 < h3FourierGradientMagnitude ξ :=
    gradientMagnitude_pos_of_mem_longitudinalAngularBadCone
      hBad

  have hJNonneg :
      0 ≤ ‖h3TerminalNormalizedDerivativeSymbol j ξ‖ :=
    norm_nonneg _

  have hJHalf :
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

  have hJRawHalf :
      (1 / 2 : ℝ) * h3FourierGradientMagnitude ξ
        <
      ‖h3FourierDerivativeSymbol j ξ‖ := by
    rw [
      norm_h3TerminalNormalizedDerivativeSymbol_eq_div
        j ξ hGrad
    ] at hJHalf
    exact
      (lt_div_iff₀ hGrad).1
        hJHalf

  have hGradLtTwiceJ :
      h3FourierGradientMagnitude ξ
        <
      2 * ‖h3FourierDerivativeSymbol j ξ‖ := by
    nlinarith

  have hJRawPos :
      0 < ‖h3FourierDerivativeSymbol j ξ‖ := by
    have hHalfGradPos :
        0 < (1 / 2 : ℝ) * h3FourierGradientMagnitude ξ := by
      positivity
    exact
      lt_trans
        hHalfGradPos
        hJRawHalf

  have hBadRaw :
      ‖h3FourierDerivativeSymbol i ξ‖
        <
      κ * h3FourierGradientMagnitude ξ := by
    exact hBad

  have hScaled :
      κ * h3FourierGradientMagnitude ξ
        <
      (2 * κ) * ‖h3FourierDerivativeSymbol j ξ‖ := by
    have hMul :=
      mul_lt_mul_of_pos_left
        hGradLtTwiceJ
        hκ
    nlinarith

  have hRaw :
      ‖h3FourierDerivativeSymbol i ξ‖
        <
      (2 * κ) * ‖h3FourierDerivativeSymbol j ξ‖ :=
    lt_trans hBadRaw hScaled

  have hRawRatio :
      ‖h3FourierDerivativeSymbol i ξ‖
          /
        ‖h3FourierDerivativeSymbol j ξ‖
        <
      2 * κ :=
    (div_lt_iff₀ hJRawPos).2
      hRaw

  rw [
    norm_h3FourierDerivativeSymbol_eq_two_pi_mul_abs_coordinate,
    norm_h3FourierDerivativeSymbol_eq_two_pi_mul_abs_coordinate
  ] at hRawRatio

  have hTwoPiPos :
      0 < 2 * Real.pi := by
    positivity

  have hCoordinateProductPos :
      0
        <
      (2 * Real.pi) * |ξ (h3AxisOfFin3 j)| := by
    rw [
      ← norm_h3FourierDerivativeSymbol_eq_two_pi_mul_abs_coordinate
    ]
    exact hJRawPos

  have hProductPos :
      0
        <
      |ξ (h3AxisOfFin3 j)| * (2 * Real.pi) := by
    simpa only [mul_comm] using hCoordinateProductPos

  have hAbsJPos :
      0 < |ξ (h3AxisOfFin3 j)| :=
    pos_of_mul_pos_left
      hProductPos
      hTwoPiPos.le

  have hCancel :
      ((2 * Real.pi) * |ξ (h3AxisOfFin3 i)|)
          /
        ((2 * Real.pi) * |ξ (h3AxisOfFin3 j)|)
        =
      |ξ (h3AxisOfFin3 i)| / |ξ (h3AxisOfFin3 j)| := by
    field_simp [
      ne_of_gt hTwoPiPos,
      ne_of_gt hAbsJPos
    ]

  rw [hCancel] at hRawRatio
  exact hRawRatio

/-! ## Ratio-collapse branch -/

/--
A single-time physical H³ dissipation concentration branch with one fixed
transverse Fourier coordinate and a cofinal extraction on which

    `|ξ_i| / |ξ_j| -> 0`,

while `|ξ_j|` remains above the positive scale `ρ/(4π)` at every extracted
index.
-/
def H3TerminalPhysicalDissipationSingleTimeTransverseCoordinateRatioBranchAtCutoff
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
          ∃ m : ℕ → ℕ,
            (∀ n, n ≤ m n)
              ∧
            (∀ n,
              ρ / (4 * Real.pi)
                <
              |(ξ (m n)) (h3AxisOfFin3 j)|)
              ∧
            Tendsto
              (fun n =>
                |(ξ (m n)) (h3AxisOfFin3 i)|
                  /
                |(ξ (m n)) (h3AxisOfFin3 j)|)
              atTop
              (𝓝 0)

/--
The frozen recurrent normalized transverse channel admits a cofinal extraction
with literal coordinate aspect ratio tending to zero.  The positive radial
cutoff simultaneously keeps the selected transverse coordinate uniformly away
from zero.
-/
theorem physicalDissipationSingleTimeTransverseCoordinateRatioBranchAtCutoff_of_fixedTransverseChannelBranch
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
    H3TerminalPhysicalDissipationSingleTimeTransverseCoordinateRatioBranchAtCutoff
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

  obtain ⟨k, hkCofinal⟩ :=
    hSelected.2.2

  let j : Fin 3 :=
    h3TerminalTransverseCoordinate i k

  have hjNe :
      j ≠ i := by
    dsimp only [j]
    exact
      h3TerminalTransverseCoordinate_ne
        i k

  choose m hm using hkCofinal

  have hmTop :
      Tendsto m atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact
      le_trans
        hn
        (hm n).1

  have hCoordinateLower :
      ∀ n,
        ρ / (4 * Real.pi)
          <
        |(ξ (m n)) (h3AxisOfFin3 j)| := by
    intro n

    have hDerivative :
        ρ / 2
          <
        ‖h3FourierDerivativeSymbol j (ξ (m n))‖ := by
      dsimp only [j]
      exact
        norm_h3FourierDerivativeSymbol_gt_half_cutoff_of_not_mem_radialBelow_of_normalized_sq_gt_quarter
          (h3TerminalTransverseCoordinate i k)
          hρ
          (hξ (m n)).2
          (hm n).2

    exact
      abs_fourierCoordinate_gt_cutoff_div_four_pi_of_derivativeSymbol_gt_half_cutoff
        j
        hDerivative

  have hRatioUpper :
      ∀ n,
        |(ξ (m n)) (h3AxisOfFin3 i)|
            /
          |(ξ (m n)) (h3AxisOfFin3 j)|
          <
        2 * κ (m n) := by
    intro n

    dsimp only [j]

    exact
      abs_fourierCoordinate_ratio_lt_two_mul_aperture_of_badCone_of_normalized_transverse_sq_gt_quarter
        i
        (h3TerminalTransverseCoordinate i k)
        (hκPos (m n))
        (hξ (m n)).1
        (hm n).2

  have hκSub :
      Tendsto
        (fun n => κ (m n))
        atTop
        (𝓝 0) :=
    hκTendsto.comp
      hmTop

  have hTwoκ :
      Tendsto
        (fun n => (2 : ℝ) * κ (m n))
        atTop
        (𝓝 0) := by
    have hMul :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul
        hκSub
    simpa only [mul_zero] using hMul

  have hRatioZero :
      Tendsto
        (fun n =>
          |(ξ (m n)) (h3AxisOfFin3 i)|
            /
          |(ξ (m n)) (h3AxisOfFin3 j)|)
        atTop
        (𝓝 0) := by
    apply squeeze_zero'
    · exact
        Filter.Eventually.of_forall
          (fun n =>
            div_nonneg
              (abs_nonneg _)
              (abs_nonneg _))
    · exact
        Filter.Eventually.of_forall
          (fun n =>
            le_of_lt
              (hRatioUpper n))
    · exact hTwoκ

  exact
    ⟨
      j,
      hjNe,
      m,
      (fun n => (hm n).1),
      hCoordinateLower,
      hRatioZero
    ⟩

/-! ## Necessary ratio collapse under hypothetical nonextension -/

/--
Under the retained raw-Fourier `L²` Cauchy hypothesis, hypothetical
nonextension and one surviving physical-vorticity strong H³ endpoint force a
single-time physical H³ dissipation concentration branch with a fixed
transverse coordinate and a cofinal frequency extraction whose longitudinal to
transverse literal Fourier-coordinate ratio tends to zero.
-/
theorem exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationTransverseCoordinateRatio_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
        H3TerminalPhysicalDissipationSingleTimeTransverseCoordinateRatioBranchAtCutoff
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
    physicalDissipationSingleTimeTransverseCoordinateRatioBranchAtCutoff_of_fixedTransverseChannelBranch
      hH3
      hClass
      i
      hρ
      hFixed

end

end Euclidean
end Bridge
end PrimeTensor
