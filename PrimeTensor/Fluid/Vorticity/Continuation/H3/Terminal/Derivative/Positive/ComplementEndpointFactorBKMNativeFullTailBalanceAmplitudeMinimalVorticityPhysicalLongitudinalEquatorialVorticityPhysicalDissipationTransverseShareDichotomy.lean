import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityPhysicalDissipationTransverseShareCluster

/-!
# Split the transverse polarization cluster into axial and two-channel regimes

The previous checkpoint extracts a fixed transverse coordinate whose normalized
square share converges to

    theta ∈ [1/2, 1].

There are exactly two transverse coordinate channels.  On the same strictly
increasing subsequence their square shares add to the total transverse share,
which converges to one.  Therefore the complementary transverse channel has
limit exactly

    1 - theta.

This gives an exact geometric dichotomy:

* `theta = 1`: the complementary transverse share tends to zero, so the
  concentration is asymptotically axial inside the equatorial plane;
* `theta < 1`: the complementary transverse share tends to the strictly
  positive number `1 - theta`, so both transverse directions survive.

The same subsequence retains the positive literal transverse frequency scale
and the longitudinal/transverse coordinate-ratio collapse.  This remains a
conditional necessary mechanism under hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Complement the two-element transverse channel -/

/-- The other member of `Fin 2`. -/
def h3TerminalOtherTransverseChannel
    (k : Fin 2) : Fin 2 :=
  if k = 0 then 1 else 0

@[simp]
theorem h3TerminalOtherTransverseChannel_zero :
    h3TerminalOtherTransverseChannel (0 : Fin 2) = 1 := by
  simp [h3TerminalOtherTransverseChannel]

@[simp]
theorem h3TerminalOtherTransverseChannel_one :
    h3TerminalOtherTransverseChannel (1 : Fin 2) = 0 := by
  simp [h3TerminalOtherTransverseChannel]

/-- The two transverse channel indices are distinct. -/
theorem h3TerminalOtherTransverseChannel_ne
    (k : Fin 2) :
    h3TerminalOtherTransverseChannel k ≠ k := by
  fin_cases k <;>
    simp [h3TerminalOtherTransverseChannel]

/-- The two actual transverse coordinates indexed by `k` and its complement are
both transverse to `i` and distinct from each other. -/
theorem h3TerminalTransverseCoordinate_other_geometry
    (i : Fin 3)
    (k : Fin 2) :
    h3TerminalTransverseCoordinate i k ≠ i
      ∧
    h3TerminalTransverseCoordinate i (h3TerminalOtherTransverseChannel k) ≠ i
      ∧
    h3TerminalTransverseCoordinate i (h3TerminalOtherTransverseChannel k)
      ≠
    h3TerminalTransverseCoordinate i k := by
  fin_cases i <;>
    fin_cases k <;>
    simp [
      h3TerminalTransverseCoordinate,
      h3TerminalOtherTransverseChannel
    ]

/-- For either choice of transverse channel, its square share plus the square
share of the complementary channel is exactly the total transverse square. -/
theorem normalizedTransverseDerivativeSymbolSquareMagnitude_eq_channel_add_other
    (i : Fin 3)
    (k : Fin 2)
    (ξ : H3FourierPoint3) :
    h3TerminalNormalizedTransverseDerivativeSymbolSquareMagnitude i ξ
      =
    ‖h3TerminalNormalizedDerivativeSymbol
        (h3TerminalTransverseCoordinate i k) ξ‖ ^ 2
      +
    ‖h3TerminalNormalizedDerivativeSymbol
        (h3TerminalTransverseCoordinate i
          (h3TerminalOtherTransverseChannel k)) ξ‖ ^ 2 := by
  fin_cases k <;>
    simpa [h3TerminalOtherTransverseChannel, add_comm] using
      normalizedTransverseDerivativeSymbolSquareMagnitude_eq_coordinate_zero_add_one
        i ξ

/-! ## Exact cluster dichotomy -/

/--
A transverse polarization sequence admits a fixed transverse channel whose
square share tends to `theta ∈ [1/2,1]`; on the same strict subsequence the
other transverse share tends to `1-theta`.  Hence either the first share tends
to one and the other vanishes, or both limiting shares are positive.
-/
theorem exists_transverseCoordinate_share_dichotomy_of_transversePolarization
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
      ∃ theta : ℝ,
        theta ∈ Set.Icc ((1 : ℝ) / 2) 1
          ∧
        ∃ m : ℕ → ℕ,
          StrictMono m
            ∧
          Tendsto
            (fun n =>
              ‖h3TerminalNormalizedDerivativeSymbol
                  (h3TerminalTransverseCoordinate i k)
                  (ξ (m n))‖ ^ 2)
            atTop
            (𝓝 theta)
            ∧
          Tendsto
            (fun n =>
              ‖h3TerminalNormalizedDerivativeSymbol
                  (h3TerminalTransverseCoordinate i
                    (h3TerminalOtherTransverseChannel k))
                  (ξ (m n))‖ ^ 2)
            atTop
            (𝓝 (1 - theta))
            ∧
          (
            (theta = 1
              ∧
            Tendsto
              (fun n =>
                ‖h3TerminalNormalizedDerivativeSymbol
                    (h3TerminalTransverseCoordinate i
                      (h3TerminalOtherTransverseChannel k))
                    (ξ (m n))‖ ^ 2)
              atTop
              (𝓝 0))
              ∨
            (theta < 1
              ∧
            0 < 1 - theta)
          ) := by

  obtain ⟨k, theta, htheta, m, hmMono, hShare⟩ :=
    exists_transverseCoordinate_share_cluster_of_transversePolarization
      i ξ hTransverse

  have hmTop :
      Tendsto m atTop atTop :=
    hmMono.tendsto_atTop

  have hTransverseSub :
      Tendsto
        (fun n =>
          h3TerminalNormalizedTransverseDerivativeSymbolSquareMagnitude
            i (ξ (m n)))
        atTop
        (𝓝 1) :=
    hTransverse.comp hmTop

  have hOtherEq :
      (fun n =>
        ‖h3TerminalNormalizedDerivativeSymbol
            (h3TerminalTransverseCoordinate i
              (h3TerminalOtherTransverseChannel k))
            (ξ (m n))‖ ^ 2)
        =ᶠ[atTop]
      (fun n =>
        h3TerminalNormalizedTransverseDerivativeSymbolSquareMagnitude
            i (ξ (m n))
          -
        ‖h3TerminalNormalizedDerivativeSymbol
            (h3TerminalTransverseCoordinate i k)
            (ξ (m n))‖ ^ 2) := by
    filter_upwards with n
    rw [
      normalizedTransverseDerivativeSymbolSquareMagnitude_eq_channel_add_other
        i k (ξ (m n))
    ]
    ring

  have hOther :
      Tendsto
        (fun n =>
          ‖h3TerminalNormalizedDerivativeSymbol
              (h3TerminalTransverseCoordinate i
                (h3TerminalOtherTransverseChannel k))
              (ξ (m n))‖ ^ 2)
        atTop
        (𝓝 (1 - theta)) := by
    have hDiff :=
      hTransverseSub.sub hShare
    exact
      hDiff.congr'
        hOtherEq.symm

  refine
    ⟨k, theta, htheta, m, hmMono, hShare, hOther, ?_⟩

  by_cases hthetaOne : theta = 1

  · left
    refine ⟨hthetaOne, ?_⟩
    simpa only [hthetaOne, sub_self] using hOther

  · right
    have hthetaLt : theta < 1 :=
      lt_of_le_of_ne htheta.2 hthetaOne
    exact
      ⟨hthetaLt, by linarith⟩

/-! ## Physical branch with classified transverse geometry -/

/--
A single-time physical H³ dissipation concentration branch whose every
supported frequency selection admits a strict subsequence, two fixed distinct
transverse coordinates `j` and `r`, and `theta ∈ [1/2,1]` such that

* the `j`-share tends to `theta`;
* the `r`-share tends to `1-theta`;
* either `theta = 1` and the `r`-share vanishes, or `theta < 1` and
  `1-theta > 0`;
* the selected literal `j` coordinate remains above `rho/(4*pi)` eventually;
* the longitudinal-to-`j` literal coordinate ratio tends to zero.
-/
def H3TerminalPhysicalDissipationSingleTimeTransverseShareDichotomyBranchAtCutoff
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
                  ‖h3TerminalNormalizedDerivativeSymbol j (ξ (m n))‖ ^ 2)
                atTop
                (𝓝 theta)
                ∧
              Tendsto
                (fun n =>
                  ‖h3TerminalNormalizedDerivativeSymbol r (ξ (m n))‖ ^ 2)
                atTop
                (𝓝 (1 - theta))
                ∧
              (
                (theta = 1
                  ∧
                Tendsto
                  (fun n =>
                    ‖h3TerminalNormalizedDerivativeSymbol r (ξ (m n))‖ ^ 2)
                  atTop
                  (𝓝 0))
                  ∨
                (theta < 1
                  ∧
                0 < 1 - theta)
              )
                ∧
              (∀ᶠ n : ℕ in atTop,
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

/-- Every fully transverse physical dissipation branch at positive radial
cutoff admits the exact axial-versus-two-channel transverse-share dichotomy on
one strict subsequence. -/
theorem physicalDissipationSingleTimeTransverseShareDichotomyBranchAtCutoff_of_transverseBranch
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    {ε ρ : ℝ}
    (hρ : 0 < ρ)
    (hBranch :
      H3TerminalPhysicalDissipationSingleTimeTransversePolarizationBranchAtCutoff
        hH3 hClass i ε ρ) :
    H3TerminalPhysicalDissipationSingleTimeTransverseShareDichotomyBranchAtCutoff
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

  obtain
    ⟨k, theta, htheta, m, hmMono, hShare, hOther, hDichotomy⟩ :=
    exists_transverseCoordinate_share_dichotomy_of_transversePolarization
      i ξ hSelected.2

  let j : Fin 3 :=
    h3TerminalTransverseCoordinate i k

  let r : Fin 3 :=
    h3TerminalTransverseCoordinate i
      (h3TerminalOtherTransverseChannel k)

  have hGeometry :=
    h3TerminalTransverseCoordinate_other_geometry i k

  have hjNe : j ≠ i := by
    simpa only [j] using hGeometry.1

  have hrNe : r ≠ i := by
    simpa only [r] using hGeometry.2.1

  have hrjNe : r ≠ j := by
    simpa only [r, j] using hGeometry.2.2

  have hmTop :
      Tendsto m atTop atTop :=
    hmMono.tendsto_atTop

  have hthetaQuarter :
      (1 / 4 : ℝ) < theta := by
    linarith [htheta.1]

  have hShareEventually :
      ∀ᶠ n : ℕ in atTop,
        (1 / 4 : ℝ)
          <
        ‖h3TerminalNormalizedDerivativeSymbol j (ξ (m n))‖ ^ 2 := by
    have hShare' :
        Tendsto
          (fun n =>
            ‖h3TerminalNormalizedDerivativeSymbol j (ξ (m n))‖ ^ 2)
          atTop
          (𝓝 theta) := by
      simpa only [j] using hShare
    exact
      (tendsto_order.1 hShare').1
        (1 / 4 : ℝ)
        hthetaQuarter

  have hCoordinateLower :
      ∀ᶠ n : ℕ in atTop,
        ρ / (4 * Real.pi)
          <
        |(ξ (m n)) (h3AxisOfFin3 j)| := by
    filter_upwards [hShareEventually] with n hnShare

    have hDerivative :
        ρ / 2
          <
        ‖h3FourierDerivativeSymbol j (ξ (m n))‖ := by
      exact
        norm_h3FourierDerivativeSymbol_gt_half_cutoff_of_not_mem_radialBelow_of_normalized_sq_gt_quarter
          j
          hρ
          (hξ (m n)).2
          hnShare

    exact
      abs_fourierCoordinate_gt_cutoff_div_four_pi_of_derivativeSymbol_gt_half_cutoff
        j
        hDerivative

  have hRatioUpper :
      ∀ᶠ n : ℕ in atTop,
        |(ξ (m n)) (h3AxisOfFin3 i)|
            /
          |(ξ (m n)) (h3AxisOfFin3 j)|
          <
        2 * κ (m n) := by
    filter_upwards [hShareEventually] with n hnShare

    exact
      abs_fourierCoordinate_ratio_lt_two_mul_aperture_of_badCone_of_normalized_transverse_sq_gt_quarter
        i
        j
        (hκPos (m n))
        (hξ (m n)).1
        hnShare

  have hκSub :
      Tendsto
        (fun n => κ (m n))
        atTop
        (𝓝 0) :=
    hκTendsto.comp hmTop

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
        hRatioUpper.mono
          (fun n hn => le_of_lt hn)
    · exact hTwoκ

  refine
    ⟨
      hSelected.1,
      hSelected.2,
      j,
      r,
      hjNe,
      hrNe,
      hrjNe,
      theta,
      htheta,
      m,
      hmMono,
      ?_,
      ?_,
      ?_,
      hCoordinateLower,
      hRatioZero
    ⟩

  · simpa only [j] using hShare
  · simpa only [r] using hOther
  · simpa only [j, r] using hDichotomy

/-! ## Necessary dichotomy under hypothetical nonextension -/

/-- Under the retained raw-Fourier `L²` Cauchy hypothesis, hypothetical
nonextension and one surviving physical-vorticity strong H³ endpoint force a
single-time physical H³ dissipation concentration branch whose transverse
polarization is either asymptotically axial or retains two positive transverse
shares. -/
theorem exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationTransverseShareDichotomy_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
        H3TerminalPhysicalDissipationSingleTimeTransverseShareDichotomyBranchAtCutoff
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
    physicalDissipationSingleTimeTransverseShareDichotomyBranchAtCutoff_of_transverseBranch
      hH3
      hClass
      i
      hρ
      hTransverse

end

end Euclidean
end Bridge
end PrimeTensor
