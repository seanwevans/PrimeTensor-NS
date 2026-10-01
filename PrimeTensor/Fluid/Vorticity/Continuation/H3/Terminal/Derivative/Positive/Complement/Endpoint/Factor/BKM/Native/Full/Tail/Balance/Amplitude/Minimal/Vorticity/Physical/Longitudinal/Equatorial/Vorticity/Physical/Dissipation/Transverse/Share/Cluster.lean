import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Transverse.Coordinate.Ratio

/-!
# Cluster the transverse polarization share

The preceding checkpoints show that the physical H³ dissipation concentration
is asymptotically transverse to one distinguished longitudinal frequency axis.
There are exactly two transverse normalized coordinate-symbol square shares,
and their sum tends to one.

This file uses compactness of `[0,1]` to extract one transverse square-share
cluster.  Along a strictly increasing subsequence, one fixed transverse
coordinate has limiting normalized square share

    theta in [1/2, 1].

On the same subsequence the positive radial cutoff keeps that literal
transverse Fourier coordinate away from zero, while the longitudinal to
transverse literal coordinate ratio tends to zero.

Thus hypothetical nonextension forces a classified transverse polarization
profile: either `theta = 1` (asymptotically axial inside the equatorial plane)
or `theta < 1` (both transverse directions retain a nontrivial limiting share).
No singular solution is asserted to exist.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Pure transverse-share compactness -/

/--
If the total normalized transverse square tends to one, then on a strictly
increasing subsequence one fixed transverse coordinate has a square-share
limit `theta ∈ [1/2,1]`.
-/
theorem exists_transverseCoordinate_share_cluster_of_transversePolarization
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
            (𝓝 theta) := by
  let S0 : ℕ → ℝ :=
    fun n =>
      ‖h3TerminalNormalizedDerivativeSymbol
          (h3TerminalTransverseCoordinate i (0 : Fin 2))
          (ξ n)‖ ^ 2

  let S1 : ℕ → ℝ :=
    fun n =>
      ‖h3TerminalNormalizedDerivativeSymbol
          (h3TerminalTransverseCoordinate i (1 : Fin 2))
          (ξ n)‖ ^ 2

  have hS0Interval :
      ∀ᶠ n : ℕ in atTop,
        S0 n ∈ Set.Icc (0 : ℝ) 1 := by
    exact
      Filter.Eventually.of_forall
        (fun n => by
          have hNonneg :
              0 ≤
              ‖h3TerminalNormalizedDerivativeSymbol
                  (h3TerminalTransverseCoordinate i (0 : Fin 2))
                  (ξ n)‖ :=
            norm_nonneg _
          have hLe :
              ‖h3TerminalNormalizedDerivativeSymbol
                  (h3TerminalTransverseCoordinate i (0 : Fin 2))
                  (ξ n)‖
                ≤
              1 :=
            norm_h3TerminalNormalizedDerivativeSymbol_le_one
              (h3TerminalTransverseCoordinate i (0 : Fin 2))
              (ξ n)
          have hSq :
              ‖h3TerminalNormalizedDerivativeSymbol
                  (h3TerminalTransverseCoordinate i (0 : Fin 2))
                  (ξ n)‖ ^ 2
                ≤
              (1 : ℝ) ^ 2 :=
            (sq_le_sq₀ hNonneg (by norm_num : (0 : ℝ) ≤ 1)).2 hLe
          dsimp only [S0]
          exact
            ⟨
              sq_nonneg _,
              by simpa only [one_pow] using hSq
            ⟩)

  obtain ⟨c, hc, m, hmMono, hS0Limit⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).tendsto_subseq'
      hS0Interval.frequently

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

  have hS1Eq :
      (fun n => S1 (m n))
        =ᶠ[atTop]
      (fun n =>
        h3TerminalNormalizedTransverseDerivativeSymbolSquareMagnitude
            i (ξ (m n))
          -
        S0 (m n)) := by
    filter_upwards with n
    dsimp only [S0, S1]
    rw [
      normalizedTransverseDerivativeSymbolSquareMagnitude_eq_coordinate_zero_add_one
        i (ξ (m n))
    ]
    ring

  have hS1Limit :
      Tendsto
        (fun n => S1 (m n))
        atTop
        (𝓝 (1 - c)) := by
    have hDiff :=
      hTransverseSub.sub hS0Limit
    simpa only [sub_eq_add_neg] using
      hDiff.congr' hS1Eq.symm

  rcases le_total ((1 : ℝ) / 2) c with hHalf | hBelow

  · refine
      ⟨
        (0 : Fin 2),
        c,
        ⟨hHalf, hc.2⟩,
        m,
        hmMono,
        ?_
      ⟩
    change
      Tendsto
        (fun n =>
          ‖h3TerminalNormalizedDerivativeSymbol
              (h3TerminalTransverseCoordinate i (0 : Fin 2))
              (ξ (m n))‖ ^ 2)
        atTop
        (𝓝 c)
      at hS0Limit
    exact hS0Limit

  · refine
      ⟨
        (1 : Fin 2),
        1 - c,
        ?_,
        m,
        hmMono,
        ?_
      ⟩
    · constructor <;> linarith [hc.1]
    · simpa only [S1] using hS1Limit

/-! ## Clustered physical dissipation polarization branch -/

/--
A single-time physical H³ dissipation concentration branch whose every
supported frequency selection admits one fixed transverse coordinate, a
strictly increasing subsequence, and a limiting normalized square share
`theta ∈ [1/2,1]`.  Along that same subsequence the literal transverse
coordinate stays above the positive radial scale and the longitudinal to
transverse coordinate ratio tends to zero.
-/
def H3TerminalPhysicalDissipationSingleTimeTransverseShareClusterBranchAtCutoff
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

/--
Every fully transverse physical dissipation branch at positive radial cutoff
admits the transverse-share cluster classification on the same concentration
witnesses.
-/
theorem physicalDissipationSingleTimeTransverseShareClusterBranchAtCutoff_of_transverseBranch
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
    H3TerminalPhysicalDissipationSingleTimeTransverseShareClusterBranchAtCutoff
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

  obtain ⟨k, theta, htheta, m, hmMono, hShareLimit⟩ :=
    exists_transverseCoordinate_share_cluster_of_transversePolarization
      i
      ξ
      hSelected.2

  let j : Fin 3 :=
    h3TerminalTransverseCoordinate i k

  have hjNe :
      j ≠ i := by
    dsimp only [j]
    exact
      h3TerminalTransverseCoordinate_ne
        i k

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
    exact
      (tendsto_order.1 hShareLimit).1
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
      hjNe,
      theta,
      htheta,
      m,
      hmMono,
      ?_,
      hCoordinateLower,
      hRatioZero
    ⟩

  simpa only [j] using hShareLimit

/-! ## Necessary clustered polarization under hypothetical nonextension -/

/--
Under the retained raw-Fourier `L²` Cauchy hypothesis, hypothetical
nonextension and one surviving physical-vorticity strong H³ endpoint force a
single-time physical H³ dissipation concentration branch with a fixed
transverse square-share cluster `theta ∈ [1/2,1]`, positive literal transverse
frequency scale, and longitudinal/transverse coordinate-ratio collapse on the
same strict subsequence.
-/
theorem exists_failing_complementary_vorticityComponent_singleTimePhysicalDissipationTransverseShareCluster_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
        H3TerminalPhysicalDissipationSingleTimeTransverseShareClusterBranchAtCutoff
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
    physicalDissipationSingleTimeTransverseShareClusterBranchAtCutoff_of_transverseBranch
      hH3
      hClass
      i
      hρ
      hTransverse

end

end Euclidean
end Bridge
end PrimeTensor
