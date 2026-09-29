import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeShareRefinedCascade

/-!
# Asymptotic share cluster for the canonical H³ balance amplitude

The exact decomposition

`2 B = 2 D + I`

admits a normalized share coordinate whenever `B > 0`:

`theta_D = D / B`,
`theta_I = I / (2 B)`.

These shares lie in `[0,1]` and satisfy the exact simplex identity

`theta_D + theta_I = 1`.

The preceding refined share cascade freezes one of two cofinal regimes.  Compactness
of `[0,1]` now extracts a subsequence on which the dissipation share converges to
one definite parameter `theta`.  The exact simplex identity forces the imbalance
half-share to converge to `1 - theta` on the same subsequence.

The two structural regimes become quantitative intervals for the cluster share:

* dissipation-scale: `theta ∈ [1/2, 1]`;
* imbalance-scale: `theta ∈ [0, 1/2]`.

This produces a continuous asymptotic partition of the canonical balance amplitude
without preferring either mechanism and without introducing an index-dependent rate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Fraction of the canonical balance amplitude occupied by full H³ dissipation. -/
def h3TerminalBalanceDissipationShareAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : ℝ :=
  velocityH3DissipationAt u t /
    h3TerminalBalanceAmplitudeAt u t

/-- Half-imbalance fraction of the canonical balance amplitude.  The factor two
matches the exact identity `2 B = 2 D + I`. -/
def h3TerminalBalanceImbalanceHalfShareAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : ℝ :=
  h3TerminalBalanceImbalanceAt u t /
    (2 * h3TerminalBalanceAmplitudeAt u t)

/-- At every strict class time with positive canonical amplitude, dissipation and
half-imbalance form an exact two-coordinate simplex. -/
theorem h3TerminalBalanceShares_mem_Icc_and_sum_eq_one
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hBPos : 0 < h3TerminalBalanceAmplitudeAt u t) :
    h3TerminalBalanceDissipationShareAt u t ∈ Set.Icc (0 : ℝ) 1
      ∧
    h3TerminalBalanceImbalanceHalfShareAt u t ∈ Set.Icc (0 : ℝ) 1
      ∧
    h3TerminalBalanceDissipationShareAt u t
        + h3TerminalBalanceImbalanceHalfShareAt u t
      = 1 := by
  have hDNonneg :
      0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t

  have hDLeB :
      velocityH3DissipationAt u t
        ≤ h3TerminalBalanceAmplitudeAt u t :=
    velocityH3DissipationAt_le_h3TerminalBalanceAmplitudeAt
      hH3 hClass ht

  have hINonneg :
      0 ≤ h3TerminalBalanceImbalanceAt u t :=
    h3TerminalBalanceImbalanceAt_nonneg u t

  have hExact :=
    two_mul_h3TerminalBalanceAmplitudeAt_eq_two_mul_dissipation_add_imbalance
      hH3 hClass ht

  have hILeTwoB :
      h3TerminalBalanceImbalanceAt u t
        ≤ 2 * h3TerminalBalanceAmplitudeAt u t := by
    linarith

  have hTwoBPos :
      0 < 2 * h3TerminalBalanceAmplitudeAt u t := by
    positivity

  have hDShareNonneg :
      0 ≤ h3TerminalBalanceDissipationShareAt u t := by
    unfold h3TerminalBalanceDissipationShareAt
    exact div_nonneg hDNonneg hBPos.le

  have hDShareLeOne :
      h3TerminalBalanceDissipationShareAt u t ≤ 1 := by
    unfold h3TerminalBalanceDissipationShareAt
    exact (div_le_one hBPos).2 hDLeB

  have hIShareNonneg :
      0 ≤ h3TerminalBalanceImbalanceHalfShareAt u t := by
    unfold h3TerminalBalanceImbalanceHalfShareAt
    exact div_nonneg hINonneg hTwoBPos.le

  have hIShareLeOne :
      h3TerminalBalanceImbalanceHalfShareAt u t ≤ 1 := by
    unfold h3TerminalBalanceImbalanceHalfShareAt
    exact (div_le_one hTwoBPos).2 hILeTwoB

  have hBNe :
      h3TerminalBalanceAmplitudeAt u t ≠ 0 :=
    ne_of_gt hBPos

  have hSum :
      h3TerminalBalanceDissipationShareAt u t
          + h3TerminalBalanceImbalanceHalfShareAt u t
        = 1 := by
    unfold h3TerminalBalanceDissipationShareAt
      h3TerminalBalanceImbalanceHalfShareAt
    calc
      velocityH3DissipationAt u t /
            h3TerminalBalanceAmplitudeAt u t
          + h3TerminalBalanceImbalanceAt u t /
            (2 * h3TerminalBalanceAmplitudeAt u t)
          =
        (2 * velocityH3DissipationAt u t
            + h3TerminalBalanceImbalanceAt u t) /
          (2 * h3TerminalBalanceAmplitudeAt u t) := by
            field_simp [hBNe]
      _ =
        (2 * h3TerminalBalanceAmplitudeAt u t) /
          (2 * h3TerminalBalanceAmplitudeAt u t) := by
            rw [← hExact]
      _ = 1 := by
        exact div_self (by positivity)

  exact
    ⟨
      ⟨hDShareNonneg, hDShareLeOne⟩,
      ⟨hIShareNonneg, hIShareLeOne⟩,
      hSum
    ⟩

/-- Dissipation-scale times force the dissipation share into `[1/2,1]`. -/
theorem h3TerminalBalanceDissipationShareAt_mem_Icc_of_dissipationScale
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hBPos : 0 < h3TerminalBalanceAmplitudeAt u t)
    (hScale : H3TerminalBalanceAmplitudeDissipationScaleAt u t) :
    h3TerminalBalanceDissipationShareAt u t ∈
      Set.Icc ((1 : ℝ) / 2) 1 := by
  have hCorridor :=
    h3TerminalBalanceAmplitude_dissipationShare_half_corridor
      hH3 hClass ht hScale

  have hLower :
      (1 : ℝ) / 2
        ≤ h3TerminalBalanceDissipationShareAt u t := by
    unfold h3TerminalBalanceDissipationShareAt
    apply (le_div_iff₀ hBPos).2
    nlinarith [hCorridor.1]

  have hUpper :
      h3TerminalBalanceDissipationShareAt u t ≤ 1 := by
    unfold h3TerminalBalanceDissipationShareAt
    exact (div_le_one hBPos).2 hCorridor.2.1

  exact ⟨hLower, hUpper⟩

/-- Imbalance-scale times force the dissipation share into `[0,1/2]`. -/
theorem h3TerminalBalanceDissipationShareAt_mem_Icc_of_imbalanceScale
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hBPos : 0 < h3TerminalBalanceAmplitudeAt u t)
    (hScale : H3TerminalBalanceAmplitudeImbalanceScaleAt u t) :
    h3TerminalBalanceDissipationShareAt u t ∈
      Set.Icc (0 : ℝ) ((1 : ℝ) / 2) := by
  have hCorridor :=
    h3TerminalBalanceAmplitude_imbalanceShare_half_corridor
      hH3 hClass ht hScale

  have hDNonneg :
      0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t

  have hLower :
      0 ≤ h3TerminalBalanceDissipationShareAt u t := by
    unfold h3TerminalBalanceDissipationShareAt
    exact div_nonneg hDNonneg hBPos.le

  have hUpper :
      h3TerminalBalanceDissipationShareAt u t
        ≤ (1 : ℝ) / 2 := by
    unfold h3TerminalBalanceDissipationShareAt
    apply (div_le_iff₀ hBPos).2
    nlinarith [hCorridor.1]

  exact ⟨hLower, hUpper⟩

/-- The amplitude/intrinsic cascade together with an asymptotic partition of
canonical balance amplitude into dissipation share `theta` and imbalance
half-share `1 - theta`. -/
def H3TerminalBalanceShareClusterAlong
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ)
    (τ : ℕ → ℝ)
    (theta : ℝ) : Prop :=
  H3TerminalBalanceAmplitudeAndIntrinsicCascadeAlong u T τ
    ∧
  Tendsto
      (fun n : ℕ =>
        h3TerminalBalanceDissipationShareAt u (τ n))
      atTop (𝓝 theta)
    ∧
  Tendsto
      (fun n : ℕ =>
        h3TerminalBalanceImbalanceHalfShareAt u (τ n))
      atTop (𝓝 (1 - theta))

/-- A dissipation-scale terminal cluster has an asymptotic dissipation share in
`[1/2,1]`. -/
def H3TerminalDissipationShareClusterWitness
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T b : ℝ) : Prop :=
  ∃ theta : ℝ,
    theta ∈ Set.Icc ((1 : ℝ) / 2) 1
      ∧
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ,
        τ n ∈ Set.Ioo b T
          ∧
        H3TerminalBalanceAmplitudePolynomialRatesAt u T b (τ n)
          ∧
        H3TerminalBalanceAmplitudeDissipationScaleAt u (τ n))
        ∧
      H3TerminalBalanceShareClusterAlong u T τ theta

/-- An imbalance-scale terminal cluster has an asymptotic dissipation share in
`[0,1/2]`; the transferred imbalance cascade is retained. -/
def H3TerminalImbalanceShareClusterWitness
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T b : ℝ) : Prop :=
  ∃ theta : ℝ,
    theta ∈ Set.Icc (0 : ℝ) ((1 : ℝ) / 2)
      ∧
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ,
        τ n ∈ Set.Ioo b T
          ∧
        H3TerminalBalanceAmplitudePolynomialRatesAt u T b (τ n)
          ∧
        H3TerminalBalanceAmplitudeImbalanceScaleAt u (τ n)
          ∧
        H3TerminalBalanceImbalancePolynomialRatesAt u T b (τ n))
        ∧
      H3TerminalBalanceShareClusterAlong u T τ theta
        ∧
      H3TerminalBalanceImbalanceCascadeAlong u T τ

private theorem imbalanceHalfShare_tendsto_one_sub_of_dissipationShare_tendsto
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCascade : H3TerminalBalanceAmplitudeAndIntrinsicCascadeAlong u T τ)
    (hShare :
      Tendsto
        (fun n : ℕ => h3TerminalBalanceDissipationShareAt u (τ n))
        atTop (𝓝 theta)) :
    Tendsto
      (fun n : ℕ => h3TerminalBalanceImbalanceHalfShareAt u (τ n))
      atTop (𝓝 (1 - theta)) := by
  have hBPos :
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalBalanceAmplitudeAt u (τ n) :=
    hCascade.2.1.eventually
      (eventually_gt_atTop (0 : ℝ))

  have hEq :
      ∀ᶠ n : ℕ in atTop,
        h3TerminalBalanceImbalanceHalfShareAt u (τ n)
          =
        1 - h3TerminalBalanceDissipationShareAt u (τ n) := by
    filter_upwards [hBPos] with n hn
    have hSimplex :=
      h3TerminalBalanceShares_mem_Icc_and_sum_eq_one
        hH3 hClass (hAt n) hn
    linarith [hSimplex.2.2]

  have hOneSub :
      Tendsto
        (fun n : ℕ =>
          (1 : ℝ) - h3TerminalBalanceDissipationShareAt u (τ n))
        atTop
        (𝓝 ((1 : ℝ) - theta)) :=
    tendsto_const_nhds.sub hShare

  have hEq' :
      ∀ᶠ n : ℕ in atTop,
        (1 : ℝ) - h3TerminalBalanceDissipationShareAt u (τ n)
          =
        h3TerminalBalanceImbalanceHalfShareAt u (τ n) := by
    filter_upwards [hEq] with n hn
    exact hn.symm

  exact hOneSub.congr' hEq'

/-- Under hypothetical nonextension, the balance-amplitude share admits a
cofinal asymptotic cluster.  Dissipation-scale clusters have `theta ≥ 1/2`;
imbalance-scale clusters have `theta ≤ 1/2`. -/
theorem exists_fixed_balanceAmplitudeShare_cluster_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    H3TerminalDissipationShareClusterWitness u T b
      ∨
    H3TerminalImbalanceShareClusterWitness u T b := by
  rcases
    exists_fixed_balanceAmplitudeShare_refinedCascade_of_noH3PathExtension
      hH3 hNoExtension hClass hb
    with hDissipation | hImbalance

  · left
    rcases hDissipation with ⟨τ, hData, hCascade, _hCorridor⟩

    have hBPos :
        ∀ᶠ n : ℕ in atTop,
          0 < h3TerminalBalanceAmplitudeAt u (τ n) :=
      hCascade.2.1.eventually
        (eventually_gt_atTop (0 : ℝ))

    have hShareInterval :
        ∀ᶠ n : ℕ in atTop,
          h3TerminalBalanceDissipationShareAt u (τ n) ∈
            Set.Icc ((1 : ℝ) / 2) 1 := by
      filter_upwards [hBPos] with n hn
      have htClass : τ n ∈ Set.Ioo a T :=
        ⟨
          lt_trans hb.1 (hData n).1.1,
          (hData n).1.2
        ⟩
      exact
        h3TerminalBalanceDissipationShareAt_mem_Icc_of_dissipationScale
          hH3 hClass htClass hn (hData n).2.2.2

    obtain ⟨theta, hTheta, k, hkMono, hShareLimit⟩ :=
      (isCompact_Icc : IsCompact (Set.Icc ((1 : ℝ) / 2) 1)).tendsto_subseq'
        hShareInterval.frequently

    have hkTop : Tendsto k atTop atTop :=
      hkMono.tendsto_atTop

    have hTau :
        Tendsto (fun n : ℕ => τ (k n)) atTop (𝓝 T) :=
      hCascade.1.comp hkTop

    have hAt :
        ∀ n : ℕ,
          τ (k n) ∈ Set.Ioo a T := by
      intro n
      exact
        ⟨
          lt_trans hb.1 (hData (k n)).1.1,
          (hData (k n)).1.2
        ⟩

    have hCascade' :
        H3TerminalBalanceAmplitudeAndIntrinsicCascadeAlong
          u T (fun n : ℕ => τ (k n)) :=
      h3TerminalBalanceAmplitudeAndIntrinsicCascadeAlong_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hTau
        (fun n => (hData (k n)).1.2)

    have hImbalanceLimit :
        Tendsto
          (fun n : ℕ =>
            h3TerminalBalanceImbalanceHalfShareAt u (τ (k n)))
          atTop
          (𝓝 (1 - theta)) :=
      imbalanceHalfShare_tendsto_one_sub_of_dissipationShare_tendsto
        hH3 hClass hAt hCascade' hShareLimit

    refine
      ⟨
        theta,
        hTheta,
        (fun n : ℕ => τ (k n)),
        ?_,
        hCascade',
        hShareLimit,
        hImbalanceLimit
      ⟩

    intro n
    exact
      ⟨
        (hData (k n)).1,
        (hData (k n)).2.2.1,
        (hData (k n)).2.2.2
      ⟩

  · right
    rcases hImbalance with
      ⟨τ, hData, hCascade, hRefined, _hImbalanceCascade⟩

    have hBPos :
        ∀ᶠ n : ℕ in atTop,
          0 < h3TerminalBalanceAmplitudeAt u (τ n) :=
      hCascade.2.1.eventually
        (eventually_gt_atTop (0 : ℝ))

    have hShareInterval :
        ∀ᶠ n : ℕ in atTop,
          h3TerminalBalanceDissipationShareAt u (τ n) ∈
            Set.Icc (0 : ℝ) ((1 : ℝ) / 2) := by
      filter_upwards [hBPos] with n hn
      have htClass : τ n ∈ Set.Ioo a T :=
        ⟨
          lt_trans hb.1 (hData n).1.1,
          (hData n).1.2
        ⟩
      exact
        h3TerminalBalanceDissipationShareAt_mem_Icc_of_imbalanceScale
          hH3 hClass htClass hn (hData n).2.2.2

    obtain ⟨theta, hTheta, k, hkMono, hShareLimit⟩ :=
      (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) ((1 : ℝ) / 2))).tendsto_subseq'
        hShareInterval.frequently

    have hkTop : Tendsto k atTop atTop :=
      hkMono.tendsto_atTop

    have hTau :
        Tendsto (fun n : ℕ => τ (k n)) atTop (𝓝 T) :=
      hCascade.1.comp hkTop

    have hAt :
        ∀ n : ℕ,
          τ (k n) ∈ Set.Ioo a T := by
      intro n
      exact
        ⟨
          lt_trans hb.1 (hData (k n)).1.1,
          (hData (k n)).1.2
        ⟩

    have hCascade' :
        H3TerminalBalanceAmplitudeAndIntrinsicCascadeAlong
          u T (fun n : ℕ => τ (k n)) :=
      h3TerminalBalanceAmplitudeAndIntrinsicCascadeAlong_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hTau
        (fun n => (hData (k n)).1.2)

    have hImbalanceLimit :
        Tendsto
          (fun n : ℕ =>
            h3TerminalBalanceImbalanceHalfShareAt u (τ (k n)))
          atTop
          (𝓝 (1 - theta)) :=
      imbalanceHalfShare_tendsto_one_sub_of_dissipationShare_tendsto
        hH3 hClass hAt hCascade' hShareLimit

    have hImbalanceCascade' :
        H3TerminalBalanceImbalanceCascadeAlong
          u T (fun n : ℕ => τ (k n)) :=
      h3TerminalBalanceImbalanceCascadeAlong_of_imbalanceScale
        hClass
        hAt
        (fun n => (hData (k n)).2.2.2)
        hCascade'

    refine
      ⟨
        theta,
        hTheta,
        (fun n : ℕ => τ (k n)),
        ?_,
        ⟨hCascade', hShareLimit, hImbalanceLimit⟩,
        hImbalanceCascade'
      ⟩

    intro n
    exact
      ⟨
        (hData (k n)).1,
        (hData (k n)).2.2.1,
        (hData (k n)).2.2.2,
        (hRefined (k n)).2.2.2
      ⟩

/-- Neutral form: either smooth continuation exists or the canonical balance
amplitude admits one of the two asymptotic share clusters. -/
theorem smoothContinuationExtension_or_exists_fixed_balanceAmplitudeShare_cluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      H3TerminalDissipationShareClusterWitness u T b
        ∨
      H3TerminalImbalanceShareClusterWitness u T b
    ) := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact
      Or.inr
        (exists_fixed_balanceAmplitudeShare_cluster_of_noH3PathExtension
          hH3 hExtension hClass hb)

/-- Canonical midpoint-anchor specialization of the asymptotic share cluster. -/
theorem exists_fixed_balanceAmplitudeShare_cluster_midpoint_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    H3TerminalDissipationShareClusterWitness
        u T (h3BKMKineticTailMidpoint a T)
      ∨
    H3TerminalImbalanceShareClusterWitness
        u T (h3BKMKineticTailMidpoint a T) := by
  exact
    exists_fixed_balanceAmplitudeShare_cluster_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)

end

end Euclidean
end Bridge
end PrimeTensor
