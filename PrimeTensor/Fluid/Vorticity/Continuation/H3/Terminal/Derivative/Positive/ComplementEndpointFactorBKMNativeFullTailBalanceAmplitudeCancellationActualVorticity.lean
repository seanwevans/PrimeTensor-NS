import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeCancellationBKM
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ActualVorticitySynchronization

/-!
# Actual vorticity on the cancellation share cluster

In the below-half cancellation regime, the preceding orientation theorem leaves
one neutral fork.  If the energy derivative is positive on the frozen
subsequence, the terminal BKM estimate applies there.  This file specializes
that estimate to the minimal common actual-vorticity envelope and removes the
remaining external envelope parameter.

The characteristic frequency already diverges on the same balance-share
cluster.  Therefore the minimal vorticity envelope diverges there as well.
At each selected time, an actual vorticity component exceeds the minimal
envelope minus one, so choosing only spatial points (not new times) yields an
actual-vorticity amplitude tending to `+∞` on the same `theta` witness.

The alternative cancellation orientation, with positive transport derivative,
is retained unchanged.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Maximum magnitude of the three actual logged-vorticity components at one
space-time point. -/
def h3ActualVorticityMaxAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (x : Point3) : ℝ :=
  max
    (abs
      (realVorticityX
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        t x))
    (max
      (abs
        (realVorticityY
          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
          t x))
      (abs
        (realVorticityZ
          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
          t x)))

/-- The fixed denominator in the linear BKM lower bound is strictly positive. -/
theorem h3TerminalBalanceBKMLinearDenominator_pos
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b : ℝ) :
    0 < h3TerminalBalanceBKMLinearDenominator u b := by
  have hE0Nonneg :
      0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b

  have hCPos :
      0 < 4 + 3 * velocityH3Energy0At u b := by
    linarith

  have hBNonneg :
      0 ≤
        h3BKMCanonicalSelectedLogGradientConstant
          (Real.sqrt (velocityH3Energy0At u b)) :=
    h3BKMCanonicalSelectedLogGradientConstant_nonneg
      (Real.sqrt_nonneg _)

  unfold h3TerminalBalanceBKMLinearDenominator
  exact
    mul_pos
      (mul_pos
        (mul_pos hCPos (by norm_num))
        (by linarith))
      (by
        have hEnergyPlus :
            0 < velocityH3Energy0At u b + 1 := by
          linarith
        have hLeft :
            0 <
              (4 + 3 * velocityH3Energy0At u b) *
                (velocityH3Energy0At u b + 1) :=
          mul_pos hCPos hEnergyPlus
        linarith)

/-- On a share-cluster sequence with eventually positive H³ energy derivative,
the minimal common actual-vorticity envelope diverges on that same sequence. -/
theorem h3MinimalVorticityEnvelopeAt_tendsto_atTop_of_balanceShareCluster_positiveGrowth
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hGrowth :
      ∀ᶠ n : ℕ in atTop,
        0 < deriv (velocityH3EnergyAt u) (τ n)) :
    Tendsto
      (fun n : ℕ => h3MinimalVorticityEnvelopeAt u (τ n))
      atTop atTop := by
  have hg :
      ∀ s : ℝ,
        s ∈ Set.Ioo b T →
          VorticityEnvelope
            u (h3MinimalVorticityEnvelopeAt u) s := by
    intro s hs
    have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
      ⟨
        lt_trans
          (lt_trans hClass.terminal_start.1 hb.1)
          hs.1,
        hs.2
      ⟩
    exact
      vorticityEnvelope_h3MinimalVorticityEnvelopeAt
        hH3 hsAbs

  have hBKM :
      ∀ᶠ n : ℕ in atTop,
        (2 * h3TopCharacteristicFrequencyAt u (τ n)) /
            h3TerminalBalanceBKMLinearDenominator u b
          <
        1 + |h3MinimalVorticityEnvelopeAt u (τ n)| :=
    eventually_balanceShareCluster_characteristicFrequency_linear_lt_vorticityEnvelope_of_positiveGrowth
      hH3 hNoExtension hClass hb hg hAt hCluster hGrowth

  have hIntrinsic :
      H3TerminalIntrinsicCascadeAlong u T τ :=
    hCluster.1.2.2.2.2

  rcases hIntrinsic with
    ⟨_, _, _, _, _, _, _, _, _, hFrequency, _, _, _, _, _⟩

  have hDPos :
      0 < h3TerminalBalanceBKMLinearDenominator u b :=
    h3TerminalBalanceBKMLinearDenominator_pos u b

  refine tendsto_atTop.2 ?_
  intro M

  by_cases hM : M ≤ 0
  · exact
      Eventually.of_forall
        (fun n =>
          le_trans hM
            (h3MinimalVorticityEnvelopeAt_nonneg_of_h3Path
              hH3
              ⟨
                lt_trans hClass.terminal_start.1 (hAt n).1,
                (hAt n).2
              ⟩))

  · have hMPos : 0 < M := lt_of_not_ge hM

    let R : ℝ :=
      h3TerminalBalanceBKMLinearDenominator u b * (M + 2)

    have hFrequencyEventually :
        ∀ᶠ n : ℕ in atTop,
          R ≤ h3TopCharacteristicFrequencyAt u (τ n) :=
      hFrequency.eventually (eventually_ge_atTop R)

    filter_upwards [hBKM, hFrequencyEventually] with n hBKMn hFrequencyN

    have hEnvelopeNonneg :
        0 ≤ h3MinimalVorticityEnvelopeAt u (τ n) :=
      h3MinimalVorticityEnvelopeAt_nonneg_of_h3Path
        hH3
        ⟨
          lt_trans hClass.terminal_start.1 (hAt n).1,
          (hAt n).2
        ⟩

    have hFrequencyLower :
        h3TerminalBalanceBKMLinearDenominator u b * (M + 2)
          ≤ h3TopCharacteristicFrequencyAt u (τ n) := by
      simpa only [R] using hFrequencyN

    have hThreshold :
        M + 1
          <
        (2 * h3TopCharacteristicFrequencyAt u (τ n)) /
          h3TerminalBalanceBKMLinearDenominator u b := by
      apply (lt_div_iff₀ hDPos).2
      have hPositiveMargin :
          0 <
            h3TerminalBalanceBKMLinearDenominator u b * (M + 3) :=
        mul_pos hDPos (by linarith)
      nlinarith

    rw [abs_of_nonneg hEnvelopeNonneg] at hBKMn
    have hMEnvelope :
        M < h3MinimalVorticityEnvelopeAt u (τ n) := by
      linarith

    exact le_of_lt hMEnvelope

/-- Divergence of the minimal common envelope produces actual spatial witnesses
at the same selected times whose vorticity amplitude diverges. -/
theorem exists_actualVorticityMax_tendsto_atTop_of_minimalEnvelope_tendsto_atTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {τ : ℕ → ℝ}
    (hEnvelope :
      Tendsto
        (fun n : ℕ => h3MinimalVorticityEnvelopeAt u (τ n))
        atTop atTop) :
    ∃ y : ℕ → Point3,
      Tendsto
        (fun n : ℕ => h3ActualVorticityMaxAt u (τ n) (y n))
        atTop atTop := by
  have hWitness :
      ∀ n : ℕ,
        ∃ x : Point3,
          h3MinimalVorticityEnvelopeAt u (τ n) - 1
            < h3ActualVorticityMaxAt u (τ n) x := by
    intro n
    obtain ⟨x, hx⟩ :=
      exists_actualVorticityComponent_gt_of_lt_h3MinimalVorticityEnvelopeAt
        (u := u)
        (t := τ n)
        (M := h3MinimalVorticityEnvelopeAt u (τ n) - 1)
        (by linarith)

    refine ⟨x, ?_⟩
    rcases hx with hX | hY | hZ
    · exact
        lt_of_lt_of_le hX
          (le_max_left _ _)
    · exact
        lt_of_lt_of_le hY
          (le_trans
            (le_max_left _ _)
            (le_max_right _ _))
    · exact
        lt_of_lt_of_le hZ
          (le_trans
            (le_max_right _ _)
            (le_max_right _ _))

  choose y hy using hWitness
  refine ⟨y, ?_⟩
  refine tendsto_atTop.2 ?_
  intro M

  have hEnvelopeEventually :
      ∀ᶠ n : ℕ in atTop,
        M + 1 ≤ h3MinimalVorticityEnvelopeAt u (τ n) :=
    hEnvelope.eventually (eventually_ge_atTop (M + 1))

  filter_upwards [hEnvelopeEventually] with n hn
  have hLower :
      M ≤ h3MinimalVorticityEnvelopeAt u (τ n) - 1 := by
    linarith
  exact le_trans hLower (le_of_lt (hy n))

/-- In the below-half cancellation regime, freeze the orientation on a cofinal
subsequence.  The positive-energy-growth orientation now carries divergent
minimal actual-vorticity envelope and divergent actual vorticity at selected
spatial points on exactly the same time sequence.  The positive-transport
orientation remains the neutral alternative. -/
theorem exists_fixed_balanceCancellationOrientation_actualVorticitySubsequence_of_shareCluster_lt_half
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b theta : ℝ}
    {τ : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hAt : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCluster : H3TerminalBalanceShareClusterAlong u T τ theta)
    (hTheta : theta < (1 : ℝ) / 2) :
    ∃ k : ℕ → ℕ,
      StrictMono k
        ∧
      H3TerminalBalanceShareClusterAlong
        u T (fun n : ℕ => τ (k n)) theta
        ∧
      (
        (
          (∀ n : ℕ,
            h3TerminalBalanceSubordinateChannelAt u (τ (k n))
                = - deriv (velocityH3EnergyAt u) (τ (k n))
              ∧
            h3TerminalBalanceAmplitudeAt u (τ (k n))
                = - velocityH3TransportDerivativeAt u (τ (k n)))
            ∧
          (∀ᶠ n : ℕ in atTop,
            0 < deriv (velocityH3EnergyAt u) (τ (k n)))
            ∧
          Tendsto
            (fun n : ℕ =>
              h3MinimalVorticityEnvelopeAt u (τ (k n)))
            atTop atTop
            ∧
          ∃ y : ℕ → Point3,
            Tendsto
              (fun n : ℕ =>
                h3ActualVorticityMaxAt u (τ (k n)) (y n))
              atTop atTop
        )
          ∨
        (
          (∀ n : ℕ,
            h3TerminalBalanceSubordinateChannelAt u (τ (k n))
                = - velocityH3TransportDerivativeAt u (τ (k n))
              ∧
            h3TerminalBalanceAmplitudeAt u (τ (k n))
                = - deriv (velocityH3EnergyAt u) (τ (k n)))
            ∧
          ∀ᶠ n : ℕ in atTop,
            0 < velocityH3TransportDerivativeAt u (τ (k n))
        )
      ) := by
  have hg :
      ∀ s : ℝ,
        s ∈ Set.Ioo b T →
          VorticityEnvelope
            u (h3MinimalVorticityEnvelopeAt u) s := by
    intro s hs
    exact
      vorticityEnvelope_h3MinimalVorticityEnvelopeAt
        hH3
        ⟨
          lt_trans
            (lt_trans hClass.terminal_start.1 hb.1)
            hs.1,
          hs.2
        ⟩

  obtain ⟨k, hKMono, hClusterSub, hOrientation⟩ :=
    exists_fixed_balanceCancellationOrientation_bkmSubsequence_of_shareCluster_lt_half
      hH3
      hNoExtension
      hClass
      hb
      hg
      hAt
      hCluster
      hTheta

  have hAtSub :
      ∀ n : ℕ,
        τ (k n) ∈ Set.Ioo a T :=
    fun n => hAt (k n)

  rcases hOrientation with hGrowth | hTransport
  · rcases hGrowth with ⟨hIdentities, hGrowthPositive, _hBKM⟩

    have hEnvelope :
        Tendsto
          (fun n : ℕ =>
            h3MinimalVorticityEnvelopeAt u (τ (k n)))
          atTop atTop :=
      h3MinimalVorticityEnvelopeAt_tendsto_atTop_of_balanceShareCluster_positiveGrowth
        hH3
        hNoExtension
        hClass
        hb
        hAtSub
        hClusterSub
        hGrowthPositive

    obtain ⟨y, hActual⟩ :=
      exists_actualVorticityMax_tendsto_atTop_of_minimalEnvelope_tendsto_atTop
        hEnvelope

    exact
      ⟨
        k,
        hKMono,
        hClusterSub,
        Or.inl
          ⟨
            hIdentities,
            hGrowthPositive,
            hEnvelope,
            y,
            hActual
          ⟩
      ⟩

  · exact
      ⟨
        k,
        hKMono,
        hClusterSub,
        Or.inr hTransport
      ⟩

end

end Euclidean
end Bridge
end PrimeTensor
