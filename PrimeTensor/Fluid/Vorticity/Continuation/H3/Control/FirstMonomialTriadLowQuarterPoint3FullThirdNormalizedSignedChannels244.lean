import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSignedChannelAlternative244
import Mathlib.Tactic

/-!
# Normalized signed H³ channel excesses: exact additive rate and cofinal sequences

The canonical physical top transport has the EXACT signed split G₃ + 3M₃.
The previous cofinal theorem isolates one of G₃ or 3M₃ below half the
physical energy budget at arbitrarily large thresholds on every tail.

Dividing by the positive, *actual* H³ energy makes the growth-rate meaning
of that obstruction precise. We introduce two scalar channel excesses, each
charged HALF the 24 C₁ sqrt(E) lower-order allowance, HALF the constant 4422,
and ONE copy of physical dissipation. Their SUM, not merely an inequality,
is the canonical full signed rate minus 4422.

Under hypothetical nonextension one fixed channel has unbounded normalized
excess on every strict terminal subtail. In particular, one can select an
explicit indexed sequence of physical times in any given tail along which
that same excess exceeds the natural-number threshold. Consequently a finite
upper bound for BOTH channel excesses on one strict subtail ensures extension.

These statements DO NOT say that G₃ or M₃ is negative; the split normalized
excess still contains the energy-dependent 12 C₁ sqrt(E) allowance. Nor do
these algebraic results provide a uniform upper bound on either channel.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory

noncomputable section
set_option maxHeartbeats 1200000

/-- The 972-slot physical gradient contribution to the excess rate. The
full dissipation is split exactly once between the two channels. -/
noncomputable def h3PathWeightedGradientNormalizedExcess244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) : ℝ :=
  12 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t)) - 2211 -
    (weightedH3CanonicalGradientTransport244
      (h3PathWeightedSpectralState244 u T hH3 t) +
      velocityH3DissipationAt u t) / velocityH3EnergyAt u t

/-- The signed 243-slot interpolation contribution, with the EXACT
physical cyclic multiplicity three retained. -/
noncomputable def h3PathWeightedInterpolationNormalizedExcess244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) : ℝ :=
  12 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t)) - 2211 -
    (3 * weightedH3CanonicalSignedFirstMonomial244
      (h3PathWeightedSpectralState244 u T hH3 t) +
      velocityH3DissipationAt u t) / velocityH3EnergyAt u t

/-- Exact channel decomposition of the physical signed normalized H³ rate,
with NO additional hypotheses, estimates, or discarded signs. -/
theorem h3Path_weightedSignedRate_subBaseline_eq_channelSum244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) :
    h3PathWeightedSignedTopRate244 u T hH3 t - 4422 =
      h3PathWeightedGradientNormalizedExcess244 u T hH3 t +
      h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t := by
  unfold h3PathWeightedSignedTopRate244
    h3PathWeightedGradientNormalizedExcess244
    h3PathWeightedInterpolationNormalizedExcess244
    weightedH3CanonicalFullThirdCommutator244
  ring

/-- The entire continuation remainder is the positive part of the SUM
of the two exact normalized signed channels. -/
theorem h3Path_weightedRemainder_eq_positiveChannelSum244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) :
    h3PathWeightedSignedTopRemainder244 u T hH3 t =
      max 0 (h3PathWeightedGradientNormalizedExcess244 u T hH3 t +
        h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t) := by
  unfold h3PathWeightedSignedTopRemainder244
  rw [h3Path_weightedSignedRate_subBaseline_eq_channelSum244]

/-- At exactly twice the target threshold, the physical gradient half-budget
G₃ gap, divided by E, equals the gradient excess minus the target threshold. -/
theorem h3Path_weightedGradientGap_quotient244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t K : ℝ) :
    (h3PathWeightedThirdSplitBudget244 u t (2 * K) / 2 -
      weightedH3CanonicalGradientTransport244
        (h3PathWeightedSpectralState244 u T hH3 t)) /
      velocityH3EnergyAt u t =
      h3PathWeightedGradientNormalizedExcess244 u T hH3 t - K := by
  have hEpos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hEne : velocityH3EnergyAt u t ≠ 0 := ne_of_gt hEpos
  unfold h3PathWeightedThirdSplitBudget244
    h3PathWeightedGradientNormalizedExcess244
  field_simp [hEne]
  <;> ring

/-- The second half-budget quotient identifies precisely the 3M₃ channel
normalized excess, with the same factor of two in its threshold. -/
theorem h3Path_weightedInterpolationGap_quotient244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t K : ℝ) :
    (h3PathWeightedThirdSplitBudget244 u t (2 * K) / 2 -
      3 * weightedH3CanonicalSignedFirstMonomial244
        (h3PathWeightedSpectralState244 u T hH3 t)) /
      velocityH3EnergyAt u t =
      h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t - K := by
  have hEpos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hEne : velocityH3EnergyAt u t ≠ 0 := ne_of_gt hEpos
  unfold h3PathWeightedThirdSplitBudget244
    h3PathWeightedInterpolationNormalizedExcess244
  field_simp [hEne]
  <;> ring

/-- A gradient half-budget failure at threshold 2K yields actual normalized
gradient excess STRICTLY above K. No sign of G₃ is inferred. -/
theorem h3Path_weightedGradientThreshold_implies_highExcess244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t K : ℝ)
    (hBelow : weightedH3CanonicalGradientTransport244
      (h3PathWeightedSpectralState244 u T hH3 t) <
      h3PathWeightedThirdSplitBudget244 u t (2 * K) / 2) :
    K < h3PathWeightedGradientNormalizedExcess244 u T hH3 t := by
  have hEpos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hGap : 0 <
      (h3PathWeightedThirdSplitBudget244 u t (2 * K) / 2 -
        weightedH3CanonicalGradientTransport244
          (h3PathWeightedSpectralState244 u T hH3 t)) /
        velocityH3EnergyAt u t :=
    div_pos (sub_pos.mpr hBelow) hEpos
  rw [h3Path_weightedGradientGap_quotient244] at hGap
  linarith only [hGap]

/-- Corresponding exact implication for the signed 3M₃ channel. -/
theorem h3Path_weightedInterpolationThreshold_implies_highExcess244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t K : ℝ)
    (hBelow : 3 * weightedH3CanonicalSignedFirstMonomial244
      (h3PathWeightedSpectralState244 u T hH3 t) <
      h3PathWeightedThirdSplitBudget244 u t (2 * K) / 2) :
    K < h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t := by
  have hEpos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hGap : 0 <
      (h3PathWeightedThirdSplitBudget244 u t (2 * K) / 2 -
        3 * weightedH3CanonicalSignedFirstMonomial244
          (h3PathWeightedSpectralState244 u T hH3 t)) /
        velocityH3EnergyAt u t :=
    div_pos (sub_pos.mpr hBelow) hEpos
  rw [h3Path_weightedInterpolationGap_quotient244] at hGap
  linarith only [hGap]

/-- The SAME signed spectral channel carries arbitrarily large normalized
H³ growth-rate excess on every strict physical terminal subtail. The choice
of gradient versus interpolation is OUTSIDE both universal quantifiers. -/
theorem h3Path_weightedThird_fixedNormalizedCofinal244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∀ d : ℝ, d ∈ Set.Ioo a T → ∀ K : ℝ, 0 ≤ K →
      ∃ t : ℝ, t ∈ Set.Ioo d T ∧
        K < h3PathWeightedGradientNormalizedExcess244 u T hH3 t) ∨
    (∀ d : ℝ, d ∈ Set.Ioo a T → ∀ K : ℝ, 0 ≤ K →
      ∃ t : ℝ, t ∈ Set.Ioo d T ∧
        K < h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t) := by
  rcases h3Path_weightedThird_fixedCofinalChannel244
      hH3 hNoExtension hClass with hGradient | hInterpolation
  · left
    intro d hd K hK
    have h2K : 0 ≤ 2 * K := by nlinarith only [hK]
    obtain ⟨t, ht, hBelow⟩ := hGradient d hd (2 * K) h2K
    exact ⟨t, ht,
      h3Path_weightedGradientThreshold_implies_highExcess244
        u T hH3 t K hBelow⟩
  · right
    intro d hd K hK
    have h2K : 0 ≤ 2 * K := by nlinarith only [hK]
    obtain ⟨t, ht, hBelow⟩ := hInterpolation d hd (2 * K) h2K
    exact ⟨t, ht,
      h3Path_weightedInterpolationThreshold_implies_highExcess244
        u T hH3 t K hBelow⟩

/-- Along ANY specified terminal subtail, a single normalized signed
channel admits physical time samples whose normalized excess exceeds n.
This does not claim these chosen times are monotone or that the cubic itself
is negative. The parent fixed-cofinal theorem gives arbitrarily late samples. -/
theorem h3Path_weightedThird_fixedNormalizedNatSequence244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T) :
    (∃ times : ℕ → ℝ, ∀ n : ℕ,
      times n ∈ Set.Ioo d T ∧
      (n : ℝ) < h3PathWeightedGradientNormalizedExcess244
        u T hH3 (times n)) ∨
    (∃ times : ℕ → ℝ, ∀ n : ℕ,
      times n ∈ Set.Ioo d T ∧
      (n : ℝ) < h3PathWeightedInterpolationNormalizedExcess244
        u T hH3 (times n)) := by
  classical
  rcases h3Path_weightedThird_fixedNormalizedCofinal244
      hH3 hNoExtension hClass with hGradient | hInterpolation
  · left
    have hExists : ∀ n : ℕ, ∃ t : ℝ, t ∈ Set.Ioo d T ∧
        (n : ℝ) < h3PathWeightedGradientNormalizedExcess244
          u T hH3 t := by
      intro n
      exact hGradient d hd (n : ℝ) (Nat.cast_nonneg n)
    choose times ht hHigh using hExists
    exact ⟨times, fun n => ⟨ht n, hHigh n⟩⟩
  · right
    have hExists : ∀ n : ℕ, ∃ t : ℝ, t ∈ Set.Ioo d T ∧
        (n : ℝ) < h3PathWeightedInterpolationNormalizedExcess244
          u T hH3 t := by
      intro n
      exact hInterpolation d hd (n : ℝ) (Nat.cast_nonneg n)
    choose times ht hHigh using hExists
    exact ⟨times, fun n => ⟨ht n, hHigh n⟩⟩

/-- A pair of merely FINITE normalized upper bounds on ONE strict terminal
subtail is enough for smooth extension. Neither channel need be nonpositive,
and no uniform-in-time global bound is demanded. Under nonextension the
fixed cofinal channel would exceed its proposed finite bound. -/
theorem h3Path_extension_of_boundedNormalizedSignedChannels244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d Gmax Imax : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T)
    (hGradient : ∀ t : ℝ, t ∈ Set.Ioo d T →
      h3PathWeightedGradientNormalizedExcess244 u T hH3 t ≤ Gmax)
    (hInterpolation : ∀ t : ℝ, t ∈ Set.Ioo d T →
      h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t ≤ Imax) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  rcases h3Path_weightedThird_fixedNormalizedCofinal244
      hH3 hNoExtension hClass with hHighGradient | hHighInterpolation
  · have hK : 0 ≤ max 0 Gmax + 1 := by
      have hL : (0 : ℝ) ≤ max 0 Gmax := le_max_left _ _
      linarith only [hL]
    obtain ⟨t, ht, hHigh⟩ := hHighGradient d hd (max 0 Gmax + 1) hK
    have hUpper := hGradient t ht
    have hMax : Gmax ≤ max 0 Gmax := le_max_right _ _
    linarith only [hHigh, hUpper, hMax]
  · have hK : 0 ≤ max 0 Imax + 1 := by
      have hL : (0 : ℝ) ≤ max 0 Imax := le_max_left _ _
      linarith only [hL]
    obtain ⟨t, ht, hHigh⟩ := hHighInterpolation d hd (max 0 Imax + 1) hK
    have hUpper := hInterpolation t ht
    have hMax : Imax ≤ max 0 Imax := le_max_right _ _
    linarith only [hHigh, hUpper, hMax]

end
end PrimeTensor.FirstMonomialTriad
