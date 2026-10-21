import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalCanonicalSignedRate244
import Mathlib.Tactic

/-!
# Cofinal signed-channel obstruction for the canonical physical H³ cubic

The exact physical-to-weighted-spectral identification gives
  C₃(U) = G₃(U) + 3 M₃(U).
If the original physical H³ path cannot extend, the signed spectral
adversity inequality occurs above every normalized threshold, arbitrarily
late. Splitting the lower-order allowance and dissipation equally between
G₃ and 3M₃ yields a genuine TWO-CHANNEL obstruction.

A finite cofinality lemma upgrades the pointwise disjunction: one of the
two channels (the same channel) must carry arbitrarily high threshold
failures on every strict terminal subtail. Importantly, this does NOT say
either cubic contribution is negative. The threshold contains the positive
24 C₁ sqrt(E) E allowance, and no unproved signed coercivity is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory

noncomputable section
set_option maxHeartbeats 1200000

/-- Remaining cubic budget after paying the exact 4422+M normalized
threshold and twice the physical dissipation. -/
noncomputable def h3PathWeightedThirdSplitBudget244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t M : ℝ) : ℝ :=
  24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t -
    (4422 + M) * velocityH3EnergyAt u t -
    2 * velocityH3DissipationAt u t

/-- Larger requested growth excess decreases the available budget.
Only positivity of the original H³ energy is used. -/
theorem h3PathWeightedThirdSplitBudget_antitone244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t M N : ℝ) (hMN : M ≤ N) :
    h3PathWeightedThirdSplitBudget244 u t N ≤
      h3PathWeightedThirdSplitBudget244 u t M := by
  have hE : 0 ≤ velocityH3EnergyAt u t :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_velocityH3EnergyAt u t)
  have hProd : 0 ≤ (N - M) * velocityH3EnergyAt u t :=
    mul_nonneg (sub_nonneg.mpr hMN) hE
  unfold h3PathWeightedThirdSplitBudget244
  nlinarith only [hProd]

/-- Any late physical adverse event is carried by the exact 972-gradient
channel or by three times the signed 243-slot interpolation channel.
The equal split of the budget is an algebraic partition, not a bound
on either channel. -/
theorem h3Path_weightedThirdSplit_adverse_witness244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T)
    (hM : 0 ≤ M) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      (weightedH3CanonicalGradientTransport244
          (h3PathWeightedSpectralState244 u T hH3 t) <
        h3PathWeightedThirdSplitBudget244 u t M / 2 ∨
       3 * weightedH3CanonicalSignedFirstMonomial244
          (h3PathWeightedSpectralState244 u T hH3 t) <
        h3PathWeightedThirdSplitBudget244 u t M / 2) := by
  obtain ⟨t, ht, hAdverse⟩ :=
    h3Path_weightedFullThird_adverse_witness_of_noExtension244
      hH3 hNoExtension hClass hd hM
  refine ⟨t, ht, ?_⟩
  have hSum :
      weightedH3CanonicalGradientTransport244
          (h3PathWeightedSpectralState244 u T hH3 t) +
        3 * weightedH3CanonicalSignedFirstMonomial244
          (h3PathWeightedSpectralState244 u T hH3 t) <
        h3PathWeightedThirdSplitBudget244 u t M := by
    unfold weightedH3CanonicalFullThirdCommutator244 at hAdverse
    unfold h3PathWeightedThirdSplitBudget244
    linarith only [hAdverse]
  by_contra hNone
  push_neg at hNone
  linarith only [hSum, hNone.1, hNone.2]

/-- Two monotonically thresholded predicates cannot alternate their
entire late-time cofinality away: if their union witnesses every (tail,
threshold) pair, one FIXED predicate witnesses every such pair. -/
theorem h3_twoChannel_cofinal_threshold_selection244
    {a T : ℝ} (P Q : ℝ → ℝ → Prop)
    (hP : ∀ t M N : ℝ, M ≤ N → P t N → P t M)
    (hQ : ∀ t M N : ℝ, M ≤ N → Q t N → Q t M)
    (hCover : ∀ (d : ℝ), d ∈ Set.Ioo a T →
      ∀ (M : ℝ), 0 ≤ M →
        ∃ t : ℝ, t ∈ Set.Ioo d T ∧ (P t M ∨ Q t M)) :
    (∀ (d : ℝ), d ∈ Set.Ioo a T →
      ∀ (M : ℝ), 0 ≤ M →
        ∃ t : ℝ, t ∈ Set.Ioo d T ∧ P t M) ∨
    (∀ (d : ℝ), d ∈ Set.Ioo a T →
      ∀ (M : ℝ), 0 ≤ M →
        ∃ t : ℝ, t ∈ Set.Ioo d T ∧ Q t M) := by
  classical
  by_cases hAllP : ∀ (d : ℝ), d ∈ Set.Ioo a T →
      ∀ (M : ℝ), 0 ≤ M →
        ∃ t : ℝ, t ∈ Set.Ioo d T ∧ P t M
  · exact Or.inl hAllP
  · right
    push_neg at hAllP
    obtain ⟨d₀, hd₀, M₀, hM₀, hNoP⟩ := hAllP
    intro d hd M hM
    let e : ℝ := max d d₀
    let N : ℝ := max M M₀
    have he : e ∈ Set.Ioo a T := by
      constructor
      · exact lt_of_lt_of_le hd.1 (le_max_left d d₀)
      · exact max_lt hd.2 hd₀.2
    have hN : 0 ≤ N := le_trans hM (le_max_left M M₀)
    obtain ⟨t, ht, hAlt⟩ := hCover e he N hN
    have ht₀ : t ∈ Set.Ioo d₀ T :=
      ⟨lt_of_le_of_lt (le_max_right d d₀) ht.1, ht.2⟩
    have htD : t ∈ Set.Ioo d T :=
      ⟨lt_of_le_of_lt (le_max_left d d₀) ht.1, ht.2⟩
    rcases hAlt with hPt | hQt
    · have hOldP : P t M₀ := hP t M₀ N (le_max_right M M₀) hPt
      exact False.elim (hNoP t ht₀ hOldP)
    · exact ⟨t, htD, hQ t M N (le_max_left M M₀) hQt⟩

/-- Under hypothetical nonextension, the SAME physical signed channel
must absorb arbitrarily high normalized thresholds on EVERY terminal
subtail. The disjunction is outside both the time and threshold quantifiers.
This is strictly stronger than choosing a potentially different channel at
each individual adverse instant. -/
theorem h3Path_weightedThird_fixedCofinalChannel244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∀ (d : ℝ), d ∈ Set.Ioo a T →
      ∀ (M : ℝ), 0 ≤ M →
        ∃ t : ℝ, t ∈ Set.Ioo d T ∧
          weightedH3CanonicalGradientTransport244
            (h3PathWeightedSpectralState244 u T hH3 t) <
          h3PathWeightedThirdSplitBudget244 u t M / 2) ∨
    (∀ (d : ℝ), d ∈ Set.Ioo a T →
      ∀ (M : ℝ), 0 ≤ M →
        ∃ t : ℝ, t ∈ Set.Ioo d T ∧
          3 * weightedH3CanonicalSignedFirstMonomial244
            (h3PathWeightedSpectralState244 u T hH3 t) <
          h3PathWeightedThirdSplitBudget244 u t M / 2) := by
  apply h3_twoChannel_cofinal_threshold_selection244
    (P := fun t M =>
      weightedH3CanonicalGradientTransport244
        (h3PathWeightedSpectralState244 u T hH3 t) <
          h3PathWeightedThirdSplitBudget244 u t M / 2)
    (Q := fun t M =>
      3 * weightedH3CanonicalSignedFirstMonomial244
        (h3PathWeightedSpectralState244 u T hH3 t) <
          h3PathWeightedThirdSplitBudget244 u t M / 2)
  · intro t M N hMN hN
    have hBudget := h3PathWeightedThirdSplitBudget_antitone244 u t M N hMN
    linarith only [hN, hBudget]
  · intro t M N hMN hN
    have hBudget := h3PathWeightedThirdSplitBudget_antitone244 u t M N hMN
    linarith only [hN, hBudget]
  · intro d hd M hM
    exact h3Path_weightedThirdSplit_adverse_witness244
      hH3 hNoExtension hClass hd hM

/-- A direct two-channel sufficient condition: each physical signed channel
beats HALF the threshold-zero budget on one genuine H³ energy-class tail.
Adding the inequalities supplies precisely the previously proved complete
spectral dominance condition and hence smooth continuation. The two half
inequalities are hypotheses, not universal assertions. -/
theorem h3Path_extension_of_bothWeightedHalfBudgets244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hGradient : ∀ t : ℝ, t ∈ Set.Ioo a T →
      h3PathWeightedThirdSplitBudget244 u t 0 / 2 ≤
        weightedH3CanonicalGradientTransport244
          (h3PathWeightedSpectralState244 u T hH3 t))
    (hInterpolation : ∀ t : ℝ, t ∈ Set.Ioo a T →
      h3PathWeightedThirdSplitBudget244 u t 0 / 2 ≤
        3 * weightedH3CanonicalSignedFirstMonomial244
          (h3PathWeightedSpectralState244 u T hH3 t)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  apply h3Path_extension_of_weightedFullThird_dominance244 hH3 hClass
  intro t ht
  have hTotal := add_le_add (hGradient t ht) (hInterpolation t ht)
  unfold h3PathWeightedThirdSplitBudget244 at hTotal
  unfold weightedH3CanonicalFullThirdCommutator244
  linarith only [hTotal]

end
end PrimeTensor.FirstMonomialTriad
