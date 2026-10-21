import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdNormalizedSignedChannels244
import Mathlib.Tactic

/-!
# Essential terminal obstruction for the canonical H³ signed channels

The exact physical signed rate is the SUM of the normalized G₃ and 3M₃
excesses.  The earlier cofinal extraction gave one fixed channel with
arbitrarily large pointwise witnesses, but such witnesses alone need not
occupy a positive measure set of physical times.

The independently established measurable unabsorbed Riccati rate is bounded
pointwise by the SUM of the positive parts of the normalized channels.
Its already-proved essential unboundedness under nonextension therefore
forces a positive-measure channel obstruction on every terminal subtail.
A nested-tail finite selection proves that ONE FIXED channel has no finite
almost-everywhere ceiling on ANY strict terminal subtail.

We make NO assertion that either individual spectral channel is measurable;
the almost-everywhere statements are valid without such an assertion. No
unconditional signed cubic estimate or continuation is claimed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory

noncomputable section
set_option maxHeartbeats 1200000

/-- The genuine measurable physical unabsorbed Riccati rate is controlled
by the positive parts of the two EXACT signed spectral channel rates. -/
theorem h3Path_unabsorbed_le_positiveNormalizedChannels244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathCanonicalUnabsorbedRiccatiRate u t ≤
      max 0 (h3PathWeightedGradientNormalizedExcess244 u T hH3 t) +
      max 0 (h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t) := by
  have hPhysical := h3PathCanonical_unabsorbed_le_signedTopTransportRemainder
    hH3 hClass ht
  have hCanonical :=
    (h3Path_weightedSignedTopRemainder_eq_physical244 hH3 hClass ht).symm
  have hG : h3PathWeightedGradientNormalizedExcess244 u T hH3 t ≤
      max 0 (h3PathWeightedGradientNormalizedExcess244 u T hH3 t) :=
    le_max_right 0 _
  have hI : h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t ≤
      max 0 (h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t) :=
    le_max_right 0 _
  have hZero : 0 ≤
      max 0 (h3PathWeightedGradientNormalizedExcess244 u T hH3 t) +
      max 0 (h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t) :=
    add_nonneg (le_max_left 0 _) (le_max_left 0 _)
  have hAdd : max 0
      (h3PathWeightedGradientNormalizedExcess244 u T hH3 t +
       h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t) ≤
      max 0 (h3PathWeightedGradientNormalizedExcess244 u T hH3 t) +
      max 0 (h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t) :=
    max_le hZero (add_le_add hG hI)
  calc
    h3PathCanonicalUnabsorbedRiccatiRate u t ≤
        h3PathCanonicalSignedTopTransportRemainder u t := hPhysical
    _ = h3PathWeightedSignedTopRemainder244 u T hH3 t := hCanonical
    _ = max 0 (h3PathWeightedGradientNormalizedExcess244 u T hH3 t +
          h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t) :=
      h3Path_weightedRemainder_eq_positiveChannelSum244 u T hH3 t
    _ ≤ _ := hAdd

/-- Under hypothetical nonextension, on EACH strict terminal subtail,
AT LEAST ONE channel cannot obey the given finite a.e. upper bound.
This is a measure-theoretic, not merely a pointwise, obstruction. -/
theorem h3Path_positiveNormalizedChannels_essentialAlternative244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d : ℝ} (M : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T) :
    ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
      h3PathWeightedGradientNormalizedExcess244 u T hH3 t ≤ M) ∨
    ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
      h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t ≤ M) := by
  by_cases hGradient : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
      h3PathWeightedGradientNormalizedExcess244 u T hH3 t ≤ M
  · right
    intro hInterpolation
    apply h3PathCanonical_unabsorbedRate_not_ae_bounded_on_subtail
      (2 * max 0 M) hH3 hNoExtension hClass hd
    filter_upwards [hGradient, hInterpolation,
      ae_restrict_mem measurableSet_Ioo] with t hG hI ht
    have htClass : t ∈ Set.Ioo a T :=
      ⟨lt_trans hd.1 ht.1, ht.2⟩
    have hMajor := h3Path_unabsorbed_le_positiveNormalizedChannels244
      hH3 hClass htClass
    have hGM : max 0 (h3PathWeightedGradientNormalizedExcess244
        u T hH3 t) ≤ max 0 M := max_le_max_left 0 hG
    have hIM : max 0 (h3PathWeightedInterpolationNormalizedExcess244
        u T hH3 t) ≤ max 0 M := max_le_max_left 0 hI
    linarith only [hMajor, hGM, hIM]
  · exact Or.inl hGradient

/-- Strengthen pointwise fixed-channel cofinality: the SAME signed spectral
channel fails EVERY finite almost-everywhere upper bound on EVERY strict
terminal subtail. No time-measurability of G₃ or M₃ is silently assumed.
The selection only uses restriction of a.e. predicates to nested intervals. -/
theorem h3Path_positiveNormalizedChannels_fixedEssentialCofinal244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∀ d : ℝ, d ∈ Set.Ioo a T → ∀ M : ℝ,
      ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
        h3PathWeightedGradientNormalizedExcess244 u T hH3 t ≤ M)) ∨
    (∀ d : ℝ, d ∈ Set.Ioo a T → ∀ M : ℝ,
      ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
        h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t ≤ M)) := by
  classical
  by_cases hAllG : ∀ d : ℝ, d ∈ Set.Ioo a T → ∀ M : ℝ,
      ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
        h3PathWeightedGradientNormalizedExcess244 u T hH3 t ≤ M)
  · exact Or.inl hAllG
  · right
    push Not at hAllG
    obtain ⟨d₀, hd₀, M₀, hBoundG⟩ := hAllG
    intro d hd M hBoundI
    let e : ℝ := max d d₀
    have he : e ∈ Set.Ioo a T := by
      constructor
      · exact lt_of_lt_of_le hd.1 (le_max_left d d₀)
      · exact max_lt hd.2 hd₀.2
    have hSubsetG : Set.Ioo e T ⊆ Set.Ioo d₀ T := by
      intro t ht
      exact ⟨lt_of_le_of_lt (le_max_right d d₀) ht.1, ht.2⟩
    have hSubsetI : Set.Ioo e T ⊆ Set.Ioo d T := by
      intro t ht
      exact ⟨lt_of_le_of_lt (le_max_left d d₀) ht.1, ht.2⟩
    have hAeG : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo e T)),
        h3PathWeightedGradientNormalizedExcess244 u T hH3 t ≤ M₀ :=
      ae_restrict_of_ae_restrict_of_subset hSubsetG hBoundG
    have hAeI : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo e T)),
        h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t ≤ M :=
      ae_restrict_of_ae_restrict_of_subset hSubsetI hBoundI
    let N : ℝ := max M M₀
    have hAeGN : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo e T)),
        h3PathWeightedGradientNormalizedExcess244 u T hH3 t ≤ N :=
      hAeG.mono (fun t ht => le_trans ht (le_max_right M M₀))
    have hAeIN : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo e T)),
        h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t ≤ N :=
      hAeI.mono (fun t ht => le_trans ht (le_max_left M M₀))
    rcases h3Path_positiveNormalizedChannels_essentialAlternative244 N
        hH3 hNoExtension hClass he with hNotG | hNotI
    · exact hNotG hAeGN
    · exact hNotI hAeIN

/-- Integrability of the positive parts of BOTH normalized channels is a
valid continuation criterion.  The only measurability used for the dominated
quantity is the previously proved measurability of the PHYSICAL unabsorbed
rate; this theorem adds no measurability hypothesis for the spectral path. -/
theorem h3Path_extension_of_integrable_positiveNormalizedChannels244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hGradient : IntegrableOn
      (fun t : ℝ => max 0 (h3PathWeightedGradientNormalizedExcess244
        u T hH3 t)) (Set.Ioo a T))
    (hInterpolation : IntegrableOn
      (fun t : ℝ => max 0 (h3PathWeightedInterpolationNormalizedExcess244
        u T hH3 t)) (Set.Ioo a T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hSum : IntegrableOn
      (fun t : ℝ =>
        max 0 (h3PathWeightedGradientNormalizedExcess244 u T hH3 t) +
        max 0 (h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t))
      (Set.Ioo a T) := hGradient.add hInterpolation
  have hMeas := h3PathCanonical_unabsorbedRate_aestronglyMeasurableOnTail
    hH3 hClass
  -- `Integrable.mono'` expects the norm of the dominated rate bounded
  -- directly by the integrable, nonnegative channel sum (not its norm).
  have hDom : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo a T)),
      ‖h3PathCanonicalUnabsorbedRiccatiRate u t‖ ≤
        max 0 (h3PathWeightedGradientNormalizedExcess244 u T hH3 t) +
          max 0 (h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs,
      abs_of_nonneg (h3PathCanonical_unabsorbedRiccatiRate_nonneg u t)]
    exact h3Path_unabsorbed_le_positiveNormalizedChannels244 hH3 hClass ht
  have hU : IntegrableOn (h3PathCanonicalUnabsorbedRiccatiRate u)
      (Set.Ioo a T) := Integrable.mono' hSum hMeas hDom
  exact h3PathCanonical_extension_of_integrable_unabsorbedRiccatiRate
    hH3 hClass hU

/-- Without smooth continuation, the positive part of at least one channel
fails time-integrability on EVERY strict terminal subtail. The choice of
channel is fixed before the subtail, and the result is complementary to the
stronger essential unboundedness theorem above. -/
theorem h3Path_positiveNormalizedChannels_fixedNonintegrable244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∀ d : ℝ, d ∈ Set.Ioo a T →
      ¬ IntegrableOn
        (fun t : ℝ => max 0 (h3PathWeightedGradientNormalizedExcess244
          u T hH3 t)) (Set.Ioo d T)) ∨
    (∀ d : ℝ, d ∈ Set.Ioo a T →
      ¬ IntegrableOn
        (fun t : ℝ => max 0 (h3PathWeightedInterpolationNormalizedExcess244
          u T hH3 t)) (Set.Ioo d T)) := by
  classical
  by_cases hAllG : ∀ d : ℝ, d ∈ Set.Ioo a T →
      ¬ IntegrableOn
        (fun t : ℝ => max 0 (h3PathWeightedGradientNormalizedExcess244
          u T hH3 t)) (Set.Ioo d T)
  · exact Or.inl hAllG
  · right
    push Not at hAllG
    obtain ⟨d₀, hd₀, hIntG⟩ := hAllG
    intro d hd hIntI
    let e : ℝ := max d d₀
    have he : e ∈ Set.Ioo a T := by
      constructor
      · exact lt_of_lt_of_le hd.1 (le_max_left d d₀)
      · exact max_lt hd.2 hd₀.2
    have hSubsetG : Set.Ioo e T ⊆ Set.Ioo d₀ T := by
      intro t ht
      exact ⟨lt_of_le_of_lt (le_max_right d d₀) ht.1, ht.2⟩
    have hSubsetI : Set.Ioo e T ⊆ Set.Ioo d T := by
      intro t ht
      exact ⟨lt_of_le_of_lt (le_max_left d d₀) ht.1, ht.2⟩
    have hG : IntegrableOn
        (fun t : ℝ => max 0 (h3PathWeightedGradientNormalizedExcess244
          u T hH3 t)) (Set.Ioo e T) := hIntG.mono_set hSubsetG
    have hI : IntegrableOn
        (fun t : ℝ => max 0 (h3PathWeightedInterpolationNormalizedExcess244
          u T hH3 t)) (Set.Ioo e T) := hIntI.mono_set hSubsetI
    have hClassE : PreterminalH3EnergyClass u e T :=
      preterminalH3EnergyClass_restrict_left hClass (le_of_lt he.1) he.2
    exact hNoExtension
      (h3Path_extension_of_integrable_positiveNormalizedChannels244
        hH3 hClassE hG hI)

end
end PrimeTensor.FirstMonomialTriad
