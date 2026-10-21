import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdEssentialSignedChannels244
import Mathlib.Tactic

/-!
# One fixed signed H³ channel defeats every integrable time envelope

The earlier fixed-essential-channel theorem rules out constant almost-everywhere
ceilings. This module obtains a stronger terminal-time obstruction: under
hypothetical failure of smooth continuation, one FIXED normalized signed
channel cannot be almost-everywhere dominated by ANY integrable function on
ANY strict terminal subtail.

The proof does not assert measurability of either spectral channel. Instead it
uses the established measurable physical unabsorbed Riccati rate and its
non-domination by integrable majorants. If BOTH signed channels possessed
integrable a.e. upper envelopes on a common tail, their positive parts would
dominate the unabsorbed rate by an integrable function, contradicting that
physical PDE theorem. The finite two-channel/nested-tail argument fixes a
single channel ahead of both the subtail and the time-dependent envelope.

This is a necessary condition for hypothetical nonextension, not an estimate
that rules it out. No spectral-path measurability assumption is added.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory

noncomputable section
set_option maxHeartbeats 1200000

/-- The physical H³ energy-rate obstruction excludes simultaneous
integrable time-dependent a.e. upper envelopes for the two normalized
signed spectral channels on any strict subtail. Crucially, the spectral
channels themselves need not be measurable: only the envelopes are
integrable and the PHYSICAL unabsorbed rate is known measurable. -/
theorem h3Path_signedChannels_no_joint_ae_integrable_majorants244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d : ℝ} (rG rI : ℝ → ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T)
    (hrG : IntegrableOn rG (Set.Ioo d T))
    (hrI : IntegrableOn rI (Set.Ioo d T)) :
    ¬ ((∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
        h3PathWeightedGradientNormalizedExcess244 u T hH3 t ≤ rG t) ∧
       (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
        h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t ≤ rI t)) := by
  rintro ⟨hAeG, hAeI⟩
  have hr : IntegrableOn (fun t : ℝ => ‖rG t‖ + ‖rI t‖)
      (Set.Ioo d T) := hrG.norm.add hrI.norm
  apply h3PathCanonical_unabsorbedRate_not_ae_le_integrable_on_subtail
    (r := fun t : ℝ => ‖rG t‖ + ‖rI t‖)
    hH3 hNoExtension hClass hd hr
  filter_upwards [hAeG, hAeI, ae_restrict_mem measurableSet_Ioo]
    with t hG hI ht
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hd.1 ht.1, ht.2⟩
  have hPhysical := h3Path_unabsorbed_le_positiveNormalizedChannels244
    hH3 hClass htClass
  have hGPlus :
      max 0 (h3PathWeightedGradientNormalizedExcess244 u T hH3 t) ≤
        ‖rG t‖ := by
    rw [Real.norm_eq_abs]
    exact max_le (abs_nonneg _) (le_trans hG (le_abs_self _))
  have hIPlus :
      max 0 (h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t) ≤
        ‖rI t‖ := by
    rw [Real.norm_eq_abs]
    exact max_le (abs_nonneg _) (le_trans hI (le_abs_self _))
  linarith only [hPhysical, hGPlus, hIPlus]

/-- Genuine continuation from TWO integrable, almost-everywhere upper
envelopes for the normalized signed physical H³ channels. Unlike the
previous integrability criterion, no measurability or integrability of
the individual spectral channels is required. -/
theorem h3Path_extension_of_ae_integrable_signedChannel_majorants244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d : ℝ} (rG rI : ℝ → ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T)
    (hrG : IntegrableOn rG (Set.Ioo d T))
    (hrI : IntegrableOn rI (Set.Ioo d T))
    (hAeG : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
      h3PathWeightedGradientNormalizedExcess244 u T hH3 t ≤ rG t)
    (hAeI : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
      h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t ≤ rI t) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  exact (h3Path_signedChannels_no_joint_ae_integrable_majorants244
    rG rI hH3 hNoExtension hClass hd hrG hrI) ⟨hAeG, hAeI⟩

/-- One and the SAME normalized signed spectral channel cannot be dominated
almost everywhere by ANY integrable time-dependent upper envelope on ANY
strict terminal subtail under hypothetical nonextension. The disjunction
sits outside the choice of subtail AND outside the function quantifier. -/
theorem h3Path_signedChannels_fixed_ae_integrableMajorantBarrier244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∀ d : ℝ, d ∈ Set.Ioo a T → ∀ r : ℝ → ℝ,
      IntegrableOn r (Set.Ioo d T) →
      ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
        h3PathWeightedGradientNormalizedExcess244 u T hH3 t ≤ r t)) ∨
    (∀ d : ℝ, d ∈ Set.Ioo a T → ∀ r : ℝ → ℝ,
      IntegrableOn r (Set.Ioo d T) →
      ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
        h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t ≤ r t)) := by
  classical
  by_cases hAllG : ∀ d : ℝ, d ∈ Set.Ioo a T → ∀ r : ℝ → ℝ,
      IntegrableOn r (Set.Ioo d T) →
      ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
        h3PathWeightedGradientNormalizedExcess244 u T hH3 t ≤ r t)
  · exact Or.inl hAllG
  · right
    push Not at hAllG
    obtain ⟨d₀, hd₀, r₀, hr₀, hBoundG⟩ := hAllG
    intro d hd r hr hBoundI
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
    have hIntG : IntegrableOn r₀ (Set.Ioo e T) := hr₀.mono_set hSubsetG
    have hIntI : IntegrableOn r (Set.Ioo e T) := hr.mono_set hSubsetI
    have hAeG : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo e T)),
        h3PathWeightedGradientNormalizedExcess244 u T hH3 t ≤ r₀ t :=
      ae_restrict_of_ae_restrict_of_subset hSubsetG hBoundG
    have hAeI : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo e T)),
        h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t ≤ r t :=
      ae_restrict_of_ae_restrict_of_subset hSubsetI hBoundI
    exact (h3Path_signedChannels_no_joint_ae_integrable_majorants244
      r₀ r hH3 hNoExtension hClass he hIntG hIntI) ⟨hAeG, hAeI⟩

/-- The completed alternative makes the logical boundary explicit:
either the original H³ path extends, or a single normalized spectral
channel defeats all integrable a.e. envelopes on every strict tail. -/
theorem h3Path_extension_or_fixed_signedChannel_integrableMajorantBarrier244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ((∀ d : ℝ, d ∈ Set.Ioo a T → ∀ r : ℝ → ℝ,
        IntegrableOn r (Set.Ioo d T) →
        ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
          h3PathWeightedGradientNormalizedExcess244 u T hH3 t ≤ r t)) ∨
     (∀ d : ℝ, d ∈ Set.Ioo a T → ∀ r : ℝ → ℝ,
        IntegrableOn r (Set.Ioo d T) →
        ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
          h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t ≤ r t))) := by
  by_cases hExt : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExt
  · exact Or.inr
      (h3Path_signedChannels_fixed_ae_integrableMajorantBarrier244
        hH3 hExt hClass)

end
end PrimeTensor.FirstMonomialTriad
