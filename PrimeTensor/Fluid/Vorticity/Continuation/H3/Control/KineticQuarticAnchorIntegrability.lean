import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticAnchorCompensation

/-!
# Integrability transfer and anchor-synchronized selected obstructions

The selected direct coefficient decreases as the kinetic anchor advances.
An integrable earlier selected direct share therefore transfers to a later
anchor, provided the later share is measurable. Under nonextension, this
forces the later selected absorbed share to remain nonintegrable on every
terminal subtail. The resulting anchor dichotomy is conditional on explicit
measurability; pointwise comparison alone cannot provide it.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory

/-- A selected direct coefficient is nonnegative when the transport
coefficient is nonnegative. -/
theorem h3ExactAdaptiveSelectedDirectCoefficient_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {B : ℝ → ℝ} {b t : ℝ} (hB : 0 ≤ B t) :
    0 ≤ h3ExactAdaptiveSelectedDirectCoefficient u B b t := by
  unfold h3ExactAdaptiveSelectedDirectCoefficient
  split_ifs
  · exact hB
  · exact le_refl 0

/-- Integrability of an earlier selected direct share transfers to a
later kinetic anchor on the same strict terminal subtail, provided the
later selected function is measurable. -/
theorem h3ExactAdaptiveSelectedDirectCoefficient_integrableOn_mono_anchor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b c d : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hc : c ∈ Set.Ioo b T)
    (hd : d ∈ Set.Ioo c T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo d T → 1 ≤ B t)
    (hMeas : Measurable (h3ExactAdaptiveSelectedDirectCoefficient u B c))
    (hEarlier : MeasureTheory.IntegrableOn
      (h3ExactAdaptiveSelectedDirectCoefficient u B b) (Set.Ioo d T)) :
    MeasureTheory.IntegrableOn
      (h3ExactAdaptiveSelectedDirectCoefficient u B c) (Set.Ioo d T) := by
  apply Integrable.mono' hEarlier
  · exact hMeas.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hB0 : 0 ≤ B t := le_trans zero_le_one (hB t ht)
    have hNewNonneg :=
      h3ExactAdaptiveSelectedDirectCoefficient_nonneg
        (u := u) (B := B) (b := c) (t := t) hB0
    have hOldNonneg :=
      h3ExactAdaptiveSelectedDirectCoefficient_nonneg
        (u := u) (B := B) (b := b) (t := t) hB0
    have hOrder := h3ExactAdaptiveSelectedDirectCoefficient_mono_anchor
      hH3 hClass hb hc hB0
    simp only [Real.norm_eq_abs, abs_of_nonneg hNewNonneg,
      abs_of_nonneg hOldNonneg]
    exact hOrder

/-- If the selected direct share is integrable at an earlier kinetic
anchor, then under nonextension the selected absorbed share at every
later anchor is nonintegrable on every still later tail. -/
theorem h3PathSelectedAbsorbed_nonintegrableOn_of_earlierDirectIntegrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b c d : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hc : c ∈ Set.Ioo b T)
    (hd : d ∈ Set.Ioo b T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo a T → 1 ≤ B t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo a T →
      |velocityH3TransportDerivativeAt u t| ≤ B t * velocityH3EnergyAt u t)
    (hMeas : Measurable (h3ExactAdaptiveSelectedDirectCoefficient u B c))
    (hEarlier : MeasureTheory.IntegrableOn
      (h3ExactAdaptiveSelectedDirectCoefficient u B b) (Set.Ioo d T)) :
    ∀ e : ℝ, e ∈ Set.Ioo c T →
      ¬ MeasureTheory.IntegrableOn
        (h3ExactAdaptiveSelectedAbsorbedCoefficient u B c) (Set.Ioo e T) := by
  intro e he hAbs
  let z : ℝ := max d e
  have hz : z ∈ Set.Ioo c T := by
    exact ⟨lt_of_lt_of_le he.1 (le_max_right d e), max_lt hd.2 he.2⟩
  have hcOld : c ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hc.1, hc.2⟩
  have hEarlierZ : MeasureTheory.IntegrableOn
      (h3ExactAdaptiveSelectedDirectCoefficient u B b) (Set.Ioo z T) := by
    apply hEarlier.mono_set
    intro t ht
    exact ⟨lt_of_le_of_lt (le_max_left d e) ht.1, ht.2⟩
  have hDirectZ : MeasureTheory.IntegrableOn
      (h3ExactAdaptiveSelectedDirectCoefficient u B c) (Set.Ioo z T) := by
    exact h3ExactAdaptiveSelectedDirectCoefficient_integrableOn_mono_anchor
      hH3 hClass hb hc hz
      (fun t ht => hB t ⟨lt_trans hcOld.1 (lt_trans hz.1 ht.1), ht.2⟩)
      hMeas hEarlierZ
  have hAbsZ : MeasureTheory.IntegrableOn
      (h3ExactAdaptiveSelectedAbsorbedCoefficient u B c) (Set.Ioo z T) := by
    apply hAbs.mono_set
    intro t ht
    exact ⟨lt_of_le_of_lt (le_max_right d e) ht.1, ht.2⟩
  exact hNoExtension
    (h3PathExtension_of_integrableSelectedExactAdaptiveRegimesOnLaterSubtail
      hH3 hClass hcOld hz
      (fun t ht => hB t ⟨lt_trans hcOld.1 (lt_trans hz.1 ht.1), ht.2⟩)
      (fun t ht => hTransport t
        ⟨lt_trans hcOld.1 (lt_trans hz.1 ht.1), ht.2⟩)
      hDirectZ hAbsZ)

/-- Anchor-synchronized alternative under nonextension and measurability:
either no selected direct share is integrable on a later tail at any anchor,
or one direct-integrable anchor forces the absorbed obstruction at every
strictly later kinetic anchor and every terminal subtail. -/
theorem h3PathSelectedExactAdaptiveAnchorSynchronizedObstruction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo a T → 1 ≤ B t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo a T →
      |velocityH3TransportDerivativeAt u t| ≤ B t * velocityH3EnergyAt u t)
    (hMeas : ∀ c : ℝ, c ∈ Set.Ioo a T →
      Measurable (h3ExactAdaptiveSelectedDirectCoefficient u B c)) :
    (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ d : ℝ, d ∈ Set.Ioo b T →
      ¬ MeasureTheory.IntegrableOn
        (h3ExactAdaptiveSelectedDirectCoefficient u B b) (Set.Ioo d T)) ∨
    (∃ b : ℝ, b ∈ Set.Ioo a T ∧
      ∀ c : ℝ, c ∈ Set.Ioo b T → ∀ e : ℝ, e ∈ Set.Ioo c T →
        ¬ MeasureTheory.IntegrableOn
          (h3ExactAdaptiveSelectedAbsorbedCoefficient u B c) (Set.Ioo e T)) := by
  classical
  by_cases hSome : ∃ b : ℝ, b ∈ Set.Ioo a T ∧
      ∃ d : ℝ, d ∈ Set.Ioo b T ∧
        MeasureTheory.IntegrableOn
          (h3ExactAdaptiveSelectedDirectCoefficient u B b) (Set.Ioo d T)
  · right
    obtain ⟨b, hb, d, hd, hEarlier⟩ := hSome
    refine ⟨b, hb, ?_⟩
    intro c hc
    exact h3PathSelectedAbsorbed_nonintegrableOn_of_earlierDirectIntegrable
      hH3 hNoExtension hClass hb hc hd hB hTransport
      (hMeas c ⟨lt_trans hb.1 hc.1, hc.2⟩) hEarlier
  · left
    intro b hb d hd hEarlier
    exact hSome ⟨b, hb, d, hd, hEarlier⟩

/-- Continuation/nonextension formulation of the anchor-synchronized
selected-share alternative, retaining the measurability requirement. -/
theorem h3PathSelectedExactAdaptiveAnchorSynchronizedContinuationOrObstruction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo a T → 1 ≤ B t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo a T →
      |velocityH3TransportDerivativeAt u t| ≤ B t * velocityH3EnergyAt u t)
    (hMeas : ∀ c : ℝ, c ∈ Set.Ioo a T →
      Measurable (h3ExactAdaptiveSelectedDirectCoefficient u B c)) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ((∀ b : ℝ, b ∈ Set.Ioo a T → ∀ d : ℝ, d ∈ Set.Ioo b T →
        ¬ MeasureTheory.IntegrableOn
          (h3ExactAdaptiveSelectedDirectCoefficient u B b) (Set.Ioo d T)) ∨
     (∃ b : ℝ, b ∈ Set.Ioo a T ∧
       ∀ c : ℝ, c ∈ Set.Ioo b T → ∀ e : ℝ, e ∈ Set.Ioo c T →
         ¬ MeasureTheory.IntegrableOn
           (h3ExactAdaptiveSelectedAbsorbedCoefficient u B c) (Set.Ioo e T))) := by
  by_cases hExtension : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact Or.inr
      (h3PathSelectedExactAdaptiveAnchorSynchronizedObstruction
        hH3 hExtension hClass hB hTransport hMeas)

end Euclidean
end Bridge
end PrimeTensor
