import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticAnchorIntegrability

/-!
# Local measurability of the selected direct regime

The closed H3 energy derivative identities give continuity of the canonical
energy on every strict energy-class tail. If the transport coefficient B is
measurable, the threshold-selected direct coefficient is consequently almost
everywhere strongly measurable on each terminal tail, even without assuming
anything about the energy outside that tail.

This removes the *global* selected-coefficient measurability assumption from
the direct-share integrability transfer and the anchor-synchronized conditional
nonextension alternative. It does not prove the required time integrability.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory

/-- The already-closed energy derivative identities imply temporal continuity
of the normalized H3 energy on the strict energy-class tail. -/
theorem continuousOn_velocityH3EnergyAt_on_energyClassTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ContinuousOn (velocityH3EnergyAt u) (Set.Ioo a T) := by
  intro t ht
  have hIds : H3OrderEnergyDerivativeIdentities u t :=
    h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      u T hH3 a hClass t ht
  exact (hasDerivAt_velocityH3EnergyAt hIds).continuousAt.continuousWithinAt

/-- Measurability of the transport coefficient and tail continuity of the
energy yield selected-direct measurability for the restricted volume measure.
No global measurability of the old path outside (a,T) is required. -/
theorem h3ExactAdaptiveSelectedDirectCoefficient_aestronglyMeasurableOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hd : d ∈ Set.Ioo b T)
    (hBMeas : Measurable B) :
    AEStronglyMeasurable
      (h3ExactAdaptiveSelectedDirectCoefficient u B b)
      ((volume : Measure ℝ).restrict (Set.Ioo d T)) := by
  classical
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo d T)
  have hCont : ContinuousOn (velocityH3EnergyAt u) (Set.Ioo d T) :=
    (continuousOn_velocityH3EnergyAt_on_energyClassTail hH3 hClass).mono
      (by
        intro t ht
        exact ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩)
  have hEnergyAE : AEStronglyMeasurable (velocityH3EnergyAt u) μ := by
    exact hCont.aestronglyMeasurable measurableSet_Ioo
  have hThresholdMeas : Measurable (fun t : ℝ =>
      1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) * velocityH3Energy0At u b) := by
    fun_prop
  have hThresholdAE : AEStronglyMeasurable (fun t : ℝ =>
      1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) * velocityH3Energy0At u b) μ :=
    hThresholdMeas.aestronglyMeasurable
  have hRegion : NullMeasurableSet
      {t : ℝ | velocityH3EnergyAt u t ≤
        1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) * velocityH3Energy0At u b} μ :=
    hEnergyAE.nullMeasurableSet_le hThresholdAE
  have hSelectedAE : AEStronglyMeasurable
      ({t : ℝ | velocityH3EnergyAt u t ≤
        1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) * velocityH3Energy0At u b}.indicator
        B) μ :=
    hBMeas.aestronglyMeasurable.indicator₀ hRegion
  have hEq :
      h3ExactAdaptiveSelectedDirectCoefficient u B b =
        ({t : ℝ | velocityH3EnergyAt u t ≤
          1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) * velocityH3Energy0At u b}.indicator B) := by
    funext t
    by_cases ht : velocityH3EnergyAt u t ≤
        1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) * velocityH3Energy0At u b
    · simp [h3ExactAdaptiveSelectedDirectCoefficient, Set.indicator, ht]
    · simp [h3ExactAdaptiveSelectedDirectCoefficient, Set.indicator, ht]
  change AEStronglyMeasurable
    (h3ExactAdaptiveSelectedDirectCoefficient u B b) μ
  rw [hEq]
  exact hSelectedAE

/-- Move an integrable selected-direct share to a later kinetic anchor using
only measurability of B, not global measurability of the selected share. -/
theorem h3ExactAdaptiveSelectedDirectCoefficient_integrableOn_mono_anchor_of_measurableB
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b c d : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hc : c ∈ Set.Ioo b T)
    (hd : d ∈ Set.Ioo c T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo d T → 1 ≤ B t)
    (hBMeas : Measurable B)
    (hEarlier : MeasureTheory.IntegrableOn
      (h3ExactAdaptiveSelectedDirectCoefficient u B b) (Set.Ioo d T)) :
    MeasureTheory.IntegrableOn
      (h3ExactAdaptiveSelectedDirectCoefficient u B c) (Set.Ioo d T) := by
  apply Integrable.mono' hEarlier
  · exact h3ExactAdaptiveSelectedDirectCoefficient_aestronglyMeasurableOnTail
      hH3 hClass ⟨lt_trans hb.1 hc.1, hc.2⟩ hd hBMeas
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hB0 : 0 ≤ B t := le_trans zero_le_one (hB t ht)
    have hNewNonneg :=
      h3ExactAdaptiveSelectedDirectCoefficient_nonneg
        (u := u) (B := B) (b := c) (t := t) hB0
    have hOrder := h3ExactAdaptiveSelectedDirectCoefficient_mono_anchor
      hH3 hClass hb hc hB0
    simp only [Real.norm_eq_abs, abs_of_nonneg hNewNonneg]
    exact hOrder

/-- A previously integrable direct share forces persistent absorbed-share
nonintegrability at every later kinetic anchor under nonextension. -/
theorem h3PathSelectedAbsorbed_nonintegrableOn_of_earlierDirectIntegrable_of_measurableB
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
    (hBMeas : Measurable B)
    (hEarlier : MeasureTheory.IntegrableOn
      (h3ExactAdaptiveSelectedDirectCoefficient u B b) (Set.Ioo d T)) :
    ∀ e : ℝ, e ∈ Set.Ioo c T →
      ¬ MeasureTheory.IntegrableOn
        (h3ExactAdaptiveSelectedAbsorbedCoefficient u B c) (Set.Ioo e T) := by
  intro e he hAbs
  let z : ℝ := max d e
  have hz : z ∈ Set.Ioo c T :=
    ⟨lt_of_lt_of_le he.1 (le_max_right d e), max_lt hd.2 he.2⟩
  have hcOld : c ∈ Set.Ioo a T := ⟨lt_trans hb.1 hc.1, hc.2⟩
  have hEarlierZ : MeasureTheory.IntegrableOn
      (h3ExactAdaptiveSelectedDirectCoefficient u B b) (Set.Ioo z T) := by
    apply hEarlier.mono_set
    intro t ht
    exact ⟨lt_of_le_of_lt (le_max_left d e) ht.1, ht.2⟩
  have hDirectZ : MeasureTheory.IntegrableOn
      (h3ExactAdaptiveSelectedDirectCoefficient u B c) (Set.Ioo z T) := by
    exact h3ExactAdaptiveSelectedDirectCoefficient_integrableOn_mono_anchor_of_measurableB
      hH3 hClass hb hc hz
      (fun t ht => hB t ⟨lt_trans hcOld.1 (lt_trans hz.1 ht.1), ht.2⟩)
      hBMeas hEarlierZ
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

/-- Anchor-synchronized conditional obstruction with only global
measurability of B, and no global energy-measurability assumption. -/
theorem h3PathSelectedExactAdaptiveAnchorSynchronizedObstruction_of_measurableB
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo a T → 1 ≤ B t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo a T →
      |velocityH3TransportDerivativeAt u t| ≤ B t * velocityH3EnergyAt u t)
    (hBMeas : Measurable B) :
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
    exact h3PathSelectedAbsorbed_nonintegrableOn_of_earlierDirectIntegrable_of_measurableB
      hH3 hNoExtension hClass hb hc hd hB hTransport hBMeas hEarlier
  · left
    intro b hb d hd hEarlier
    exact hSome ⟨b, hb, d, hd, hEarlier⟩

/-- Continuation/nonextension version without a separate measurable-selected
share premise. Only B is assumed measurable, plus the original PDE bounds. -/
theorem h3PathSelectedExactAdaptiveAnchorSynchronizedContinuationOrObstruction_of_measurableB
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo a T → 1 ≤ B t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo a T →
      |velocityH3TransportDerivativeAt u t| ≤ B t * velocityH3EnergyAt u t)
    (hBMeas : Measurable B) :
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
      (h3PathSelectedExactAdaptiveAnchorSynchronizedObstruction_of_measurableB
        hH3 hExtension hClass hB hTransport hBMeas)

end Euclidean
end Bridge
end PrimeTensor
