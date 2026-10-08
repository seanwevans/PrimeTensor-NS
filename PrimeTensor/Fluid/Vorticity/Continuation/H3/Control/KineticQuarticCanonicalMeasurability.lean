import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticLocalMeasurability
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Growth.Sqrt

/-!
# Tail-continuous coefficients and the canonical square-root H3 gradient envelope

Selected direct coefficients need only be measurable on the terminal tail,
not on all real times. Continuity of B on the energy-class tail supplies this
measurability. The canonical square-root-energy gradient envelope is such a
continuous envelope: its continuity follows from the closed H3 energy
identities, and its gradient bound is already a theorem of the H3 path API.

This is a conditional continuation/nonextension refinement, not an assertion
that the exact temporal integrability obstruction is resolved.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory

/-- A threshold-selected direct share is almost everywhere strongly
measurable on a strict terminal interval if B is continuous only on the
larger admissible H3 energy-class interval. -/
theorem h3ExactAdaptiveSelectedDirectCoefficient_aestronglyMeasurableOnTail_of_continuousOnB
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hd : d ∈ Set.Ioo b T)
    (hBCont : ContinuousOn B (Set.Ioo a T)) :
    AEStronglyMeasurable
      (h3ExactAdaptiveSelectedDirectCoefficient u B b)
      ((volume : Measure ℝ).restrict (Set.Ioo d T)) := by
  classical
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo d T)
  have hSubset : Set.Ioo d T ⊆ Set.Ioo a T := by
    intro t ht
    exact ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
  have hBLocal : ContinuousOn B (Set.Ioo d T) := hBCont.mono hSubset
  have hELocal : ContinuousOn (velocityH3EnergyAt u) (Set.Ioo d T) :=
    (continuousOn_velocityH3EnergyAt_on_energyClassTail hH3 hClass).mono hSubset
  have hBAE : AEStronglyMeasurable B μ :=
    hBLocal.aestronglyMeasurable measurableSet_Ioo
  have hEAE : AEStronglyMeasurable (velocityH3EnergyAt u) μ :=
    hELocal.aestronglyMeasurable measurableSet_Ioo
  have hThresholdCont : ContinuousOn
      (fun t : ℝ => 1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) *
        velocityH3Energy0At u b) (Set.Ioo d T) := by
    fun_prop
  have hThresholdAE : AEStronglyMeasurable
      (fun t : ℝ => 1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) *
        velocityH3Energy0At u b) μ :=
    hThresholdCont.aestronglyMeasurable measurableSet_Ioo
  have hRegion : NullMeasurableSet
      {t : ℝ | velocityH3EnergyAt u t ≤
        1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) * velocityH3Energy0At u b} μ :=
    hEAE.nullMeasurableSet_le hThresholdAE
  have hSelectedAE : AEStronglyMeasurable
      ({t : ℝ | velocityH3EnergyAt u t ≤
        1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) * velocityH3Energy0At u b}.indicator B) μ :=
    hBAE.indicator₀ hRegion
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

/-- The selected direct coefficient inherits terminal integrability after
kinetic reanchoring when the transport coefficient is tail-continuous. -/
theorem h3ExactAdaptiveSelectedDirectCoefficient_integrableOn_mono_anchor_of_continuousOnB
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b c d : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hc : c ∈ Set.Ioo b T)
    (hd : d ∈ Set.Ioo c T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo d T → 1 ≤ B t)
    (hBCont : ContinuousOn B (Set.Ioo a T))
    (hEarlier : MeasureTheory.IntegrableOn
      (h3ExactAdaptiveSelectedDirectCoefficient u B b) (Set.Ioo d T)) :
    MeasureTheory.IntegrableOn
      (h3ExactAdaptiveSelectedDirectCoefficient u B c) (Set.Ioo d T) := by
  apply Integrable.mono' hEarlier
  · exact h3ExactAdaptiveSelectedDirectCoefficient_aestronglyMeasurableOnTail_of_continuousOnB
      hH3 hClass ⟨lt_trans hb.1 hc.1, hc.2⟩ hd hBCont
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hB0 : 0 ≤ B t := le_trans zero_le_one (hB t ht)
    have hNewNonneg := h3ExactAdaptiveSelectedDirectCoefficient_nonneg
      (u := u) (B := B) (b := c) (t := t) hB0
    have hOrder := h3ExactAdaptiveSelectedDirectCoefficient_mono_anchor
      hH3 hClass hb hc hB0
    simp only [Real.norm_eq_abs, abs_of_nonneg hNewNonneg]
    exact hOrder

/-- Synchronize kinetic anchors with tail-continuity of B, without any
global measurability requirement on B or the normalized H3 energy. -/
theorem h3PathSelectedExactAdaptiveAnchorSynchronizedContinuationOrObstruction_of_continuousOnB
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo a T → 1 ≤ B t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo a T →
      |velocityH3TransportDerivativeAt u t| ≤ B t * velocityH3EnergyAt u t)
    (hBCont : ContinuousOn B (Set.Ioo a T)) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ((∀ b : ℝ, b ∈ Set.Ioo a T → ∀ d : ℝ, d ∈ Set.Ioo b T →
        ¬ MeasureTheory.IntegrableOn
          (h3ExactAdaptiveSelectedDirectCoefficient u B b) (Set.Ioo d T)) ∨
     (∃ b : ℝ, b ∈ Set.Ioo a T ∧
       ∀ c : ℝ, c ∈ Set.Ioo b T → ∀ e : ℝ, e ∈ Set.Ioo c T →
         ¬ MeasureTheory.IntegrableOn
           (h3ExactAdaptiveSelectedAbsorbedCoefficient u B c) (Set.Ioo e T))) := by
  classical
  by_cases hExtension : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · right
    by_cases hSome : ∃ b : ℝ, b ∈ Set.Ioo a T ∧
        ∃ d : ℝ, d ∈ Set.Ioo b T ∧
          MeasureTheory.IntegrableOn
            (h3ExactAdaptiveSelectedDirectCoefficient u B b) (Set.Ioo d T)
    · right
      obtain ⟨b, hb, d, hd, hEarlier⟩ := hSome
      refine ⟨b, hb, ?_⟩
      intro c hc e he hAbs
      let z : ℝ := max d e
      have hz : z ∈ Set.Ioo c T :=
        ⟨lt_of_lt_of_le he.1 (le_max_right d e), max_lt hd.2 he.2⟩
      have hEarlierZ : MeasureTheory.IntegrableOn
          (h3ExactAdaptiveSelectedDirectCoefficient u B b) (Set.Ioo z T) := by
        apply hEarlier.mono_set
        intro t ht
        exact ⟨lt_of_le_of_lt (le_max_left d e) ht.1, ht.2⟩
      have hDirectZ : MeasureTheory.IntegrableOn
          (h3ExactAdaptiveSelectedDirectCoefficient u B c) (Set.Ioo z T) :=
        h3ExactAdaptiveSelectedDirectCoefficient_integrableOn_mono_anchor_of_continuousOnB
          hH3 hClass hb hc hz
          (fun t ht => hB t
            ⟨lt_trans hb.1 (lt_trans hc.1 (lt_trans hz.1 ht.1)), ht.2⟩)
          hBCont hEarlierZ
      have hAbsZ : MeasureTheory.IntegrableOn
          (h3ExactAdaptiveSelectedAbsorbedCoefficient u B c) (Set.Ioo z T) := by
        apply hAbs.mono_set
        intro t ht
        exact ⟨lt_of_le_of_lt (le_max_right d e) ht.1, ht.2⟩
      have hcOld : c ∈ Set.Ioo a T := ⟨lt_trans hb.1 hc.1, hc.2⟩
      exact hExtension
        (h3PathExtension_of_integrableSelectedExactAdaptiveRegimesOnLaterSubtail
          hH3 hClass hcOld hz
          (fun t ht => hB t
            ⟨lt_trans hcOld.1 (lt_trans hz.1 ht.1), ht.2⟩)
          (fun t ht => hTransport t
            ⟨lt_trans hcOld.1 (lt_trans hz.1 ht.1), ht.2⟩)
          hDirectZ hAbsZ)
    · left
      intro b hb d hd hEarlier
      exact hSome ⟨b, hb, d, hd, hEarlier⟩

/-- The concrete canonical square-root-energy transport coefficient is
continuous on each strict energy-class interval. -/
theorem continuousOn_h3PathCanonicalSqrtEnergyGradientCoefficient_on_energyClassTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ContinuousOn (fun t : ℝ =>
      4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u t|))
      (Set.Ioo a T) := by
  have hEnergyCont : ContinuousOn (velocityH3EnergyAt u) (Set.Ioo a T) :=
    continuousOn_velocityH3EnergyAt_on_energyClassTail hH3 hClass
  have hSqrtCont : ContinuousOn
      (fun t : ℝ => Real.sqrt (velocityH3EnergyAt u t)) (Set.Ioo a T) :=
    Real.continuous_sqrt.comp_continuousOn hEnergyCont
  have hGradientCont : ContinuousOn (h3PathCanonicalSqrtEnergyGradientEnvelope u)
      (Set.Ioo a T) := by
    unfold h3PathCanonicalSqrtEnergyGradientEnvelope
    exact continuousOn_const.mul hSqrtCont
  fun_prop

/-- The closed canonical gradient envelope yields the anchor-synchronized
continuation/nonextension dichotomy without an auxiliary measurable-envelope
assumption: its temporal regularity is inherited from the H3 energy. -/
theorem h3PathCanonicalGradientAnchorSynchronizedContinuationOrObstruction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ((∀ b : ℝ, b ∈ Set.Ioo a T → ∀ d : ℝ, d ∈ Set.Ioo b T →
        ¬ MeasureTheory.IntegrableOn
          (h3ExactAdaptiveSelectedDirectCoefficient u
            (fun t : ℝ => 4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u t|)) b)
          (Set.Ioo d T)) ∨
     (∃ b : ℝ, b ∈ Set.Ioo a T ∧
       ∀ c : ℝ, c ∈ Set.Ioo b T → ∀ e : ℝ, e ∈ Set.Ioo c T →
         ¬ MeasureTheory.IntegrableOn
           (h3ExactAdaptiveSelectedAbsorbedCoefficient u
             (fun t : ℝ => 4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u t|)) c)
           (Set.Ioo e T))) := by
  have hB : ∀ t : ℝ, t ∈ Set.Ioo a T →
      1 ≤ 4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u t|) := by
    intro t ht
    nlinarith [abs_nonneg (h3PathCanonicalSqrtEnergyGradientEnvelope u t)]
  have hTransport : ∀ t : ℝ, t ∈ Set.Ioo a T →
      |velocityH3TransportDerivativeAt u t| ≤
        (4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u t|)) *
          velocityH3EnergyAt u t := by
    intro t ht
    exact (h3TransportControlledOnTail_of_h3Path_exactPDEPairing
      h3PathEnergyClassProducesPDEPairingIntegrability_closed
      hH3 hClass
      (fun s hs => h3PathCanonicalSqrtEnergyGradientEnvelope_at hH3 hClass hs)
      t ht).2
  exact h3PathSelectedExactAdaptiveAnchorSynchronizedContinuationOrObstruction_of_continuousOnB
    hH3 hClass hB hTransport
    (continuousOn_h3PathCanonicalSqrtEnergyGradientCoefficient_on_energyClassTail
      hH3 hClass)

end Euclidean
end Bridge
end PrimeTensor
