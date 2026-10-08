import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalAbsorptionCeiling

/-!
# Finite temporal integral for the canonical exact absorbed share

The canonical H3 energy and gradient envelope are continuous on a strict
preterminal energy-class interval.  Hence the exact normalized absorption
coefficient is continuous before threshold selection, and the selected
absorbed coefficient is almost everywhere strongly measurable on any
later strict terminal interval.  The preceding weighted activation ceiling
bounds that coefficient uniformly when the kinetic anchor has positive mass.
A bounded measurable real function is integrable on a finite interval.

Thus, under hypothetical nonextension, the direct selected coefficient must
be nonintegrable at each positive-kinetic-mass anchor on every strict later
subtail.  This is an obstruction alternative, not a claim that nonextension
exists, nor an unconditional continuation theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory

/-- Local continuity of the exact full normalized absorption expression. -/
theorem h3ExactAdaptiveAbsorbedExpression_continuousOn_of_continuousOnB
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hd : d ∈ Set.Ioo b T)
    (hBCont : ContinuousOn B (Set.Ioo a T)) :
    ContinuousOn (fun t : ℝ =>
      (B t + (3 * B t + (3 * B t) ^ 4 / (2 : ℝ) ^ 3) *
        velocityH3Energy0At u b) / velocityH3EnergyAt u t)
      (Set.Ioo d T) := by
  have hSubset : Set.Ioo d T ⊆ Set.Ioo a T := by
    intro t ht
    exact ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
  have hBLocal : ContinuousOn B (Set.Ioo d T) := hBCont.mono hSubset
  have hELocal : ContinuousOn (velocityH3EnergyAt u) (Set.Ioo d T) :=
    (continuousOn_velocityH3EnergyAt_on_energyClassTail hH3 hClass).mono hSubset
  have hNum : ContinuousOn (fun t : ℝ =>
      B t + (3 * B t + (3 * B t) ^ 4 / (2 : ℝ) ^ 3) *
        velocityH3Energy0At u b) (Set.Ioo d T) := by
    fun_prop
  exact hNum.div hELocal (fun t ht =>
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)))

/-- The selected absorbed share is measurable for the restricted tail measure,
with no regularity requirement outside the H3 energy-class interval. -/
theorem h3ExactAdaptiveSelectedAbsorbedCoefficient_aestronglyMeasurableOnTail_of_continuousOnB
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hd : d ∈ Set.Ioo b T)
    (hBCont : ContinuousOn B (Set.Ioo a T)) :
    AEStronglyMeasurable
      (h3ExactAdaptiveSelectedAbsorbedCoefficient u B b)
      ((volume : Measure ℝ).restrict (Set.Ioo d T)) := by
  classical
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo d T)
  have hSubset : Set.Ioo d T ⊆ Set.Ioo a T := by
    intro t ht
    exact ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
  have hBLocal : ContinuousOn B (Set.Ioo d T) := hBCont.mono hSubset
  have hELocal : ContinuousOn (velocityH3EnergyAt u) (Set.Ioo d T) :=
    (continuousOn_velocityH3EnergyAt_on_energyClassTail hH3 hClass).mono hSubset
  have hEAE : AEStronglyMeasurable (velocityH3EnergyAt u) μ :=
    hELocal.aestronglyMeasurable measurableSet_Ioo
  have hThresholdCont : ContinuousOn (fun t : ℝ =>
      1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) * velocityH3Energy0At u b)
      (Set.Ioo d T) := by
    fun_prop
  have hThresholdAE : AEStronglyMeasurable (fun t : ℝ =>
      1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) * velocityH3Energy0At u b) μ :=
    hThresholdCont.aestronglyMeasurable measurableSet_Ioo
  have hRegion : NullMeasurableSet
      {t : ℝ | velocityH3EnergyAt u t ≤
        1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) * velocityH3Energy0At u b} μ :=
    hEAE.nullMeasurableSet_le hThresholdAE
  let Q : ℝ → ℝ := fun t =>
    (B t + (3 * B t + (3 * B t) ^ 4 / (2 : ℝ) ^ 3) *
      velocityH3Energy0At u b) / velocityH3EnergyAt u t
  have hQAE : AEStronglyMeasurable Q μ :=
    (h3ExactAdaptiveAbsorbedExpression_continuousOn_of_continuousOnB
      hH3 hClass hb hd hBCont).aestronglyMeasurable measurableSet_Ioo
  have hSelectedAE : AEStronglyMeasurable
      (({t : ℝ | velocityH3EnergyAt u t ≤
        1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) * velocityH3Energy0At u b}ᶜ).indicator Q) μ :=
    hQAE.indicator₀ hRegion.compl
  have hEq :
      h3ExactAdaptiveSelectedAbsorbedCoefficient u B b =
        (({t : ℝ | velocityH3EnergyAt u t ≤
          1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) * velocityH3Energy0At u b}ᶜ).indicator Q) := by
    funext t
    by_cases ht : velocityH3EnergyAt u t ≤
        1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) * velocityH3Energy0At u b
    · simp [h3ExactAdaptiveSelectedAbsorbedCoefficient, Set.indicator, Q, ht]
    · simp [h3ExactAdaptiveSelectedAbsorbedCoefficient, Set.indicator, Q, ht]
  change AEStronglyMeasurable
    (h3ExactAdaptiveSelectedAbsorbedCoefficient u B b) μ
  rw [hEq]
  exact hSelectedAE

/-- Nonnegativity of the selected canonical absorbed coefficient. -/
theorem h3PathCanonicalSelectedAbsorbedCoefficient_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (b t : ℝ) :
    0 ≤ h3ExactAdaptiveSelectedAbsorbedCoefficient u
      (h3PathCanonicalKineticTransportCoefficient u) b t := by
  have hB : 0 ≤ h3PathCanonicalKineticTransportCoefficient u t :=
    le_of_lt (h3PathCanonicalKineticTransportCoefficient_pos u t)
  have hM : 0 ≤ velocityH3Energy0At u b := velocityH3Energy0At_nonneg u b
  have hE : 0 ≤ velocityH3EnergyAt u t :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_velocityH3EnergyAt u t)
  unfold h3ExactAdaptiveSelectedAbsorbedCoefficient
  split_ifs
  · exact le_refl 0
  · positivity

/-- Positive kinetic mass and the activation ceiling make the selected
canonical absorbed coefficient integrable on every finite terminal subtail. -/
theorem h3PathCanonicalSelectedAbsorbedCoefficient_integrableOn_of_positive_kinetic_mass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hd : d ∈ Set.Ioo b T)
    (hMass : 0 < velocityH3Energy0At u b) :
    MeasureTheory.IntegrableOn
      (h3ExactAdaptiveSelectedAbsorbedCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b)
      (Set.Ioo d T) := by
  have hBCont : ContinuousOn (h3PathCanonicalKineticTransportCoefficient u)
      (Set.Ioo a T) := by
    change ContinuousOn (fun t : ℝ =>
      4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u t|)) (Set.Ioo a T)
    exact continuousOn_h3PathCanonicalSqrtEnergyGradientCoefficient_on_energyClassTail
      hH3 hClass
  have hMeas : AEStronglyMeasurable
      (h3ExactAdaptiveSelectedAbsorbedCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b)
      ((volume : Measure ℝ).restrict (Set.Ioo d T)) :=
    h3ExactAdaptiveSelectedAbsorbedCoefficient_aestronglyMeasurableOnTail_of_continuousOnB
      hH3 hClass hb hd hBCont
  have hFinite : (volume : Measure ℝ) (Set.Ioo d T) < (⊤ : ENNReal) := by
    exact measure_Ioo_lt_top
  refine IntegrableOn.of_bound hFinite hMeas
    (8 / (81 * velocityH3Energy0At u b *
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 2)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg
    (h3PathCanonicalSelectedAbsorbedCoefficient_nonneg u b t)]
  exact h3PathCanonicalSelectedAbsorbedCoefficient_le_of_positive_kinetic_mass
    u b t hMass

/-- Under nonextension, positive anchor kinetic mass rules out integrability
of the direct selected coefficient on every later strict tail. -/
theorem h3PathCanonicalSelectedDirect_nonintegrableOn_of_noExtension_positive_kinetic_mass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hd : d ∈ Set.Ioo b T)
    (hMass : 0 < velocityH3Energy0At u b) :
    ¬ MeasureTheory.IntegrableOn
      (h3ExactAdaptiveSelectedDirectCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b)
      (Set.Ioo d T) := by
  intro hDirect
  have hAbs :=
    h3PathCanonicalSelectedAbsorbedCoefficient_integrableOn_of_positive_kinetic_mass
      hH3 hClass hb hd hMass
  have hB : ∀ t : ℝ, t ∈ Set.Ioo d T →
      1 ≤ h3PathCanonicalKineticTransportCoefficient u t := by
    intro t ht
    unfold h3PathCanonicalKineticTransportCoefficient
    nlinarith [abs_nonneg (h3PathCanonicalSqrtEnergyGradientEnvelope u t)]
  have hTransport : ∀ t : ℝ, t ∈ Set.Ioo d T →
      |velocityH3TransportDerivativeAt u t| ≤
        h3PathCanonicalKineticTransportCoefficient u t * velocityH3EnergyAt u t := by
    intro t ht
    have htClass : t ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
    have hControl := h3TransportControlledOnTail_of_h3Path_exactPDEPairing
      h3PathEnergyClassProducesPDEPairingIntegrability_closed
      hH3 hClass
      (fun s hs => h3PathCanonicalSqrtEnergyGradientEnvelope_at hH3 hClass hs)
      t htClass
    simpa only [h3PathCanonicalKineticTransportCoefficient,
      H3TransportCommutatorBoundAt] using hControl.2
  exact hNoExtension
    (h3PathExtension_of_integrableSelectedExactAdaptiveRegimesOnLaterSubtail
      hH3 hClass hb hd hB hTransport hDirect hAbs)

/-- A single conditional continuation/nonextension statement that holds at
all positive-kinetic-mass anchors, without any branch-selection assumptions. -/
theorem h3PathCanonicalPositiveKineticAnchorContinuationOrDirectObstruction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      0 < velocityH3Energy0At u b →
      ∀ d : ℝ, d ∈ Set.Ioo b T →
        ¬ MeasureTheory.IntegrableOn
          (h3ExactAdaptiveSelectedDirectCoefficient u
            (h3PathCanonicalKineticTransportCoefficient u) b)
          (Set.Ioo d T) := by
  by_cases hExtension : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · right
    intro b hb hMass d hd
    exact h3PathCanonicalSelectedDirect_nonintegrableOn_of_noExtension_positive_kinetic_mass
      hH3 hExtension hClass hb hd hMass

end Euclidean
end Bridge
end PrimeTensor
