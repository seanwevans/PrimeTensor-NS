import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalActivation

/-!
# Localize the canonical selected direct obstruction at high H3 energy

The canonical direct coefficient is selected from B(t)=4422(1+C1 sqrt(E(t))).
Its contribution on any fixed bounded-energy region E(t) <= L is bounded by
4422(1+C1 sqrt(L)), independently of the number of threshold crossings.

The closed H3 energy identity gives continuity on each strict tail. Consequently
both restrictions of the selected direct coefficient, to E <= L and to E > L,
are measurable for the restricted time measure. Since terminal intervals have
finite volume, the bounded-energy restriction is integrable. Hypothetical
nonextension at an anchor with positive kinetic mass therefore forces the
high-energy restriction to be nonintegrable on every strict terminal subtail.

This makes no claim of a priori upper energy bounds or of continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory

/-- Direct coefficient restricted to the region of bounded canonical H3 energy. -/
noncomputable def h3PathCanonicalSelectedDirectLowEnergyCoefficient
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (b L : ℝ) : ℝ → ℝ :=
  {t : ℝ | velocityH3EnergyAt u t ≤ L}.indicator
    (h3ExactAdaptiveSelectedDirectCoefficient u
      (h3PathCanonicalKineticTransportCoefficient u) b)

/-- Complementary direct coefficient supported on the high-energy region. -/
noncomputable def h3PathCanonicalSelectedDirectHighEnergyCoefficient
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (b L : ℝ) : ℝ → ℝ :=
  ({t : ℝ | velocityH3EnergyAt u t ≤ L}ᶜ).indicator
    (h3ExactAdaptiveSelectedDirectCoefficient u
      (h3PathCanonicalKineticTransportCoefficient u) b)

/-- Threshold selection never exceeds the canonical transport coefficient. -/
theorem h3PathCanonicalSelectedDirectCoefficient_le_transport
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (b t : ℝ) :
    h3ExactAdaptiveSelectedDirectCoefficient u
      (h3PathCanonicalKineticTransportCoefficient u) b t ≤
        h3PathCanonicalKineticTransportCoefficient u t := by
  unfold h3ExactAdaptiveSelectedDirectCoefficient
  split_ifs
  · exact le_refl _
  · exact le_of_lt (h3PathCanonicalKineticTransportCoefficient_pos u t)

/-- The canonical coefficient has an explicit bound wherever energy is <= L. -/
theorem h3PathCanonicalKineticTransportCoefficient_le_of_energy_le
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t L : ℝ)
    (hEnergy : velocityH3EnergyAt u t ≤ L) :
    h3PathCanonicalKineticTransportCoefficient u t ≤
      4422 * (1 + h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt L) := by
  have hC : 0 ≤ h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
  have hProd : 0 ≤ h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t) :=
    mul_nonneg hC (Real.sqrt_nonneg _)
  have hSqrt : Real.sqrt (velocityH3EnergyAt u t) ≤ Real.sqrt L :=
    Real.sqrt_le_sqrt hEnergy
  have hScale := mul_le_mul_of_nonneg_left hSqrt hC
  have hCoeff : h3PathCanonicalKineticTransportCoefficient u t =
      4422 * (1 + h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) := by
    simp only [h3PathCanonicalKineticTransportCoefficient,
      h3PathCanonicalSqrtEnergyGradientEnvelope, abs_of_nonneg hProd]
  rw [hCoeff]
  apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
  linarith only [hScale]

/-- Global pointwise bound for the bounded-energy *restriction* of the direct
share. No regularity assumption is needed for the pointwise inequality. -/
theorem h3PathCanonicalSelectedDirectLowEnergyCoefficient_norm_le
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (b L t : ℝ) :
    ‖h3PathCanonicalSelectedDirectLowEnergyCoefficient u b L t‖ ≤
      4422 * (1 + h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt L) := by
  have hC : 0 ≤ h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
  by_cases hLow : velocityH3EnergyAt u t ≤ L
  · have hNonneg : 0 ≤ h3ExactAdaptiveSelectedDirectCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t :=
      h3ExactAdaptiveSelectedDirectCoefficient_nonneg
        (le_of_lt (h3PathCanonicalKineticTransportCoefficient_pos u t))
    have hSelectedBound := h3PathCanonicalSelectedDirectCoefficient_le_transport u b t
    have hTransportBound :=
      h3PathCanonicalKineticTransportCoefficient_le_of_energy_le u t L hLow
    change ‖({s : ℝ | velocityH3EnergyAt u s ≤ L}.indicator
      (h3ExactAdaptiveSelectedDirectCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b)) t‖ ≤ _
    simp only [Set.indicator, Set.mem_setOf_eq, if_pos hLow,
      Real.norm_eq_abs, abs_of_nonneg hNonneg]
    exact hSelectedBound.trans hTransportBound
  · change ‖({s : ℝ | velocityH3EnergyAt u s ≤ L}.indicator
      (h3ExactAdaptiveSelectedDirectCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b)) t‖ ≤ _
    simp only [Set.indicator, Set.mem_setOf_eq, if_neg hLow, norm_zero]
    have hScale : 0 ≤ h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt L := mul_nonneg hC (Real.sqrt_nonneg _)
    linarith only [hScale]

/-- The energy cutoff is null-measurable on each strict energy-class tail. -/
theorem h3PathCanonicalEnergySublevel_nullMeasurableOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ} (L : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hd : d ∈ Set.Ioo b T) :
    NullMeasurableSet {t : ℝ | velocityH3EnergyAt u t ≤ L}
      ((volume : Measure ℝ).restrict (Set.Ioo d T)) := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo d T)
  have hSubset : Set.Ioo d T ⊆ Set.Ioo a T := by
    intro t ht
    exact ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
  have hEnergyCont : ContinuousOn (velocityH3EnergyAt u) (Set.Ioo d T) :=
    (continuousOn_velocityH3EnergyAt_on_energyClassTail hH3 hClass).mono hSubset
  have hEnergyAE : AEStronglyMeasurable (velocityH3EnergyAt u) μ :=
    hEnergyCont.aestronglyMeasurable measurableSet_Ioo
  exact hEnergyAE.nullMeasurableSet_le aestronglyMeasurable_const

/-- Both localizations are strongly measurable for the restricted tail measure. -/
theorem h3PathCanonicalSelectedDirectEnergyParts_aestronglyMeasurableOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ} (L : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hd : d ∈ Set.Ioo b T) :
    AEStronglyMeasurable (h3PathCanonicalSelectedDirectLowEnergyCoefficient u b L)
        ((volume : Measure ℝ).restrict (Set.Ioo d T)) ∧
    AEStronglyMeasurable (h3PathCanonicalSelectedDirectHighEnergyCoefficient u b L)
        ((volume : Measure ℝ).restrict (Set.Ioo d T)) := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo d T)
  have hBCont : ContinuousOn (h3PathCanonicalKineticTransportCoefficient u)
      (Set.Ioo a T) := by
    change ContinuousOn (fun t : ℝ =>
      4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u t|)) (Set.Ioo a T)
    exact continuousOn_h3PathCanonicalSqrtEnergyGradientCoefficient_on_energyClassTail
      hH3 hClass
  have hDirectAE : AEStronglyMeasurable
      (h3ExactAdaptiveSelectedDirectCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b) μ :=
    h3ExactAdaptiveSelectedDirectCoefficient_aestronglyMeasurableOnTail_of_continuousOnB
      hH3 hClass hb hd hBCont
  have hRegion := h3PathCanonicalEnergySublevel_nullMeasurableOnTail
    L hH3 hClass hb hd
  constructor
  · change AEStronglyMeasurable
      ({t : ℝ | velocityH3EnergyAt u t ≤ L}.indicator
        (h3ExactAdaptiveSelectedDirectCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b)) μ
    exact hDirectAE.indicator₀ hRegion
  · change AEStronglyMeasurable
      (({t : ℝ | velocityH3EnergyAt u t ≤ L}ᶜ).indicator
        (h3ExactAdaptiveSelectedDirectCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b)) μ
    exact hDirectAE.indicator₀ hRegion.compl

/-- On every finite terminal interval, the bounded-energy part is integrable,
regardless of how often the selected regime switches. -/
theorem h3PathCanonicalSelectedDirectLowEnergyCoefficient_integrableOn
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ} (L : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hd : d ∈ Set.Ioo b T) :
    MeasureTheory.IntegrableOn (h3PathCanonicalSelectedDirectLowEnergyCoefficient u b L)
      (Set.Ioo d T) := by
  have hMeas :=
    (h3PathCanonicalSelectedDirectEnergyParts_aestronglyMeasurableOnTail
      L hH3 hClass hb hd).1
  have hFinite : (volume : Measure ℝ) (Set.Ioo d T) < (⊤ : ENNReal) := by
    exact measure_Ioo_lt_top
  refine IntegrableOn.of_bound hFinite hMeas
    (4422 * (1 + h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt L)) ?_
  filter_upwards with t
  exact h3PathCanonicalSelectedDirectLowEnergyCoefficient_norm_le u b L t

/-- Decomposition into complementary bounded-energy and high-energy shares. -/
theorem h3PathCanonicalSelectedDirectCoefficient_eq_energy_parts
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (b L : ℝ) :
    h3ExactAdaptiveSelectedDirectCoefficient u
      (h3PathCanonicalKineticTransportCoefficient u) b =
    h3PathCanonicalSelectedDirectLowEnergyCoefficient u b L +
      h3PathCanonicalSelectedDirectHighEnergyCoefficient u b L := by
  funext t
  by_cases hLow : velocityH3EnergyAt u t ≤ L
  · simp [h3PathCanonicalSelectedDirectLowEnergyCoefficient,
      h3PathCanonicalSelectedDirectHighEnergyCoefficient, Set.indicator, hLow]
  · simp [h3PathCanonicalSelectedDirectLowEnergyCoefficient,
      h3PathCanonicalSelectedDirectHighEnergyCoefficient, Set.indicator, hLow]

/-- Integrability of only the high-energy direct share suffices for extension
at a positive-mass kinetic anchor. -/
theorem h3PathExtension_of_integrableCanonicalHighEnergySelectedDirect
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ} (L : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hd : d ∈ Set.Ioo b T)
    (hMass : 0 < velocityH3Energy0At u b)
    (hHigh : MeasureTheory.IntegrableOn
      (h3PathCanonicalSelectedDirectHighEnergyCoefficient u b L) (Set.Ioo d T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hLow := h3PathCanonicalSelectedDirectLowEnergyCoefficient_integrableOn
    L hH3 hClass hb hd
  have hDirect : MeasureTheory.IntegrableOn
      (h3ExactAdaptiveSelectedDirectCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b) (Set.Ioo d T) := by
    rw [h3PathCanonicalSelectedDirectCoefficient_eq_energy_parts u b L]
    exact hLow.add hHigh
  by_contra hNoExtension
  exact (h3PathCanonicalSelectedDirect_nonintegrableOn_of_noExtension_positive_kinetic_mass
    hH3 hNoExtension hClass hb hd hMass) hDirect

/-- Under nonextension, all nonintegrable selected-direct mass is necessarily
carried by the high-energy region, for *every* finite cutoff L. -/
theorem h3PathCanonicalHighEnergySelectedDirect_nonintegrableOn_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ} (L : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hd : d ∈ Set.Ioo b T)
    (hMass : 0 < velocityH3Energy0At u b) :
    ¬ MeasureTheory.IntegrableOn
      (h3PathCanonicalSelectedDirectHighEnergyCoefficient u b L) (Set.Ioo d T) := by
  intro hHigh
  exact hNoExtension
    (h3PathExtension_of_integrableCanonicalHighEnergySelectedDirect
      L hH3 hClass hb hd hMass hHigh)

/-- The high-energy localization preserves a neutral continuation/obstruction
alternative simultaneously at every positive-mass kinetic anchor. -/
theorem h3PathCanonicalHighEnergySelectedDirectContinuationOrObstruction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (L : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      0 < velocityH3Energy0At u b →
      ∀ d : ℝ, d ∈ Set.Ioo b T →
        ¬ MeasureTheory.IntegrableOn
          (h3PathCanonicalSelectedDirectHighEnergyCoefficient u b L) (Set.Ioo d T) := by
  by_cases hExtension : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · right
    intro b hb hMass d hd
    exact h3PathCanonicalHighEnergySelectedDirect_nonintegrableOn_of_noExtension
      L hH3 hExtension hClass hb hd hMass

end Euclidean
end Bridge
end PrimeTensor
