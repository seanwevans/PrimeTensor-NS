import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalDirectLocalization

/-!
# High-energy square-root moments forced by the selected direct obstruction

An integrable high-energy square-root H3 moment makes the selected direct
coefficient integrable on that same high-energy region: the latter is bounded
by the canonical affine square-root coefficient, and the high-energy constant
part is integrable on a finite terminal interval. Under nonextension, a
positive-mass kinetic anchor therefore forces failure of integrability of
this high-energy square-root moment on every strict terminal tail and for
every fixed cutoff. The statement does not assert that nonextension occurs.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory

/-- The high-energy indicator of the constant function one. -/
noncomputable def h3PathCanonicalHighEnergyUnitMoment
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (L : ℝ) : ℝ → ℝ :=
  ({t : ℝ | velocityH3EnergyAt u t ≤ L}ᶜ).indicator (fun _ => (1 : ℝ))

/-- The square-root H3 energy supported on the high-energy time set. -/
noncomputable def h3PathCanonicalHighEnergySqrtMoment
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (L : ℝ) : ℝ → ℝ :=
  ({t : ℝ | velocityH3EnergyAt u t ≤ L}ᶜ).indicator
    (fun t => Real.sqrt (velocityH3EnergyAt u t))

/-- The high-energy constant indicator is measurable and integrable on every
strict terminal tail, independently of the geometry of the high-energy set. -/
theorem h3PathCanonicalHighEnergyUnitMoment_integrableOn
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ} (L : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hd : d ∈ Set.Ioo b T) :
    IntegrableOn (h3PathCanonicalHighEnergyUnitMoment u L) (Set.Ioo d T) := by
  have hRegion := h3PathCanonicalEnergySublevel_nullMeasurableOnTail
    L hH3 hClass hb hd
  have hMeas : AEStronglyMeasurable
      (h3PathCanonicalHighEnergyUnitMoment u L)
      ((volume : Measure ℝ).restrict (Set.Ioo d T)) := by
    change AEStronglyMeasurable
      (({t : ℝ | velocityH3EnergyAt u t ≤ L}ᶜ).indicator (fun _ => (1 : ℝ)))
      ((volume : Measure ℝ).restrict (Set.Ioo d T))
    exact aestronglyMeasurable_const.indicator₀ hRegion.compl
  have hFinite : (volume : Measure ℝ) (Set.Ioo d T) < (⊤ : ENNReal) :=
    measure_Ioo_lt_top
  refine IntegrableOn.of_bound hFinite hMeas 1 ?_
  filter_upwards with t
  by_cases ht : velocityH3EnergyAt u t ≤ L
  · simp [h3PathCanonicalHighEnergyUnitMoment, Set.indicator, ht]
  · simp [h3PathCanonicalHighEnergyUnitMoment, Set.indicator, ht]

/-- The cutoff square-root moment is measurable for the restricted tail measure. -/
theorem h3PathCanonicalHighEnergySqrtMoment_aestronglyMeasurableOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ} (L : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hd : d ∈ Set.Ioo b T) :
    AEStronglyMeasurable (h3PathCanonicalHighEnergySqrtMoment u L)
      ((volume : Measure ℝ).restrict (Set.Ioo d T)) := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo d T)
  have hRegion := h3PathCanonicalEnergySublevel_nullMeasurableOnTail
    L hH3 hClass hb hd
  have hSubset : Set.Ioo d T ⊆ Set.Ioo a T := by
    intro t ht
    exact ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
  have hEnergyCont : ContinuousOn (velocityH3EnergyAt u) (Set.Ioo d T) :=
    (continuousOn_velocityH3EnergyAt_on_energyClassTail hH3 hClass).mono hSubset
  have hEnergyAE : AEStronglyMeasurable (velocityH3EnergyAt u) μ :=
    hEnergyCont.aestronglyMeasurable measurableSet_Ioo
  have hSqrtAE : AEStronglyMeasurable
      (fun t : ℝ => Real.sqrt (velocityH3EnergyAt u t)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hEnergyAE
  change AEStronglyMeasurable
    (({t : ℝ | velocityH3EnergyAt u t ≤ L}ᶜ).indicator
      (fun t => Real.sqrt (velocityH3EnergyAt u t))) μ
  exact hSqrtAE.indicator₀ hRegion.compl

/-- The localized direct coefficient is dominated by the high-energy
indicator of the canonical affine square-root H3 envelope. -/
theorem h3PathCanonicalSelectedDirectHighEnergyCoefficient_norm_le_moments
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (b L t : ℝ) :
    ‖h3PathCanonicalSelectedDirectHighEnergyCoefficient u b L t‖ ≤
      4422 * (h3PathCanonicalHighEnergyUnitMoment u L t +
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          h3PathCanonicalHighEnergySqrtMoment u L t) := by
  by_cases hLow : velocityH3EnergyAt u t ≤ L
  · simp [h3PathCanonicalSelectedDirectHighEnergyCoefficient,
      h3PathCanonicalHighEnergyUnitMoment,
      h3PathCanonicalHighEnergySqrtMoment, Set.indicator, hLow]
  · have hNonneg : 0 ≤ h3ExactAdaptiveSelectedDirectCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b t :=
      h3ExactAdaptiveSelectedDirectCoefficient_nonneg
        (le_of_lt (h3PathCanonicalKineticTransportCoefficient_pos u t))
    have hSelected := h3PathCanonicalSelectedDirectCoefficient_le_transport u b t
    have hC : 0 ≤ h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient :=
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
    have hProd : 0 ≤ h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t) :=
      mul_nonneg hC (Real.sqrt_nonneg _)
    have hCoefficient : h3PathCanonicalKineticTransportCoefficient u t =
        4422 * (1 + h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) := by
      simp only [h3PathCanonicalKineticTransportCoefficient,
        h3PathCanonicalSqrtEnergyGradientEnvelope, abs_of_nonneg hProd]
    calc
      ‖h3PathCanonicalSelectedDirectHighEnergyCoefficient u b L t‖ =
          h3ExactAdaptiveSelectedDirectCoefficient u
            (h3PathCanonicalKineticTransportCoefficient u) b t := by
        simp [h3PathCanonicalSelectedDirectHighEnergyCoefficient,
          Set.indicator, hLow, Real.norm_eq_abs, abs_of_nonneg hNonneg]
      _ ≤ h3PathCanonicalKineticTransportCoefficient u t := hSelected
      _ = 4422 * (1 + h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) := hCoefficient
      _ = 4422 * (h3PathCanonicalHighEnergyUnitMoment u L t +
            h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
              h3PathCanonicalHighEnergySqrtMoment u L t) := by
        simp [h3PathCanonicalHighEnergyUnitMoment,
          h3PathCanonicalHighEnergySqrtMoment, Set.indicator, hLow]

/-- An integrable square-root energy moment on the high-energy region implies
integrability of the selected direct share on that same region. -/
theorem h3PathCanonicalSelectedDirectHighEnergy_integrableOn_of_sqrtMoment
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ} (L : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hd : d ∈ Set.Ioo b T)
    (hMoment : IntegrableOn
      (h3PathCanonicalHighEnergySqrtMoment u L) (Set.Ioo d T)) :
    IntegrableOn (h3PathCanonicalSelectedDirectHighEnergyCoefficient u b L)
      (Set.Ioo d T) := by
  have hUnit := h3PathCanonicalHighEnergyUnitMoment_integrableOn
    L hH3 hClass hb hd
  have hSum : IntegrableOn (fun t : ℝ =>
      h3PathCanonicalHighEnergyUnitMoment u L t +
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          h3PathCanonicalHighEnergySqrtMoment u L t) (Set.Ioo d T) :=
    hUnit.add (hMoment.const_mul _)
  have hMajor : IntegrableOn (fun t : ℝ =>
      4422 * (h3PathCanonicalHighEnergyUnitMoment u L t +
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          h3PathCanonicalHighEnergySqrtMoment u L t)) (Set.Ioo d T) :=
    hSum.const_mul (4422 : ℝ)
  have hMeas :=
    (h3PathCanonicalSelectedDirectEnergyParts_aestronglyMeasurableOnTail
      L hH3 hClass hb hd).2
  apply Integrable.mono' hMajor hMeas
  filter_upwards with t
  have hBound := h3PathCanonicalSelectedDirectHighEnergyCoefficient_norm_le_moments
    u b L t
  exact hBound

/-- Under hypothetical nonextension, every high-energy sqrt(H3) moment is
nonintegrable on every strict terminal subtail at a positive-mass anchor. -/
theorem h3PathCanonicalHighEnergySqrtMoment_nonintegrableOn_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ} (L : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hd : d ∈ Set.Ioo b T)
    (hMass : 0 < velocityH3Energy0At u b) :
    ¬ IntegrableOn (h3PathCanonicalHighEnergySqrtMoment u L) (Set.Ioo d T) := by
  intro hMoment
  exact (h3PathCanonicalHighEnergySelectedDirect_nonintegrableOn_of_noExtension
    L hH3 hNoExtension hClass hb hd hMass)
    (h3PathCanonicalSelectedDirectHighEnergy_integrableOn_of_sqrtMoment
      L hH3 hClass hb hd hMoment)

/-- Neutral continuation/obstruction alternative for every fixed energy cutoff:
nonextension forces divergent high-energy sqrt(H3) mass at every positive anchor. -/
theorem h3PathCanonicalHighEnergySqrtMomentContinuationOrObstruction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (L : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      0 < velocityH3Energy0At u b →
      ∀ d : ℝ, d ∈ Set.Ioo b T →
        ¬ IntegrableOn (h3PathCanonicalHighEnergySqrtMoment u L) (Set.Ioo d T) := by
  by_cases hExtension : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · right
    intro b hb hMass d hd
    exact h3PathCanonicalHighEnergySqrtMoment_nonintegrableOn_of_noExtension
      L hH3 hExtension hClass hb hd hMass

end Euclidean
end Bridge
end PrimeTensor
