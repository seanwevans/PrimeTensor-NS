import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalHighEnergyClock

/-!
# Eventual exact direct selection on a hypothetical nonextension tail

The terminal Riccati clock forces the canonical H3 energy above every
fixed threshold on some final interval. For each fixed kinetic anchor
with positive mass M, the canonical quartic activation threshold supplies
a finite energy cutoff above which direct selection is mandatory.

Combining these statements yields eventual *pointwise* direct selection:
on one final interval the selected direct coefficient is the entire
canonical Landau transport coefficient, while selected absorption is zero.
The direct-selection time set consequently has full interval measure.
The canonical direct coefficient also inherits the already-proved harmonic
lower bound under hypothetical nonextension.

No unconditional continuation or blowup claim is made.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory

/-- A positive coefficient admits a finite square-root energy cutoff that
forces the strict numerical activation barrier. -/
theorem exact_kinetic_exists_sqrt_activation_cutoff
    (A : ℝ) (hA : 0 < A) :
    ∃ L : ℝ, ∀ E : ℝ, L < E → 8 ≤ A * Real.sqrt E := by
  refine ⟨(9 / A) ^ 2, ?_⟩
  intro E hE
  have hRoot : Real.sqrt ((9 / A) ^ 2) = 9 / A := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (div_pos (by norm_num) hA)]
  have hRootLe : Real.sqrt ((9 / A) ^ 2) ≤ Real.sqrt E :=
    Real.sqrt_le_sqrt (le_of_lt hE)
  have hScaled : A * Real.sqrt ((9 / A) ^ 2) ≤ A * Real.sqrt E :=
    mul_le_mul_of_nonneg_left hRootLe (le_of_lt hA)
  have hNine : A * Real.sqrt ((9 / A) ^ 2) = 9 := by
    rw [hRoot]
    field_simp [ne_of_gt hA]
    <;> ring
  linarith only [hScaled, hNine]

/-- Positive anchor kinetic mass gives an explicit finite-energy sufficient
threshold for canonical *direct* selection. -/
theorem h3PathCanonical_exists_direct_activation_energy_cutoff
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (b : ℝ)
    (hMass : 0 < velocityH3Energy0At u b) :
    ∃ L : ℝ, ∀ t : ℝ, L < velocityH3EnergyAt u t →
      8 ≤ 81 * velocityH3Energy0At u b *
        (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 3 *
          Real.sqrt (velocityH3EnergyAt u t) := by
  have hC : 0 < h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_pos
  have hK : 0 < 4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient := by
    positivity
  have hA : 0 < 81 * velocityH3Energy0At u b *
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 3 := by
    positivity
  obtain ⟨L, hL⟩ := exact_kinetic_exists_sqrt_activation_cutoff
    (81 * velocityH3Energy0At u b *
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 3) hA
  exact ⟨L, fun t ht => hL (velocityH3EnergyAt u t) ht⟩

/-- On a nonextendible H3 tail, each positive kinetic anchor eventually
selects direct transport at *every* time and selects no absorption. -/
theorem h3PathCanonical_eventually_direct_of_noExtension_positive_mass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b) :
    ∃ c : ℝ, c ∈ Set.Ioo a T ∧
      ∀ t : ℝ, t ∈ Set.Ioo c T →
        h3ExactAdaptiveSelectedDirectCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b t =
            h3PathCanonicalKineticTransportCoefficient u t ∧
        h3ExactAdaptiveSelectedAbsorbedCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b t = 0 := by
  obtain ⟨L, hL⟩ :=
    h3PathCanonical_exists_direct_activation_energy_cutoff u b hMass
  obtain ⟨c, hc, hEnergy⟩ :=
    h3PathCanonical_energy_eventually_gt_cutoff_of_noExtension
      L hH3 hNoExtension hClass
  refine ⟨c, hc, ?_⟩
  intro t ht
  have hLarge := hL t (hEnergy t ht)
  have hDirect := h3PathCanonical_direct_regime_of_sqrt_energy_large
    u b t hLarge
  constructor
  · unfold h3ExactAdaptiveSelectedDirectCoefficient
    exact if_pos hDirect
  · unfold h3ExactAdaptiveSelectedAbsorbedCoefficient
    exact if_pos hDirect

/-- Under nonextension, the direct regime at a positive kinetic anchor
occupies the *entire* final time interval, with its full Lebesgue measure. -/
theorem h3PathCanonical_eventually_direct_full_terminal_measure
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b) :
    ∃ c : ℝ, c ∈ Set.Ioo a T ∧
      (volume : Measure ℝ)
        ({t : ℝ | h3ExactAdaptiveSelectedDirectCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b t =
            h3PathCanonicalKineticTransportCoefficient u t} ∩ Set.Ioo c T) =
        ENNReal.ofReal (T - c) := by
  obtain ⟨c, hc, hDirect⟩ :=
    h3PathCanonical_eventually_direct_of_noExtension_positive_mass
      hH3 hNoExtension hClass hMass
  refine ⟨c, hc, ?_⟩
  have hSets :
      {t : ℝ | h3ExactAdaptiveSelectedDirectCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t =
          h3PathCanonicalKineticTransportCoefficient u t} ∩ Set.Ioo c T =
        Set.Ioo c T := by
    ext t
    constructor
    · intro ht
      exact ht.2
    · intro ht
      exact ⟨(hDirect t ht).1, ht⟩
  rw [hSets, Real.volume_Ioo]

/-- On the eventual direct tail, the exact selected coefficient inherits
the canonical Landau harmonic lower rate. -/
theorem h3PathCanonical_eventually_direct_harmonic_lower
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b) :
    ∃ c : ℝ, c ∈ Set.Ioo a T ∧
      ∀ t : ℝ, t ∈ Set.Ioo c T →
        h3CanonicalLandauHarmonicCoefficient / (T - t) ≤
          h3ExactAdaptiveSelectedDirectCoefficient u
            (h3PathCanonicalKineticTransportCoefficient u) b t := by
  obtain ⟨c, hc, hDirect⟩ :=
    h3PathCanonical_eventually_direct_of_noExtension_positive_mass
      hH3 hNoExtension hClass hMass
  refine ⟨c, hc, ?_⟩
  intro t ht
  rw [(hDirect t ht).1]
  have htOld : t ∈ Set.Ioo a T :=
    ⟨lt_trans hc.1 ht.1, ht.2⟩
  have hRate :=
    canonicalLandauTransportCoefficient_harmonic_lower_of_noH3PathExtension
      hH3 hNoExtension hClass htOld
  have hProd : 0 ≤ h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t) :=
    mul_nonneg h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
      (Real.sqrt_nonneg _)
  simpa only [h3PathCanonicalLandauTransportCoefficient,
    h3PathCanonicalKineticTransportCoefficient,
    h3PathCanonicalSqrtEnergyGradientEnvelope, abs_of_nonneg hProd] using hRate

/-- Neutral formulation: continuation, or all positive kinetic anchors have
an eventual full direct branch with no selected absorption. -/
theorem h3PathCanonical_extension_or_eventual_direct_at_positive_anchors
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ b : ℝ, 0 < velocityH3Energy0At u b →
      ∃ c : ℝ, c ∈ Set.Ioo a T ∧
        ∀ t : ℝ, t ∈ Set.Ioo c T →
          h3ExactAdaptiveSelectedDirectCoefficient u
            (h3PathCanonicalKineticTransportCoefficient u) b t =
              h3PathCanonicalKineticTransportCoefficient u t ∧
          h3ExactAdaptiveSelectedAbsorbedCoefficient u
            (h3PathCanonicalKineticTransportCoefficient u) b t = 0 := by
  by_cases hExt : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExt
  · right
    intro b hMass
    exact h3PathCanonical_eventually_direct_of_noExtension_positive_mass
      hH3 hExt hClass hMass

end Euclidean
end Bridge
end PrimeTensor
