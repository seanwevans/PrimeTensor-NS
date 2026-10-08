import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticTwoAnchor

/-!
# Exact adaptive direct and absorbed temporal regimes

The previous two-anchor obstruction retains the minimum of two coefficients.
On a later tail where the exact energy threshold selects one branch everywhere,
integrability of that branch implies continuation. Under nonextension the
selected branch must therefore be nonintegrable. No global branch selection is
assumed, and no new Navier--Stokes estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- In the direct regime, time integrability of B itself gives continuation.
The kinetic anchor b can precede the integrability start c. -/
theorem h3PathExtension_of_integrableDirectUnderExactThresholdOnLaterSubtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b c : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hc : c ∈ Set.Ioo b T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo c T → 1 ≤ B t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo c T →
      |velocityH3TransportDerivativeAt u t| ≤ B t * velocityH3EnergyAt u t)
    (hLow : ∀ t : ℝ, t ∈ Set.Ioo c T →
      velocityH3EnergyAt u t ≤
        1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) * velocityH3Energy0At u b)
    (hInt : MeasureTheory.IntegrableOn B (Set.Ioo c T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hMinimum : MeasureTheory.IntegrableOn
      (fun t : ℝ => min (B t)
        ((B t + (3 * B t + (3 * B t) ^ 4 / (2 : ℝ) ^ 3) *
          velocityH3Energy0At u b) / velocityH3EnergyAt u t)) (Set.Ioo c T) := by
    apply MeasureTheory.IntegrableOn.congr_fun hInt _ measurableSet_Ioo
    intro t ht
    have hBPos : 0 < B t := lt_of_lt_of_le zero_lt_one (hB t ht)
    have hEPos : 0 < velocityH3EnergyAt u t :=
      lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
    exact (exact_kinetic_quartic_adaptive_min_eq_direct_of_below_threshold
      hBPos hEPos (hLow t ht)).symm
  exact h3PathExtension_of_integrableFixedAnchorExactAdaptiveCoefficientOnLaterSubtail
    hH3 hClass hb hc hB hTransport hMinimum

/-- In the absorbed regime, the exact anchored normalized remainder
is the coefficient whose integrability suffices for continuation. -/
theorem h3PathExtension_of_integrableAbsorbedAboveExactThresholdOnLaterSubtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b c : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hc : c ∈ Set.Ioo b T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo c T → 1 ≤ B t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo c T →
      |velocityH3TransportDerivativeAt u t| ≤ B t * velocityH3EnergyAt u t)
    (hHigh : ∀ t : ℝ, t ∈ Set.Ioo c T →
      1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) * velocityH3Energy0At u b <
        velocityH3EnergyAt u t)
    (hInt : MeasureTheory.IntegrableOn
      (fun t : ℝ =>
        (B t + (3 * B t + (3 * B t) ^ 4 / (2 : ℝ) ^ 3) *
          velocityH3Energy0At u b) / velocityH3EnergyAt u t)
      (Set.Ioo c T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hMinimum : MeasureTheory.IntegrableOn
      (fun t : ℝ => min (B t)
        ((B t + (3 * B t + (3 * B t) ^ 4 / (2 : ℝ) ^ 3) *
          velocityH3Energy0At u b) / velocityH3EnergyAt u t)) (Set.Ioo c T) := by
    apply MeasureTheory.IntegrableOn.congr_fun hInt _ measurableSet_Ioo
    intro t ht
    have hBPos : 0 < B t := lt_of_lt_of_le zero_lt_one (hB t ht)
    have hEPos : 0 < velocityH3EnergyAt u t :=
      lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
    exact (exact_kinetic_quartic_adaptive_min_eq_absorbed_of_above_threshold
      hBPos hEPos (hHigh t ht)).symm
  exact h3PathExtension_of_integrableFixedAnchorExactAdaptiveCoefficientOnLaterSubtail
    hH3 hClass hb hc hB hTransport hMinimum

/-- Under nonextension, a uniformly direct later tail cannot have an
integrable direct transport coefficient. -/
theorem not_integrableOn_direct_of_noH3PathExtension_in_exactDirectRegime
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b c : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hc : c ∈ Set.Ioo b T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo c T → 1 ≤ B t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo c T →
      |velocityH3TransportDerivativeAt u t| ≤ B t * velocityH3EnergyAt u t)
    (hLow : ∀ t : ℝ, t ∈ Set.Ioo c T →
      velocityH3EnergyAt u t ≤
        1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) * velocityH3Energy0At u b) :
    ¬ MeasureTheory.IntegrableOn B (Set.Ioo c T) := by
  intro hInt
  exact hNoExtension
    (h3PathExtension_of_integrableDirectUnderExactThresholdOnLaterSubtail
      hH3 hClass hb hc hB hTransport hLow hInt)

/-- Under nonextension, a uniformly absorbed later tail cannot have
an integrable exact normalized absorption coefficient. -/
theorem not_integrableOn_absorbed_of_noH3PathExtension_in_exactAbsorbedRegime
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b c : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hc : c ∈ Set.Ioo b T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo c T → 1 ≤ B t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo c T →
      |velocityH3TransportDerivativeAt u t| ≤ B t * velocityH3EnergyAt u t)
    (hHigh : ∀ t : ℝ, t ∈ Set.Ioo c T →
      1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) * velocityH3Energy0At u b <
        velocityH3EnergyAt u t) :
    ¬ MeasureTheory.IntegrableOn
      (fun t : ℝ =>
        (B t + (3 * B t + (3 * B t) ^ 4 / (2 : ℝ) ^ 3) *
          velocityH3Energy0At u b) / velocityH3EnergyAt u t)
      (Set.Ioo c T) := by
  intro hInt
  exact hNoExtension
    (h3PathExtension_of_integrableAbsorbedAboveExactThresholdOnLaterSubtail
      hH3 hClass hb hc hB hTransport hHigh hInt)

/-- The direct-regime obstruction applies on every later subtail when the
direct comparison holds throughout the original anchored interval. -/
theorem h3PathDirectRegimeContinuationOrObstruction_on_every_laterSubtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo b T → 1 ≤ B t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo b T →
      |velocityH3TransportDerivativeAt u t| ≤ B t * velocityH3EnergyAt u t)
    (hLow : ∀ t : ℝ, t ∈ Set.Ioo b T →
      velocityH3EnergyAt u t ≤
        1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) * velocityH3Energy0At u b) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ c : ℝ, c ∈ Set.Ioo b T →
      ¬ MeasureTheory.IntegrableOn B (Set.Ioo c T) := by
  by_cases hExtension : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · right
    intro c hc
    exact not_integrableOn_direct_of_noH3PathExtension_in_exactDirectRegime
      hH3 hExtension hClass hb hc
      (fun t ht => hB t ⟨lt_trans hc.1 ht.1, ht.2⟩)
      (fun t ht => hTransport t ⟨lt_trans hc.1 ht.1, ht.2⟩)
      (fun t ht => hLow t ⟨lt_trans hc.1 ht.1, ht.2⟩)

/-- The absorbed-regime obstruction applies on every later subtail when
strict activation holds throughout the original anchored interval. -/
theorem h3PathAbsorbedRegimeContinuationOrObstruction_on_every_laterSubtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo b T → 1 ≤ B t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo b T →
      |velocityH3TransportDerivativeAt u t| ≤ B t * velocityH3EnergyAt u t)
    (hHigh : ∀ t : ℝ, t ∈ Set.Ioo b T →
      1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) * velocityH3Energy0At u b <
        velocityH3EnergyAt u t) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ c : ℝ, c ∈ Set.Ioo b T →
      ¬ MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          (B t + (3 * B t + (3 * B t) ^ 4 / (2 : ℝ) ^ 3) *
            velocityH3Energy0At u b) / velocityH3EnergyAt u t)
        (Set.Ioo c T) := by
  by_cases hExtension : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · right
    intro c hc
    exact not_integrableOn_absorbed_of_noH3PathExtension_in_exactAbsorbedRegime
      hH3 hExtension hClass hb hc
      (fun t ht => hB t ⟨lt_trans hc.1 ht.1, ht.2⟩)
      (fun t ht => hTransport t ⟨lt_trans hc.1 ht.1, ht.2⟩)
      (fun t ht => hHigh t ⟨lt_trans hc.1 ht.1, ht.2⟩)

end Euclidean
end Bridge
end PrimeTensor
