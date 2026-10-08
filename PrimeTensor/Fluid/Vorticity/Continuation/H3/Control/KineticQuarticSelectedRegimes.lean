import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticRegimes

/-!
# Exact adaptive obstruction under arbitrary temporal regime switching

The exact adaptive minimum can select direct growth at some times and the
absorbed remainder at other times.  Split its value into two nonnegative
selected contributions without assuming either regime persists on a tail.
If both contributions were integrable on one strict tail, their sum would be
integrable and the existing exact adaptive continuation criterion would apply.
Thus nonextension requires at least one nonintegrable selected contribution
on every later two-anchor subtail.  The responsible contribution may change
between subtails; no new analytic estimate is asserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- Direct transport coefficient, retained only where direct transport is
at least as sharp as the exact absorbed coefficient. -/
noncomputable def h3ExactAdaptiveSelectedDirectCoefficient
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (B : ℝ → ℝ) (b : ℝ) : ℝ → ℝ :=
  fun t =>
    if velocityH3EnergyAt u t ≤
        1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) * velocityH3Energy0At u b
    then B t else 0

/-- Exact normalized absorption coefficient, retained only where it is
strictly sharper than direct transport. -/
noncomputable def h3ExactAdaptiveSelectedAbsorbedCoefficient
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (B : ℝ → ℝ) (b : ℝ) : ℝ → ℝ :=
  fun t =>
    if velocityH3EnergyAt u t ≤
        1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) * velocityH3Energy0At u b
    then 0
    else (B t + (3 * B t + (3 * B t) ^ 4 / (2 : ℝ) ^ 3) *
      velocityH3Energy0At u b) / velocityH3EnergyAt u t

/-- Exact scalar minimum as the sum of the two selected coefficients.
The threshold may be crossed any number of times. -/
theorem h3_exact_quartic_adaptive_min_eq_selected_sum
    {B M E : ℝ} (hB : 0 < B) (hE : 0 < E) :
    min B ((B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) * M) / E) =
      (if E ≤ 1 + (3 + (81 / 8 : ℝ) * B ^ 3) * M then B else 0) +
      (if E ≤ 1 + (3 + (81 / 8 : ℝ) * B ^ 3) * M
        then 0 else (B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) * M) / E) := by
  by_cases hLow : E ≤ 1 + (3 + (81 / 8 : ℝ) * B ^ 3) * M
  · simp only [if_pos hLow, add_zero]
    exact exact_kinetic_quartic_adaptive_min_eq_direct_of_below_threshold
      hB hE hLow
  · have hHigh : 1 + (3 + (81 / 8 : ℝ) * B ^ 3) * M < E :=
      lt_of_not_ge hLow
    simp only [if_neg hLow, zero_add]
    exact exact_kinetic_quartic_adaptive_min_eq_absorbed_of_above_threshold
      hB hE hHigh

/-- Integrability of the two selected components on a single later tail
suffices for continuation, even with arbitrary regime switching. -/
theorem h3PathExtension_of_integrableSelectedExactAdaptiveRegimesOnLaterSubtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b c : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hc : c ∈ Set.Ioo b T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo c T → 1 ≤ B t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo c T →
      |velocityH3TransportDerivativeAt u t| ≤ B t * velocityH3EnergyAt u t)
    (hDirect : MeasureTheory.IntegrableOn
      (h3ExactAdaptiveSelectedDirectCoefficient u B b) (Set.Ioo c T))
    (hAbsorbed : MeasureTheory.IntegrableOn
      (h3ExactAdaptiveSelectedAbsorbedCoefficient u B b) (Set.Ioo c T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hSum : MeasureTheory.IntegrableOn
      (fun t : ℝ => h3ExactAdaptiveSelectedDirectCoefficient u B b t +
        h3ExactAdaptiveSelectedAbsorbedCoefficient u B b t) (Set.Ioo c T) :=
    hDirect.add hAbsorbed
  have hMinimum : MeasureTheory.IntegrableOn
      (fun t : ℝ => min (B t)
        ((B t + (3 * B t + (3 * B t) ^ 4 / (2 : ℝ) ^ 3) *
          velocityH3Energy0At u b) / velocityH3EnergyAt u t)) (Set.Ioo c T) := by
    apply MeasureTheory.IntegrableOn.congr_fun hSum _ measurableSet_Ioo
    intro t ht
    have hBPos : 0 < B t := lt_of_lt_of_le zero_lt_one (hB t ht)
    have hEPos : 0 < velocityH3EnergyAt u t :=
      lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
    simpa only [h3ExactAdaptiveSelectedDirectCoefficient,
      h3ExactAdaptiveSelectedAbsorbedCoefficient] using
      (h3_exact_quartic_adaptive_min_eq_selected_sum
        (B := B t) (M := velocityH3Energy0At u b)
        (E := velocityH3EnergyAt u t) hBPos hEPos).symm
  exact h3PathExtension_of_integrableFixedAnchorExactAdaptiveCoefficientOnLaterSubtail
    hH3 hClass hb hc hB hTransport hMinimum

/-- Under nonextension, at least one of the two selected components is
nonintegrable on every two-anchor subtail.  The selected failing component
need not be the same on different subtails. -/
theorem h3PathSelectedExactAdaptiveContinuationOrObstruction_on_every_two_anchor_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo a T → 1 ≤ B t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo a T →
      |velocityH3TransportDerivativeAt u t| ≤ B t * velocityH3EnergyAt u t) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∀ c : ℝ, c ∈ Set.Ioo b T →
        (¬ MeasureTheory.IntegrableOn
          (h3ExactAdaptiveSelectedDirectCoefficient u B b) (Set.Ioo c T) ∨
         ¬ MeasureTheory.IntegrableOn
          (h3ExactAdaptiveSelectedAbsorbedCoefficient u B b) (Set.Ioo c T)) := by
  by_cases hExtension : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · right
    intro b hb c hc
    by_cases hDirect : MeasureTheory.IntegrableOn
        (h3ExactAdaptiveSelectedDirectCoefficient u B b) (Set.Ioo c T)
    · right
      intro hAbsorbed
      apply hExtension
      exact h3PathExtension_of_integrableSelectedExactAdaptiveRegimesOnLaterSubtail
        hH3 hClass hb hc
        (fun t ht => hB t ⟨lt_trans hb.1 (lt_trans hc.1 ht.1), ht.2⟩)
        (fun t ht => hTransport t ⟨lt_trans hb.1 (lt_trans hc.1 ht.1), ht.2⟩)
        hDirect hAbsorbed
    · exact Or.inl hDirect

/-- Closed gradient-envelope specialization of the mixed-regime obstruction.
No persistent direct/absorbed regime is required. -/
theorem h3PathSelectedExactAdaptiveGradientContinuationOrObstruction_on_every_two_anchor_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} {h : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hGradient : ∀ t : ℝ, t ∈ Set.Ioo a T → VelocityGradientEnvelope u h t) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∀ c : ℝ, c ∈ Set.Ioo b T →
        (¬ MeasureTheory.IntegrableOn
          (h3ExactAdaptiveSelectedDirectCoefficient u
            (fun t : ℝ => 4422 * (1 + |h t|)) b) (Set.Ioo c T) ∨
         ¬ MeasureTheory.IntegrableOn
          (h3ExactAdaptiveSelectedAbsorbedCoefficient u
            (fun t : ℝ => 4422 * (1 + |h t|)) b) (Set.Ioo c T)) := by
  have hB : ∀ t : ℝ, t ∈ Set.Ioo a T →
      1 ≤ 4422 * (1 + |h t|) := by
    intro t ht
    nlinarith [abs_nonneg (h t)]
  have hTransport : ∀ t : ℝ, t ∈ Set.Ioo a T →
      |velocityH3TransportDerivativeAt u t| ≤
        (4422 * (1 + |h t|)) * velocityH3EnergyAt u t := by
    intro t ht
    exact (h3TransportControlledOnTail_of_h3Path_exactPDEPairing
      h3PathEnergyClassProducesPDEPairingIntegrability_closed
      hH3 hClass hGradient t ht).2
  exact h3PathSelectedExactAdaptiveContinuationOrObstruction_on_every_two_anchor_subtail
    hH3 hClass hB hTransport

end Euclidean
end Bridge
end PrimeTensor
