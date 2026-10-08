import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticFixedAnchor

/-!
# Two-anchor adaptive obstruction and exact activation threshold

The first anchor fixes the kinetic ceiling; the second moves the integration
interval. We retain the continuation/nonextension dichotomy jointly for both
anchors. Separately, the exact scalar threshold selects the direct or absorbed
branch, and the threshold decreases with later kinetic anchors.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- A larger kinetic ceiling moves the exact absorption threshold upward. -/
theorem exact_kinetic_quartic_activation_threshold_mono_mass
    {B M₁ M₂ : ℝ} (hB : 0 ≤ B) (hMass : M₁ ≤ M₂) :
    1 + (3 + (81 / 8 : ℝ) * B ^ 3) * M₁ ≤
      1 + (3 + (81 / 8 : ℝ) * B ^ 3) * M₂ := by
  have hCoefficient : 0 ≤ 3 + (81 / 8 : ℝ) * B ^ 3 := by
    positivity
  have hProduct := mul_le_mul_of_nonneg_left hMass hCoefficient
  linarith only [hProduct]

/-- The exact activation threshold can only fall under a later kinetic
anchor on the closed H3 energy-class tail. -/
theorem exact_kinetic_quartic_activation_threshold_mono_anchor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b c B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hc : c ∈ Set.Ioo b T) (hB : 0 ≤ B) :
    1 + (3 + (81 / 8 : ℝ) * B ^ 3) * velocityH3Energy0At u c ≤
      1 + (3 + (81 / 8 : ℝ) * B ^ 3) * velocityH3Energy0At u b := by
  have hAnti := antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
    h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed hH3 hClass
  have hMass : velocityH3Energy0At u c ≤ velocityH3Energy0At u b :=
    hAnti hb ⟨lt_trans hb.1 hc.1, hc.2⟩ (le_of_lt hc.1)
  exact exact_kinetic_quartic_activation_threshold_mono_mass hB hMass

/-- Below the exact activation threshold, the adaptive minimum uses direct
transport growth. This is a scalar fact, independent of the PDE. -/
theorem exact_kinetic_quartic_adaptive_min_eq_direct_of_below_threshold
    {B M E : ℝ} (hB : 0 < B) (hE : 0 < E)
    (hLow : E ≤ 1 + (3 + (81 / 8 : ℝ) * B ^ 3) * M) :
    min B ((B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) * M) / E) = B := by
  have hNot : ¬ ((B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) * M) / E < B) := by
    intro hSmaller
    exact (not_lt_of_ge hLow)
      ((h3_exact_quartic_coefficient_lt_direct_iff hB hE).mp hSmaller)
  exact min_eq_left (le_of_not_gt hNot)

/-- Above the exact activation threshold, the adaptive minimum uses the
absorbed coefficient instead of the direct coefficient. -/
theorem exact_kinetic_quartic_adaptive_min_eq_absorbed_of_above_threshold
    {B M E : ℝ} (hB : 0 < B) (hE : 0 < E)
    (hHigh : 1 + (3 + (81 / 8 : ℝ) * B ^ 3) * M < E) :
    min B ((B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) * M) / E) =
      (B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) * M) / E := by
  have hSmaller := (h3_exact_quartic_coefficient_lt_direct_iff hB hE).2 hHigh
  exact min_eq_right (le_of_lt hSmaller)

/-- If absorption is active for an earlier kinetic anchor, it stays active
when the anchor is advanced while observing the same later time. -/
theorem exact_kinetic_quartic_absorption_active_after_later_anchor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b c t B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hc : c ∈ Set.Ioo b T)
    (ht : t ∈ Set.Ioo c T) (hB : 0 < B)
    (hHigh : 1 + (3 + (81 / 8 : ℝ) * B ^ 3) *
        velocityH3Energy0At u b < velocityH3EnergyAt u t) :
    min B ((B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) *
      velocityH3Energy0At u c) / velocityH3EnergyAt u t) =
      (B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) *
        velocityH3Energy0At u c) / velocityH3EnergyAt u t := by
  have hThreshold := exact_kinetic_quartic_activation_threshold_mono_anchor
    hH3 hClass hb hc (le_of_lt hB)
  have hEnergyPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  exact exact_kinetic_quartic_adaptive_min_eq_absorbed_of_above_threshold
    hB hEnergyPos (lt_of_le_of_lt hThreshold hHigh)

/-- Universal two-anchor scalar dichotomy: the kinetic anchor b and the
later start c of the integrability interval may both vary. -/
theorem h3PathExactAdaptiveQuarticContinuationOrObstruction_on_every_two_anchor_subtail
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
        ¬ MeasureTheory.IntegrableOn
          (fun t : ℝ => min (B t)
            ((B t + (3 * B t + (3 * B t) ^ 4 / (2 : ℝ) ^ 3) *
              velocityH3Energy0At u b) / velocityH3EnergyAt u t))
          (Set.Ioo c T) := by
  by_cases hExtension : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · right
    intro b hb c hc
    have hFixed :=
      h3PathExactAdaptiveFixedAnchorContinuationOrObstruction_on_every_laterSubtail
        hH3 hClass hb
        (fun t ht => hB t ⟨lt_trans hb.1 ht.1, ht.2⟩)
        (fun t ht => hTransport t ⟨lt_trans hb.1 ht.1, ht.2⟩)
    exact hFixed.elim (fun h => False.elim (hExtension h)) (fun h => h c hc)

/-- Universal two-anchor gradient-envelope dichotomy, keeping the original
closed gradient hypothesis on the energy-class interval. -/
theorem h3PathExactAdaptiveGradientContinuationOrObstruction_on_every_two_anchor_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} {h : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hGradient : ∀ t : ℝ, t ∈ Set.Ioo a T → VelocityGradientEnvelope u h t) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∀ c : ℝ, c ∈ Set.Ioo b T →
        ¬ MeasureTheory.IntegrableOn
          (fun t : ℝ => min (4422 * (1 + |h t|))
            ((4422 * (1 + |h t|) +
              (3 * (4422 * (1 + |h t|)) +
                (3 * (4422 * (1 + |h t|))) ^ 4 / (2 : ℝ) ^ 3) *
                velocityH3Energy0At u b) / velocityH3EnergyAt u t))
          (Set.Ioo c T) := by
  by_cases hExtension : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · right
    intro b hb c hc
    have hFixed :=
      h3PathExactAdaptiveGradientFixedAnchorContinuationOrObstruction_on_every_laterSubtail
        hH3 hClass hb
        (fun t ht => hGradient t ⟨lt_trans hb.1 ht.1, ht.2⟩)
    exact hFixed.elim (fun h => False.elim (hExtension h)) (fun h => h c hc)

end Euclidean
end Bridge
end PrimeTensor
