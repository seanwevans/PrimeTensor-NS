import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticAnchorOrder

/-!
# Compensation between selected adaptive shares under kinetic reanchoring

A later kinetic anchor lowers the exact adaptive minimum, but the absorbed
selected contribution can jump from zero to positive when the threshold is
crossed. This module proves that any absorbed-share increase is compensated
by a loss in the selected direct contribution. The result is pointwise and
does not silently assume measurability or temporal integrability.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- Decreasing the kinetic ceiling cannot increase the exact adaptive minimum. -/
theorem exact_kinetic_quartic_min_mono_mass
    {B E M₁ M₂ : ℝ} (hB : 0 < B) (hE : 0 < E)
    (hMass : M₁ ≤ M₂) :
    min B ((B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) * M₁) / E) ≤
    min B ((B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) * M₂) / E) := by
  apply le_min
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans
      (exact_kinetic_quartic_coefficient_mono_mass hB.le hMass hE)

/-- The *sum* of the two selected shares is antitone in the kinetic ceiling,
although its absorbed summand alone need not be. -/
theorem exact_kinetic_selected_shares_sum_mono_mass
    {B E M₁ M₂ : ℝ} (hB : 0 < B) (hE : 0 < E)
    (hMass : M₁ ≤ M₂) :
    (if E ≤ 1 + (3 + (81 / 8 : ℝ) * B ^ 3) * M₁ then B else 0) +
      (if E ≤ 1 + (3 + (81 / 8 : ℝ) * B ^ 3) * M₁ then 0
       else (B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) * M₁) / E) ≤
    (if E ≤ 1 + (3 + (81 / 8 : ℝ) * B ^ 3) * M₂ then B else 0) +
      (if E ≤ 1 + (3 + (81 / 8 : ℝ) * B ^ 3) * M₂ then 0
       else (B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) * M₂) / E) := by
  calc
    _ = min B ((B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) * M₁) / E) :=
      (h3_exact_quartic_adaptive_min_eq_selected_sum
        (B := B) (M := M₁) (E := E) hB hE).symm
    _ ≤ min B ((B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) * M₂) / E) :=
      exact_kinetic_quartic_min_mono_mass hB hE hMass
    _ = _ :=
      h3_exact_quartic_adaptive_min_eq_selected_sum
        (B := B) (M := M₂) (E := E) hB hE

/-- Along the closed energy-class path the sum of the selected shares
cannot increase when the kinetic-energy anchor is advanced. -/
theorem h3ExactAdaptiveSelectedShares_sum_mono_anchor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b c t : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hc : c ∈ Set.Ioo b T)
    (hB : 1 ≤ B t) :
    h3ExactAdaptiveSelectedDirectCoefficient u B c t +
        h3ExactAdaptiveSelectedAbsorbedCoefficient u B c t ≤
      h3ExactAdaptiveSelectedDirectCoefficient u B b t +
        h3ExactAdaptiveSelectedAbsorbedCoefficient u B b t := by
  have hAnti := antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
    h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed hH3 hClass
  have hMass : velocityH3Energy0At u c ≤ velocityH3Energy0At u b :=
    hAnti hb ⟨lt_trans hb.1 hc.1, hc.2⟩ (le_of_lt hc.1)
  have hEnergyPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hScalar := exact_kinetic_selected_shares_sum_mono_mass
    (B := B t) (E := velocityH3EnergyAt u t)
    (M₁ := velocityH3Energy0At u c)
    (M₂ := velocityH3Energy0At u b)
    (lt_of_lt_of_le zero_lt_one hB) hEnergyPos hMass
  simpa only [h3ExactAdaptiveSelectedDirectCoefficient,
    h3ExactAdaptiveSelectedAbsorbedCoefficient] using hScalar

/-- Any increase in the selected absorbed share is compensated by at least
as much decrease in the selected direct share. This remains true across
arbitrarily frequent threshold crossings. -/
theorem h3ExactAdaptiveSelectedAbsorbed_gain_le_direct_drop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b c t : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hc : c ∈ Set.Ioo b T)
    (hB : 1 ≤ B t) :
    h3ExactAdaptiveSelectedAbsorbedCoefficient u B c t -
        h3ExactAdaptiveSelectedAbsorbedCoefficient u B b t ≤
      h3ExactAdaptiveSelectedDirectCoefficient u B b t -
        h3ExactAdaptiveSelectedDirectCoefficient u B c t := by
  have hTotal := h3ExactAdaptiveSelectedShares_sum_mono_anchor
    hH3 hClass hb hc hB
  linarith only [hTotal]

/-- At a threshold crossing from earlier-direct to later-absorbed, the
newly selected absorbed coefficient is strictly smaller than the direct
coefficient that the earlier anchor selected. -/
theorem h3ExactAdaptiveSelectedAbsorbed_lt_earlier_direct_on_new_activation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {b c t : ℝ} {B : ℝ → ℝ}
    (hB : 0 < B t)
    (hEarlier : velocityH3EnergyAt u t ≤
      1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) * velocityH3Energy0At u b)
    (hLater : 1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) *
      velocityH3Energy0At u c < velocityH3EnergyAt u t) :
    h3ExactAdaptiveSelectedAbsorbedCoefficient u B c t <
      h3ExactAdaptiveSelectedDirectCoefficient u B b t := by
  have hEnergyPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hExact := (h3_exact_quartic_coefficient_lt_direct_iff
    (B := B t) (M := velocityH3Energy0At u c)
    (E := velocityH3EnergyAt u t) hB hEnergyPos).2 hLater
  simpa only [h3ExactAdaptiveSelectedDirectCoefficient,
    h3ExactAdaptiveSelectedAbsorbedCoefficient,
    if_pos hEarlier, if_neg (not_le.mpr hLater)] using hExact

end Euclidean
end Bridge
end PrimeTensor
