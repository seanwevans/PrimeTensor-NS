import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticPersistentShares

/-!
# Order of the selected shares across kinetic anchors

Advancing the kinetic anchor decreases the exact absorption threshold.
Therefore the selected direct contribution decreases pointwise, and once
absorption is active at an earlier anchor it remains active at any later
anchor. On that common absorbed region the selected absorbed contribution
also decreases. Globally, however, the absorbed contribution need not be
monotone: it can switch from zero to positive as the threshold falls.

These are pointwise facts. In particular, they do not silently assert an
integrability transfer for arbitrary possibly nonmeasurable B or an
anchor-independent selection of a nonintegrable share.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- Lowering the selection threshold cannot increase the selected direct
value when B is nonnegative. -/
theorem exact_kinetic_selected_direct_mono_threshold
    {B E later earlier : ℝ} (hB : 0 ≤ B) (hThreshold : later ≤ earlier) :
    (if E ≤ later then B else 0) ≤ (if E ≤ earlier then B else 0) := by
  by_cases hLater : E ≤ later
  · have hEarlier : E ≤ earlier := le_trans hLater hThreshold
    simpa only [if_pos hLater, if_pos hEarlier] using (le_refl B)
  · by_cases hEarlier : E ≤ earlier
    · simpa only [if_neg hLater, if_pos hEarlier] using hB
    · simpa only [if_neg hLater, if_neg hEarlier] using (le_refl (0 : ℝ))

/-- Absorption activated above the earlier threshold is also activated
above any lower threshold. -/
theorem exact_kinetic_absorption_active_mono_threshold
    {E later earlier : ℝ} (hThreshold : later ≤ earlier)
    (hEarlierActive : earlier < E) : later < E :=
  lt_of_le_of_lt hThreshold hEarlierActive

/-- The selected direct coefficient is antitone in the kinetic anchor on
the energy-class tail. -/
theorem h3ExactAdaptiveSelectedDirectCoefficient_mono_anchor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b c t : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hc : c ∈ Set.Ioo b T)
    (hB : 0 ≤ B t) :
    h3ExactAdaptiveSelectedDirectCoefficient u B c t ≤
      h3ExactAdaptiveSelectedDirectCoefficient u B b t := by
  have hThreshold := exact_kinetic_quartic_activation_threshold_mono_anchor
    hH3 hClass hb hc hB
  unfold h3ExactAdaptiveSelectedDirectCoefficient
  exact exact_kinetic_selected_direct_mono_threshold hB hThreshold

/-- Earlier activation also identifies the later selected absorbed
coefficient with the full exact normalized absorbed expression. -/
theorem h3ExactAdaptiveSelectedAbsorbedCoefficient_eq_of_earlier_activation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b c t : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hc : c ∈ Set.Ioo b T)
    (hB : 0 ≤ B t)
    (hHigh : 1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) *
        velocityH3Energy0At u b < velocityH3EnergyAt u t) :
    h3ExactAdaptiveSelectedAbsorbedCoefficient u B c t =
      (B t + (3 * B t + (3 * B t) ^ 4 / (2 : ℝ) ^ 3) *
        velocityH3Energy0At u c) / velocityH3EnergyAt u t := by
  have hThreshold := exact_kinetic_quartic_activation_threshold_mono_anchor
    hH3 hClass hb hc hB
  have hLaterHigh :
      1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) *
        velocityH3Energy0At u c < velocityH3EnergyAt u t :=
    lt_of_le_of_lt hThreshold hHigh
  unfold h3ExactAdaptiveSelectedAbsorbedCoefficient
  simp only [if_neg (not_le.mpr hLaterHigh)]

/-- On the region where absorption is already active at the earlier anchor,
advancing the anchor also decreases the selected absorbed coefficient. -/
theorem h3ExactAdaptiveSelectedAbsorbedCoefficient_le_of_earlier_activation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b c t : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hc : c ∈ Set.Ioo b T)
    (ht : t ∈ Set.Ioo c T) (hB : 0 ≤ B t)
    (hHigh : 1 + (3 + (81 / 8 : ℝ) * (B t) ^ 3) *
        velocityH3Energy0At u b < velocityH3EnergyAt u t) :
    h3ExactAdaptiveSelectedAbsorbedCoefficient u B c t ≤
      h3ExactAdaptiveSelectedAbsorbedCoefficient u B b t := by
  have hLater := h3ExactAdaptiveSelectedAbsorbedCoefficient_eq_of_earlier_activation
    hH3 hClass hb hc hB hHigh
  have hEarlier : h3ExactAdaptiveSelectedAbsorbedCoefficient u B b t =
      (B t + (3 * B t + (3 * B t) ^ 4 / (2 : ℝ) ^ 3) *
        velocityH3Energy0At u b) / velocityH3EnergyAt u t := by
    unfold h3ExactAdaptiveSelectedAbsorbedCoefficient
    simp only [if_neg (not_le.mpr hHigh)]
  rw [hLater, hEarlier]
  exact exact_kinetic_quartic_coefficient_mono_anchor
    hH3 hClass hb hc ht hB

/-- A scalar example shows why unconditional monotonicity of the selected
absorbed share cannot be used in an anchor-synchronization argument:
the older anchor selects zero, while the later anchor selects 1/10. -/
theorem exact_kinetic_selected_absorbed_not_globally_antitone :
    (if (10 : ℝ) ≤ 1 + (3 + (81 / 8 : ℝ) * (1 : ℝ) ^ 3) * 0
      then 0 else ((1 + (3 * 1 + (3 * 1) ^ 4 / (2 : ℝ) ^ 3) * 0) / 10)) >
    (if (10 : ℝ) ≤ 1 + (3 + (81 / 8 : ℝ) * (1 : ℝ) ^ 3) * 1
      then 0 else ((1 + (3 * 1 + (3 * 1) ^ 4 / (2 : ℝ) ^ 3) * 1) / 10)) := by
  norm_num

end Euclidean
end Bridge
end PrimeTensor
