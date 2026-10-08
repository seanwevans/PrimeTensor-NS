import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuartic

/-!
# Fixed-anchor exact adaptive obstruction on later subtails

The kinetic-energy ceiling may be anchored at b while the temporal
integrability test is restricted to any later c.  In particular,
nonextension forces divergence of the same fixed-anchor adaptive
coefficient on every later tail, without reanchoring the coefficient.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- The exact anchored derivative bound retains the better of the direct
transport estimate and the epsilon-two absorption estimate. -/
theorem deriv_velocityH3EnergyAt_le_min_direct_exact_fixed_anchor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo b T)
    (hB : 1 ≤ B)
    (hTransport : |velocityH3TransportDerivativeAt u t| ≤
      B * velocityH3EnergyAt u t) :
    deriv (velocityH3EnergyAt u) t ≤
      min B ((B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) *
        velocityH3Energy0At u b) / velocityH3EnergyAt u t) *
        velocityH3EnergyAt u t := by
  have htOld : t ∈ Set.Ioo a T := ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hBalance := deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
    hH3 hClass htOld
  have hDirect : deriv (velocityH3EnergyAt u) t ≤
      B * velocityH3EnergyAt u t := by
    have hD := velocityH3DissipationAt_nonneg u t
    have hNeg := neg_le_abs (velocityH3TransportDerivativeAt u t)
    linarith only [hBalance, hD, hNeg, hTransport]
  have hExact := deriv_velocityH3EnergyAt_le_anchored_exact_quartic_majorant
    hH3 hClass hb ht (le_trans zero_le_one hB) hTransport
  by_cases hCompare : B ≤
      (B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) *
        velocityH3Energy0At u b) / velocityH3EnergyAt u t
  · simpa only [min_eq_left hCompare] using hDirect
  · simpa only [min_eq_right (le_of_not_ge hCompare)] using hExact

/-- A coefficient anchored at b needs to be integrable only on a later
strict subtail (c,T); the energy class can be restricted independently. -/
theorem h3PathExtension_of_integrableFixedAnchorExactAdaptiveCoefficientOnLaterSubtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b c : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hc : c ∈ Set.Ioo b T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo c T → 1 ≤ B t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo c T →
      |velocityH3TransportDerivativeAt u t| ≤ B t * velocityH3EnergyAt u t)
    (hMinimum : MeasureTheory.IntegrableOn
      (fun t : ℝ => min (B t)
        ((B t + (3 * B t + (3 * B t) ^ 4 / (2 : ℝ) ^ 3) *
          velocityH3Energy0At u b) / velocityH3EnergyAt u t)) (Set.Ioo c T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hClassC : PreterminalH3EnergyClass u c T :=
    preterminalH3EnergyClass_restrict_left hClass
      (le_of_lt (lt_trans hb.1 hc.1)) hc.2
  apply h3PathExtension_of_integrableLinearEnergyGrowthMajorantOnTail
    hH3 hClassC hMinimum
  intro t ht
  exact deriv_velocityH3EnergyAt_le_min_direct_exact_fixed_anchor
    hH3 hClass hb ⟨lt_trans hc.1 ht.1, ht.2⟩
      (hB t ht) (hTransport t ht)

/-- Under nonextension, one fixed-anchor scalar coefficient remains
nonintegrable on every strictly later subtail. -/
theorem h3PathExactAdaptiveFixedAnchorContinuationOrObstruction_on_every_laterSubtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo b T → 1 ≤ B t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo b T →
      |velocityH3TransportDerivativeAt u t| ≤ B t * velocityH3EnergyAt u t) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ c : ℝ, c ∈ Set.Ioo b T →
      ¬ MeasureTheory.IntegrableOn
        (fun t : ℝ => min (B t)
          ((B t + (3 * B t + (3 * B t) ^ 4 / (2 : ℝ) ^ 3) *
            velocityH3Energy0At u b) / velocityH3EnergyAt u t)) (Set.Ioo c T) := by
  by_cases hExtension : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · right
    intro c hc hMinimum
    apply hExtension
    apply h3PathExtension_of_integrableFixedAnchorExactAdaptiveCoefficientOnLaterSubtail
      hH3 hClass hb hc
    · intro t ht
      exact hB t ⟨lt_trans hc.1 ht.1, ht.2⟩
    · intro t ht
      exact hTransport t ⟨lt_trans hc.1 ht.1, ht.2⟩
    · exact hMinimum

/-- Specialize the fixed-anchor obstruction to the closed gradient-envelope
coefficient, without adding a temporal regularity hypothesis. -/
theorem h3PathExactAdaptiveGradientFixedAnchorContinuationOrObstruction_on_every_laterSubtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ} {h : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hGradient : ∀ t : ℝ, t ∈ Set.Ioo b T → VelocityGradientEnvelope u h t) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ c : ℝ, c ∈ Set.Ioo b T →
      ¬ MeasureTheory.IntegrableOn
        (fun t : ℝ => min (4422 * (1 + |h t|))
          ((4422 * (1 + |h t|) +
            (3 * (4422 * (1 + |h t|)) +
              (3 * (4422 * (1 + |h t|))) ^ 4 / (2 : ℝ) ^ 3) *
              velocityH3Energy0At u b) /
            velocityH3EnergyAt u t)) (Set.Ioo c T) := by
  have hClassB : PreterminalH3EnergyClass u b T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hb.1) hb.2
  have hB : ∀ t : ℝ, t ∈ Set.Ioo b T →
      1 ≤ 4422 * (1 + |h t|) := by
    intro t ht
    nlinarith [abs_nonneg (h t)]
  have hTransport : ∀ t : ℝ, t ∈ Set.Ioo b T →
      |velocityH3TransportDerivativeAt u t| ≤
        (4422 * (1 + |h t|)) * velocityH3EnergyAt u t := by
    intro t ht
    exact (h3TransportControlledOnTail_of_h3Path_exactPDEPairing
      h3PathEnergyClassProducesPDEPairingIntegrability_closed
      hH3 hClassB hGradient t ht).2
  exact h3PathExactAdaptiveFixedAnchorContinuationOrObstruction_on_every_laterSubtail
    hH3 hClass hb hB hTransport

/-- The fixed-anchor adaptive minimum improves when the kinetic-energy
anchor moves later; both coefficients are compared at the same later time. -/
theorem exact_kinetic_quartic_adaptive_min_mono_anchor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b c t B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hc : c ∈ Set.Ioo b T)
    (ht : t ∈ Set.Ioo c T) (hB : 0 ≤ B) :
    min B ((B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) *
      velocityH3Energy0At u c) / velocityH3EnergyAt u t) ≤
    min B ((B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) *
      velocityH3Energy0At u b) / velocityH3EnergyAt u t) := by
  apply le_min
  · exact min_le_left _ _
  · exact le_trans (min_le_right _ _)
      (exact_kinetic_quartic_coefficient_mono_anchor hH3 hClass hb hc ht hB)

end Euclidean
end Bridge
end PrimeTensor
