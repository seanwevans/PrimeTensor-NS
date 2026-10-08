import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalDirectMargin

/-!
# Minimal normalized full-dissipation margin excess

For a prescribed nonnegative dissipation margin `ε`, the exact H3 balance
identifies the quantity

  q_ε(t) = max 0 ((-transport(t) - (2 - ε) * D(t)) / E(t))

with the positive part of `(E'(t) + ε * D(t)) / E(t)`.
This is the least *nonnegative* pointwise coefficient absorbing adverse
transport with `(2 - ε)` copies of the full H3 dissipation remaining.
The family increases with ε, and dominates the previously closed full-
dissipation positive logarithmic growth rate when ε is nonnegative.

If q_ε were temporally integrable on one H3 energy-class tail, the exact
balance and the previous scalar continuation theorem would extend the path.
Thus hypothetical nonextension forces its nonintegrability on every strict
terminal tail, without any kinetic-anchor positivity assumption. This is a
necessary condition, not a new estimate that proves q_ε integrable.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory

/-- Minimal nonnegative normalized transport coefficient after retaining a
specified `ε` portion of the full H3 dissipation. -/
noncomputable def h3PathCanonicalMarginExcessRate
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (ε : ℝ) : ℝ → ℝ :=
  fun t => max 0
    ((- velocityH3TransportDerivativeAt u t -
        (2 - ε) * velocityH3DissipationAt u t) /
      velocityH3EnergyAt u t)

/-- Every margin excess rate is pointwise nonnegative. -/
theorem h3PathCanonicalMarginExcessRate_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (ε t : ℝ) :
    0 ≤ h3PathCanonicalMarginExcessRate u ε t := by
  unfold h3PathCanonicalMarginExcessRate
  exact le_max_left _ _

/-- The canonical margin rate gives an exact valid transport upper envelope.
This requires no sign assumption on the chosen scalar margin. -/
theorem h3PathCanonicalMarginExcessRate_transport_bound
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (ε t : ℝ) :
    - velocityH3TransportDerivativeAt u t ≤
      (2 - ε) * velocityH3DissipationAt u t +
        h3PathCanonicalMarginExcessRate u ε t * velocityH3EnergyAt u t := by
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hDiv :
      (- velocityH3TransportDerivativeAt u t -
          (2 - ε) * velocityH3DissipationAt u t) /
          velocityH3EnergyAt u t ≤
        h3PathCanonicalMarginExcessRate u ε t := by
    unfold h3PathCanonicalMarginExcessRate
    exact le_max_right _ _
  have hMul := (div_le_iff₀ hEPos).1 hDiv
  nlinarith only [hMul]

/-- Minimality among nonnegative scalar remainder coefficients when the
same amount `(2 - ε)` of viscous dissipation is retained. -/
theorem h3PathCanonicalMarginExcessRate_le_of_transport_bound
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {r : ℝ → ℝ} {ε t : ℝ}
    (hr : 0 ≤ r t)
    (hTransport :
      - velocityH3TransportDerivativeAt u t ≤
        (2 - ε) * velocityH3DissipationAt u t +
          r t * velocityH3EnergyAt u t) :
    h3PathCanonicalMarginExcessRate u ε t ≤ r t := by
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hDiv :
      (- velocityH3TransportDerivativeAt u t -
          (2 - ε) * velocityH3DissipationAt u t) /
          velocityH3EnergyAt u t ≤ r t := by
    apply (div_le_iff₀ hEPos).2
    nlinarith only [hTransport]
  unfold h3PathCanonicalMarginExcessRate
  exact max_le hr hDiv

/-- Retaining more of the dissipation makes the minimal transport remainder
larger, since the full H3 dissipation is nonnegative. -/
theorem h3PathCanonicalMarginExcessRate_mono_margin
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) (t : ℝ) :
    h3PathCanonicalMarginExcessRate u ε₁ t ≤
      h3PathCanonicalMarginExcessRate u ε₂ t := by
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hD : 0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t
  have hMargin : 0 ≤ (ε₂ - ε₁) * velocityH3DissipationAt u t :=
    mul_nonneg (sub_nonneg.mpr hε) hD
  have hNumerator :
      - velocityH3TransportDerivativeAt u t -
          (2 - ε₁) * velocityH3DissipationAt u t ≤
        - velocityH3TransportDerivativeAt u t -
          (2 - ε₂) * velocityH3DissipationAt u t := by
    nlinarith only [hMargin]
  have hDiv :=
    (div_le_div_iff_of_pos_right hEPos).2 hNumerator
  unfold h3PathCanonicalMarginExcessRate
  exact max_le_max_left 0 hDiv

/-- Every nonnegative retained margin dominates the exact minimal positive
full-dissipation logarithmic growth rate. -/
theorem h3PathFullDissipationTransportExcessRate_le_marginExcessRate
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    h3PathFullDissipationTransportExcessRate u t ≤
      h3PathCanonicalMarginExcessRate u ε t := by
  have hZero :=
    h3PathCanonicalMarginExcessRate_mono_margin u hε t
  simpa only [h3PathCanonicalMarginExcessRate,
    h3PathFullDissipationTransportExcessRate, sub_zero] using hZero

/-- The exact PDE balance identifies the scalar margin excess with positive
normalized H3-energy slope plus the retained dissipation penalty. -/
theorem h3PathCanonicalMarginExcessRate_eq_energyDissipationRatio
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ} (ε : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathCanonicalMarginExcessRate u ε t =
      max 0 ((deriv (velocityH3EnergyAt u) t +
        ε * velocityH3DissipationAt u t) /
          velocityH3EnergyAt u t) := by
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass ht
  have hNum :
      - velocityH3TransportDerivativeAt u t -
          (2 - ε) * velocityH3DissipationAt u t =
        deriv (velocityH3EnergyAt u) t +
          ε * velocityH3DissipationAt u t := by
    nlinarith only [hBalance]
  unfold h3PathCanonicalMarginExcessRate
  rw [hNum]

/-- Integrability of the explicit minimal margin rate, for any nonnegative
margin, closes H3 continuation without assuming a positive kinetic anchor. -/
theorem h3PathCanonical_extension_of_integrable_marginExcessRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hε : 0 ≤ ε)
    (hInt : IntegrableOn (h3PathCanonicalMarginExcessRate u ε)
      (Set.Ioo a T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  apply h3PathExtension_of_integrableLinearEnergyGrowthMajorantOnTail
    hH3 hClass hInt
  intro t ht
  exact h3PathCanonical_energyGrowth_le_of_dissipationMargin
    hH3 hClass ht hε
    (h3PathCanonicalMarginExcessRate_transport_bound u ε t)

/-- Nonextension forces every nonnegative-margin rate to fail L1 on every
energy-class terminal interval, with no kinetic-anchor assumption. -/
theorem h3PathCanonicalMarginExcessRate_nonintegrable_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hε : 0 ≤ ε) :
    ¬ IntegrableOn (h3PathCanonicalMarginExcessRate u ε)
      (Set.Ioo a T) := by
  intro hInt
  exact hNoExtension
    (h3PathCanonical_extension_of_integrable_marginExcessRate
      hH3 hClass hε hInt)

/-- The nonintegrability statement persists on *every* later strict tail
and simultaneously at every fixed nonnegative dissipation margin. -/
theorem h3PathCanonicalMarginExcessRate_nonintegrable_on_all_later_tails
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∀ ε : ℝ, 0 ≤ ε →
    ∀ d : ℝ, d ∈ Set.Ioo a T →
      ¬ IntegrableOn (h3PathCanonicalMarginExcessRate u ε)
        (Set.Ioo d T) := by
  intro ε hε d hd
  have hClassD : PreterminalH3EnergyClass u d T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hd.1) hd.2
  exact h3PathCanonicalMarginExcessRate_nonintegrable_of_noExtension
    hH3 hNoExtension hClassD hε

/-- Neutral dichotomy: continuation, or all nonnegative exact dissipation
margin remainders are nonintegrable on every strict terminal tail. -/
theorem h3PathCanonical_extension_or_all_marginExcessRates_nonintegrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ ε : ℝ, 0 ≤ ε →
    ∀ d : ℝ, d ∈ Set.Ioo a T →
      ¬ IntegrableOn (h3PathCanonicalMarginExcessRate u ε)
        (Set.Ioo d T) := by
  by_cases hExt : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExt
  · exact Or.inr
      (h3PathCanonicalMarginExcessRate_nonintegrable_on_all_later_tails
        hH3 hExt hClass)

end Euclidean
end Bridge
end PrimeTensor
