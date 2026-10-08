import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalUnabsorbedSuperlevelTail

/-!
# Essential simultaneous deficit of the two physical Riccati absorption channels

The exact normalized H3 balance has the two nonnegative channels

  Q = Delta + 2*D/E,  A = 4422*C1,
  U = max 0 (A*sqrt(E) - Q) = max 0 (E'/E - 4422).

For M >= 0, the superlevel U > M is exactly the PDE deficit

  Delta + 2*D/E + M < A*sqrt(E)

and, at strict H3 energy-class times, exactly the normalized slope inequality

  4422 + M < E'/E.

Hypothetical nonextension excludes almost-everywhere domination of the
combined defect by any integrable scalar remainder. Since both channels are
nonnegative, it also excludes a.e. *one-channel* compensation: for every
strict terminal subtail and every integrable remainder r, a non-null set
of times must simultaneously fail absorption by Delta + r and by 2*D/E + r.

This is a precise structural/essential-time necessary condition. It is NOT
an independently proved lower bound on Delta or D, a lower bound on the
measure of the deficit set, or a proof of continuation or blowup existence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- The positive unabsorbed growth exceeds a nonnegative threshold exactly
when the effective H3 PDE defect misses the leading nonlinear scale by
more than that threshold. This identity requires no path hypothesis. -/
theorem h3PathCanonical_unabsorbedAbove_iff_effectiveDefectDeficit
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (M t : ℝ) (hM : 0 ≤ M) :
    M < h3PathCanonicalUnabsorbedRiccatiRate u t ↔
      h3PathCanonicalEffectiveRiccatiDefect u t + M <
        (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) := by
  unfold h3PathCanonicalUnabsorbedRiccatiRate
  constructor
  · intro hAbove
    by_contra hNot
    have hCeiling :
        (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
            Real.sqrt (velocityH3EnergyAt u t) -
          h3PathCanonicalEffectiveRiccatiDefect u t ≤ M := by
      have hBound := le_of_not_gt hNot
      linarith only [hBound]
    have hMax :
        max 0 ((4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
            Real.sqrt (velocityH3EnergyAt u t) -
          h3PathCanonicalEffectiveRiccatiDefect u t) ≤ M :=
      max_le hM hCeiling
    exact (not_lt_of_ge hMax) hAbove
  · intro hDeficit
    have hRaw : M <
        (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) -
        h3PathCanonicalEffectiveRiccatiDefect u t := by
      linarith only [hDeficit]
    exact lt_of_lt_of_le hRaw (le_max_right _ _)

/-- On H3 energy-class times a positive unabsorbed superlevel is equivalent
to a physical positive logarithmic-energy slope above `4422 + M`. -/
theorem h3PathCanonical_unabsorbedAbove_iff_normalizedEnergySlopeAbove
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hM : 0 ≤ M) :
    M < h3PathCanonicalUnabsorbedRiccatiRate u t ↔
      4422 + M < deriv (velocityH3EnergyAt u) t /
        velocityH3EnergyAt u t := by
  rw [h3PathCanonical_unabsorbedRiccatiRate_eq_positiveAboveBaseline
    hH3 hClass ht]
  constructor
  · intro hAbove
    by_contra hNot
    have hRaw :
        deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t - 4422 ≤ M := by
      have hBound := le_of_not_gt hNot
      linarith only [hBound]
    have hMax : max 0
        (deriv (velocityH3EnergyAt u) t /
          velocityH3EnergyAt u t - 4422) ≤ M := max_le hM hRaw
    exact (not_lt_of_ge hMax) hAbove
  · intro hSlope
    have hRaw : M <
        deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t - 4422 := by
      linarith only [hSlope]
    exact lt_of_lt_of_le hRaw (le_max_right _ _)

/-- At any high-unabsorbed-growth instant, **both** nonnegative PDE
absorption channels individually fall below the nonlinear scale by the
specified threshold. In fact their sum does. -/
theorem h3PathCanonical_unabsorbedAbove_forces_bothChannelsBelow
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hM : 0 ≤ M)
    (hAbove : M < h3PathCanonicalUnabsorbedRiccatiRate u t) :
    h3PathCanonicalTransportCancellationGap u t + M <
        (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) ∧
      2 * velocityH3DissipationAt u t / velocityH3EnergyAt u t + M <
        (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) := by
  have hGap := (h3PathCanonical_unabsorbedAbove_iff_effectiveDefectDeficit
    u M t hM).1 hAbove
  have hCancel : 0 ≤ h3PathCanonicalTransportCancellationGap u t :=
    h3PathCanonicalTransportCancellationGap_nonneg hH3 hClass ht
  have hD : 0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t
  have hE : 0 ≤ velocityH3EnergyAt u t :=
    le_trans zero_le_one (one_le_velocityH3EnergyAt u t)
  have hNormalizedD : 0 ≤
      2 * velocityH3DissipationAt u t / velocityH3EnergyAt u t :=
    div_nonneg (mul_nonneg (by norm_num) hD) hE
  unfold h3PathCanonicalEffectiveRiccatiDefect at hGap
  constructor
  · linarith only [hGap, hNormalizedD]
  · linarith only [hGap, hCancel]

/-- A nonextendible H3 path cannot be compensated almost everywhere on a
strict terminal subtail by *either* nonnegative PDE channel separately,
up to one integrable scalar remainder. Thus simultaneous individual
channel deficits have essential (non-null) temporal presence. -/
theorem h3PathCanonical_not_ae_oneChannelCompensation_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d : ℝ} (r : ℝ → ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T)
    (hr : IntegrableOn r (Set.Ioo d T)) :
    ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) ≤
            h3PathCanonicalTransportCancellationGap u t + r t ∨
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) ≤
            2 * velocityH3DissipationAt u t / velocityH3EnergyAt u t + r t) := by
  have hFailure :=
    h3PathCanonical_effectiveDefect_not_ae_absorb_mod_integrable
      r hH3 hNoExtension hClass hd hr
  intro hEither
  apply hFailure
  filter_upwards [hEither, ae_restrict_mem measurableSet_Ioo] with t hOr ht
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hd.1 ht.1, ht.2⟩
  have hCancel : 0 ≤ h3PathCanonicalTransportCancellationGap u t :=
    h3PathCanonicalTransportCancellationGap_nonneg hH3 hClass htClass
  have hD : 0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t
  have hE : 0 ≤ velocityH3EnergyAt u t :=
    le_trans zero_le_one (one_le_velocityH3EnergyAt u t)
  have hNormalizedD : 0 ≤
      2 * velocityH3DissipationAt u t / velocityH3EnergyAt u t :=
    div_nonneg (mul_nonneg (by norm_num) hD) hE
  change
    (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
        Real.sqrt (velocityH3EnergyAt u t) ≤
      (h3PathCanonicalTransportCancellationGap u t +
        2 * velocityH3DissipationAt u t /
          velocityH3EnergyAt u t) + r t
  rcases hOr with hCancelMajor | hDissMajor
  · linarith only [hCancelMajor, hNormalizedD]
  · linarith only [hDissMajor, hCancel]

/-- A PDE result establishing almost-everywhere absorption by at least one
of the two physical channels modulo an integrable remainder on one tail
would suffice for continuation. This criterion does not assert such an
estimate for all Navier--Stokes paths. -/
theorem h3PathCanonical_extension_of_ae_oneChannelCompensation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d : ℝ} (r : ℝ → ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T)
    (hr : IntegrableOn r (Set.Ioo d T))
    (hEither : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) ≤
            h3PathCanonicalTransportCancellationGap u t + r t ∨
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) ≤
            2 * velocityH3DissipationAt u t / velocityH3EnergyAt u t + r t) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  exact (h3PathCanonical_not_ae_oneChannelCompensation_of_noExtension
    r hH3 hNoExtension hClass hd hr) hEither

/-- The simultaneous essential channel obstruction is also a statement
about physical time-derivatives: under hypothetical nonextension no finite
ceiling controls normalized positive H3 energy growth almost everywhere
on a terminal tail. -/
theorem h3PathCanonical_not_ae_normalizedEnergySlopeCeiling_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d : ℝ} (M : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T)
    (hM : 0 ≤ M) :
    ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
      deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t ≤ 4422 + M) := by
  have hNoBound :=
    h3PathCanonical_unabsorbedRate_not_ae_bounded_on_subtail
      M hH3 hNoExtension hClass hd
  intro hSlope
  apply hNoBound
  filter_upwards [hSlope, ae_restrict_mem measurableSet_Ioo] with t hLe ht
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hd.1 ht.1, ht.2⟩
  rw [h3PathCanonical_unabsorbedRiccatiRate_eq_positiveAboveBaseline
    hH3 hClass htClass]
  have hShift :
      deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t - 4422 ≤ M := by
    linarith only [hLe]
  exact max_le hM hShift

/-- Neutral alternative stating the essential simultaneous PDE-channel
obstruction for every integrable remainder and every strict terminal tail.
This remains a necessary condition, not a new coercivity inequality. -/
theorem h3PathCanonical_extension_or_essential_oneChannelDeficit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ d : ℝ, d ∈ Set.Ioo a T → ∀ r : ℝ → ℝ,
      IntegrableOn r (Set.Ioo d T) →
      ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
        (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
            Real.sqrt (velocityH3EnergyAt u t) ≤
              h3PathCanonicalTransportCancellationGap u t + r t ∨
        (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
            Real.sqrt (velocityH3EnergyAt u t) ≤
              2 * velocityH3DissipationAt u t / velocityH3EnergyAt u t + r t) := by
  by_cases hExt : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExt
  · right
    intro d hd r hr
    exact h3PathCanonical_not_ae_oneChannelCompensation_of_noExtension
      r hH3 hExt hClass hd hr

end Euclidean
end Bridge
end PrimeTensor
