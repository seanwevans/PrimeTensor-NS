import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalChannelOccupationBarrier

/-!
# Pure H3 dissipation deficit and the critical cubic PDE ceiling

The exact canonical H3 energy budget reads

  E'/E + Delta + 2*D/E = 4422 + A*sqrt(E),   A=4422*C1.

Rather than assuming a new coercive inequality for Delta or D, isolate the
*dissipation-only* positive deficit

  V(t) = max 0 (A*sqrt(E(t)) - 2*D(t)/E(t)).

On every strict H3 energy-class time, the actual unabsorbed positive growth
U satisfies the quantitative two-channel comparison

  U <= V <= U + Delta.

Thus V is a directly physical upper envelope for U and its difference from U
is bounded by the nonnegative transport cancellation gap. Integrability of V
on one terminal H3 energy-class tail suffices for smooth continuation.

For M>=0, V>M is *equivalent* to the raw cubic dissipation shortfall

  2*D + M*E < A*sqrt(E)*E.

Nonextension therefore precludes an almost-everywhere cubic dissipation floor
up to any fixed linear margin on every terminal energy-class subtail.

None of these statements proves such a floor, a new interpolation estimate,
continuation without an additional analytic input, or existence of blowup.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- The leading cubic growth left over after retaining *only* the actual H3
viscous dissipation, before using any transport-cancellation saving. -/
noncomputable def h3PathCanonicalDissipationOnlyRiccatiDeficit
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) : ℝ → ℝ :=
  fun t => max 0
    ((4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
      Real.sqrt (velocityH3EnergyAt u t) -
      2 * velocityH3DissipationAt u t / velocityH3EnergyAt u t)

/-- The dissipation-only deficit is nonnegative, without any path hypothesis. -/
theorem h3PathCanonical_dissipationOnlyDeficit_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) :
    0 ≤ h3PathCanonicalDissipationOnlyRiccatiDeficit u t := by
  unfold h3PathCanonicalDissipationOnlyRiccatiDeficit
  exact le_max_left _ _

/-- Dropping nonnegative transport cancellation gives a physical PDE upper
bound for the *actual* unabsorbed nonlinear Riccati growth rate. -/
theorem h3PathCanonical_unabsorbedRate_le_dissipationOnlyDeficit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathCanonicalUnabsorbedRiccatiRate u t ≤
      h3PathCanonicalDissipationOnlyRiccatiDeficit u t := by
  have hDelta : 0 ≤ h3PathCanonicalTransportCancellationGap u t :=
    h3PathCanonicalTransportCancellationGap_nonneg hH3 hClass ht
  have hRaw :
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) -
        (h3PathCanonicalTransportCancellationGap u t +
          2 * velocityH3DissipationAt u t / velocityH3EnergyAt u t) ≤
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) -
        2 * velocityH3DissipationAt u t / velocityH3EnergyAt u t := by
    linarith only [hDelta]
  unfold h3PathCanonicalUnabsorbedRiccatiRate
    h3PathCanonicalEffectiveRiccatiDefect
    h3PathCanonicalDissipationOnlyRiccatiDeficit
  exact max_le_max_left 0 hRaw

/-- The cost of discarding transport cancellation is at most the exact
nonnegative normalized cancellation gap. The comparison is two-sided. -/
theorem h3PathCanonical_dissipationOnlyDeficit_le_unabsorbed_add_cancellation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathCanonicalDissipationOnlyRiccatiDeficit u t ≤
      h3PathCanonicalUnabsorbedRiccatiRate u t +
        h3PathCanonicalTransportCancellationGap u t := by
  have hDelta : 0 ≤ h3PathCanonicalTransportCancellationGap u t :=
    h3PathCanonicalTransportCancellationGap_nonneg hH3 hClass ht
  have hUNonneg : 0 ≤ h3PathCanonicalUnabsorbedRiccatiRate u t :=
    h3PathCanonical_unabsorbedRiccatiRate_nonneg u t
  have hRaw :
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) -
        2 * velocityH3DissipationAt u t / velocityH3EnergyAt u t ≤
      h3PathCanonicalUnabsorbedRiccatiRate u t +
        h3PathCanonicalTransportCancellationGap u t := by
    have hMax :
        (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
            Real.sqrt (velocityH3EnergyAt u t) -
          (h3PathCanonicalTransportCancellationGap u t +
            2 * velocityH3DissipationAt u t / velocityH3EnergyAt u t) ≤
        h3PathCanonicalUnabsorbedRiccatiRate u t := by
      unfold h3PathCanonicalUnabsorbedRiccatiRate
        h3PathCanonicalEffectiveRiccatiDefect
      exact le_max_right _ _
    linarith only [hMax]
  unfold h3PathCanonicalDissipationOnlyRiccatiDeficit
  exact max_le (add_nonneg hUNonneg hDelta) hRaw

/-- A positive dissipation-only deficit above threshold M is *exactly* a
failure of the corresponding raw cubic-scale dissipation ceiling. -/
theorem h3PathCanonical_dissipationOnlyDeficit_above_iff_cubicDissipationShortfall
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (M t : ℝ) (hM : 0 ≤ M) :
    M < h3PathCanonicalDissipationOnlyRiccatiDeficit u t ↔
      2 * velocityH3DissipationAt u t + M * velocityH3EnergyAt u t <
        ((4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t := by
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  constructor
  · intro hAbove
    have hRaw : M <
        (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) -
        2 * velocityH3DissipationAt u t / velocityH3EnergyAt u t := by
      by_contra hNot
      have hUpper : h3PathCanonicalDissipationOnlyRiccatiDeficit u t ≤ M := by
        unfold h3PathCanonicalDissipationOnlyRiccatiDeficit
        exact max_le hM (le_of_not_gt hNot)
      exact (not_lt_of_ge hUpper) hAbove
    have hRatio :
        2 * velocityH3DissipationAt u t / velocityH3EnergyAt u t <
          (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
            Real.sqrt (velocityH3EnergyAt u t) - M := by
      linarith only [hRaw]
    have hScaled := (div_lt_iff₀ hEPos).1 hRatio
    nlinarith only [hScaled]
  · intro hScaled
    have hRatio :
        2 * velocityH3DissipationAt u t / velocityH3EnergyAt u t <
          (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
            Real.sqrt (velocityH3EnergyAt u t) - M := by
      apply (div_lt_iff₀ hEPos).2
      nlinarith only [hScaled]
    have hRaw : M <
        (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) -
        2 * velocityH3DissipationAt u t / velocityH3EnergyAt u t := by
      linarith only [hRatio]
    unfold h3PathCanonicalDissipationOnlyRiccatiDeficit
    exact lt_of_lt_of_le hRaw (le_max_right _ _)

/-- If actual unabsorbed growth exceeds M, the *raw viscous dissipation*
must lie below the critical cubic energy scale with a linear M margin. -/
theorem h3PathCanonical_unabsorbedAbove_forces_cubicDissipationShortfall
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hM : 0 ≤ M)
    (hAbove : M < h3PathCanonicalUnabsorbedRiccatiRate u t) :
    2 * velocityH3DissipationAt u t + M * velocityH3EnergyAt u t <
      ((4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t := by
  have hV : M < h3PathCanonicalDissipationOnlyRiccatiDeficit u t :=
    lt_of_lt_of_le hAbove
      (h3PathCanonical_unabsorbedRate_le_dissipationOnlyDeficit
        hH3 hClass ht)
  exact (h3PathCanonical_dissipationOnlyDeficit_above_iff_cubicDissipationShortfall
    u M t hM).1 hV

/-- Integrability of the *dissipation-only* PDE shortfall, even without
using transport cancellation, is sufficient for smooth continuation. -/
theorem h3PathCanonical_extension_of_integrable_dissipationOnlyDeficit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hInt : IntegrableOn (h3PathCanonicalDissipationOnlyRiccatiDeficit u)
      (Set.Ioo a T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hMeas : AEStronglyMeasurable
      (h3PathCanonicalUnabsorbedRiccatiRate u)
      ((volume : Measure ℝ).restrict (Set.Ioo a T)) :=
    h3PathCanonical_unabsorbedRate_aestronglyMeasurableOnTail hH3 hClass
  have hNorm : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo a T)),
      ‖h3PathCanonicalUnabsorbedRiccatiRate u t‖ ≤
        h3PathCanonicalDissipationOnlyRiccatiDeficit u t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs,
      abs_of_nonneg (h3PathCanonical_unabsorbedRiccatiRate_nonneg u t)]
    exact h3PathCanonical_unabsorbedRate_le_dissipationOnlyDeficit
      hH3 hClass ht
  have hU : IntegrableOn (h3PathCanonicalUnabsorbedRiccatiRate u)
      (Set.Ioo a T) := Integrable.mono' hInt hMeas hNorm
  exact h3PathCanonical_extension_of_integrable_unabsorbedRiccatiRate
    hH3 hClass hU

/-- Hypothetical nonextension forces nonintegrability of the pure viscous
cubic deficit on *every* strict H3 energy-class terminal subtail. -/
theorem h3PathCanonical_not_integrable_dissipationOnlyDeficit_on_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T) :
    ¬ IntegrableOn (h3PathCanonicalDissipationOnlyRiccatiDeficit u)
      (Set.Ioo d T) := by
  have hClassD : PreterminalH3EnergyClass u d T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hd.1) hd.2
  intro hInt
  exact hNoExtension
    (h3PathCanonical_extension_of_integrable_dissipationOnlyDeficit
      hH3 hClassD hInt)

/-- A hypothetical nonextendible H3 path cannot have the critical cubic
viscous-dissipation floor (even with any fixed linear-energy slack) almost
everywhere on a strict terminal subtail. The shortfall has non-null time
presence; no quantitative duration bound is asserted. -/
theorem h3PathCanonical_not_ae_cubicDissipationFloor_on_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d : ℝ} (M : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T)
    (hM : 0 ≤ M) :
    ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
      ((4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t ≤
        2 * velocityH3DissipationAt u t + M * velocityH3EnergyAt u t) := by
  have hNoU := h3PathCanonical_unabsorbedRate_not_ae_bounded_on_subtail
    M hH3 hNoExtension hClass hd
  intro hFloor
  apply hNoU
  filter_upwards [hFloor, ae_restrict_mem measurableSet_Ioo] with t hDissFloor ht
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hd.1 ht.1, ht.2⟩
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hDLower :
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) - M ≤
        2 * velocityH3DissipationAt u t / velocityH3EnergyAt u t := by
    apply (le_div_iff₀ hEPos).2
    nlinarith only [hDissFloor]
  have hRaw :
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) -
        2 * velocityH3DissipationAt u t / velocityH3EnergyAt u t ≤ M := by
    linarith only [hDLower]
  have hV : h3PathCanonicalDissipationOnlyRiccatiDeficit u t ≤ M := by
    unfold h3PathCanonicalDissipationOnlyRiccatiDeficit
    exact max_le hM hRaw
  exact (h3PathCanonical_unabsorbedRate_le_dissipationOnlyDeficit
    hH3 hClass htClass).trans hV

/-- Neutral physical-PDE alternative: continuation, or failure of every
fixed-margin critical cubic dissipation floor on each strict terminal tail. -/
theorem h3PathCanonical_extension_or_essential_cubicDissipationShortfall
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ d : ℝ, d ∈ Set.Ioo a T → ∀ M : ℝ, 0 ≤ M →
      ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
        ((4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t ≤
          2 * velocityH3DissipationAt u t + M * velocityH3EnergyAt u t) := by
  by_cases hExt : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExt
  · right
    intro d hd M hM
    exact h3PathCanonical_not_ae_cubicDissipationFloor_on_subtail
      M hH3 hExt hClass hd hM

end Euclidean
end Bridge
end PrimeTensor
