import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalUnabsorbedEssentialBarrier

/-!
# Nonintegrability of every positive superlevel excess of unabsorbed H3 growth

Write `U(t) = max 0 (4422*C1*sqrt(E(t)) - (Delta(t)+2*D(t)/E(t)))`.
The preceding module established that hypothetical nonextension forces `U`
to be nonintegrable on every strict terminal H3 energy-class tail, and that
`U` is a.e. strongly measurable for the corresponding restricted time measure.

A stronger distributional obstruction follows without any new PDE premise:
for every fixed real threshold `M`, the superlevel *excess*

  U_M(t) = max 0 (U(t) - M)

is itself nonintegrable on every strict terminal tail. Indeed,

  0 <= U(t) <= U_M(t) + max 0 M,

and the second summand is integrable on the finite terminal interval.
Thus if the contribution strictly above one fixed height were integrable,
so would be the full unabsorbed growth, forcing smooth continuation.

This rules out explaining the infinite L1 time cost entirely by the
bounded-height portion of U. It is not a lower bound on the measure of
any fixed superlevel set, nor any new cancellation/dissipation coercivity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- Positive excess above a freely fixed time-independent rate threshold. -/
noncomputable def h3PathCanonicalUnabsorbedSuperlevelExcess
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (M : ℝ) : ℝ → ℝ :=
  fun t => max 0 (h3PathCanonicalUnabsorbedRiccatiRate u t - M)

/-- Every superlevel excess is pointwise nonnegative, at all times. -/
theorem h3PathCanonical_unabsorbedSuperlevelExcess_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (M t : ℝ) :
    0 ≤ h3PathCanonicalUnabsorbedSuperlevelExcess u M t := by
  unfold h3PathCanonicalUnabsorbedSuperlevelExcess
  exact le_max_left _ _

/-- At each time, discarding growth beneath a fixed threshold loses at most
its positive part. The inequality is independent of H3 path admissibility. -/
theorem h3PathCanonical_unabsorbedRate_le_superlevelExcess_add_threshold
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (M t : ℝ) :
    h3PathCanonicalUnabsorbedRiccatiRate u t ≤
      h3PathCanonicalUnabsorbedSuperlevelExcess u M t + max 0 M := by
  have hGap : h3PathCanonicalUnabsorbedRiccatiRate u t - M ≤
      max 0 (h3PathCanonicalUnabsorbedRiccatiRate u t - M) :=
    le_max_right _ _
  have hThreshold : M ≤ max (0 : ℝ) M := le_max_right _ _
  unfold h3PathCanonicalUnabsorbedSuperlevelExcess
  linarith only [hGap, hThreshold]

/-- Every fixed-threshold superlevel excess is a.e. strongly measurable on
an admissible strict terminal H3 energy-class interval. -/
theorem h3PathCanonical_unabsorbedSuperlevelExcess_aestronglyMeasurableOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (M : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    AEStronglyMeasurable (h3PathCanonicalUnabsorbedSuperlevelExcess u M)
      ((volume : Measure ℝ).restrict (Set.Ioo a T)) := by
  have hU := h3PathCanonical_unabsorbedRate_aestronglyMeasurableOnTail
    hH3 hClass
  have hShift : AEStronglyMeasurable
      (fun t : ℝ => h3PathCanonicalUnabsorbedRiccatiRate u t - M)
      ((volume : Measure ℝ).restrict (Set.Ioo a T)) :=
    hU.sub aestronglyMeasurable_const
  have hContinuous : Continuous (fun x : ℝ => max 0 x) :=
    continuous_const.max continuous_id
  change AEStronglyMeasurable
    (fun t : ℝ => max 0 (h3PathCanonicalUnabsorbedRiccatiRate u t - M))
    ((volume : Measure ℝ).restrict (Set.Ioo a T))
  exact hContinuous.comp_aestronglyMeasurable hShift

/-- Integrability of only the time spent *above any fixed threshold*,
weighted by the excess over that threshold, suffices for smooth continuation.
This is a precise high-growth truncation criterion, not an analytic estimate
asserting that its integrability premise holds. -/
theorem h3PathCanonical_extension_of_integrable_unabsorbedSuperlevelExcess
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (M : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hExcess : IntegrableOn (h3PathCanonicalUnabsorbedSuperlevelExcess u M)
      (Set.Ioo a T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hConst : IntegrableOn (fun _ : ℝ => max (0 : ℝ) M)
      (Set.Ioo a T) := integrableOn_const measure_Ioo_lt_top.ne
  have hMajor : IntegrableOn
      (fun t : ℝ => h3PathCanonicalUnabsorbedSuperlevelExcess u M t + max 0 M)
      (Set.Ioo a T) := hExcess.add hConst
  have hMeas : AEStronglyMeasurable
      (h3PathCanonicalUnabsorbedRiccatiRate u)
      ((volume : Measure ℝ).restrict (Set.Ioo a T)) :=
    h3PathCanonical_unabsorbedRate_aestronglyMeasurableOnTail hH3 hClass
  have hNorm : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo a T)),
      ‖h3PathCanonicalUnabsorbedRiccatiRate u t‖ ≤
        h3PathCanonicalUnabsorbedSuperlevelExcess u M t + max 0 M := by
    filter_upwards with t
    have hUpper := h3PathCanonical_unabsorbedRate_le_superlevelExcess_add_threshold
      u M t
    have hUNonneg := h3PathCanonical_unabsorbedRiccatiRate_nonneg u t
    simpa only [Real.norm_eq_abs, abs_of_nonneg hUNonneg] using hUpper
  have hIntegrable : IntegrableOn (h3PathCanonicalUnabsorbedRiccatiRate u)
      (Set.Ioo a T) := Integrable.mono' hMajor hMeas hNorm
  exact h3PathCanonical_extension_of_integrable_unabsorbedRiccatiRate
    hH3 hClass hIntegrable

/-- Hypothetical failure of H3 continuation forces a nonintegrable
positive superlevel excess for *every* fixed threshold on *every* H3
energy-class terminal tail, not merely large isolated pointwise values. -/
theorem h3PathCanonical_not_integrable_unabsorbedSuperlevelExcess_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (M : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ¬ IntegrableOn (h3PathCanonicalUnabsorbedSuperlevelExcess u M)
      (Set.Ioo a T) := by
  intro hExcess
  exact hNoExtension
    (h3PathCanonical_extension_of_integrable_unabsorbedSuperlevelExcess
      M hH3 hClass hExcess)

/-- On any later strict energy-class subtail, high-rate superlevel excess
remains nonintegrable for every fixed positive or negative threshold. -/
theorem h3PathCanonical_not_integrable_unabsorbedSuperlevelExcess_on_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d : ℝ} (M : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T) :
    ¬ IntegrableOn (h3PathCanonicalUnabsorbedSuperlevelExcess u M)
      (Set.Ioo d T) := by
  have hClassD : PreterminalH3EnergyClass u d T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hd.1) hd.2
  exact h3PathCanonical_not_integrable_unabsorbedSuperlevelExcess_of_noExtension
    M hH3 hNoExtension hClassD

/-- Neutral formulation: either the path extends, or every fixed-height
positive high-rate excess has an infinite L1 cost on every strict tail. -/
theorem h3PathCanonical_extension_or_all_unabsorbedSuperlevelExcess_nonintegrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ d : ℝ, d ∈ Set.Ioo a T → ∀ M : ℝ,
      ¬ IntegrableOn (h3PathCanonicalUnabsorbedSuperlevelExcess u M)
        (Set.Ioo d T) := by
  by_cases hExt : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExt
  · right
    intro d hd M
    exact h3PathCanonical_not_integrable_unabsorbedSuperlevelExcess_on_subtail
      M hH3 hExt hClass hd

end Euclidean
end Bridge
end PrimeTensor
