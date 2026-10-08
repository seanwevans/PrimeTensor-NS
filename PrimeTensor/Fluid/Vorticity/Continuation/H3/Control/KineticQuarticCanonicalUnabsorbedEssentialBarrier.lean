import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalUnabsorbedClockSynchronization
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticLocalMeasurability

/-!
# Essential terminal obstruction for unabsorbed H3 Riccati growth

The existing exact positive unabsorbed rate

  U(t) = max 0 (4422*C1*sqrt(E(t)) - (Delta(t) + 2*D(t)/E(t)))

is nonintegrable on every strict H3 energy-class terminal tail under
hypothetical nonextension. Nonintegrability is stronger than the previously
extracted *pointwise* high-rate witnesses: once U is shown measurable for the
restricted time measure, it rules out **almost-everywhere** domination by
any integrable scalar envelope. Thus an unabsorbed excess above every fixed
height persists on a non-null portion of every terminal subtail.

This is an essential-supremum/temporal-occupation *necessary condition*
for hypothetical nonextension. It does not claim that any uniform duration,
quantitative proportion of time, or new PDE coercive bound has been proved.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- The exact unabsorbed Riccati rate is measurable for the restricted
physical-time measure on any strict H3 energy-class tail. No global
continuity of the old path outside that interval is assumed. -/
theorem h3PathCanonical_unabsorbedRate_aestronglyMeasurableOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    AEStronglyMeasurable (h3PathCanonicalUnabsorbedRiccatiRate u)
      ((volume : Measure ℝ).restrict (Set.Ioo a T)) := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo a T)
  have hEnergy : AEStronglyMeasurable (velocityH3EnergyAt u) μ :=
    (continuousOn_velocityH3EnergyAt_on_energyClassTail
      hH3 hClass).aestronglyMeasurable measurableSet_Ioo
  have hDeriv : AEStronglyMeasurable
      (fun t : ℝ => deriv (velocityH3EnergyAt u) t) μ :=
    aestronglyMeasurable_deriv (velocityH3EnergyAt u) μ
  have hRatio : AEStronglyMeasurable
      (fun t : ℝ => deriv (velocityH3EnergyAt u) t /
        velocityH3EnergyAt u t) μ :=
    (hDeriv.aemeasurable.div hEnergy.aemeasurable).aestronglyMeasurable
  have hResidual : AEStronglyMeasurable
      (fun t : ℝ => deriv (velocityH3EnergyAt u) t /
        velocityH3EnergyAt u t - 4422) μ :=
    hRatio.sub aestronglyMeasurable_const
  have hContinuous : Continuous (fun x : ℝ => max 0 x) :=
    continuous_const.max continuous_id
  have hMax : AEStronglyMeasurable
      (fun t : ℝ => max 0 (deriv (velocityH3EnergyAt u) t /
        velocityH3EnergyAt u t - 4422)) μ :=
    hContinuous.comp_aestronglyMeasurable hResidual
  apply hMax.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact (h3PathCanonical_unabsorbedRiccatiRate_eq_positiveAboveBaseline
    hH3 hClass ht).symm

/-- Integrable time envelopes cannot almost-everywhere dominate the
unabsorbed nonlinear rate on any strict terminal energy-class subtail
if smooth continuation fails. The obstruction is essential, not just
an isolated pointwise comparison. -/
theorem h3PathCanonical_unabsorbedRate_not_ae_le_integrable_on_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d : ℝ} (r : ℝ → ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T)
    (hr : IntegrableOn r (Set.Ioo d T)) :
    ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
      h3PathCanonicalUnabsorbedRiccatiRate u t ≤ r t) := by
  have hClassD : PreterminalH3EnergyClass u d T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hd.1) hd.2
  have hMeas : AEStronglyMeasurable
      (h3PathCanonicalUnabsorbedRiccatiRate u)
      ((volume : Measure ℝ).restrict (Set.Ioo d T)) :=
    h3PathCanonical_unabsorbedRate_aestronglyMeasurableOnTail hH3 hClassD
  intro hDominates
  have hNorm : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
      ‖h3PathCanonicalUnabsorbedRiccatiRate u t‖ ≤ ‖r t‖ := by
    filter_upwards [hDominates] with t ht
    rw [Real.norm_eq_abs,
      abs_of_nonneg (h3PathCanonical_unabsorbedRiccatiRate_nonneg u t)]
    exact ht.trans (le_abs_self (r t))
  have hInt : IntegrableOn (h3PathCanonicalUnabsorbedRiccatiRate u)
      (Set.Ioo d T) :=
    Integrable.mono' hr.norm hMeas hNorm
  exact (h3PathCanonical_not_integrable_unabsorbedRiccatiRate_on_subtail
    hH3 hNoExtension hClass hd) hInt

/-- Essential unboundedness: a hypothetical nonextension path cannot
have an almost-everywhere finite ceiling for unabsorbed growth on any
strict terminal H3 energy-class subtail. -/
theorem h3PathCanonical_unabsorbedRate_not_ae_bounded_on_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d : ℝ} (M : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T) :
    ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
      h3PathCanonicalUnabsorbedRiccatiRate u t ≤ M) := by
  have hConst : IntegrableOn (fun _ : ℝ => M) (Set.Ioo d T) :=
    integrableOn_const measure_Ioo_lt_top.ne
  exact h3PathCanonical_unabsorbedRate_not_ae_le_integrable_on_subtail
    (r := fun _ : ℝ => M) hH3 hNoExtension hClass hd hConst

/-- An almost-everywhere upper bound on the positive unabsorbed rate by
one integrable envelope suffices for continuation. Thus a PDE estimate
which holds outside a null set would already close the present frontier. -/
theorem h3PathCanonical_extension_of_ae_integrable_unabsorbed_majorant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} {r : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : IntegrableOn r (Set.Ioo a T))
    (hMajorant : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo a T)),
      h3PathCanonicalUnabsorbedRiccatiRate u t ≤ r t) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hMeas : AEStronglyMeasurable
      (h3PathCanonicalUnabsorbedRiccatiRate u)
      ((volume : Measure ℝ).restrict (Set.Ioo a T)) :=
    h3PathCanonical_unabsorbedRate_aestronglyMeasurableOnTail hH3 hClass
  have hNorm : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo a T)),
      ‖h3PathCanonicalUnabsorbedRiccatiRate u t‖ ≤ ‖r t‖ := by
    filter_upwards [hMajorant] with t ht
    rw [Real.norm_eq_abs,
      abs_of_nonneg (h3PathCanonical_unabsorbedRiccatiRate_nonneg u t)]
    exact ht.trans (le_abs_self (r t))
  have hInt : IntegrableOn (h3PathCanonicalUnabsorbedRiccatiRate u)
      (Set.Ioo a T) := Integrable.mono' hr.norm hMeas hNorm
  exact h3PathCanonical_extension_of_integrable_unabsorbedRiccatiRate
    hH3 hClass hInt

/-- Under hypothetical nonextension, every terminal subtail has a genuine
failure of almost-everywhere compensation in terms of the original
nonnegative PDE channels Q=Delta+2D/E. -/
theorem h3PathCanonical_effectiveDefect_not_ae_absorb_mod_integrable
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
          h3PathCanonicalEffectiveRiccatiDefect u t + r t) := by
  have hClassD : PreterminalH3EnergyClass u d T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hd.1) hd.2
  intro hComp
  have hMajor : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
      h3PathCanonicalUnabsorbedRiccatiRate u t ≤ max 0 (r t) := by
    filter_upwards [hComp, ae_restrict_mem measurableSet_Ioo] with t ht hmem
    have hGap :
        (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) -
          h3PathCanonicalEffectiveRiccatiDefect u t ≤ r t := by
      linarith only [ht]
    unfold h3PathCanonicalUnabsorbedRiccatiRate
    exact max_le_max_left 0 hGap
  have hRPlus : IntegrableOn (fun t : ℝ => max 0 (r t)) (Set.Ioo d T) := by
    have hRMeas : AEStronglyMeasurable (fun t : ℝ => max 0 (r t))
        ((volume : Measure ℝ).restrict (Set.Ioo d T)) :=
      (continuous_const.max continuous_id).comp_aestronglyMeasurable hr.aestronglyMeasurable
    apply Integrable.mono' hr.norm hRMeas
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left (0 : ℝ) (r t))]
    have hZero : (0 : ℝ) ≤ |r t| := abs_nonneg _
    have hRight : r t ≤ |r t| := le_abs_self _
    exact max_le hZero hRight
  exact (h3PathCanonical_unabsorbedRate_not_ae_le_integrable_on_subtail
    (r := fun t => max 0 (r t)) hH3 hNoExtension hClass hd hRPlus) hMajor

/-- Neutral continuation alternative exposing the essential (non-null)
terminal-time obstruction rather than just isolated direct witness times. -/
theorem h3PathCanonical_extension_or_unabsorbed_essentialBarrier
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ d : ℝ, d ∈ Set.Ioo a T →
      ∀ M : ℝ,
        ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
          h3PathCanonicalUnabsorbedRiccatiRate u t ≤ M) := by
  by_cases hExt : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExt
  · right
    intro d hd M
    exact h3PathCanonical_unabsorbedRate_not_ae_bounded_on_subtail
      M hH3 hExt hClass hd

end Euclidean
end Bridge
end PrimeTensor
