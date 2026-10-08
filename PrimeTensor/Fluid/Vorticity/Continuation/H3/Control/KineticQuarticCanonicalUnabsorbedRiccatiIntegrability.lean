import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalEffectiveDefectBarrier

/-!
# Positive unabsorbed canonical Riccati rate on terminal H3 tails

The exact PDE energy budget on a strict H3 energy-class time is

  E'/E + Q = 4422 + A * sqrt(E),

where Q = Delta + 2D/E is the combined nonnegative cancellation/dissipation
channel and A = 4422*C1. Define the *unabsorbed* nonlinear growth rate

  U = max 0 (A * sqrt(E) - Q).

The same exact identity gives U = max 0 (E'/E - 4422). Hence the ordinary
constant baseline plus U controls the physical H3 energy derivative.
Integrability of U on just one strict terminal energy-class tail suffices
for smooth continuation by the existing linear majorant theorem.

Consequently, on a hypothetical nonextension path, U is nonintegrable on
every strict energy-class subtail. Moreover it must exceed every integrable
scalar remainder at some time on each such tail. These are necessary
conditions for nonextension, not a new estimate providing coercivity of Q.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- Positive part of the leading Riccati coefficient not absorbed by the
canonical cancellation and viscous-dissipation defect. -/
noncomputable def h3PathCanonicalUnabsorbedRiccatiRate
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) : ℝ → ℝ :=
  fun t => max 0
    ((4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
        Real.sqrt (velocityH3EnergyAt u t) -
      h3PathCanonicalEffectiveRiccatiDefect u t)

/-- The unabsorbed nonlinear growth rate is pointwise nonnegative. -/
theorem h3PathCanonical_unabsorbedRiccatiRate_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) :
    0 ≤ h3PathCanonicalUnabsorbedRiccatiRate u t := by
  unfold h3PathCanonicalUnabsorbedRiccatiRate
  exact le_max_left _ _

/-- Exact PDE identification of the unabsorbed nonlinear rate as the
positive normalized energy-growth rate *above the fixed baseline 4422*.
This is an identity on energy-class times, not a new a priori bound. -/
theorem h3PathCanonical_unabsorbedRiccatiRate_eq_positiveAboveBaseline
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathCanonicalUnabsorbedRiccatiRate u t =
      max 0 (deriv (velocityH3EnergyAt u) t /
        velocityH3EnergyAt u t - 4422) := by
  have hExact :=
    h3PathCanonical_effectiveDefect_add_normalizedGrowth_eq_budget
      hH3 hClass ht
  have hResidual :
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) -
        h3PathCanonicalEffectiveRiccatiDefect u t =
      deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t - 4422 := by
    linarith only [hExact]
  unfold h3PathCanonicalUnabsorbedRiccatiRate
  rw [hResidual]

/-- The fixed commutator baseline plus the positive unabsorbed defect is
an exact pointwise linear energy-growth majorant. -/
theorem h3PathCanonical_energyGrowth_le_unabsorbedRiccatiRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    deriv (velocityH3EnergyAt u) t ≤
      (4422 + h3PathCanonicalUnabsorbedRiccatiRate u t) *
        velocityH3EnergyAt u t := by
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hExact :=
    h3PathCanonical_effectiveDefect_add_normalizedGrowth_eq_budget
      hH3 hClass ht
  have hGap :
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) -
        h3PathCanonicalEffectiveRiccatiDefect u t ≤
      h3PathCanonicalUnabsorbedRiccatiRate u t := by
    unfold h3PathCanonicalUnabsorbedRiccatiRate
    exact le_max_right _ _
  have hRatio :
      deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t ≤
        4422 + h3PathCanonicalUnabsorbedRiccatiRate u t := by
    linarith only [hExact, hGap]
  exact (div_le_iff₀ hEPos).1 hRatio

/-- Integrability of the actual positive *unabsorbed* Riccati growth rate
on a single terminal energy-class tail is sufficient for continuation. -/
theorem h3PathCanonical_extension_of_integrable_unabsorbedRiccatiRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hInt : IntegrableOn (h3PathCanonicalUnabsorbedRiccatiRate u)
      (Set.Ioo a T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hConst : IntegrableOn (fun _ : ℝ => (4422 : ℝ))
      (Set.Ioo a T) := integrableOn_const measure_Ioo_lt_top.ne
  have hMajorant : IntegrableOn
      (fun t : ℝ => 4422 + h3PathCanonicalUnabsorbedRiccatiRate u t)
      (Set.Ioo a T) := hConst.add hInt
  apply h3PathExtension_of_integrableLinearEnergyGrowthMajorantOnTail
    hH3 hClass hMajorant
  intro t ht
  exact h3PathCanonical_energyGrowth_le_unabsorbedRiccatiRate
    hH3 hClass ht

/-- On a hypothetical nonextension branch the unabsorbed leading nonlinear
rate cannot be integrable on a full terminal energy-class tail. -/
theorem h3PathCanonical_not_integrable_unabsorbedRiccatiRate_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ¬ IntegrableOn (h3PathCanonicalUnabsorbedRiccatiRate u)
      (Set.Ioo a T) := by
  intro hInt
  exact hNoExtension
    (h3PathCanonical_extension_of_integrable_unabsorbedRiccatiRate
      hH3 hClass hInt)

/-- Nonintegrability persists on *every* strict terminal subtail, not just
some initial choice of energy-class anchor. -/
theorem h3PathCanonical_not_integrable_unabsorbedRiccatiRate_on_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T) :
    ¬ IntegrableOn (h3PathCanonicalUnabsorbedRiccatiRate u)
      (Set.Ioo d T) := by
  have hClassD : PreterminalH3EnergyClass u d T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hd.1) hd.2
  exact h3PathCanonical_not_integrable_unabsorbedRiccatiRate_of_noExtension
    hH3 hNoExtension hClassD

/-- Nonextension forces an unabsorbed-growth witness exceeding *any*
integrable scalar remainder on every strict terminal tail. This sharpens
the zero-remainder pointwise defect-dip obstruction. -/
theorem h3PathCanonical_unabsorbedRiccatiRate_exceeds_integrable_remainder
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d : ℝ} (r : ℝ → ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T)
    (hr : IntegrableOn r (Set.Ioo d T)) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      r t < h3PathCanonicalUnabsorbedRiccatiRate u t := by
  obtain ⟨t, ht, hDeficit⟩ :=
    h3PathCanonical_effectiveDefectCompensation_fails_on_tail_of_noExtension
      r hH3 hNoExtension hClass hd hr
  refine ⟨t, ht, ?_⟩
  have hGap : r t <
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
        Real.sqrt (velocityH3EnergyAt u t) -
        h3PathCanonicalEffectiveRiccatiDefect u t := by
    linarith only [hDeficit]
  exact lt_of_lt_of_le hGap
    (show
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) -
        h3PathCanonicalEffectiveRiccatiDefect u t ≤
        h3PathCanonicalUnabsorbedRiccatiRate u t by
      unfold h3PathCanonicalUnabsorbedRiccatiRate
      exact le_max_right _ _)

/-- The positive unabsorbed rate is unbounded on each strict terminal tail
under hypothetical nonextension. This does not assert interval-wide growth. -/
theorem h3PathCanonical_unabsorbedRiccatiRate_unbounded_on_tail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d : ℝ} (M : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      M < h3PathCanonicalUnabsorbedRiccatiRate u t := by
  have hr : IntegrableOn (fun _ : ℝ => M) (Set.Ioo d T) :=
    integrableOn_const measure_Ioo_lt_top.ne
  simpa only [] using
    (h3PathCanonical_unabsorbedRiccatiRate_exceeds_integrable_remainder
      (r := fun _ : ℝ => M) hH3 hNoExtension hClass hd hr)

/-- Neutral terminal alternative: continuation or a genuinely
nonintegrable positive unabsorbed nonlinear rate on every strict tail. -/
theorem h3PathCanonical_extension_or_unabsorbedRiccatiRate_nonintegrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ d : ℝ, d ∈ Set.Ioo a T →
      ¬ IntegrableOn (h3PathCanonicalUnabsorbedRiccatiRate u)
        (Set.Ioo d T) := by
  by_cases hExt : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExt
  · right
    intro d hd
    exact h3PathCanonical_not_integrable_unabsorbedRiccatiRate_on_subtail
      hH3 hExt hClass hd

end Euclidean
end Bridge
end PrimeTensor
