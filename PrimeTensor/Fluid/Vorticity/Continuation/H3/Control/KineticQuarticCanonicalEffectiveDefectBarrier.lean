import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalRefinedRiccatiClock

/-!
# Exact leading-order Riccati defect barrier and integrable compensation

The canonical H3 commutator coefficient contains the genuinely nonlinear
term `4422*C1*sqrt(E)`. The signed PDE balance and the exact cancellation
identity split its normalized growth budget as

  E'/E + (Delta + 2*D/E) = 4422 + 4422*C1*sqrt(E).

Here Delta is the normalized gap between the commutator envelope and actual
transport, and D is the nonnegative full H3 dissipation. Their sum is the
*effective* dissipative/cancellation defect. It is nonnegative, but nothing
in the existing estimates forces it to absorb the leading square-root term.

If it does absorb the leading term on a terminal H3 energy-class tail, modulo
an integrable scalar remainder r, then E' <= (4422+r) E and the established
linear-growth continuation theorem applies. Conversely, hypothetical
nonextension forces the effective defect below the leading nonlinear term
plus *every* prescribed integrable allowance somewhere on every strict tail.
This identifies a genuine analytic coercivity frontier; it does not assert
that the missing lower bound holds for Navier--Stokes solutions.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- Combined normalized gap between canonical commutator transport and the
actual physical energy derivative, retaining *both* positive full-dissipation
and cancellation channels. -/
noncomputable def h3PathCanonicalEffectiveRiccatiDefect
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) : ℝ → ℝ :=
  fun t => h3PathCanonicalTransportCancellationGap u t +
    2 * velocityH3DissipationAt u t / velocityH3EnergyAt u t

/-- Exact growth identity: the effective defect and normalized H3 energy
slope exhaust the constant-plus-square-root canonical spectral budget. -/
theorem h3PathCanonical_effectiveDefect_add_normalizedGrowth_eq_budget
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t +
      h3PathCanonicalEffectiveRiccatiDefect u t =
        4422 +
          (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
            Real.sqrt (velocityH3EnergyAt u t) := by
  have hDecomp :=
    h3PathCanonical_riccatiDefect_eq_baseline_add_cancellation_add_dissipation
      hH3 hClass ht
  have hIdentity :
      h3PathSqrtEnergyRiccatiCoefficient *
          Real.sqrt (velocityH3EnergyAt u t) -
        deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t =
      4422 * (Real.sqrt (velocityH3EnergyAt u t) - 1) +
        h3PathCanonicalEffectiveRiccatiDefect u t := by
    simpa only [h3PathCanonicalRiccatiGrowthDefect,
      h3PathCanonicalEffectiveRiccatiDefect, add_assoc] using hDecomp
  calc
    deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t +
        h3PathCanonicalEffectiveRiccatiDefect u t =
        h3PathSqrtEnergyRiccatiCoefficient *
          Real.sqrt (velocityH3EnergyAt u t) -
        4422 * (Real.sqrt (velocityH3EnergyAt u t) - 1) := by
          linarith only [hIdentity]
    _ = 4422 +
        (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) := by
          unfold h3PathSqrtEnergyRiccatiCoefficient
          ring

/-- The effective defect is nonnegative on an admissible H3 energy-class
time, although this alone is too weak to force continuation. -/
theorem h3PathCanonical_effectiveRiccatiDefect_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    0 ≤ h3PathCanonicalEffectiveRiccatiDefect u t := by
  have hCancel := h3PathCanonicalTransportCancellationGap_nonneg
    hH3 hClass ht
  have hD : 0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t
  have hE : 0 ≤ velocityH3EnergyAt u t :=
    le_trans zero_le_one (one_le_velocityH3EnergyAt u t)
  unfold h3PathCanonicalEffectiveRiccatiDefect
  exact add_nonneg hCancel
    (div_nonneg (mul_nonneg (by norm_num) hD) hE)

/-- Cancellation plus dissipation absorbing the leading nonlinear
`4422*C1*sqrt(E)` term, modulo a scalar remainder, leaves an *exact linear*
energy-growth majorant `E' <= (4422+r)E`. -/
theorem h3PathCanonical_energyGrowth_le_of_effectiveDefectCompensation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hCompensation :
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) ≤
        h3PathCanonicalEffectiveRiccatiDefect u t + r) :
    deriv (velocityH3EnergyAt u) t ≤
      (4422 + r) * velocityH3EnergyAt u t := by
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hExact :=
    h3PathCanonical_effectiveDefect_add_normalizedGrowth_eq_budget
      hH3 hClass ht
  have hRatio :
      deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t ≤
        4422 + r := by
    linarith only [hExact, hCompensation]
  exact (div_le_iff₀ hEPos).1 hRatio

/-- A single terminal H3 energy-class tail on which the effective PDE
defect absorbs the nonlinear spectral coefficient, up to any integrable
remainder, already suffices for smooth continuation. -/
theorem h3PathCanonical_extension_of_integrable_effectiveDefectCompensation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} {r : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : IntegrableOn r (Set.Ioo a T))
    (hCompensation : ∀ t : ℝ, t ∈ Set.Ioo a T →
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) ≤
        h3PathCanonicalEffectiveRiccatiDefect u t + r t) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hConst : IntegrableOn (fun _ : ℝ => (4422 : ℝ))
      (Set.Ioo a T) := integrableOn_const measure_Ioo_lt_top.ne
  have hMajorant : IntegrableOn (fun t : ℝ => 4422 + r t)
      (Set.Ioo a T) := hConst.add hr
  apply h3PathExtension_of_integrableLinearEnergyGrowthMajorantOnTail
    hH3 hClass hMajorant
  intro t ht
  exact h3PathCanonical_energyGrowth_le_of_effectiveDefectCompensation
    hH3 hClass ht (hCompensation t ht)

/-- In the hypothetical nonextension branch, no integrable remainder can
compensate a uniform leading-order defect floor on a complete terminal
tail. The strict deficit witness lies in every prescribed strict subtail. -/
theorem h3PathCanonical_effectiveDefectCompensation_fails_on_tail_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d : ℝ} (r : ℝ → ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T)
    (hr : IntegrableOn r (Set.Ioo d T)) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      h3PathCanonicalEffectiveRiccatiDefect u t + r t <
        (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) := by
  by_contra hNoWitness
  have hComp : ∀ t : ℝ, t ∈ Set.Ioo d T →
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) ≤
        h3PathCanonicalEffectiveRiccatiDefect u t + r t := by
    intro t ht
    by_contra hNot
    exact hNoWitness ⟨t, ht, lt_of_not_ge hNot⟩
  have hClassD : PreterminalH3EnergyClass u d T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hd.1) hd.2
  exact hNoExtension
    (h3PathCanonical_extension_of_integrable_effectiveDefectCompensation
      hH3 hClassD hr hComp)

/-- The zero-remainder obstruction: under hypothetical nonextension,
combined cancellation and viscous dissipation must miss the *complete*
leading nonlinear H3 coefficient at some time on every terminal tail. -/
theorem h3PathCanonical_effectiveDefect_dips_below_leadingScale_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      h3PathCanonicalEffectiveRiccatiDefect u t <
        (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
          Real.sqrt (velocityH3EnergyAt u t) := by
  have hr : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Set.Ioo d T) :=
    integrableOn_const measure_Ioo_lt_top.ne
  obtain ⟨t, ht, hDeficit⟩ :=
    h3PathCanonical_effectiveDefectCompensation_fails_on_tail_of_noExtension
      (r := fun _ : ℝ => 0) hH3 hNoExtension hClass hd hr
  refine ⟨t, ht, ?_⟩
  simpa only [add_zero] using hDeficit

/-- Neutral terminal alternative retaining the exact nonlinear-coercivity
obstruction without assuming which cancellation/dissipation channel is weak. -/
theorem h3PathCanonical_extension_or_effectiveDefect_dips_on_every_tail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ d : ℝ, d ∈ Set.Ioo a T →
      ∃ t : ℝ, t ∈ Set.Ioo d T ∧
        h3PathCanonicalEffectiveRiccatiDefect u t <
          (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
            Real.sqrt (velocityH3EnergyAt u t) := by
  by_cases hExt : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExt
  · right
    intro d hd
    exact h3PathCanonical_effectiveDefect_dips_below_leadingScale_of_noExtension
      hH3 hExt hClass hd

end Euclidean
end Bridge
end PrimeTensor
