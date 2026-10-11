import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPositiveTimeResidualRelativeEnergy

/-!
# Initial relative-energy comparison with a time-varying Gronwall coefficient

The positive-time residual criterion formerly asked for a scalar coefficient
`κ` for each approximation tolerance. Physical PDE estimates can instead give
an instantaneous coefficient `κ t`. If `κ t ≤ K` on the initial interval,
the nonnegative forward energy integral permits pointwise replacement of
`κ t` by the single Gronwall coefficient `K`.

This module proves the coefficient-reduction inequality explicitly, then
reuses the established epsilon-residual, initial scalar-integrability,
canonical weak-test and initial physical H³ trace results. Unlike merely
postulating equality of old and selected paths, the relative-energy
comparison and its vanishing L¹ error remain explicit PDE obligations.

No actual Navier--Stokes comparison estimate, interval integrability, or
positive-time continuity follows from open-time admissibility here. The
terminal strong-H³ actual-vorticity endpoint is also independent.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- On a forward interval, nonnegative comparison energy absorbs an
instantaneously varying Gronwall coefficient below the uniform ceiling `K`.
The residual density is unchanged; its sign and integrability are irrelevant
for this algebraic estimate. -/
theorem h3Audit_initialPositiveTime_boundedVariableCoefficient_reduction
    (e : ℝ → ℝ) (b K : ℝ) (κ R : ℝ → ℝ)
    (heNonneg : ∀ s : ℝ, 0 ≤ e s)
    (hκ : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b → κ t ≤ K)
    (hApprox : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
      e t ≤ ((κ t) * ∫ s in (0 : ℝ)..t, e s) +
        (∫ s in (0 : ℝ)..t, |R s|))
    (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) b) :
    e t ≤ (K * ∫ s in (0 : ℝ)..t, e s) +
      (∫ s in (0 : ℝ)..t, |R s|) := by
  have hIntegralNonneg :
      0 ≤ ∫ s in (0 : ℝ)..t, e s :=
    intervalIntegral.integral_nonneg ht.1.le
      (fun s _hs => heNonneg s)
  have hCoefficient :
      (κ t) * ∫ s in (0 : ℝ)..t, e s ≤
        K * ∫ s in (0 : ℝ)..t, e s :=
    mul_le_mul_of_nonneg_right (hκ t ht) hIntegralNonneg
  exact (hApprox t ht).trans (add_le_add hCoefficient le_rfl)

/-- An epsilon-accurate family of *time-dependent* coefficients, uniformly
bounded above on `(0,b]`, yields the exact positive-time relative-energy
inequality. Its time-dependent coefficients need not be measurable, because
they are removed pointwise before any integration. -/
theorem h3Audit_initialRelativeEnergy_exact_of_variableTimeCoefficient
    (e : ℝ → ℝ) (b K : ℝ)
    (heZero : e 0 = 0)
    (heNonneg : ∀ s : ℝ, 0 ≤ e s)
    (hEpsilon : ∀ ε : ℝ, 0 < ε →
      ∃ (κ R : ℝ → ℝ),
        (∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b → κ t ≤ K) ∧
        IntervalIntegrable (fun s : ℝ => |R s|) volume 0 b ∧
        (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
        ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
          e t ≤ ((κ t) * ∫ s in (0 : ℝ)..t, e s) +
            (∫ s in (0 : ℝ)..t, |R s|)) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) b →
      e t ≤ K * ∫ s in (0 : ℝ)..t, e s := by
  apply h3Audit_initialRelativeEnergy_exact_of_positiveTimeResidual
    e b K heZero heNonneg
  intro ε hε
  obtain ⟨κ, R, hκ, hInt, hMass, hApprox⟩ := hEpsilon ε hε
  refine ⟨K, R, le_rfl, hInt, hMass, ?_⟩
  intro t ht
  exact h3Audit_initialPositiveTime_boundedVariableCoefficient_reduction
    e b K κ R heNonneg hκ hApprox t ht

/-- Genuine scalar uniqueness from integrable energy, positive-time
continuity and variable-coefficient residual estimates. Unlike the scalar
coefficient reduction, this final step uses continuity and integrability to
justify the integral Gronwall argument at the artificial zero anchor. -/
theorem h3Audit_initialScalarEnergy_zero_of_variableTimeCoefficient
    (e : ℝ → ℝ) (b K : ℝ) (hb : 0 < b)
    (heZero : e 0 = 0)
    (heNonneg : ∀ s : ℝ, 0 ≤ e s)
    (heInt : IntervalIntegrable e volume 0 b)
    (hePositive : ContinuousOn e (Set.Ioc (0 : ℝ) b))
    (hEpsilon : ∀ ε : ℝ, 0 < ε →
      ∃ (κ R : ℝ → ℝ),
        (∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b → κ t ≤ K) ∧
        IntervalIntegrable (fun s : ℝ => |R s|) volume 0 b ∧
        (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
        ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
          e t ≤ ((κ t) * ∫ s in (0 : ℝ)..t, e s) +
            (∫ s in (0 : ℝ)..t, |R s|))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) b) :
    e t = 0 := by
  have hExact : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b →
      e s ≤ K * ∫ r in (0 : ℝ)..s, e r :=
    h3Audit_initialRelativeEnergy_exact_of_variableTimeCoefficient
      e b K heZero heNonneg hEpsilon
  have hRight : Tendsto e (𝓝[>] (0 : ℝ)) (𝓝 (e 0)) := by
    have hRightZero := h3Audit_initialScalarRightZero_of_integrableExactEnergy
      e b K hb heNonneg heInt hExact
    simpa only [heZero] using hRightZero
  have hClosed : ContinuousOn e (Set.Icc (0 : ℝ) b) :=
    h3Audit_initialScalarClosedContinuous_of_positiveAndRightTrace
      e b hb hePositive hRight
  exact h3Audit_initialScalarEnergy_integralGronwall
    e b K hb heNonneg hClosed hExact t ht

/-- Initial physical old/selected comparison with an approximation-dependent
instantaneous coefficient `κ t`. Each coefficient is bounded on the initial
interval by a common scalar `K`; residuals have arbitrarily small total
absolute temporal mass. The physical comparison energy must independently be
integrable and continuous at strictly positive times. -/
def H3AuditInitialCanonicalVariableTimeCoefficientRelativeEnergyData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (A : ℝ) (hA : 0 < A)
    (hU₀ : ‖velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0‖ ≤ A)
    (b : ℝ),
    0 < b ∧ b < T ∧
    b ≤ h3FinHeatLerayRestartRadius 1 A ∧
    ∃ K : ℝ,
      ContinuousOn
        (fun t => ‖h3AuditInitialCanonicalPhysicalDifference
          hH3 hFourier0 A hA hU₀ t‖ ^ 2)
        (Set.Ioc (0 : ℝ) b) ∧
      IntervalIntegrable
        (fun t => ‖h3AuditInitialCanonicalPhysicalDifference
          hH3 hFourier0 A hA hU₀ t‖ ^ 2)
        volume 0 b ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ (κ R : ℝ → ℝ),
          (∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b → κ t ≤ K) ∧
          IntervalIntegrable (fun s : ℝ => |R s|) volume 0 b ∧
          (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
          ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
            ‖h3AuditInitialCanonicalPhysicalDifference
              hH3 hFourier0 A hA hU₀ t‖ ^ 2 ≤
              ((κ t) * ∫ s in (0 : ℝ)..t,
                ‖h3AuditInitialCanonicalPhysicalDifference
                  hH3 hFourier0 A hA hU₀ s‖ ^ 2) +
              (∫ s in (0 : ℝ)..t, |R s|)

/-- Variable-time coefficient PDE comparisons imply the established
positive-time scalar residual contract. No new hidden continuity or initial
old/selected equality hypothesis is introduced by this reduction. -/
theorem h3Audit_initialVariableTimeCoefficient_implies_positiveTimeResidualData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalVariableTimeCoefficientRelativeEnergyData hH3) :
    H3AuditInitialCanonicalPositiveTimeResidualRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, hContinuous, hIntegrable, hEpsilon⟩ := hData
  refine ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, hContinuous, hIntegrable, ?_⟩
  intro ε hε
  obtain ⟨κ, R, hκ, hRInt, hMass, hApprox⟩ := hEpsilon ε hε
  refine ⟨K, R, le_rfl, hRInt, hMass, ?_⟩
  intro t ht
  exact h3Audit_initialPositiveTime_boundedVariableCoefficient_reduction
    (fun s => ‖h3AuditInitialCanonicalPhysicalDifference
      hH3 hFourier0 A hA hU₀ s‖ ^ 2)
    b K κ R (fun s => sq_nonneg _) hκ hApprox t ht

/-- Positive-time variable-coefficient relative energy implies actual-old
and canonical selected compact physical weak-test equality. -/
theorem h3Audit_initialVariableTimeCoefficient_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalVariableTimeCoefficientRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialPositiveTimeResidual_implies_compactWeakComparisonData
    hH3
    (h3Audit_initialVariableTimeCoefficient_implies_positiveTimeResidualData
      hH3 hData)

/-- The same variable-coefficient contract yields the physical initial
L² trace and the upper H³ energy right trace. -/
theorem h3Audit_initialVariableTimeCoefficient_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalVariableTimeCoefficientRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialPositiveTimeResidual_implies_physicalZeroJetAndEnergyUpper
    hH3
    (h3Audit_initialVariableTimeCoefficient_implies_positiveTimeResidualData
      hH3 hData)

/-- The full-time two-coordinate intrinsic Ḣ^(3/2) time estimate still
requires the separate actual strong-H³ terminal vorticity endpoint. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialVariableTimeCoefficient
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalVariableTimeCoefficientRelativeEnergyData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialPositiveTimeResidual
    hH3 hClass i hPhysical
    (h3Audit_initialVariableTimeCoefficient_implies_positiveTimeResidualData
      hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
