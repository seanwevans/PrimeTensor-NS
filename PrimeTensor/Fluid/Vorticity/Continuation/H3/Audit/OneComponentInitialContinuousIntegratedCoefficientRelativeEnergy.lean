import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialTimeIntegratedCoefficientRelativeEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Initial relative energy with continuous time-integrated coefficients

The time-integrated coefficient comparison proved in the preceding module
assumes that the energy `e` AND every product `κ * e` are integrable on the
initial time interval. That product integrability need not be a separate
PDE obligation when the coefficient is continuous on the closed interval:
mathlib's `IntervalIntegrable.continuousOn_mul` derives it from integrability
of `e` alone.

The coefficient need not be nonnegative. An upper ceiling `κ ≤ K` remains
necessary to dominate the energy-weighted integral. The old/selected
approximate relative-energy inequalities and L¹-small residuals remain
independent PDE inputs; nothing here deduces them from open-time NS
admissibility. The terminal strong-H³ actual-vorticity endpoint is likewise
an independent hypothesis of the full-time conclusion.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- Continuous time coefficients automatically give integrable weighted
comparison energy. No pointwise boundedness estimate is needed for this
particular step, only closed-interval coefficient continuity. -/
theorem h3Audit_initialContinuousCoefficient_product_integrable
    (e κ : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (heInt : IntervalIntegrable e volume 0 b)
    (hκCont : ContinuousOn κ (Set.Icc (0 : ℝ) b)) :
    IntervalIntegrable (fun s : ℝ => κ s * e s) volume 0 b := by
  have hκU : ContinuousOn κ (Set.uIcc (0 : ℝ) b) := by
    simpa only [Set.uIcc_of_le hb] using hκCont
  exact heInt.continuousOn_mul hκU

/-- Exact initial relative energy follows from continuously varying
integrated coefficients with a uniform upper ceiling and arbitrarily small
signed residual mass. Product integrability is no longer a premise. -/
theorem h3Audit_initialRelativeEnergy_exact_of_continuousIntegratedCoefficient
    (e : ℝ → ℝ) (b K : ℝ) (hb : 0 ≤ b)
    (heZero : e 0 = 0)
    (heNonneg : ∀ s : ℝ, 0 ≤ e s)
    (heInt : IntervalIntegrable e volume 0 b)
    (hEpsilon : ∀ ε : ℝ, 0 < ε →
      ∃ (κ R : ℝ → ℝ),
        ContinuousOn κ (Set.Icc (0 : ℝ) b) ∧
        (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b → κ s ≤ K) ∧
        IntervalIntegrable (fun s : ℝ => |R s|) volume 0 b ∧
        (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
        ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
          e t ≤ (∫ s in (0 : ℝ)..t, κ s * e s) +
            (∫ s in (0 : ℝ)..t, |R s|)) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) b →
      e t ≤ K * ∫ s in (0 : ℝ)..t, e s := by
  apply h3Audit_initialRelativeEnergy_exact_of_timeIntegratedCoefficient
    e b K heZero heNonneg heInt
  intro ε hε
  obtain ⟨κ, R, hκCont, hκBound, hRInt, hMass, hApprox⟩ :=
    hEpsilon ε hε
  exact ⟨κ, R, hκBound,
    h3Audit_initialContinuousCoefficient_product_integrable
      e κ b hb heInt hκCont,
    hRInt, hMass, hApprox⟩

/-- Scalar initial uniqueness with a continuous integrated coefficient.
Only energy integrability and positive-time scalar continuity are required,
not separate integrability of coefficient times energy. -/
theorem h3Audit_initialScalarEnergy_zero_of_continuousIntegratedCoefficient
    (e : ℝ → ℝ) (b K : ℝ) (hb : 0 < b)
    (heZero : e 0 = 0)
    (heNonneg : ∀ s : ℝ, 0 ≤ e s)
    (heInt : IntervalIntegrable e volume 0 b)
    (hePositive : ContinuousOn e (Set.Ioc (0 : ℝ) b))
    (hEpsilon : ∀ ε : ℝ, 0 < ε →
      ∃ (κ R : ℝ → ℝ),
        ContinuousOn κ (Set.Icc (0 : ℝ) b) ∧
        (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b → κ s ≤ K) ∧
        IntervalIntegrable (fun s : ℝ => |R s|) volume 0 b ∧
        (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
        ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
          e t ≤ (∫ s in (0 : ℝ)..t, κ s * e s) +
            (∫ s in (0 : ℝ)..t, |R s|))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) b) :
    e t = 0 := by
  have hExact :=
    h3Audit_initialRelativeEnergy_exact_of_continuousIntegratedCoefficient
      e b K hb.le heZero heNonneg heInt hEpsilon
  have hRightZero : Tendsto e (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    h3Audit_initialScalarRightZero_of_integrableExactEnergy
      e b K hb heNonneg heInt hExact
  have hRight : Tendsto e (𝓝[>] (0 : ℝ)) (𝓝 (e 0)) := by
    simpa only [heZero] using hRightZero
  have hClosed : ContinuousOn e (Set.Icc (0 : ℝ) b) :=
    h3Audit_initialScalarClosedContinuous_of_positiveAndRightTrace
      e b hb hePositive hRight
  exact h3Audit_initialScalarEnergy_integralGronwall
    e b K hb heNonneg hClosed hExact t ht

/-- PDE-facing continuous-coefficient criterion. The product `κ(s)*e(s)`
no longer needs an integrability witness: it will be constructed from the
continuous coefficient and the existing `L¹` comparison-energy witness. -/
def H3AuditInitialCanonicalContinuousIntegratedCoefficientRelativeEnergyData
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
          ContinuousOn κ (Set.Icc (0 : ℝ) b) ∧
          (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b → κ s ≤ K) ∧
          IntervalIntegrable (fun s : ℝ => |R s|) volume 0 b ∧
          (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
          ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
            ‖h3AuditInitialCanonicalPhysicalDifference
              hH3 hFourier0 A hA hU₀ t‖ ^ 2 ≤
              (∫ s in (0 : ℝ)..t,
                κ s * ‖h3AuditInitialCanonicalPhysicalDifference
                  hH3 hFourier0 A hA hU₀ s‖ ^ 2) +
              (∫ s in (0 : ℝ)..t, |R s|)

/-- Construct the missing weighted-product interval integrability and
recover the previous coefficient-inside-the-integral comparison contract. -/
theorem h3Audit_initialContinuousIntegratedCoefficient_implies_timeIntegratedCoefficientData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalContinuousIntegratedCoefficientRelativeEnergyData hH3) :
    H3AuditInitialCanonicalTimeIntegratedCoefficientRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, hEnergyCont, hEnergyInt, hEpsilon⟩ := hData
  refine ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, hEnergyCont, hEnergyInt, ?_⟩
  intro ε hε
  obtain ⟨κ, R, hκCont, hκBound, hRInt, hMass, hApprox⟩ :=
    hEpsilon ε hε
  refine ⟨κ, R, hκBound, ?_, hRInt, hMass, hApprox⟩
  exact h3Audit_initialContinuousCoefficient_product_integrable
    (fun s => ‖h3AuditInitialCanonicalPhysicalDifference
      hH3 hFourier0 A hA hU₀ s‖ ^ 2)
    κ b hb.le hEnergyInt hκCont

/-- Physical compact weak-test agreement follows from this reduced
continuous-coefficient interface. -/
theorem h3Audit_initialContinuousIntegratedCoefficient_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalContinuousIntegratedCoefficientRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialTimeIntegratedCoefficient_implies_compactWeakComparisonData
    hH3
    (h3Audit_initialContinuousIntegratedCoefficient_implies_timeIntegratedCoefficientData
      hH3 hData)

/-- The actual physical initial L² trace and upper H³ energy right trace
also follow, without a separately asserted `κ*e` integrability condition. -/
theorem h3Audit_initialContinuousIntegratedCoefficient_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalContinuousIntegratedCoefficientRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialTimeIntegratedCoefficient_implies_physicalZeroJetAndEnergyUpper
    hH3
    (h3Audit_initialContinuousIntegratedCoefficient_implies_timeIntegratedCoefficientData
      hH3 hData)

/-- Full-time transverse intrinsic `L²_t Ḣ^(3/2)_x` estimates retain the
separate terminal strong-H³ endpoint of an actual vorticity component. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialContinuousIntegratedCoefficient
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalContinuousIntegratedCoefficientRelativeEnergyData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialTimeIntegratedCoefficient
    hH3 hClass i hPhysical
    (h3Audit_initialContinuousIntegratedCoefficient_implies_timeIntegratedCoefficientData
      hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
