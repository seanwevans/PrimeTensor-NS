import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialIntegrableScalarRelativeEnergy

/-!
# Initial uniqueness from positive-time approximate relative energy

The integrable-scalar criterion previously asked for the approximate
relative-energy inequality on the entire closed interval `[0,b]`. The
Navier--Stokes equation is actually supplied only at strict physical times.
For the explicitly zero-anchored old-minus-selected difference, the omitted
`t=0` inequality is automatic: both forward integrals vanish there.

This module makes the strict-positive-time domain explicit. All further
requirements remain substantive: the scalar comparison is integrable and
continuous for positive times, and the arbitrarily small time-residual
inequalities must actually be constructed from the PDE. In particular, no
new weak--strong uniqueness theorem for the open-time NS predicate is claimed.
The independent terminal strong-H³ vorticity path remains a hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- The strict-positive-time relative-energy inequality extends to its zero
endpoint when the actual comparison energy is anchored to zero. No continuity
or integrability is needed for this purely algebraic endpoint step. -/
theorem h3Audit_initialPositiveRelativeEnergy_extend_to_zero
    (e : ℝ → ℝ) (b κ : ℝ) (R : ℝ → ℝ)
    (heZero : e 0 = 0)
    (hPositive : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
      e t ≤ (κ * ∫ s in (0 : ℝ)..t, e s) +
        (∫ s in (0 : ℝ)..t, |R s|)) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) b →
      e t ≤ (κ * ∫ s in (0 : ℝ)..t, e s) +
        (∫ s in (0 : ℝ)..t, |R s|) := by
  intro t ht
  by_cases htZero : t = 0
  · subst t
    simp [heZero]
  · exact hPositive t ⟨lt_of_le_of_ne ht.1 (Ne.symm htZero), ht.2⟩

/-- Epsilon-accurate L¹ residual comparisons are needed only at strictly
positive physical times; the zero endpoint of the comparison is automatic. -/
theorem h3Audit_initialRelativeEnergy_exact_of_positiveTimeResidual
    (e : ℝ → ℝ) (b K : ℝ)
    (heZero : e 0 = 0)
    (heNonneg : ∀ s : ℝ, 0 ≤ e s)
    (hEpsilon : ∀ ε : ℝ, 0 < ε →
      ∃ (κ : ℝ) (R : ℝ → ℝ),
        κ ≤ K ∧
        IntervalIntegrable (fun s : ℝ => |R s|) volume 0 b ∧
        (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
        ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
          e t ≤ (κ * ∫ s in (0 : ℝ)..t, e s) +
            (∫ s in (0 : ℝ)..t, |R s|)) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) b →
      e t ≤ K * ∫ s in (0 : ℝ)..t, e s := by
  apply h3Audit_initialRelativeEnergy_exact_of_arbitrarySmallIntegratedResidual
    e b K heNonneg
  intro ε hε
  obtain ⟨κ, R, hκ, hRInt, hMass, hStrict⟩ := hEpsilon ε hε
  exact ⟨κ, R, hκ, hRInt, hMass,
    h3Audit_initialPositiveRelativeEnergy_extend_to_zero
      e b κ R heZero hStrict⟩

/-- Once the scalar energy is interval-integrable, the positive-time
approximate inequalities themselves force the right-zero energy trace. -/
theorem h3Audit_initialScalarRightZero_of_positiveTimeResidual
    (e : ℝ → ℝ) (b K : ℝ) (hb : 0 < b)
    (heZero : e 0 = 0)
    (heNonneg : ∀ s : ℝ, 0 ≤ e s)
    (heInt : IntervalIntegrable e volume 0 b)
    (hEpsilon : ∀ ε : ℝ, 0 < ε →
      ∃ (κ : ℝ) (R : ℝ → ℝ),
        κ ≤ K ∧
        IntervalIntegrable (fun s : ℝ => |R s|) volume 0 b ∧
        (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
        ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
          e t ≤ (κ * ∫ s in (0 : ℝ)..t, e s) +
            (∫ s in (0 : ℝ)..t, |R s|)) :
    Tendsto e (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  exact h3Audit_initialScalarRightZero_of_integrableExactEnergy
    e b K hb heNonneg heInt
    (h3Audit_initialRelativeEnergy_exact_of_positiveTimeResidual
      e b K heZero heNonneg hEpsilon)

/-- PDE-facing criterion: all approximate energy inequalities are asserted
only on `(0,b]`. Integrability and positive-time scalar continuity remain
explicit independent assumptions, while the zero comparison trace follows. -/
def H3AuditInitialCanonicalPositiveTimeResidualRelativeEnergyData
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
        ∃ (κ : ℝ) (R : ℝ → ℝ),
          κ ≤ K ∧
          IntervalIntegrable (fun s : ℝ => |R s|) volume 0 b ∧
          (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
          ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
            ‖h3AuditInitialCanonicalPhysicalDifference
              hH3 hFourier0 A hA hU₀ t‖ ^ 2 ≤
              (κ * ∫ s in (0 : ℝ)..t,
                ‖h3AuditInitialCanonicalPhysicalDifference
                  hH3 hFourier0 A hA hU₀ s‖ ^ 2) +
              (∫ s in (0 : ℝ)..t, |R s|)

/-- All positive-time-only residual data imply the previous integrable
comparison contract. The absent zero-time PDE inequality is reconstructed
by the exact anchored value of the actual physical difference. -/
theorem h3Audit_initialPositiveTimeResidual_implies_integrableScalarData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalPositiveTimeResidualRelativeEnergyData hH3) :
    H3AuditInitialCanonicalIntegrableScalarRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, hContinuous, hIntegrable, hEpsilon⟩ := hData
  refine ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, hContinuous, hIntegrable, ?_⟩
  intro ε hε
  obtain ⟨κ, R, hκ, hRInt, hMass, hStrict⟩ := hEpsilon ε hε
  refine ⟨κ, R, hκ, hRInt, hMass, ?_⟩
  exact h3Audit_initialPositiveRelativeEnergy_extend_to_zero
    (fun t => ‖h3AuditInitialCanonicalPhysicalDifference
      hH3 hFourier0 A hA hU₀ t‖ ^ 2)
    b κ R (by simp) hStrict

/-- The positive-time PDE criterion implies the canonical compact weak-test
comparison without assuming old/selected velocity equality. -/
theorem h3Audit_initialPositiveTimeResidual_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalPositiveTimeResidualRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialIntegrableScalar_implies_compactWeakComparisonData
    hH3
    (h3Audit_initialPositiveTimeResidual_implies_integrableScalarData
      hH3 hData)

/-- The same positive-time residual criterion identifies the actual initial
physical L² trace and H³ energy upper trace. -/
theorem h3Audit_initialPositiveTimeResidual_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalPositiveTimeResidualRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialIntegrableScalar_implies_physicalZeroJetAndEnergyUpper
    hH3
    (h3Audit_initialPositiveTimeResidual_implies_integrableScalarData
      hH3 hData)

/-- Full-time transverse estimates retain the separate strong-H³ endpoint
condition for one actual physical vorticity component. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialPositiveTimeResidual
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalPositiveTimeResidualRelativeEnergyData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialIntegrableScalar
    hH3 hClass i hPhysical
    (h3Audit_initialPositiveTimeResidual_implies_integrableScalarData
      hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
