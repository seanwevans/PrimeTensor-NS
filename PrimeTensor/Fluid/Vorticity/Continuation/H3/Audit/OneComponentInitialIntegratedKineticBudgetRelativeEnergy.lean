import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialRightKineticTraceReduction

/-!
# Initial weak--strong uniqueness from an integrated physical kinetic budget

The previous criterion asked for a finite right limit of the old solution's
order-zero kinetic energy. That is stronger than the control actually used:
the Gronwall comparison only needs a uniform physical L² bound near t = 0.

A natural initial-value PDE input is a one-sided kinetic balance with a
single integrable signed defect `r`. If

  E₀(t) ≤ E₀(0) + ∫₀ᵗ |r(s)| ds      (0 < t < b),

then the primitive-monotonicity theorem supplies the uniform bound

  E₀(t) ≤ E₀(0) + ∫₀ᵇ |r(s)| ds.

The exact physical velocity norm-squared identity from the preceding module
then gives a uniform L² ceiling for the OLD solution. The SELECTED mild
solution already has its own independent L² ceiling. Time measurability of
the old velocity was proved automatically from local H³-path continuity.

The signed kinetic defect `r` here is separate from the epsilon-dependent
relative-energy comparison defect `R`. Neither the initial kinetic balance
nor the relative-energy comparison is inferred merely from positive-time
`LoggedPreterminalH3PathAdmissible`. In particular, the kinetic budget
REPLACES the right kinetic-energy trace, not the substantive PDE estimate.
The terminal actual-vorticity strong-H³ endpoint remains independent.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- A nonnegative integrated defect gives a uniform upper bound on every
strict initial subinterval, with only one `L¹` defect rather than a right
kinetic-energy limit. -/
theorem h3Audit_initialIntegratedKineticBudget_uniformUpper
    (e r : ℝ → ℝ) (b C : ℝ)
    (hRInt : IntervalIntegrable (fun s : ℝ => |r s|) volume 0 b)
    (hBudget : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      e t ≤ C + ∫ s in (0 : ℝ)..t, |r s|) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      e t ≤ C + ∫ s in (0 : ℝ)..b, |r s| := by
  intro t ht
  have hPrimitive :
      (∫ s in (0 : ℝ)..t, |r s|) ≤
        ∫ s in (0 : ℝ)..b, |r s| :=
    h3Audit_initialResidualPrimitive_le_totalAbsMass
      r b t ⟨ht.1.le, ht.2.le⟩ hRInt
  exact (hBudget t ht).trans (add_le_add (le_refl C) hPrimitive)

/-- Apply the generic budget to the actual order-zero physical kinetic
energy, with its actual specified time-zero value as the initial anchor. -/
theorem h3Audit_initialPhysicalKineticBudget_uniformCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    (r : ℝ → ℝ) (b : ℝ)
    (hRInt : IntervalIntegrable (fun s : ℝ => |r s|) volume 0 b)
    (hBudget : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      velocityH3Energy0At u t ≤
        velocityH3Energy0At u 0 +
          ∫ s in (0 : ℝ)..t, |r s|) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      velocityH3Energy0At u t ≤
        velocityH3Energy0At u 0 +
          ∫ s in (0 : ℝ)..b, |r s| := by
  exact h3Audit_initialIntegratedKineticBudget_uniformUpper
    (velocityH3Energy0At u) r b (velocityH3Energy0At u 0)
    hRInt hBudget

/-- A finite integrated kinetic-energy defect produces the old physical
velocity's uniform norm bound with NO right-limit assumption. -/
theorem h3Audit_initialOldPhysicalHilbert_norm_le_of_integratedKineticBudget
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (r : ℝ → ℝ) (b : ℝ) (hbT : b ≤ T)
    (hRInt : IntervalIntegrable (fun s : ℝ => |r s|) volume 0 b)
    (hBudget : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      velocityH3Energy0At u t ≤
        velocityH3Energy0At u 0 +
          ∫ s in (0 : ℝ)..t, |r s|) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ≤
        Real.sqrt (velocityH3Energy0At u 0 +
          ∫ s in (0 : ℝ)..b, |r s|) := by
  exact h3Audit_initialOldPhysicalHilbert_norm_le_of_kineticCeiling
    hH3 b _ hbT
    (h3Audit_initialPhysicalKineticBudget_uniformCeiling
      r b hRInt hBudget)

/-- A PDE-facing initial relative-energy interface in which the old physical
kinetic ceiling follows from a *single* initial integrated kinetic budget.
The residual in the kinetic budget is NOT required to vanish: its finite
`L¹` mass suffices for boundedness. Separately, the epsilon-dependent
old/selected comparison residuals must vanish in `L¹`. -/
def H3AuditInitialCanonicalIntegratedKineticBudgetRelativeEnergyData
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
    ∃ (r : ℝ → ℝ) (K : ℝ),
      IntervalIntegrable (fun s : ℝ => |r s|) volume 0 b ∧
      (∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        velocityH3Energy0At u t ≤
          velocityH3Energy0At u 0 +
            ∫ s in (0 : ℝ)..t, |r s|) ∧
      (∀ ε : ℝ, 0 < ε →
        ∃ (κ R : ℝ → ℝ),
          ContinuousOn κ (Set.Icc (0 : ℝ) b) ∧
          (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b → κ s ≤ K) ∧
          IntervalIntegrable (fun s => |R s|) volume 0 b ∧
          (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
          ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
            ‖h3AuditInitialCanonicalPhysicalDifference
              hH3 hFourier0 A hA hU₀ t‖ ^ 2 ≤
              (∫ s in (0 : ℝ)..t,
                κ s * ‖h3AuditInitialCanonicalPhysicalDifference
                  hH3 hFourier0 A hA hU₀ s‖ ^ 2) +
              (∫ s in (0 : ℝ)..t, |R s|))

/-- Discharge the old physical L² ceiling and its time measurability
without invoking either full-H³ or kinetic right-time limits. -/
theorem h3Audit_initialIntegratedKineticBudget_implies_oldKineticData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalIntegratedKineticBudgetRelativeEnergyData hH3) :
    H3AuditInitialCanonicalOldKineticCeilingRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, r, K, hRInt, hBudget, hEpsilon⟩ := hData
  let B : ℝ := Real.sqrt (velocityH3Energy0At u 0 +
    ∫ s in (0 : ℝ)..b, |r s|)
  have hOldMeas : AEStronglyMeasurable
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) b)) :=
    h3Audit_initialOldPhysicalHilbert_aestronglyMeasurableOnInitial
      hH3 b hbT.le
  have hOldBound : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ≤ B :=
    h3Audit_initialOldPhysicalHilbert_norm_le_of_integratedKineticBudget
      hH3 r b hbT.le hRInt hBudget
  exact ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, B, K, Real.sqrt_nonneg _,
    hOldMeas, hOldBound, hEpsilon⟩

/-- Initial weak-test uniqueness from a finite signed kinetic-energy defect
and the independent epsilon-vanishing relative-energy comparison. -/
theorem h3Audit_initialIntegratedKineticBudget_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalIntegratedKineticBudgetRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialOldKineticCeiling_implies_compactWeakComparisonData
    hH3 (h3Audit_initialIntegratedKineticBudget_implies_oldKineticData
      hH3 hData)

/-- Initial physical L² trace and upper H³ energy trace from the integrated
kinetic-budget criterion, without assuming either trace beforehand. -/
theorem h3Audit_initialIntegratedKineticBudget_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalIntegratedKineticBudgetRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialOldKineticCeiling_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialIntegratedKineticBudget_implies_oldKineticData
      hH3 hData)

/-- Full-time transverse estimates still require the separate strong-H³
actual-vorticity terminal endpoint for the chosen physical component. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialIntegratedKineticBudget
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalIntegratedKineticBudgetRelativeEnergyData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialOldKineticCeiling
    hH3 hClass i hPhysical
    (h3Audit_initialIntegratedKineticBudget_implies_oldKineticData
      hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
