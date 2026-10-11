import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialIntegratedResidualRelativeEnergy

/-!
# Initial uniqueness from arbitrarily small integrated PDE errors

The previous initial physical comparison requires a numbered family of
residual densities whose full-interval L¹ masses converge to zero. In weak
PDE estimates, one instead often obtains a construction for *each* error
tolerance `ε > 0`: a cutoff/mollifier choice and its residual density,
with full-interval absolute mass at most `ε`.

This file proves an epsilon-form closure of the same scalar relative-energy
argument, with no preselected approximation sequence. The approximation
coefficient may depend on epsilon, but must remain bounded above by the same
finite `K` independently of epsilon. The residual is permitted to be signed;
only its absolute temporal mass enters the comparison.

Existence of the epsilon-dependent PDE inequality and actual initial scalar
energy continuity are still explicit analytic hypotheses. Neither follows
merely from the existing open-time Navier--Stokes admissibility predicate.
The terminal strong-H³ actual-vorticity endpoint remains separate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- Every positive tolerance admits an integrated-error comparison with a
uniform Gronwall-coefficient ceiling. Thus the *exact* scalar energy
inequality holds, without first choosing a vanishing sequence. -/
theorem h3Audit_initialRelativeEnergy_exact_of_arbitrarySmallIntegratedResidual
    (e : ℝ → ℝ) (b K : ℝ)
    (heNonneg : ∀ s : ℝ, 0 ≤ e s)
    (hEpsilon : ∀ ε : ℝ, 0 < ε →
      ∃ (κ : ℝ) (R : ℝ → ℝ),
        κ ≤ K ∧
        IntervalIntegrable (fun s : ℝ => |R s|) volume 0 b ∧
        (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
        ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) b →
          e t ≤ (κ * ∫ s in (0 : ℝ)..t, e s) +
            (∫ s in (0 : ℝ)..t, |R s|)) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) b →
      e t ≤ K * ∫ s in (0 : ℝ)..t, e s := by
  intro t ht
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨κ, R, hκ, hRInt, hMass, hApprox⟩ := hEpsilon ε hε
  let I : ℝ := ∫ s in (0 : ℝ)..t, e s
  have hINonneg : 0 ≤ I := by
    dsimp only [I]
    exact intervalIntegral.integral_nonneg ht.1
      (fun s _hs => heNonneg s)
  have hCoefficient : κ * I ≤ K * I :=
    mul_le_mul_of_nonneg_right hκ hINonneg
  have hResidual :
      (∫ s in (0 : ℝ)..t, |R s|) ≤ ε :=
    (h3Audit_initialResidualPrimitive_le_totalAbsMass
      R b t ht hRInt).trans hMass
  have hEstimate :
      e t ≤ κ * I + (∫ s in (0 : ℝ)..t, |R s|) := by
    exact hApprox t ht
  have hCombined :
      κ * I + (∫ s in (0 : ℝ)..t, |R s|) ≤
        K * I + ε :=
    add_le_add hCoefficient hResidual
  change e t ≤ K * I + ε
  exact hEstimate.trans hCombined

/-- Scalar Gronwall closes the energy when each positive error tolerance
admits a relative-energy comparison with controlled L¹ residual. -/
theorem h3Audit_initialScalarEnergy_integralGronwall_of_arbitrarySmallIntegratedResidual
    (e : ℝ → ℝ) (b K : ℝ) (hb : 0 < b)
    (heNonneg : ∀ s : ℝ, 0 ≤ e s)
    (heCont : ContinuousOn e (Set.Icc (0 : ℝ) b))
    (hEpsilon : ∀ ε : ℝ, 0 < ε →
      ∃ (κ : ℝ) (R : ℝ → ℝ),
        κ ≤ K ∧
        IntervalIntegrable (fun s : ℝ => |R s|) volume 0 b ∧
        (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
        ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) b →
          e t ≤ (κ * ∫ s in (0 : ℝ)..t, e s) +
            (∫ s in (0 : ℝ)..t, |R s|))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) b) :
    e t = 0 := by
  exact h3Audit_initialScalarEnergy_integralGronwall
    e b K hb heNonneg heCont
    (h3Audit_initialRelativeEnergy_exact_of_arbitrarySmallIntegratedResidual
      e b K heNonneg hEpsilon) t ht

/-- PDE-facing initial energy interface using directly quantified arbitrary
positive accuracy, instead of a prescribed sequence of approximants. -/
def H3AuditInitialCanonicalEpsilonResidualRelativeEnergyData
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
        (Set.Icc (0 : ℝ) b) ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ (κ : ℝ) (R : ℝ → ℝ),
          κ ≤ K ∧
          IntervalIntegrable (fun s : ℝ => |R s|) volume 0 b ∧
          (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
          ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) b →
            ‖h3AuditInitialCanonicalPhysicalDifference
              hH3 hFourier0 A hA hU₀ t‖ ^ 2 ≤
              (κ * ∫ s in (0 : ℝ)..t,
                ‖h3AuditInitialCanonicalPhysicalDifference
                  hH3 hFourier0 A hA hU₀ s‖ ^ 2) +
              (∫ s in (0 : ℝ)..t, |R s|)

/-- Direct epsilon-dependent PDE estimates imply the exact scalar
relative-energy contract; all analytic inputs remain visible above. -/
theorem h3Audit_initialEpsilonResidual_implies_scalarRelativeEnergyData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalEpsilonResidualRelativeEnergyData hH3) :
    H3AuditInitialCanonicalScalarRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, hScalar, hEpsilon⟩ := hData
  refine ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, hScalar, ?_⟩
  exact h3Audit_initialRelativeEnergy_exact_of_arbitrarySmallIntegratedResidual
    (fun t => ‖h3AuditInitialCanonicalPhysicalDifference
      hH3 hFourier0 A hA hU₀ t‖ ^ 2)
    b K (fun s => sq_nonneg _) hEpsilon

/-- Existing sequenced L¹ residual data satisfy the direct epsilon
interface: for each epsilon, choose one sufficiently accurate index. -/
theorem h3Audit_initialIntegratedResidual_implies_epsilonResidualData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalIntegratedResidualRelativeEnergyData hH3) :
    H3AuditInitialCanonicalEpsilonResidualRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, κ, R, hκ, hInt, hMass,
    hScalar, hApprox⟩ := hData
  refine ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, hScalar, ?_⟩
  intro ε hε
  obtain ⟨n, hn⟩ :=
    (hMass.eventually (Iio_mem_nhds hε)).exists
  exact ⟨κ n, R n, hκ n, hInt n, le_of_lt hn, hApprox n⟩

/-- Canonical physical compact weak-test agreement from epsilon-dependent
approximations whose absolute residual mass can be arbitrarily small. -/
theorem h3Audit_initialEpsilonResidual_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalEpsilonResidualRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialScalarRelativeEnergy_implies_compactWeakComparisonData
    hH3 (h3Audit_initialEpsilonResidual_implies_scalarRelativeEnergyData
      hH3 hData)

/-- Recover the true physical initial L² trace and H³ energy upper trace
from arbitrary-small residual errors and scalar-energy continuity. -/
theorem h3Audit_initialEpsilonResidual_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalEpsilonResidualRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialScalarRelativeEnergy_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialEpsilonResidual_implies_scalarRelativeEnergyData
      hH3 hData)

/-- Conditional full-time transverse Ḣ^(3/2) control: the independent
strong-H³ endpoint of one actual physical vorticity component is retained. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialEpsilonResidual
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalEpsilonResidualRelativeEnergyData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialScalarRelativeEnergy
    hH3 hClass i hPhysical
    (h3Audit_initialEpsilonResidual_implies_scalarRelativeEnergyData
      hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
