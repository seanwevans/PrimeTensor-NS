import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialVariableResidualRelativeEnergy

/-!
# Initial relative-energy uniqueness from integrable time-residual densities

The preceding variable-residual theorem assumes a time-dependent residual
`ρ n t` that is uniformly bounded by a scalar sequence `δ n → 0`.
An approximation/commutator argument more naturally supplies a scalar error
density `R n : ℝ → ℝ`, whose absolute value is interval-integrable and whose
L¹ mass on the initial interval tends to zero. Here the residual is the
forward primitive `∫₀ᵗ |R n s| ds`.

Nonnegativity of `|R n s|` makes the forward primitive bounded by its total
mass on `[0,b]`. That supplies the precise budget required by the previous
variable-residual theorem, without any pointwise bound on `R n` and without
assuming that `R n` converges pointwise.

This is a PDE-FACING sufficient criterion, not a proof that Navier--Stokes
admissibility supplies the approximate inequality or the vanishing L¹ error.
Scalar relative-energy continuity at the artificially anchored time zero
also remains a separate obligation. The terminal actual-vorticity strong-H³
endpoint remains independent.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- Nonnegative residual densities have monotone forward primitives. The
single assumption is interval-integrability of `|r|` on `[0,b]`. -/
theorem h3Audit_initialResidualPrimitive_le_totalAbsMass
    (r : ℝ → ℝ) (b t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) b)
    (hInt : IntervalIntegrable (fun s : ℝ => |r s|) volume 0 b) :
    (∫ s in (0 : ℝ)..t, |r s|) ≤
      ∫ s in (0 : ℝ)..b, |r s| := by
  have hNonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) b)]
        (fun s : ℝ => |r s|) := by
    filter_upwards [] with s
    exact abs_nonneg (r s)
  exact intervalIntegral.integral_mono_interval
    le_rfl ht.1 ht.2 hNonneg hInt

/-- Approximation-dependent comparison coefficients and L¹-small temporal
residual densities imply the exact integral relative-energy inequality.
No convergence of the residual densities is required pointwise. -/
theorem h3Audit_initialRelativeEnergy_exact_of_integratedResidual
    (e : ℝ → ℝ) (b K : ℝ)
    (κ : ℕ → ℝ) (R : ℕ → ℝ → ℝ)
    (heNonneg : ∀ s : ℝ, 0 ≤ e s)
    (hκ : ∀ n : ℕ, κ n ≤ K)
    (hInt : ∀ n : ℕ,
      IntervalIntegrable (fun s : ℝ => |R n s|) volume 0 b)
    (hMass : Tendsto
      (fun n : ℕ => ∫ s in (0 : ℝ)..b, |R n s|)
      atTop (𝓝 (0 : ℝ)))
    (hApprox : ∀ (n : ℕ) (t : ℝ),
      t ∈ Set.Icc (0 : ℝ) b →
        e t ≤ (κ n * ∫ s in (0 : ℝ)..t, e s) +
          (∫ s in (0 : ℝ)..t, |R n s|)) :
    ∀ t ∈ Set.Icc (0 : ℝ) b,
      e t ≤ K * ∫ s in (0 : ℝ)..t, e s := by
  have hBudget : ∀ (n : ℕ) (t : ℝ),
      t ∈ Set.Icc (0 : ℝ) b →
        (∫ s in (0 : ℝ)..t, |R n s|) ≤
          ∫ s in (0 : ℝ)..b, |R n s| := by
    intro n t ht
    exact h3Audit_initialResidualPrimitive_le_totalAbsMass
      (R n) b t ht (hInt n)
  exact h3Audit_initialRelativeEnergy_exact_of_variableResidualBudget
    e b K κ
    (fun n : ℕ => ∫ s in (0 : ℝ)..b, |R n s|)
    (fun n t => ∫ s in (0 : ℝ)..t, |R n s|)
    heNonneg hκ hMass hBudget hApprox

/-- PDE-facing initial comparison with an actual L¹-in-time error-density
family. The relative-energy bound and its uniform coefficient remain
explicit analytic hypotheses; no old/selected equality is postulated. -/
def H3AuditInitialCanonicalIntegratedResidualRelativeEnergyData
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
    ∃ (K : ℝ) (κ : ℕ → ℝ) (R : ℕ → ℝ → ℝ),
      (∀ n : ℕ, κ n ≤ K) ∧
      (∀ n : ℕ,
        IntervalIntegrable (fun s : ℝ => |R n s|) volume 0 b) ∧
      Tendsto
        (fun n : ℕ => ∫ s in (0 : ℝ)..b, |R n s|)
        atTop (𝓝 (0 : ℝ)) ∧
      ContinuousOn
        (fun t => ‖h3AuditInitialCanonicalPhysicalDifference
          hH3 hFourier0 A hA hU₀ t‖ ^ 2)
        (Set.Icc (0 : ℝ) b) ∧
      ∀ (n : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) b →
        ‖h3AuditInitialCanonicalPhysicalDifference
          hH3 hFourier0 A hA hU₀ t‖ ^ 2 ≤
        (κ n * ∫ s in (0 : ℝ)..t,
          ‖h3AuditInitialCanonicalPhysicalDifference
            hH3 hFourier0 A hA hU₀ s‖ ^ 2) +
        (∫ s in (0 : ℝ)..t, |R n s|)

/-- Integrable residual densities with vanishing total L¹ mass produce the
previous variable-profile residual budget. -/
theorem h3Audit_initialIntegratedResidual_implies_variableResidualData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalIntegratedResidualRelativeEnergyData hH3) :
    H3AuditInitialCanonicalVariableResidualRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, κ, R, hκ, hInt, hMass,
    hScalar, hApprox⟩ := hData
  refine ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, κ,
    (fun n : ℕ => ∫ s in (0 : ℝ)..b, |R n s|),
    (fun n t => ∫ s in (0 : ℝ)..t, |R n s|),
    hκ, hMass, ?_, hScalar, hApprox⟩
  intro n t ht
  exact h3Audit_initialResidualPrimitive_le_totalAbsMass
    (R n) b t ht (hInt n)

/-- Canonical old/selected weak-test comparison from the L¹ residual source. -/
theorem h3Audit_initialIntegratedResidual_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalIntegratedResidualRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialVariableResidual_implies_compactWeakComparisonData
    hH3 (h3Audit_initialIntegratedResidual_implies_variableResidualData
      hH3 hData)

/-- Initial physical L² trace and H³ energy upper bound from integrable
residual densities and the independent initial scalar continuity input. -/
theorem h3Audit_initialIntegratedResidual_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalIntegratedResidualRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialVariableResidual_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialIntegratedResidual_implies_variableResidualData
      hH3 hData)

/-- Initial L¹ residual density control yields the full-time transverse
Ḣ^(3/2) estimates only with the separate terminal strong-H³ condition. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialIntegratedResidual
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalIntegratedResidualRelativeEnergyData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialVariableResidual
    hH3 hClass i hPhysical
    (h3Audit_initialIntegratedResidual_implies_variableResidualData
      hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
