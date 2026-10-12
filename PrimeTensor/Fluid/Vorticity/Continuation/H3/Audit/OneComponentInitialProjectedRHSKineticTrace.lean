import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPhysicalHilbertGlobalFTC
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialBochnerDerivativeKineticControl

/-!
# Projected physical momentum source controls the initial kinetic right trace

The global positive-time physical Hilbert FTC supplies the actual strong
physical L² derivative under the old temporal joint-continuity condition.
The earlier initial Bochner/kinetic argument required that derivative as an
independent datum. Here it is supplied by the reconstructed physical projected
Navier--Stokes source: actual spectral Laplacian minus actual Leray forcing.

An L¹_t L²_x bound on that *specific* physical source over an initial interval
then implies a strong (as yet unidentified) physical L² right limit and a
finite right kinetic-energy limit. Combined with the previously specified
initial relative-energy residual, it also supplies the initial compact weak
comparison and physical zero-jet/H³ energy upper-trace conclusions.

Neither the old temporal joint-continuity condition, the near-zero L¹ source
bound, nor the vanishing comparison residual is established here from the
bare positive-time H³ admissibility assumptions.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

/-- Near-zero Bochner integrability of the *actual* projected physical
Navier--Stokes RHS, together with the previously derived strong positive-time
derivative, yields a finite but not yet identified physical L² right trace. -/
theorem h3Audit_initialOldJointProjectedRHS_exists_physicalHilbertRightLimit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    (b : ℝ) (hb : 0 < b) (hbT : b ≤ T)
    (hSource : IntervalIntegrable
      (fun s : ℝ =>
        h3AuditInitialActualSpectralLaplacianTotal hH3 s -
          h3AuditInitialActualSpectralLerayTotal hH3 s)
      volume 0 b) :
    ∃ L : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  apply h3Audit_initialOldHilbertStrongDerivative_exists_rightLimit
    hH3 b hb
    (fun s : ℝ =>
      h3AuditInitialActualSpectralLaplacianTotal hH3 s -
        h3AuditInitialActualSpectralLerayTotal hH3 s)
    hSource
  intro s hs
  exact h3Audit_initialOldJoint_implies_physicalHilbertHasDerivAt_at_positiveTime
    hH3 hOldJoint s ⟨hs.1, lt_of_lt_of_le hs.2 hbT⟩

/-- The exact physical zeroth-order norm identity turns that physical Hilbert
right limit into a finite *kinetic* right limit. No H³ right trace is used. -/
theorem h3Audit_initialOldJointProjectedRHS_kineticRightLimit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    (b : ℝ) (hb : 0 < b) (hbT : b ≤ T)
    (hSource : IntervalIntegrable
      (fun s : ℝ =>
        h3AuditInitialActualSpectralLaplacianTotal hH3 s -
          h3AuditInitialActualSpectralLerayTotal hH3 s)
      volume 0 b) :
    ∃ E : ℝ,
      Tendsto (velocityH3Energy0At u)
        (𝓝[>] (0 : ℝ)) (𝓝 E) := by
  apply h3Audit_initialOldHilbertStrongDerivative_kineticRightLimit
    hH3 b hb hbT
    (fun s : ℝ =>
      h3AuditInitialActualSpectralLaplacianTotal hH3 s -
        h3AuditInitialActualSpectralLerayTotal hH3 s)
    hSource
  intro s hs
  exact h3Audit_initialOldJoint_implies_physicalHilbertHasDerivAt_at_positiveTime
    hH3 hOldJoint s ⟨hs.1, lt_of_lt_of_le hs.2 hbT⟩

/-- Physical initial comparison with a concrete projected-RHS Bochner
integrability hypothesis instead of a separately posited vector derivative.
The residual comparison condition is preserved unchanged. -/
def H3AuditInitialCanonicalProjectedRHSRelativeEnergyData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T ∧
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (A : ℝ) (hA : 0 < A)
    (hU₀ : ‖velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0‖ ≤ A)
    (b : ℝ),
    0 < b ∧ b < T ∧
    b ≤ h3FinHeatLerayRestartRadius 1 A ∧
    IntervalIntegrable
      (fun s : ℝ =>
        h3AuditInitialActualSpectralLaplacianTotal hH3 s -
          h3AuditInitialActualSpectralLerayTotal hH3 s)
      volume 0 b ∧
    ∃ K : ℝ,
      ∀ ε : ℝ, 0 < ε →
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
              (∫ s in (0 : ℝ)..t, |R s|)

/-- The actual projected physical RHS and old joint-continuity condition
supply the abstract Bochner derivative field used by the existing kinetic
right-trace/relative-energy theory. -/
theorem h3Audit_initialProjectedRHS_implies_BochnerDerivativeData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalProjectedRHSRelativeEnergyData hH3) :
    H3AuditInitialCanonicalBochnerDerivativeRelativeEnergyData hH3 := by
  obtain ⟨hOldJoint, hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, hSource, K, hResidual⟩ := hData
  refine ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR,
    (fun s : ℝ =>
      h3AuditInitialActualSpectralLaplacianTotal hH3 s -
        h3AuditInitialActualSpectralLerayTotal hH3 s),
    K, hSource, ?_, hResidual⟩
  intro t ht
  exact h3Audit_initialOldJoint_implies_physicalHilbertHasDerivAt_at_positiveTime
    hH3 hOldJoint t ⟨ht.1, lt_trans ht.2 hbT⟩

/-- Finite right kinetic trace from the reconstructed physical projected RHS
and one initial source-integrability assumption. -/
theorem h3Audit_initialProjectedRHS_implies_rightKineticData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalProjectedRHSRelativeEnergyData hH3) :
    H3AuditInitialCanonicalRightKineticTraceRelativeEnergyData hH3 := by
  exact h3Audit_initialBochnerDerivative_implies_rightKineticData
    hH3 (h3Audit_initialProjectedRHS_implies_BochnerDerivativeData hH3 hData)

/-- The previous relative-energy comparison now accepts a concrete
near-zero physical projected source in place of an abstract derivative. -/
theorem h3Audit_initialOldJointProjectedRHS_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalProjectedRHSRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialBochnerDerivative_implies_compactWeakComparisonData
    hH3 (h3Audit_initialProjectedRHS_implies_BochnerDerivativeData hH3 hData)

/-- The identified initial physical zero-jet right trace and H³-energy upper
trace follow from the same comparison, not from the Bochner limit alone. -/
theorem h3Audit_initialOldJointProjectedRHS_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalProjectedRHSRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialBochnerDerivative_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialProjectedRHS_implies_BochnerDerivativeData hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
