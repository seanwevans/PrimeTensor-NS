import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialProjectedRHSKineticTrace
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialActualSpectralProjectedSourceBounds

/-!
# Initial projected momentum source from actual H³ energy integrability

The previous actual-source kinetic right-trace theorem requires Bochner
integrability of the physical Laplacian minus the projected nonlinear force.
Here that independent source hypothesis is replaced with integrability of the
actual scalar H³ energy. The source is automatically strongly measurable on
every strictly positive initial interval: spectral velocity continuity and
continuous reconstruction give positive-time continuity of the difference.

The established Fourier source bounds dominate that difference pointwise by
`(3 + h3AuditInitialLerayEnergyCoefficient) * velocityH3EnergyAt u t`.
Generic Hilbert-valued dominated integrability supplies both its initial
Bochner integral and a quantitative norm-mass estimate.

The old temporal-derivative joint-continuity hypothesis is still used for
strong momentum differentiation. Initial H³-energy integrability and the
vanishing old/selected relative-energy residual are independent inputs.
No claim of unconditional regularity, or of terminal vorticity closure,
is made by these theorems.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

/-- Initial integrability of actual H³ energy already bounds the concrete,
Fourier-reconstructed physical diffusion-minus-Leray source in `L¹_t L²_x`.
Strong source measurability is derived from the positive-time continuity
already established in the global physical Hilbert momentum FTC. -/
theorem h3Audit_initialActualProjectedRHS_integrable_and_mass_of_h3Energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b : ℝ) (hb : 0 < b) (hbT : b < T)
    (hE : IntervalIntegrable (velocityH3EnergyAt u) volume 0 b) :
    IntervalIntegrable
      (fun s : ℝ =>
        h3AuditInitialActualSpectralLaplacianTotal hH3 s -
          h3AuditInitialActualSpectralLerayTotal hH3 s)
      volume 0 b ∧
    (∫ s in (0 : ℝ)..b,
      ‖h3AuditInitialActualSpectralLaplacianTotal hH3 s -
        h3AuditInitialActualSpectralLerayTotal hH3 s‖) ≤
      (3 + h3AuditInitialLerayEnergyCoefficient) *
        (∫ s in (0 : ℝ)..b, velocityH3EnergyAt u s) := by
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert := fun s =>
    h3AuditInitialActualSpectralLaplacianTotal hH3 s -
      h3AuditInitialActualSpectralLerayTotal hH3 s
  let C : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  have hSub : Set.Ioc (0 : ℝ) b ⊆ Set.Ioo (0 : ℝ) T := by
    intro s hs
    exact ⟨hs.1, lt_of_le_of_lt hs.2 hbT⟩
  have hCont : ContinuousOn G (Set.Ioc (0 : ℝ) b) := by
    exact
      (h3Audit_initialActualProjectedRHS_continuousOn_positiveTime hH3).mono hSub
  have hMeas : AEStronglyMeasurable G
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) b)) :=
    hCont.aestronglyMeasurable measurableSet_Ioc
  have hBound : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b →
      ‖G s‖ ≤ C * velocityH3EnergyAt u s := by
    intro s hs
    have hD :=
      h3Audit_initialActualSpectralLaplacian_norm_le_energy
        hH3 b hbT s hs
    have hN :=
      h3Audit_initialActualSpectralLeray_norm_le_energy
        hH3 b hbT s hs
    dsimp only [G, C]
    calc
      ‖h3AuditInitialActualSpectralLaplacianTotal hH3 s -
          h3AuditInitialActualSpectralLerayTotal hH3 s‖ ≤
        ‖h3AuditInitialActualSpectralLaplacianTotal hH3 s‖ +
          ‖h3AuditInitialActualSpectralLerayTotal hH3 s‖ :=
        norm_sub_le _ _
      _ ≤ 3 * velocityH3EnergyAt u s +
          h3AuditInitialLerayEnergyCoefficient * velocityH3EnergyAt u s :=
        add_le_add hD hN
      _ = (3 + h3AuditInitialLerayEnergyCoefficient) *
          velocityH3EnergyAt u s := by ring
  have hInt : IntervalIntegrable G volume 0 b :=
    h3Audit_initialEnergyMajorant_source_intervalIntegrable
      (velocityH3EnergyAt u) G b C hb.le hE hMeas hBound
  have hMass :
      (∫ s in (0 : ℝ)..b, ‖G s‖) ≤
        C * (∫ s in (0 : ℝ)..b, velocityH3EnergyAt u s) :=
    h3Audit_initialEnergyMajorant_source_normMass_le
      (velocityH3EnergyAt u) G b C hb.le hE hMeas hBound
  exact ⟨hInt, hMass⟩

/-- Old joint temporal continuity plus actual initial H³-energy integrability
ensures a finite strong physical L² right trace, without assuming the value
of the initial limit or a separate source integrability condition. -/
theorem h3Audit_initialOldJointEnergyRHS_exists_physicalHilbertRightLimit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    (b : ℝ) (hb : 0 < b) (hbT : b < T)
    (hE : IntervalIntegrable (velocityH3EnergyAt u) volume 0 b) :
    ∃ L : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  have hSource :=
    (h3Audit_initialActualProjectedRHS_integrable_and_mass_of_h3Energy
      hH3 b hb hbT hE).1
  exact
    h3Audit_initialOldJointProjectedRHS_exists_physicalHilbertRightLimit
      hH3 hOldJoint b hb hbT.le hSource

/-- Consequently the genuine physical kinetic energy has a finite right
limit. This does not identify that limit with its declared time-zero value. -/
theorem h3Audit_initialOldJointEnergyRHS_kineticRightLimit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    (b : ℝ) (hb : 0 < b) (hbT : b < T)
    (hE : IntervalIntegrable (velocityH3EnergyAt u) volume 0 b) :
    ∃ E : ℝ,
      Tendsto (velocityH3Energy0At u)
        (𝓝[>] (0 : ℝ)) (𝓝 E) := by
  have hSource :=
    (h3Audit_initialActualProjectedRHS_integrable_and_mass_of_h3Energy
      hH3 b hb hbT hE).1
  exact h3Audit_initialOldJointProjectedRHS_kineticRightLimit
    hH3 hOldJoint b hb hbT.le hSource

/-- Initial comparison data with the physical source's near-zero Bochner
integrability replaced by scalar actual H³-energy integrability. The old
joint temporal-continuity premise and vanishing comparison residual
remain explicitly independent. -/
def H3AuditInitialCanonicalEnergyDominatedRHSRelativeEnergyData
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
    IntervalIntegrable (velocityH3EnergyAt u) volume 0 b ∧
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

/-- The initial H³ energy envelope automatically generates the physical
source L¹ hypothesis required by the preceding projected-RHS contract. -/
theorem h3Audit_initialEnergyDominatedRHS_implies_projectedRHSData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalEnergyDominatedRHSRelativeEnergyData hH3) :
    H3AuditInitialCanonicalProjectedRHSRelativeEnergyData hH3 := by
  obtain ⟨hOldJoint, hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, hE, K, hResidual⟩ := hData
  have hSource :=
    (h3Audit_initialActualProjectedRHS_integrable_and_mass_of_h3Energy
      hH3 b hb hbT hE).1
  exact ⟨hOldJoint, hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, hSource, K, hResidual⟩

/-- Derived source integrability feeds the existing finite right kinetic
trace and relative-energy interface. -/
theorem h3Audit_initialEnergyDominatedRHS_implies_rightKineticData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalEnergyDominatedRHSRelativeEnergyData hH3) :
    H3AuditInitialCanonicalRightKineticTraceRelativeEnergyData hH3 := by
  exact h3Audit_initialProjectedRHS_implies_rightKineticData hH3
    (h3Audit_initialEnergyDominatedRHS_implies_projectedRHSData hH3 hData)

/-- The already proved nonlinear relative-energy comparison then gives
compact weak-test initial uniqueness, under its unchanged residual premise. -/
theorem h3Audit_initialEnergyDominatedRHS_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalEnergyDominatedRHSRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialOldJointProjectedRHS_implies_compactWeakComparisonData
    hH3 (h3Audit_initialEnergyDominatedRHS_implies_projectedRHSData hH3 hData)

/-- Recovery of the initial physical zero-jet L² right trace and upper H³
energy trace from the unchanged relative-energy comparison. -/
theorem h3Audit_initialEnergyDominatedRHS_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalEnergyDominatedRHSRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact
    h3Audit_initialOldJointProjectedRHS_implies_physicalZeroJetAndEnergyUpper
      hH3 (h3Audit_initialEnergyDominatedRHS_implies_projectedRHSData hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
