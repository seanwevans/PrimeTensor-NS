import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialEnergyDominatedProjectedRHS
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Initial projected momentum from a subcritical H³ energy growth rate

Instead of imposing initial integrability of the entire actual H³ energy,
the projected source can be integrated directly from a quantitative,
subcritical near-zero energy envelope

    E₃(t) ≤ M * t ^ (-α),    0 ≤ α < 1.

The real-power majorant is integrable at zero. The source is strongly
measurable on positive time because its actual Fourier reconstruction
was proved continuous there. The source estimate is established on
the closed initial interval; at zero its totalized value is zero.

The conclusion is the genuine projected physical L² source, not an
abstract surrogate. The already established strong momentum derivative
then gives finite physical and kinetic right limits.

The power-law envelope, old temporal joint continuity and the
old/selected vanishing residual are independent assumptions.
No unconditional initial or terminal regularity is asserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

/-- Subcritical actual H³ growth directly bounds the physical
diffusion-minus-Leray source in initial Bochner L¹, without
requiring an independently asserted energy integral. -/
theorem h3Audit_initialSubcriticalEnergyRate_projectedRHS_integrable_and_mass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b α M : ℝ) (hb : 0 < b) (hbT : b < T)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hM : 0 ≤ M)
    (hRate : ∀ s : ℝ, s ∈ Set.Ioc (0 : ℝ) b →
      velocityH3EnergyAt u s ≤ M * s ^ (-α)) :
    IntervalIntegrable
      (fun s : ℝ =>
        h3AuditInitialActualSpectralLaplacianTotal hH3 s -
          h3AuditInitialActualSpectralLerayTotal hH3 s)
      volume 0 b ∧
    (∫ s in (0 : ℝ)..b,
      ‖h3AuditInitialActualSpectralLaplacianTotal hH3 s -
        h3AuditInitialActualSpectralLerayTotal hH3 s‖) ≤
      ((3 + h3AuditInitialLerayEnergyCoefficient) * M) *
        (∫ s in (0 : ℝ)..b, s ^ (-α)) := by
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert := fun s =>
    h3AuditInitialActualSpectralLaplacianTotal hH3 s -
      h3AuditInitialActualSpectralLerayTotal hH3 s
  let C : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  have hC : 0 ≤ C := by
    dsimp only [C]
    linarith only [h3AuditInitialLerayEnergyCoefficient_nonneg]
  have hPower : IntervalIntegrable
      (fun s : ℝ => s ^ (-α)) volume 0 b := by
    exact intervalIntegral.intervalIntegrable_rpow'
      (show -(1 : ℝ) < -α by linarith only [hα1])
  have hSub : Set.Ioc (0 : ℝ) b ⊆ Set.Ioo (0 : ℝ) T := by
    intro s hs
    exact ⟨hs.1, lt_of_le_of_lt hs.2 hbT⟩
  have hContinuous : ContinuousOn G (Set.Ioc (0 : ℝ) b) :=
    (h3Audit_initialActualProjectedRHS_continuousOn_positiveTime
      hH3).mono hSub
  have hMeas : AEStronglyMeasurable G
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) b)) :=
    hContinuous.aestronglyMeasurable measurableSet_Ioc
  have hBound : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b →
      ‖G s‖ ≤ (C * M) * s ^ (-α) := by
    intro s hs
    by_cases hZero : s = 0
    · subst s
      have hGZero : G 0 = 0 := by
        simp [G, h3AuditInitialActualSpectralLaplacianTotal,
          h3AuditInitialActualSpectralLerayTotal]
      rw [hGZero, norm_zero]
      exact mul_nonneg (mul_nonneg hC hM)
        (Real.rpow_nonneg (le_refl (0 : ℝ)) (-α))
    · have hsIoc : s ∈ Set.Ioc (0 : ℝ) b :=
        ⟨lt_of_le_of_ne hs.1 (Ne.symm hZero), hs.2⟩
      have hD :=
        h3Audit_initialActualSpectralLaplacian_norm_le_energy
          hH3 b hbT s hs
      have hN :=
        h3Audit_initialActualSpectralLeray_norm_le_energy
          hH3 b hbT s hs
      calc
        ‖G s‖ ≤
            3 * velocityH3EnergyAt u s +
              h3AuditInitialLerayEnergyCoefficient *
                velocityH3EnergyAt u s := by
          dsimp only [G]
          exact (norm_sub_le _ _).trans (add_le_add hD hN)
        _ = C * velocityH3EnergyAt u s := by
          dsimp only [C]
          ring
        _ ≤ C * (M * s ^ (-α)) :=
          mul_le_mul_of_nonneg_left (hRate s hsIoc) hC
        _ = (C * M) * s ^ (-α) := by ring
  have hInt : IntervalIntegrable G volume 0 b :=
    h3Audit_initialEnergyMajorant_source_intervalIntegrable
      (fun s : ℝ => s ^ (-α)) G b (C * M)
      hb.le hPower hMeas hBound
  have hMass :
      (∫ s in (0 : ℝ)..b, ‖G s‖) ≤
        (C * M) * (∫ s in (0 : ℝ)..b, s ^ (-α)) :=
    h3Audit_initialEnergyMajorant_source_normMass_le
      (fun s : ℝ => s ^ (-α)) G b (C * M)
      hb.le hPower hMeas hBound
  exact ⟨hInt, hMass⟩

/-- Under the independent old-temporal-joint condition, a subcritical
initial H³ rate produces the strong physical Hilbert right limit. -/
theorem h3Audit_initialSubcriticalEnergyRate_physicalRightLimit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    (b α M : ℝ) (hb : 0 < b) (hbT : b < T)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hM : 0 ≤ M)
    (hRate : ∀ s : ℝ, s ∈ Set.Ioc (0 : ℝ) b →
      velocityH3EnergyAt u s ≤ M * s ^ (-α)) :
    ∃ L : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  have hSource :=
    (h3Audit_initialSubcriticalEnergyRate_projectedRHS_integrable_and_mass
      hH3 b α M hb hbT hα0 hα1 hM hRate).1
  exact h3Audit_initialOldJointProjectedRHS_exists_physicalHilbertRightLimit
    hH3 hOldJoint b hb hbT.le hSource

/-- Exact zeroth-order physical kinetic energy then has a finite,
not necessarily identified, right limit. -/
theorem h3Audit_initialSubcriticalEnergyRate_kineticRightLimit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    (b α M : ℝ) (hb : 0 < b) (hbT : b < T)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hM : 0 ≤ M)
    (hRate : ∀ s : ℝ, s ∈ Set.Ioc (0 : ℝ) b →
      velocityH3EnergyAt u s ≤ M * s ^ (-α)) :
    ∃ E : ℝ, Tendsto (velocityH3Energy0At u)
      (𝓝[>] (0 : ℝ)) (𝓝 E) := by
  have hSource :=
    (h3Audit_initialSubcriticalEnergyRate_projectedRHS_integrable_and_mass
      hH3 b α M hb hbT hα0 hα1 hM hRate).1
  exact h3Audit_initialOldJointProjectedRHS_kineticRightLimit
    hH3 hOldJoint b hb hbT.le hSource

/-- Initial comparison contract under a subcritical H³ growth envelope,
rather than separate initial H³ or physical RHS integrability assumptions. -/
def H3AuditInitialCanonicalSubcriticalEnergyRateResidualData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T ∧
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (A : ℝ) (hA : 0 < A)
    (hU₀ : ‖velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0‖ ≤ A)
    (b α M : ℝ),
    0 < b ∧ b < T ∧
    b ≤ h3FinHeatLerayRestartRadius 1 A ∧
    0 ≤ α ∧ α < 1 ∧ 0 ≤ M ∧
    (∀ s : ℝ, s ∈ Set.Ioc (0 : ℝ) b →
      velocityH3EnergyAt u s ≤ M * s ^ (-α)) ∧
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

/-- The subcritical pointwise envelope supplies the previously independent
physical projected RHS Bochner integrability premise. -/
theorem h3Audit_initialSubcriticalEnergyRate_implies_projectedRHSData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalSubcriticalEnergyRateResidualData hH3) :
    H3AuditInitialCanonicalProjectedRHSRelativeEnergyData hH3 := by
  obtain ⟨hOldJoint, hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, α, M, hb, hbT, hbR, hα0, hα1, hM, hRate, K, hResidual⟩ := hData
  have hSource :=
    (h3Audit_initialSubcriticalEnergyRate_projectedRHS_integrable_and_mass
      hH3 b α M hb hbT hα0 hα1 hM hRate).1
  exact ⟨hOldJoint, hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, hSource, K, hResidual⟩

/-- Recover the established initial comparison on the same unchanged
relative-energy residual, without imposing a separate source integral. -/
theorem h3Audit_initialSubcriticalEnergyRate_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalSubcriticalEnergyRateResidualData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialOldJointProjectedRHS_implies_compactWeakComparisonData
    hH3 (h3Audit_initialSubcriticalEnergyRate_implies_projectedRHSData hH3 hData)

/-- Recover the actual initial physical L² and upper H³ right traces;
the relative-energy residual condition remains essential. -/
theorem h3Audit_initialSubcriticalEnergyRate_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalSubcriticalEnergyRateResidualData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact
    h3Audit_initialOldJointProjectedRHS_implies_physicalZeroJetAndEnergyUpper
      hH3 (h3Audit_initialSubcriticalEnergyRate_implies_projectedRHSData hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
