import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialBoundedMeasurableRelativeEnergy
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.Energy.Path.Continuity

/-!
# Initial relative energy from an old-velocity kinetic ceiling

The previous bounded-measurable criterion puts a measurability assumption
and a uniform bound directly on the squared old/selected difference.
Those two assumptions follow instead from the corresponding assumptions on
only the *old physical L² velocity*: the selected restart is the already
constructed, continuous and uniformly bounded canonical mild solution.

This file proves the selected physical Hilbert decoder's norm estimate,
uses its time continuity to establish measurable squared difference, and
converts the old kinetic ceiling to the relative-energy ceiling.

The old velocity's time measurability, its uniform physical L² ceiling,
and the small-residual PDE comparison are still independent hypotheses.
Nothing here infers them from open-time Navier--Stokes admissibility.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- The three-coordinate real physical decoder of a weighted H³ spectral
state has physical L² norm at most three times the spectral norm. -/
theorem h3Audit_selectedPhysicalHilbertDecode_norm_le
    (U : H3SpectralVelocityState) :
    ‖(WithLp.toLp (2 : ℝ≥0∞)
        (fun j : Fin 3 =>
          h3FromFourierRealL2
            (h3SpectralVelocityDecodeRealL2 U j)) :
          H3PhysicalRealFinVectorL2Hilbert)‖ ≤ 3 * ‖U‖ := by
  apply norm_h3PhysicalRealFinVectorL2Hilbert_le_three_mul_of_coordinate_norm_le
    _ (norm_nonneg U)
  intro j
  simpa only [PiLp.toLp_apply, norm_h3FromFourierRealL2] using
    norm_h3SpectralVelocityDecodeRealL2_apply_le U j

/-- The selected physical velocity is uniformly bounded by `6*A`, purely
from the canonical Picard H³ spectral ball and the physical decoder. -/
theorem h3Audit_selectedPhysicalHilbertRestart_norm_le
    (U₀ : H3SpectralVelocityState) (A : ℝ)
    (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A) (t : ℝ) :
    ‖(WithLp.toLp (2 : ℝ≥0∞)
        (fun j : Fin 3 =>
          h3FromFourierRealL2 (h3SpectralScalarDecodeRealL2
            ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              (one_pos : (0 : ℝ) < 1) U₀ hA hU₀ t) j))) :
          H3PhysicalRealFinVectorL2Hilbert)‖ ≤ 6 * A := by
  let W : H3SpectralVelocityState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1) U₀ hA hU₀ t
  calc
    ‖(WithLp.toLp (2 : ℝ≥0∞)
        (fun j : Fin 3 =>
          h3FromFourierRealL2
            (h3SpectralVelocityDecodeRealL2 W j)) :
          H3PhysicalRealFinVectorL2Hilbert)‖
        ≤ 3 * ‖W‖ := h3Audit_selectedPhysicalHilbertDecode_norm_le W
    _ ≤ 3 * (2 * A) := by
      apply mul_le_mul_of_nonneg_left
      exact norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        (one_pos : (0 : ℝ) < 1) U₀ hA hU₀ t
      norm_num
    _ = 6 * A := by ring

/-- The selected old-initial-data restart has a continuous physical three-
component `L²` Hilbert path, without assumptions on the old branch. -/
theorem h3Audit_continuous_selectedPhysicalHilbertRestart
    (U₀ : H3SpectralVelocityState) (A : ℝ)
    (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A) :
    Continuous
      (fun t : ℝ =>
        (WithLp.toLp (2 : ℝ≥0∞)
          (fun j : Fin 3 =>
            h3FromFourierRealL2 (h3SpectralScalarDecodeRealL2
              ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                (one_pos : (0 : ℝ) < 1) U₀ hA hU₀ t) j))) :
            H3PhysicalRealFinVectorL2Hilbert)) := by
  exact continuous_h3SelectedPhysicalL2HilbertDecode.comp
    (continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1) U₀ hA hU₀)

/-- For an old measurable physical Hilbert path and a continuous selected
path, the squared difference is measurable; their separate bounds control
its initial kinetic mass. -/
theorem h3Audit_initialOldSelectedEnergy_measurable_and_bounded
    (O S : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hOmeas : AEStronglyMeasurable O
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) b)))
    (hScont : Continuous S)
    (hOld : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b → ‖O t‖ ≤ B)
    (hSelected : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b → ‖S t‖ ≤ C) :
    AEStronglyMeasurable (fun t : ℝ => ‖O t - S t‖ ^ 2)
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) b)) ∧
    (∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      ‖O t - S t‖ ^ 2 ≤ (B + C) ^ 2) := by
  constructor
  · exact (hOmeas.sub hScont.aestronglyMeasurable).norm.pow 2
  · intro t ht
    have hDiff : ‖O t - S t‖ ≤ B + C := by
      calc
        ‖O t - S t‖ ≤ ‖O t‖ + ‖S t‖ := norm_sub_le _ _
        _ ≤ B + C := add_le_add (hOld t ht) (hSelected t ht)
    have hDiff0 : 0 ≤ ‖O t - S t‖ := norm_nonneg _
    have hBC0 : 0 ≤ B + C := add_nonneg hB hC
    nlinarith

/-- Explicit physical old `L²` vector at any real time. Away from the
strict physical interval its coordinates use the existing totalization. -/
noncomputable def h3AuditInitialOldPhysicalHilbertTotal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) : H3PhysicalRealFinVectorL2Hilbert :=
  WithLp.toLp (2 : ℝ≥0∞)
    (fun j : Fin 3 => h3AuditActualPhysicalZeroJetL2Total hH3 j t)

/-- At strictly positive times, the canonical comparison difference really
is the old physical Hilbert path minus the selected physical Hilbert path. -/
theorem h3Audit_initialCanonicalPhysicalDifference_eq_old_sub_selected
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {hInt0 : VelocityH3IntegrableAt u (0 : ℝ)}
    {hMeas0 : VelocityH3MeasurableAt u (0 : ℝ)}
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (A : ℝ) (hA : 0 < A)
    (hU₀ : ‖velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0‖ ≤ A)
    (t : ℝ) (ht : 0 < t) :
    h3AuditInitialCanonicalPhysicalDifference hH3 hFourier0 A hA hU₀ t =
      h3AuditInitialOldPhysicalHilbertTotal hH3 t -
        (WithLp.toLp (2 : ℝ≥0∞)
          (fun j : Fin 3 =>
            h3FromFourierRealL2 (h3SpectralScalarDecodeRealL2
              ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                (one_pos : (0 : ℝ) < 1)
                (velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0)
                hA hU₀ t) j))) :
          H3PhysicalRealFinVectorL2Hilbert) := by
  apply PiLp.ext
  intro j
  simp only [h3AuditInitialCanonicalPhysicalDifference,
    if_neg (ne_of_gt ht), h3AuditInitialOldPhysicalHilbertTotal,
    PiLp.sub_apply, PiLp.toLp_apply]

/-- The old physical velocity's time-measurability and kinetic ceiling
supply the measurability and uniform bound previously demanded directly
of its old-minus-selected comparison energy. -/
def H3AuditInitialCanonicalOldKineticCeilingRelativeEnergyData
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
    ∃ (B K : ℝ),
      0 ≤ B ∧
      AEStronglyMeasurable
        (h3AuditInitialOldPhysicalHilbertTotal hH3)
        ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) b)) ∧
      (∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) b →
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3 s‖ ≤ B) ∧
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

/-- The selected mild solution supplies its own bound and measurability.
Only the original old physical velocity requires explicit kinetic input. -/
theorem h3Audit_initialOldKineticCeiling_implies_boundedMeasurableData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalOldKineticCeilingRelativeEnergyData hH3) :
    H3AuditInitialCanonicalBoundedMeasurableRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, B, K, hB, hOldMeas, hOldBound, hEpsilon⟩ := hData
  let U₀ : H3SpectralVelocityState :=
    velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0
  let O : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let S : ℝ → H3PhysicalRealFinVectorL2Hilbert := fun t =>
    WithLp.toLp (2 : ℝ≥0∞)
      (fun j : Fin 3 =>
        h3FromFourierRealL2 (h3SpectralScalarDecodeRealL2
          ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            (one_pos : (0 : ℝ) < 1) U₀ hA hU₀ t) j)))
  have hScont : Continuous S :=
    h3Audit_continuous_selectedPhysicalHilbertRestart U₀ A hA hU₀
  have hSbound : ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) b → ‖S s‖ ≤ 6 * A := by
    intro s _hs
    exact h3Audit_selectedPhysicalHilbertRestart_norm_le U₀ A hA hU₀ s
  have hSpos : 0 ≤ 6 * A := by positivity
  obtain ⟨hMeasE, hBoundE⟩ :=
    h3Audit_initialOldSelectedEnergy_measurable_and_bounded
      O S b B (6 * A) hB hSpos hOldMeas hScont hOldBound hSbound
  refine ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, (B + 6 * A) ^ 2, K, ?_, ?_, hEpsilon⟩
  · have hEq : ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) b →
        ‖h3AuditInitialCanonicalPhysicalDifference
          hH3 hFourier0 A hA hU₀ s‖ ^ 2 = ‖O s - S s‖ ^ 2 := by
      intro s hs
      rw [h3Audit_initialCanonicalPhysicalDifference_eq_old_sub_selected
        hH3 hFourier0 A hA hU₀ s hs.1]
    have hAE : (fun s : ℝ =>
        ‖h3AuditInitialCanonicalPhysicalDifference
          hH3 hFourier0 A hA hU₀ s‖ ^ 2)
        =ᵐ[((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) b))]
        (fun s : ℝ => ‖O s - S s‖ ^ 2) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hEq s hs
    exact hMeasE.congr hAE.symm
  · intro s hs
    rw [h3Audit_initialCanonicalPhysicalDifference_eq_old_sub_selected
      hH3 hFourier0 A hA hU₀ s hs.1]
    exact hBoundE s hs

/-- Canonical compact-test initial uniqueness from old-velocity physical
kinetic bounds, rather than assumptions on the difference energy. -/
theorem h3Audit_initialOldKineticCeiling_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalOldKineticCeilingRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialBoundedMeasurable_implies_compactWeakComparisonData
    hH3 (h3Audit_initialOldKineticCeiling_implies_boundedMeasurableData hH3 hData)

/-- Initial physical L² trace and H³ energy upper bound from the same
conditional old kinetic comparison. -/
theorem h3Audit_initialOldKineticCeiling_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalOldKineticCeilingRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialBoundedMeasurable_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialOldKineticCeiling_implies_boundedMeasurableData hH3 hData)

/-- The two transverse full-time estimates retain the independent
strong-H³ terminal actual-vorticity endpoint premise. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialOldKineticCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalOldKineticCeilingRelativeEnergyData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialBoundedMeasurable
    hH3 hClass i hPhysical
    (h3Audit_initialOldKineticCeiling_implies_boundedMeasurableData hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
