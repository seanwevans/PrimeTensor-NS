import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialOldKineticCeilingRelativeEnergy
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialMildWeakTraceClosure

/-!
# Initial physical kinetic ceiling from actual H³ energy

The preceding initial weak--strong relative-energy contract requires a uniform
physical `L²` norm ceiling for the actual old velocity on `(0,b)`. The real
Fourier encoder of every strict physical old-velocity slice has its norm bounded
by the square root of the actual normalized `H³` energy. Its genuine physical
zeroth-order `L²` jet is exactly the inverse-Fourier real decoder of this
spectral state. Hence the old physical Hilbert velocity is bounded by three
times the square root of its *actual* `H³` energy, not by an independently
chosen physical kinetic bound.

This module replaces the old physical `L²` ceiling assumption with a uniform
upper bound on `velocityH3EnergyAt u` on `(0,b)`. Measurability of the old
physical Hilbert path and the epsilon-accurate relative-energy estimates remain
explicit PDE-side premises. The open-time H³ admissibility predicate does not,
by itself, supply the uniform bound approaching time zero. The separate
terminal strong-H³ actual-vorticity hypothesis remains unchanged.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- The actual old physical velocity `L²` norm is controlled by its actual
positive-time normalized `H³` energy, using the exact spectral-to-physical
Fourier decoder rather than assuming an independent kinetic estimate. -/
theorem h3Audit_initialOldPhysicalHilbert_norm_le_sqrtH3Energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ≤
      3 * Real.sqrt (velocityH3EnergyAt u t) := by
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  have hPhysical :
      h3AuditInitialOldPhysicalHilbertTotal hH3 t =
        (WithLp.toLp (2 : ℝ≥0∞)
          (fun j : Fin 3 =>
            h3FromFourierRealL2 (h3SpectralScalarDecodeRealL2 (U j))) :
          H3PhysicalRealFinVectorL2Hilbert) := by
    apply PiLp.ext
    intro j
    simpa only [h3AuditInitialOldPhysicalHilbertTotal,
      PiLp.toLp_apply, U] using
      (h3Audit_actualPositivePhysicalZeroJet_eq_spectralRealDecode
        hH3 t ht j).symm
  have hState : ‖U‖ ≤ Real.sqrt (velocityH3EnergyAt u t) := by
    dsimp only [U]
    rw [h3AuditActualSpectralVelocityTotal_eq_at hH3 t ht]
    exact h3AuditActualSpectralVelocityAt_norm_le_sqrt_energy hH3 t ht
  rw [hPhysical]
  exact (h3Audit_selectedPhysicalHilbertDecode_norm_le U).trans
    (mul_le_mul_of_nonneg_left hState (by norm_num))

/-- A uniform actual `H³` energy bound on an initial strict interval yields
a uniform old physical `L²` ceiling on that interval. -/
theorem h3Audit_initialOldPhysicalHilbert_norm_le_of_H3EnergyCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b E : ℝ) (hbT : b < T)
    (hEnergy : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      velocityH3EnergyAt u t ≤ E) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ≤
        3 * Real.sqrt E := by
  intro t ht
  have htT : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨ht.1, lt_of_le_of_lt ht.2.le hbT⟩
  exact (h3Audit_initialOldPhysicalHilbert_norm_le_sqrtH3Energy
    hH3 t htT).trans
    (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (hEnergy t ht)) (by norm_num))

/-- The PDE-facing relative-energy comparison now asks for a uniform bound
on the *actual normalized H³ energy*, rather than a separate kinetic ceiling
for the old physical `L²` velocity. Time measurability and the PDE residual
comparison remain independent hypotheses. -/
def H3AuditInitialCanonicalH3EnergyCeilingRelativeEnergyData
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
    ∃ (E K : ℝ),
      AEStronglyMeasurable
        (h3AuditInitialOldPhysicalHilbertTotal hH3)
        ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) b)) ∧
      (∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) b →
        velocityH3EnergyAt u s ≤ E) ∧
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

/-- Derive the previous old-kinetic comparison data with the explicit
ceiling `B = 3 * sqrt E`; no separate old physical norm bound is assumed. -/
theorem h3Audit_initialH3EnergyCeiling_implies_oldKineticData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalH3EnergyCeilingRelativeEnergyData hH3) :
    H3AuditInitialCanonicalOldKineticCeilingRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, E, K, hMeas, hEnergy, hEpsilon⟩ := hData
  refine ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, 3 * Real.sqrt E, K, ?_, hMeas, ?_, hEpsilon⟩
  · positivity
  · exact h3Audit_initialOldPhysicalHilbert_norm_le_of_H3EnergyCeiling
      hH3 b E hbT hEnergy

/-- A bounded normalized physical H³ energy and the remaining PDE comparison
assumptions imply compact physical weak-test uniqueness at the initial time. -/
theorem h3Audit_initialH3EnergyCeiling_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalH3EnergyCeilingRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialOldKineticCeiling_implies_compactWeakComparisonData
    hH3 (h3Audit_initialH3EnergyCeiling_implies_oldKineticData hH3 hData)

/-- Recover the actual initial physical L² jet and the H³ energy upper trace
under the same explicitly conditional initial comparison assumptions. -/
theorem h3Audit_initialH3EnergyCeiling_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalH3EnergyCeilingRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialOldKineticCeiling_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialH3EnergyCeiling_implies_oldKineticData hH3 hData)

/-- The terminal vorticity strong-H³ endpoint remains an independent
hypothesis for the full-time two-coordinate intrinsic Sobolev conclusion. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialH3EnergyCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalH3EnergyCeilingRelativeEnergyData hH3) :
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
    (h3Audit_initialH3EnergyCeiling_implies_oldKineticData hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
