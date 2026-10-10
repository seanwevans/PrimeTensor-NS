import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialCanonicalMildOverlap
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Overlap.Uniqueness

/-!
# Initial old/selected identification from heat--Leray Picard uniqueness

The preceding audit assumed direct equality of the actual physical velocity's
weighted Fourier H³ states with the Banach-selected mild solution near zero.
That equality can instead be *proved* from an old-solution normalized spectral
path that (i) represents the actual velocity on an early overlap, (ii) belongs
to the canonical `2*A` Picard ball, and (iii) satisfies the SAME heat-minus-
Duhamel integral equation as the selected path.

The existing canonical-radius Picard uniqueness theorem then identifies the
whole normalized old path with the selected path; its physical-time extension
therefore agrees with the actual physical velocity on the initial overlap.

The old-solution mild equation, boundedness and Fourier representation are
EXPLICIT proof obligations, not consequences of pointwise Navier--Stokes
regularity or of a lone H³ snapshot. This file neither derives those
properties from initial data nor imports any external continuation theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

/-- A normalized H³ spectral path representing the *actual old velocity* on
`(0,b)` and satisfying the canonical unit-viscosity Picard equation inside
its uniqueness ball. This does not assume equality with the selected path. -/
def H3AuditInitialOldNormalizedMildDataAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T A : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A) (b : ℝ) : Prop :=
  ∃ V : H3SpectralVelocityPath,
    0 < b ∧ b < T ∧
    b ≤ h3FinHeatLerayRestartRadius 1 A ∧
    ‖V‖ ≤ 2 * A ∧
    (h3SpectralVelocityHeatFreePath
          1 (h3FinHeatLerayRestartRadius 1 A)
          (one_pos : (0 : ℝ) < 1).le
          (h3FinHeatLerayRestartRadius_pos 1 hA).le U₀ -
        h3SpectralFinHeatLerayDuhamelPathOperator
          (one_pos : (0 : ℝ) < 1)
          (h3FinHeatLerayRestartRadius_pos 1 hA).le V V = V) ∧
    ∀ (p : H3TerminalCurlGradientPair)
      (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T),
      t < b →
        h3TerminalComplementSpectralStateAt hH3 p t ht =
          (h3PathPhysicalRealExtension
            (h3FinHeatLerayRestartRadius 1 A) V t)
            (h3ClassicalizationFinOfAxis
              (h3TerminalComplementComponentAxisForPair p))

/-- Banach uniqueness converts an actual normalized old-solution mild path
into the canonical physical old/selected equality on `(0,b)`. -/
theorem h3Audit_initialOldNormalizedMildDataAt_implies_canonicalMildOverlap
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T A b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A)
    (hData : H3AuditInitialOldNormalizedMildDataAt hH3 U₀ hA hU₀ b) :
    H3AuditInitialCanonicalMildOverlapAt hH3 U₀ hA hU₀ b := by
  obtain ⟨V, hb, hbT, hbR, hVbound, hVmild, hMatches⟩ := hData
  have hUnique :
      V = h3SpectralFinHeatLerayMildSolutionAtRestartRadius
        (one_pos : (0 : ℝ) < 1) U₀ hA hU₀ :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_unique
      (one_pos : (0 : ℝ) < 1) U₀ hA hU₀ V hVbound hVmild
  refine ⟨hb, hbT, hbR, ?_⟩
  intro p t ht htb
  calc
    h3TerminalComplementSpectralStateAt hH3 p t ht =
        (h3PathPhysicalRealExtension
            (h3FinHeatLerayRestartRadius 1 A) V t)
          (h3ClassicalizationFinOfAxis
            (h3TerminalComplementComponentAxisForPair p)) :=
      hMatches p t ht htb
    _ = (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          (one_pos : (0 : ℝ) < 1) U₀ hA hU₀ t)
          (h3ClassicalizationFinOfAxis
            (h3TerminalComplementComponentAxisForPair p)) := by
      rw [hUnique]
      rfl

/-- Existential initial-data and normalized mild-equation contract. Its
hypotheses are sufficient for, but not automatically produced by, the
existing pointwise-classical preterminal solution class. -/
def H3AuditInitialOldNormalizedMildData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (U₀ : H3SpectralVelocityState) (A : ℝ),
    ∃ (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A) (b : ℝ),
      H3AuditInitialOldNormalizedMildDataAt hH3 U₀ hA hU₀ b

/-- The normalized mild-equation contract closes the formerly assumed
initial canonical old/selected overlap, by uniqueness and not by fiat. -/
theorem h3Audit_initialOldNormalizedMildData_implies_canonicalMildOverlap
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialOldNormalizedMildData hH3) :
    H3AuditInitialCanonicalMildOverlap hH3 := by
  obtain ⟨U₀, A, hA, hU₀, b, hAt⟩ := hData
  exact ⟨U₀, A, hA, hU₀, b,
    h3Audit_initialOldNormalizedMildDataAt_implies_canonicalMildOverlap
      hH3 U₀ hA hU₀ hAt⟩

/-- The genuine initial Fourier right H³ trace of each selected physical
velocity component, deduced from an old-solution mild equation and Picard
uniqueness. The initial right trace is not assumed separately. -/
theorem h3Audit_initialOldNormalizedMildData_rightComplementTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialOldNormalizedMildData hH3)
    (p : H3TerminalCurlGradientPair) :
    H3AuditInitialRightComplementH3SpectralTrace hH3 p := by
  exact h3Audit_initialCanonicalMildOverlap_rightComplementTrace
    hH3
    (h3Audit_initialOldNormalizedMildData_implies_canonicalMildOverlap
      hH3 hData) p

/-- Full-time intrinsic physical Ḣ^(3/2) membership for one transverse
velocity coordinate from initial old-solution mild data and the physical
terminal strong endpoint. The published continuation theorem is not used. -/
theorem h3Audit_onePhysicalEndpoint_oneIntrinsicThreeHalves_fullTime_of_initialOldNormalizedMildData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialOldNormalizedMildData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact
    h3Audit_onePhysicalEndpoint_oneIntrinsicThreeHalves_fullTime_of_initialCanonicalMildOverlap
      hH3 hClass i hPhysical
      (h3Audit_initialOldNormalizedMildData_implies_canonicalMildOverlap
        hH3 hData)

/-- The same normalized old-solution mild path gives both transverse
physical velocity components in full-time intrinsic Ḣ^(3/2) time L². -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialOldNormalizedMildData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialOldNormalizedMildData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact
    h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialCanonicalMildOverlap
      hH3 hClass i hPhysical
      (h3Audit_initialOldNormalizedMildData_implies_canonicalMildOverlap
        hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
