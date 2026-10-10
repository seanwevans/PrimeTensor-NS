import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialMildUniqueness
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Overlap.Path

/-!
# Physical-time H³ mild overlap implies the normalized uniqueness contract

The initial normalized-old-path audit previously asked for a path on the
artificial unit interval which already satisfied its normalized Picard
identity. The existing heat--Leray physical overlap library provides the
required normalization and its exact inverse on genuine physical times.

This file instead accepts a bounded continuous H³ spectral OLD solution
on the physical interval `[0,R(1,A)]` and the heat-minus-Duhamel equation
in physical time. The normalized-path uniqueness theorem identifies it
with the Banach-selected path. An explicit compatibility condition with
actual old Fourier velocity components then recovers the preceding
initial overlap, one-sided physical H³ trace and full-time homogeneous
H^(3/2) Sobolev criterion.

This is NOT a construction of the old physical-time mild path from a mere
H³ initial snapshot. Its spectral representation, norm bound, and mild
identity remain stated assumptions, rather than consequences of only
pointwise-classical Navier--Stokes admissibility.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

/-- The actual physical-time mild identity, using the *physical* restart
interval and the already-proved normalized-to-physical extension. Its
nonlinearity is the exact heat--Leray Duhamel operator, not an abstract
surrogate. -/
def H3AuditInitialOldPhysicalMildEquation
    {A : ℝ}
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (P : H3SpectralPhysicalVelocityPath
      (h3FinHeatLerayRestartRadius 1 A)) : Prop :=
  ∀ s : H3UnitTime,
    h3SpectralVelocityHeatApplyNN
        1 (one_pos : (0 : ℝ) < 1).le
        (h3PhysicalTimeNN
          (h3FinHeatLerayRestartRadius 1 A)
          (h3FinHeatLerayRestartRadius_pos 1 hA).le s)
        U₀ -
      h3SpectralFinHeatLerayDuhamel
        1
        (h3PhysicalTime (h3FinHeatLerayRestartRadius 1 A) s)
        (one_pos : (0 : ℝ) < 1)
        (h3PathPhysicalRealExtension
          (h3FinHeatLerayRestartRadius 1 A)
          (h3SpectralNormalizedPathOfPhysical
            (h3FinHeatLerayRestartRadius_pos 1 hA).le P))
        (h3PathPhysicalRealExtension
          (h3FinHeatLerayRestartRadius 1 A)
          (h3SpectralNormalizedPathOfPhysical
            (h3FinHeatLerayRestartRadius_pos 1 hA).le P))
      =
      P (h3PhysicalTimeMap
        (h3FinHeatLerayRestartRadius 1 A)
        (h3FinHeatLerayRestartRadius_pos 1 hA).le s)

/-- The physical-time version of the old-solution mild-data contract.
`P` is the actual OLD weighted spectral velocity on a short initial
interval, not a prescribed copy of the canonical Banach-selected path.
The mild identity and actual-component representation are independent
proof obligations. -/
def H3AuditInitialOldPhysicalMildDataAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T A : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A) (b : ℝ) : Prop :=
  ∃ P : H3SpectralPhysicalVelocityPath
      (h3FinHeatLerayRestartRadius 1 A),
    0 < b ∧ b < T ∧
    b ≤ h3FinHeatLerayRestartRadius 1 A ∧
    (∀ q : Set.Icc (0 : ℝ) (h3FinHeatLerayRestartRadius 1 A),
      ‖P q‖ ≤ 2 * A) ∧
    H3AuditInitialOldPhysicalMildEquation U₀ hA P ∧
    ∀ (p : H3TerminalCurlGradientPair)
      (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T),
      t < b →
        ∃ q : Set.Icc (0 : ℝ) (h3FinHeatLerayRestartRadius 1 A),
          (q : ℝ) = t ∧
          h3TerminalComplementSpectralStateAt hH3 p t ht =
            (P q) (h3ClassicalizationFinOfAxis
              (h3TerminalComplementComponentAxisForPair p))

/-- Convert physical-time old-solution data into the normalized Picard
contract. This actually invokes the pre-existing physical overlap uniqueness
theorem and the exact normalization inverse, rather than postulating
old/selected equality. -/
theorem h3Audit_initialOldPhysicalMildDataAt_implies_normalizedMildDataAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T A b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A)
    (hData : H3AuditInitialOldPhysicalMildDataAt hH3 U₀ hA hU₀ b) :
    H3AuditInitialOldNormalizedMildDataAt hH3 U₀ hA hU₀ b := by
  obtain ⟨P, hb, hbT, hbR, hPbound, hPmild, hMatches⟩ := hData
  let R : ℝ := h3FinHeatLerayRestartRadius 1 A
  have hR : 0 < R := h3FinHeatLerayRestartRadius_pos 1 hA
  let V : H3SpectralVelocityPath :=
    h3SpectralNormalizedPathOfPhysical hR.le P
  have hBound : ‖V‖ ≤ 2 * A := by
    exact norm_h3SpectralNormalizedPathOfPhysical_le_of_forall
      hR.le (by positivity) P hPbound
  have hUnique :
      V = h3SpectralFinHeatLerayMildSolutionAtRestartRadius
        (one_pos : (0 : ℝ) < 1) U₀ hA hU₀ := by
    exact h3SpectralFinHeatLerayPhysicalOverlapAtRestartRadius_normalized_unique
      (one_pos : (0 : ℝ) < 1) U₀ hA hU₀ P hPbound hPmild
  have hVmild :
      h3SpectralVelocityHeatFreePath
            1 R (one_pos : (0 : ℝ) < 1).le hR.le U₀ -
        h3SpectralFinHeatLerayDuhamelPathOperator
            (one_pos : (0 : ℝ) < 1) hR.le V V = V := by
    rw [hUnique]
    exact h3SpectralFinHeatLerayMildSolutionAtRestartRadius_satisfies_mild
      (one_pos : (0 : ℝ) < 1) U₀ hA hU₀
  refine ⟨V, hb, hbT, hbR, hBound, hVmild, ?_⟩
  intro p t ht htb
  obtain ⟨q, hq, hPhysical⟩ := hMatches p t ht htb
  have hRecover :
      h3PathPhysicalRealExtension R V (q : ℝ) = P q := by
    exact h3PathPhysicalRealExtension_normalizedPhysical_apply hR P q
  calc
    h3TerminalComplementSpectralStateAt hH3 p t ht =
        (P q) (h3ClassicalizationFinOfAxis
          (h3TerminalComplementComponentAxisForPair p)) := hPhysical
    _ = (h3PathPhysicalRealExtension R V (q : ℝ))
          (h3ClassicalizationFinOfAxis
            (h3TerminalComplementComponentAxisForPair p)) := by
          rw [hRecover]
    _ = (h3PathPhysicalRealExtension R V t)
          (h3ClassicalizationFinOfAxis
            (h3TerminalComplementComponentAxisForPair p)) := by
          rw [hq]

/-- Existential packaging of genuine physical-time initial mild data. -/
def H3AuditInitialOldPhysicalMildData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (U₀ : H3SpectralVelocityState) (A : ℝ),
    ∃ (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A) (b : ℝ),
      H3AuditInitialOldPhysicalMildDataAt hH3 U₀ hA hU₀ b

/-- The physical-time mild contract produces the earlier normalized data
by a theorem, without an additional assumed normalization or overlap. -/
theorem h3Audit_initialOldPhysicalMildData_implies_normalizedMildData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialOldPhysicalMildData hH3) :
    H3AuditInitialOldNormalizedMildData hH3 := by
  obtain ⟨U₀, A, hA, hU₀, b, hAt⟩ := hData
  exact ⟨U₀, A, hA, hU₀, b,
    h3Audit_initialOldPhysicalMildDataAt_implies_normalizedMildDataAt
      hH3 U₀ hA hU₀ hAt⟩

/-- From actual physical-time old mild data to selected/old equality. -/
theorem h3Audit_initialOldPhysicalMildData_implies_canonicalMildOverlap
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialOldPhysicalMildData hH3) :
    H3AuditInitialCanonicalMildOverlap hH3 := by
  exact h3Audit_initialOldNormalizedMildData_implies_canonicalMildOverlap
    hH3 (h3Audit_initialOldPhysicalMildData_implies_normalizedMildData hH3 hData)

/-- The actual old velocity has the physical one-sided weighted H³ Fourier
trace from physical-time initial mild data. -/
theorem h3Audit_initialOldPhysicalMildData_rightComplementTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialOldPhysicalMildData hH3)
    (p : H3TerminalCurlGradientPair) :
    H3AuditInitialRightComplementH3SpectralTrace hH3 p := by
  exact h3Audit_initialOldNormalizedMildData_rightComplementTrace
    hH3 (h3Audit_initialOldPhysicalMildData_implies_normalizedMildData hH3 hData) p

/-- One-component physical time-L² homogeneous three-halves criterion. -/
theorem h3Audit_onePhysicalEndpoint_oneIntrinsicThreeHalves_fullTime_of_initialOldPhysicalMildData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialOldPhysicalMildData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_oneIntrinsicThreeHalves_fullTime_of_initialOldNormalizedMildData
    hH3 hClass i hPhysical
    (h3Audit_initialOldPhysicalMildData_implies_normalizedMildData hH3 hData)

/-- Both transverse physical velocity components, over the full lifespan. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialOldPhysicalMildData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialOldPhysicalMildData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialOldNormalizedMildData
    hH3 hClass i hPhysical
    (h3Audit_initialOldPhysicalMildData_implies_normalizedMildData hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
