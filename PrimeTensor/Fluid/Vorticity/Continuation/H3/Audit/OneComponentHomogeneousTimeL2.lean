import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentGlobalTimeMeasurability

/-!
# Homogeneous three-halves Fourier time L² criterion

The global measurability result from `c0f87410` and its terminal-time
integrability result are combined here into an explicit `MemLp ... 2`
statement for the square root of the actual homogeneous Fourier square
energy. This uses exactly the already-proved spectral integral, not a new
abstract proxy or a purported theorem of physical Navier--Stokes.

Still outstanding: identification of this Fourier expression with the
published paper's physical homogeneous Sobolev seminorm, compatibility of
its strong-solution class, and formal import/proof of its continuation theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- The square-energy density is nonnegative at every physical time,
including times outside the preterminal interval, where it is zero. -/
theorem h3Audit_homogeneousThreeHalvesTimeDensity_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair) (t : ℝ) :
    0 ≤ h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p t := by
  by_cases ht : t ∈ Set.Ioo (0 : ℝ) T
  · exact (h3Audit_homogeneousThreeHalvesTimeDensity_domination
      hH3 p t ht).1
  · simp [h3AuditHomogeneousThreeHalvesVelocityTimeDensity, ht]

/-- Nonnegative scalar square root of the actual physical-component
homogeneous three-halves Fourier square density. This is the precise
Fourier-side quantity which must later be compared to the paper's norm. -/
noncomputable def h3AuditHomogeneousThreeHalvesVelocityTimeSeminorm
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair) (t : ℝ) : ℝ :=
  Real.sqrt (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p t)

/-- The new seminorm squares to exactly the previously proved Fourier
square energy, including at times outside the preterminal interval. -/
theorem h3Audit_homogeneousThreeHalvesTimeSeminorm_sq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair) (t : ℝ) :
    h3AuditHomogeneousThreeHalvesVelocityTimeSeminorm hH3 p t ^ 2 =
      h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p t := by
  unfold h3AuditHomogeneousThreeHalvesVelocityTimeSeminorm
  exact Real.sq_sqrt
    (h3Audit_homogeneousThreeHalvesTimeDensity_nonneg hH3 p t)

/-- The seminorm is globally Borel measurable, with no independent
measurability assumption for the original weighted Fourier state. -/
theorem h3Audit_homogeneousThreeHalvesTimeSeminorm_measurable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair) :
    Measurable (h3AuditHomogeneousThreeHalvesVelocityTimeSeminorm hH3 p) := by
  exact Real.continuous_sqrt.measurable.comp
    (h3Audit_homogeneousThreeHalvesTimeDensity_measurable hH3 p)

/-- A time-integrable homogeneous Fourier square energy gives the
corresponding real time-profile membership in L² on the same interval. -/
theorem h3Audit_homogeneousThreeHalvesTimeSeminorm_memLp_two_of_integrableOn
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T c : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (hInt : IntegrableOn
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      (Set.Ioo c T)) :
    MemLp
      (h3AuditHomogeneousThreeHalvesVelocityTimeSeminorm hH3 p)
      2 (volume.restrict (Set.Ioo c T)) := by
  have hMeas : AEStronglyMeasurable
      (h3AuditHomogeneousThreeHalvesVelocityTimeSeminorm hH3 p)
      (volume.restrict (Set.Ioo c T)) :=
    (h3Audit_homogeneousThreeHalvesTimeSeminorm_measurable
      hH3 p).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hMeas]
  have hEq :
      (fun t : ℝ =>
        ‖h3AuditHomogeneousThreeHalvesVelocityTimeSeminorm hH3 p t‖ ^ 2) =
      h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p := by
    funext t
    rw [Real.norm_eq_abs]
    have hn : 0 ≤ h3AuditHomogeneousThreeHalvesVelocityTimeSeminorm hH3 p t :=
      Real.sqrt_nonneg _
    rw [abs_of_nonneg hn]
    exact h3Audit_homogeneousThreeHalvesTimeSeminorm_sq hH3 p t
  rw [hEq]
  exact hInt

/-- One selected physical velocity component has an L² temporal homogeneous
Fourier seminorm on a late time interval, from its strong H³ endpoint. -/
theorem h3Audit_complementEndpoint_homogeneousThreeHalves_timeL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (p : H3TerminalCurlGradientPair)
    (hEndpoint : H3TerminalComplementGradientStrongH3EndpointPath hH3 p) :
    ∃ c : ℝ, c ∈ Set.Ioo a T ∧
      MemLp
        (h3AuditHomogeneousThreeHalvesVelocityTimeSeminorm hH3 p)
        2 (volume.restrict (Set.Ioo c T)) := by
  obtain ⟨c, hc, hInt⟩ :=
    h3Audit_complementEndpoint_homogeneousThreeHalves_integrable
      hH3 hClass p hEndpoint
  exact ⟨c, hc,
    h3Audit_homogeneousThreeHalvesTimeSeminorm_memLp_two_of_integrableOn
      hH3 p hInt⟩

/-- A single physical curl-component endpoint gives both transverse
physical-velocity Fourier Ḣ^(3/2) seminorms in time L² on one common
terminal interval. This is not a physical Sobolev norm identification. -/
theorem h3Audit_onePhysicalEndpoint_twoHomogeneousThreeHalves_timeL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i) :
    ∃ c : ℝ, c ∈ Set.Ioo a T ∧
      MemLp
        (h3AuditHomogeneousThreeHalvesVelocityTimeSeminorm hH3
          (h3TerminalActualVorticityPositiveComplementPair i))
        2 (volume.restrict (Set.Ioo c T)) ∧
      MemLp
        (h3AuditHomogeneousThreeHalvesVelocityTimeSeminorm hH3
          (h3TerminalActualVorticityNegativeComplementPair i))
        2 (volume.restrict (Set.Ioo c T)) := by
  obtain ⟨c, hc, hPos, hNeg⟩ :=
    h3Audit_onePhysicalEndpoint_twoHomogeneousThreeHalves_integrable
      hH3 hClass i hPhysical
  exact ⟨c, hc,
    h3Audit_homogeneousThreeHalvesTimeSeminorm_memLp_two_of_integrableOn
      hH3 _ hPos,
    h3Audit_homogeneousThreeHalvesTimeSeminorm_memLp_two_of_integrableOn
      hH3 _ hNeg⟩

end
end Euclidean
end Bridge
end PrimeTensor
