import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentIntrinsicSobolevTimeL2

/-!
# The intrinsic physical homogeneous H^(3/2) criterion on a full positive tail

The one-component endpoint argument previously yielded L² in time only on
an *existential late interval* `(c,T)`. This file removes that artificial
restriction. Every earlier positive-time compact interval `[a,c]` is covered
by already-proved strict-time continuity of the genuine physical Fourier
energy, and hence is integrable. Gluing its interval integrability to the
terminal estimate gives the criterion on the entire `(a,T)` energy-class
interval, with a COMMON start for both transverse physical velocity fields.

No assumption about regularity at the initial endpoint t=0 is made. This is
not an import of the external one-component continuation theorem and does
not establish an unconditional Navier--Stokes continuation conclusion.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

/-- An integrable terminal homogeneous Fourier *square* density extends to
any fixed earlier positive start. The missing finite middle section is
integrable by genuine strict-time continuity, not a global H³ ceiling. -/
theorem h3Audit_homogeneousThreeHalvesTimeDensity_integrableOn_positiveTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a c : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (ha : 0 < a)
    (hac : a < c)
    (hcT : c < T)
    (hTerminal : IntegrableOn
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      (Set.Ioo c T)) :
    IntegrableOn
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      (Set.Ioo a T) := by
  have hHeadContinuous : ContinuousOn
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      (Set.Icc a c) := by
    apply (h3Audit_homogeneousThreeHalvesTimeDensity_continuousOn
      hH3 p).mono
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hcT⟩
  have hHead : IntervalIntegrable
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      volume a c :=
    hHeadContinuous.intervalIntegrable_of_Icc hac.le
  have hFinal : IntervalIntegrable
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      volume c T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hcT.le).2 hTerminal
  have hFull : IntervalIntegrable
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      volume a T :=
    hHead.trans hFinal
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (lt_trans hac hcT).le).1 hFull

/-- Consequently the selected actual-velocity physical Sobolev norm belongs
to L² time on the ENTIRE positive-tail interval `(a,T)` whenever that one
selected velocity component has a strong weighted H³ terminal endpoint. -/
theorem h3Audit_complementEndpoint_intrinsicThreeHalves_fullPositiveTail_timeL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (p : H3TerminalCurlGradientPair)
    (hEndpoint : H3TerminalComplementGradientStrongH3EndpointPath hH3 p) :
    MemLp (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3 p)
      2 (volume.restrict (Set.Ioo a T)) := by
  obtain ⟨c, hc, hTail⟩ :=
    h3Audit_complementEndpoint_homogeneousThreeHalves_integrable
      hH3 hClass p hEndpoint
  have hFull :=
    h3Audit_homogeneousThreeHalvesTimeDensity_integrableOn_positiveTail
      hH3 p hClass.terminal_start.1 hc.1 hc.2 hTail
  have hL2 :=
    h3Audit_homogeneousThreeHalvesTimeSeminorm_memLp_two_of_integrableOn
      hH3 p hFull
  have hEq :
      h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3 p =
        h3AuditHomogeneousThreeHalvesVelocityTimeSeminorm hH3 p := by
    funext t
    exact
      (h3Audit_actualVelocity_intrinsicThreeHalvesTimeSeminorm_eq_fourier
        hH3 p t).trans
      (h3Audit_actualVelocityFourierSeminorm_eq_timeSeminorm hH3 p t)
  rw [hEq]
  exact hL2

/-- A single physical vorticity endpoint provides a common `(a,T)` interval
for BOTH transverse physical-velocity intrinsic homogeneous Sobolev norms.
No extra choice of a terminal threshold c survives in the conclusion. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullPositiveTail_timeL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo a T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo a T)) := by
  obtain ⟨c, hc, hPos, hNeg⟩ :=
    h3Audit_onePhysicalEndpoint_twoHomogeneousThreeHalves_integrable
      hH3 hClass i hPhysical
  have hPosFull :=
    h3Audit_homogeneousThreeHalvesTimeDensity_integrableOn_positiveTail
      hH3 (h3TerminalActualVorticityPositiveComplementPair i)
      hClass.terminal_start.1 hc.1 hc.2 hPos
  have hNegFull :=
    h3Audit_homogeneousThreeHalvesTimeDensity_integrableOn_positiveTail
      hH3 (h3TerminalActualVorticityNegativeComplementPair i)
      hClass.terminal_start.1 hc.1 hc.2 hNeg
  constructor
  · have hEq :
        h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
            (h3TerminalActualVorticityPositiveComplementPair i) =
          h3AuditHomogeneousThreeHalvesVelocityTimeSeminorm hH3
            (h3TerminalActualVorticityPositiveComplementPair i) := by
      funext t
      exact
        (h3Audit_actualVelocity_intrinsicThreeHalvesTimeSeminorm_eq_fourier
          hH3 _ t).trans
        (h3Audit_actualVelocityFourierSeminorm_eq_timeSeminorm hH3 _ t)
    rw [hEq]
    exact
      h3Audit_homogeneousThreeHalvesTimeSeminorm_memLp_two_of_integrableOn
        hH3 _ hPosFull
  · have hEq :
        h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
            (h3TerminalActualVorticityNegativeComplementPair i) =
          h3AuditHomogeneousThreeHalvesVelocityTimeSeminorm hH3
            (h3TerminalActualVorticityNegativeComplementPair i) := by
      funext t
      exact
        (h3Audit_actualVelocity_intrinsicThreeHalvesTimeSeminorm_eq_fourier
          hH3 _ t).trans
        (h3Audit_actualVelocityFourierSeminorm_eq_timeSeminorm hH3 _ t)
    rw [hEq]
    exact
      h3Audit_homogeneousThreeHalvesTimeSeminorm_memLp_two_of_integrableOn
        hH3 _ hNegFull

/-- One of the two components already supplies the analytic single-component
criterion on all of `(a,T)`. The published PDE extension theorem has NOT been
applied and its local-strong-solution compatibility remains an obligation. -/
theorem h3Audit_onePhysicalEndpoint_oneIntrinsicThreeHalves_fullPositiveTail_timeL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo a T)) :=
  (h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullPositiveTail_timeL2
    hH3 hClass i hPhysical).1

end
end Euclidean
end Bridge
end PrimeTensor
