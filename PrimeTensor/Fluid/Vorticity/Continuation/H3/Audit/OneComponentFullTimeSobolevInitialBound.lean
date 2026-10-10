import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentWholePositiveTailSobolev

/-!
# Complete `(0,T)` physical homogeneous H^(3/2) time-L² from an initial H³ bound

The previous audit established the actual physical homogeneous H^(3/2)
seminorm in time L² on every energy-class interval `(a,T)`, where `a > 0`.
A logged preterminal H³ path is only controlled strictly inside `(0,T)`;
its continuity does not give uniform control as time approaches zero.

This file isolates and discharges the remaining early-time *integrability*
obligation under a clearly stated quantitative hypothesis: one velocity
component's actual weighted spectral H³ norm is bounded on `(0,a)`.
Fourier-weight domination bounds the homogeneous H^(3/2) square density by
that H³ norm squared. Since `(0,a)` has finite measure and the density is
already Borel measurable, the square density is integrable on `(0,a)`.
Joining it to the existing `(a,T)` result produces the intrinsic physical
homogeneous H^(3/2) time-L² criterion on `(0,T)`.

The initial spectral bound is a NEW EXPLICIT hypothesis, not a theorem of the
existing logged H³ path class. This module neither proves the missing local
strong-solution compatibility with the Liu--Zhang criterion nor imports its
continuation conclusion; no unconditional Navier--Stokes result is claimed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

/-- Uniform H³ control of one actual physical velocity component on the
missing early interval `(0,a)`. This is deliberately NOT an assumption on the
whole solution; each component may have a different bound. -/
def H3AuditInitialComplementSpectralBound
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (a M : ℝ) : Prop :=
  ∀ (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T),
    t < a → ‖h3TerminalComplementSpectralStateAt hH3 p t ht‖ ≤ M

/-- An early uniform spectral H³ bound suffices to integrate the actual
homogeneous Fourier H^(3/2) square density on `(0,a)`. No initial-time limit
or early-time density continuity is used. -/
theorem h3Audit_homogeneousThreeHalvesTimeDensity_integrableOn_initial_of_bound
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (ha : 0 < a)
    (haT : a < T)
    (hEarly : H3AuditInitialComplementSpectralBound hH3 p a M) :
    IntegrableOn
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      (Set.Ioo (0 : ℝ) a) := by
  have hConst : IntegrableOn (fun _ : ℝ => M ^ 2)
      (Set.Ioo (0 : ℝ) a) :=
    integrableOn_const measure_Ioo_lt_top.ne
  apply Integrable.mono' hConst
  · exact (h3Audit_homogeneousThreeHalvesTimeDensity_measurable
      hH3 p).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have htStrict : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨ht.1, lt_trans ht.2 haT⟩
    obtain ⟨hNonneg, hDom⟩ :=
      h3Audit_homogeneousThreeHalvesTimeDensity_domination
        hH3 p t htStrict
    have hH3Bound :
        ‖h3TerminalComplementSpectralStateAt hH3 p t htStrict‖ ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hEarly t htStrict ht.2) 2
    have hUpper :
        h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p t ≤ M ^ 2 :=
      hDom.trans hH3Bound
    simpa only [Real.norm_eq_abs, abs_of_nonneg hNonneg,
      abs_of_nonneg (sq_nonneg M)] using hUpper

/-- Join an independently proved early-time integral on `(0,a)` with the
full positive-tail integral on `(a,T)`. The joining point lies strictly
inside the lifespan, so no endpoint value at `a` is required. -/
theorem h3Audit_homogeneousThreeHalvesTimeDensity_integrableOn_fullTime_of_split
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (ha : 0 < a) (haT : a < T)
    (hInitial : IntegrableOn
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      (Set.Ioo (0 : ℝ) a))
    (hPositiveTail : IntegrableOn
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      (Set.Ioo a T)) :
    IntegrableOn
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      (Set.Ioo (0 : ℝ) T) := by
  have hLeft : IntervalIntegrable
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      volume (0 : ℝ) a :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le).2 hInitial
  have hRight : IntervalIntegrable
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      volume a T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le haT.le).2 hPositiveTail
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (lt_trans ha haT).le).1 (hLeft.trans hRight)

/-- One component's strong terminal endpoint together with its explicitly
bounded actual H³ Fourier state on `(0,a)` establishes the intrinsic physical
homogeneous H^(3/2) criterion over the full lifespan `(0,T)`. -/
theorem h3Audit_complementEndpoint_intrinsicThreeHalves_fullTime_of_initialBound
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (p : H3TerminalCurlGradientPair)
    (hEndpoint : H3TerminalComplementGradientStrongH3EndpointPath hH3 p)
    (hEarly : H3AuditInitialComplementSpectralBound hH3 p a M) :
    MemLp (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3 p)
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  obtain ⟨c, hc, hTerminal⟩ :=
    h3Audit_complementEndpoint_homogeneousThreeHalves_integrable
      hH3 hClass p hEndpoint
  have hPositiveTail :=
    h3Audit_homogeneousThreeHalvesTimeDensity_integrableOn_positiveTail
      hH3 p hClass.terminal_start.1 hc.1 hc.2 hTerminal
  have hInitial :=
    h3Audit_homogeneousThreeHalvesTimeDensity_integrableOn_initial_of_bound
      hH3 p hClass.terminal_start.1 hClass.terminal_start.2 hEarly
  have hFull :=
    h3Audit_homogeneousThreeHalvesTimeDensity_integrableOn_fullTime_of_split
      hH3 p hClass.terminal_start.1 hClass.terminal_start.2
      hInitial hPositiveTail
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

/-- A single physical curl-component strong H³ endpoint, plus explicit
separate early H³ bounds for both transverse *physical velocity* components,
gives both intrinsic homogeneous H^(3/2) seminorms in L² on `(0,T)`.
The spectral early-time bounds remain visible hypotheses. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialBounds
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a Mpos Mneg : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hEarlyPos : H3AuditInitialComplementSpectralBound hH3
      (h3TerminalActualVorticityPositiveComplementPair i) a Mpos)
    (hEarlyNeg : H3AuditInitialComplementSpectralBound hH3
      (h3TerminalActualVorticityNegativeComplementPair i) a Mneg) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact ⟨
    h3Audit_complementEndpoint_intrinsicThreeHalves_fullTime_of_initialBound
      hH3 hClass _ hPhysical.1 hEarlyPos,
    h3Audit_complementEndpoint_intrinsicThreeHalves_fullTime_of_initialBound
      hH3 hClass _ hPhysical.2 hEarlyNeg⟩

/-- The first transverse physical velocity component alone suffices for the
analytic `L²(0,T; Ḣ^(3/2))` criterion under the corresponding early bound.
No PDE continuation theorem is invoked. -/
theorem h3Audit_onePhysicalEndpoint_oneIntrinsicThreeHalves_fullTime_of_initialBound
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hEarly : H3AuditInitialComplementSpectralBound hH3
      (h3TerminalActualVorticityPositiveComplementPair i) a M) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact
    h3Audit_complementEndpoint_intrinsicThreeHalves_fullTime_of_initialBound
      hH3 hClass _ hPhysical.1 hEarly

end
end Euclidean
end Bridge
end PrimeTensor
