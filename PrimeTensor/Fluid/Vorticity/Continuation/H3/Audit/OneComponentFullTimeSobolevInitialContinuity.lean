import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentFullTimeSobolevInitialBound
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Vorticity.Energy.Envelope

/-!
# Full-time physical H^(3/2) criterion from genuine initial H³ energy continuity

The full-time criterion at the preceding checkpoint required two separately
postulated early-time bounds on actual H³ spectral velocity components.
This file derives one simultaneous bound for ALL components from the single
physical-data property `ContinuousAt (velocityH3EnergyAt u) 0`.

The exact weighted Fourier H³ energy identity already provides
  ‖U(t)‖ <= sqrt (E_H3(t))
at every strict preterminal time, with no Fourier proxy. Continuity of the
physical energy at zero yields one bounded early interval, where all three
weighted Fourier components are bounded by the same finite constant.

We then combine this early interval with the previously established
positive-tail time integrability to obtain full `(0,T)` time-L² for both
selected intrinsic physical H^(3/2) seminorms. No uniform preterminal H³
bound, endpoint continuation theorem, or global Navier--Stokes regularity
is assumed or proved. The continuity at t=0 is an explicit NEW premise,
not part of `LoggedPreterminalH3PathAdmissible`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3AuditInitialContinuity
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Initial-time continuity of the actual physical H³ energy, rather than
of a separately selected spectral component. The existing path class
assumes energy continuity only at *strict* times `0 < t < T`. -/
def H3AuditInitialPhysicalH3EnergyContinuous
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) : Prop :=
  ContinuousAt (velocityH3EnergyAt u) (0 : ℝ)

/-- Physical initial energy continuity supplies a *common* early interval
and spectral H³ norm bound for every complementary velocity component. -/
theorem h3Audit_initialEnergyContinuous_exists_commonEarlySpectralBounds
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ha : 0 < a)
    (haT : a < T)
    (hInitial : H3AuditInitialPhysicalH3EnergyContinuous u) :
    ∃ b M : ℝ, 0 < b ∧ b < a ∧ 0 ≤ M ∧
      ∀ p : H3TerminalCurlGradientPair,
        H3AuditInitialComplementSpectralBound hH3 p b M := by
  obtain ⟨δ, hδ, hNear⟩ :=
    (Metric.continuousAt_iff.mp hInitial) (1 : ℝ) (by norm_num)
  let b : ℝ := min (a / 2) (δ / 2)
  let M : ℝ := Real.sqrt (velocityH3EnergyAt u 0 + 1)
  have hb : 0 < b := by
    dsimp [b]
    exact lt_min (by linarith) (by linarith)
  have hba : b < a := by
    dsimp [b]
    have h := min_le_left (a / 2) (δ / 2)
    linarith
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  refine ⟨b, M, hb, hba, hM, ?_⟩
  intro p t ht htb
  have hδsmall : t < δ := by
    have hBound : b ≤ δ / 2 := min_le_right _ _
    linarith
  have hDist : dist t (0 : ℝ) < δ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos ht.1] using hδsmall
  have hENear :
      |velocityH3EnergyAt u t - velocityH3EnergyAt u 0| < 1 := by
    simpa only [Real.dist_eq] using hNear hDist
  have hEBound :
      velocityH3EnergyAt u t ≤ velocityH3EnergyAt u 0 + 1 := by
    have hRight := (abs_lt.mp hENear).2
    linarith
  have hSqrtBound :
      Real.sqrt (velocityH3EnergyAt u t) ≤ M := by
    exact Real.sqrt_le_sqrt hEBound
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t ht
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes ht
  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes ht hInt
  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt u t hInt hMeas hFourier
  have hCoord :
      ‖U (h3ClassicalizationFinOfAxis
        (h3TerminalComplementComponentAxisForPair p))‖ ≤ ‖U‖ :=
    h3SpectralFinVector_coordinate_norm_le U _
  have hState : ‖U‖ ≤ Real.sqrt (velocityH3EnergyAt u t) :=
    norm_velocityH3SpectralStateAt_le_sqrt_energy hFourier
  change ‖U (h3ClassicalizationFinOfAxis
    (h3TerminalComplementComponentAxisForPair p))‖ ≤ M
  exact (hCoord.trans hState).trans hSqrtBound

/-- Given early-time energy continuity and terminal integrability of a
single physical Fourier density, its intrinsic 3/2 seminorm is L² on the
whole physical interval `(0,T)`. No strong endpoint is needed here beyond
the separately supplied late-time integral. -/
theorem h3Audit_intrinsicThreeHalves_fullTime_of_initialEnergyContinuous_and_terminal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a c : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (ha : 0 < a)
    (hac : a < c)
    (hcT : c < T)
    (hInitial : H3AuditInitialPhysicalH3EnergyContinuous u)
    (hTerminal : IntegrableOn
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      (Set.Ioo c T)) :
    MemLp (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3 p)
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  obtain ⟨b, M, hb, hba, _hM, hEarlyAll⟩ :=
    h3Audit_initialEnergyContinuous_exists_commonEarlySpectralBounds
      hH3 ha (lt_trans hac hcT) hInitial
  have hbT : b < T := lt_trans hba (lt_trans hac hcT)
  have hEarly : IntegrableOn
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      (Set.Ioo (0 : ℝ) b) :=
    h3Audit_homogeneousThreeHalvesTimeDensity_integrableOn_initial_of_bound
      hH3 p hb hbT (hEarlyAll p)
  have hLate : IntegrableOn
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      (Set.Ioo b T) :=
    h3Audit_homogeneousThreeHalvesTimeDensity_integrableOn_positiveTail
      hH3 p hb (lt_trans hba hac) hcT hTerminal
  have hFull : IntegrableOn
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      (Set.Ioo (0 : ℝ) T) :=
    h3Audit_homogeneousThreeHalvesTimeDensity_integrableOn_fullTime_of_split
      hH3 p hb hbT hEarly hLate
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

/-- A strong endpoint for a selected velocity coordinate and genuine
physical H³ energy continuity at the initial time supply the full-time
intrinsic one-component Sobolev criterion. -/
theorem h3Audit_complementEndpoint_intrinsicThreeHalves_fullTime_of_initialEnergyContinuous
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (p : H3TerminalCurlGradientPair)
    (hEndpoint : H3TerminalComplementGradientStrongH3EndpointPath hH3 p)
    (hInitial : H3AuditInitialPhysicalH3EnergyContinuous u) :
    MemLp (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3 p)
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  obtain ⟨c, hc, hLate⟩ :=
    h3Audit_complementEndpoint_homogeneousThreeHalves_integrable
      hH3 hClass p hEndpoint
  exact
    h3Audit_intrinsicThreeHalves_fullTime_of_initialEnergyContinuous_and_terminal
      hH3 p hClass.terminal_start.1 hc.1 hc.2 hInitial hLate

/-- One strong physical curl-component endpoint plus initial physical H³
energy continuity supplies the single-component full-time criterion, with
no separately assumed early spectral component bounds. -/
theorem h3Audit_onePhysicalEndpoint_oneIntrinsicThreeHalves_fullTime_of_initialEnergyContinuous
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hInitial : H3AuditInitialPhysicalH3EnergyContinuous u) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) :=
  h3Audit_complementEndpoint_intrinsicThreeHalves_fullTime_of_initialEnergyContinuous
    hH3 hClass _ hPhysical.1 hInitial

/-- The same initial physical H³ energy-continuity premise controls both
transverse components over the complete lifespan `(0,T)` on one common
interval; the only terminal assumption is the already explicit hPhysical. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialEnergyContinuous
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hInitial : H3AuditInitialPhysicalH3EnergyContinuous u) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact ⟨
    h3Audit_complementEndpoint_intrinsicThreeHalves_fullTime_of_initialEnergyContinuous
      hH3 hClass _ hPhysical.1 hInitial,
    h3Audit_complementEndpoint_intrinsicThreeHalves_fullTime_of_initialEnergyContinuous
      hH3 hClass _ hPhysical.2 hInitial⟩

end
end Euclidean
end Bridge
end PrimeTensor
