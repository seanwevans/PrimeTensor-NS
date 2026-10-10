import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentFullTimeSobolevInitialContinuity

/-!
# Full-time physical H^(3/2) from a strong initial spectral velocity path

The preceding audit obtained full `(0,T)` homogeneous H^(3/2) time-L²
under `ContinuousAt (velocityH3EnergyAt u) 0`. However the current
preterminal H³ path class only assumes H³ energy continuity on `(0,T)`;
it does NOT provide any initial-time continuity.

This module introduces a standard sufficient initial regularity interface:
a continuous *full three-component weighted Fourier H³ velocity path* near
zero which agrees with the genuinely encoded physical velocity components
at every strictly preterminal time. This initial spectral path is a
NEW EXPLICIT hypothesis, not obtained from a lone finite H³ initial datum.

Continuity of this H³-valued path bounds its norm near zero. A finite
coordinate projection then bounds all three actual component states,
providing the previous initial bound simultaneously. Joining the resulting
early homogeneous-square integrability with the previously proved terminal
integrability yields the full time-L² criterion on `(0,T)`.

The physical initial-data to strong spectral solution bridge, and the
published one-component continuation theorem, are still separate steps.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

/-- A genuine H³-valued *initial* spectral path for the actual real velocity.
The pointwise compatibility clause prevents substituting an unrelated
bounded spectral path. `ContinuousAt U 0` is deliberately an explicit
initial strong-solution regularity premise, not a consequence of the
open-time path `hH3`. -/
def H3AuditInitialStrongH3SpectralVelocityPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ U : ℝ → H3SpectralVelocityState,
    ContinuousAt U (0 : ℝ) ∧
    ∀ (p : H3TerminalCurlGradientPair)
      (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T),
      h3TerminalComplementSpectralStateAt hH3 p t ht =
        (U t)
          (h3ClassicalizationFinOfAxis
            (h3TerminalComplementComponentAxisForPair p))

/-- An H³-valued spectral velocity path continuous at its initial time
provides a *common* initial component norm bound on a positive interval.
The selected component is always that of the actual physical velocity. -/
theorem h3Audit_initialStrongSpectralPath_exists_commonEarlySpectralBounds
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ha : 0 < a)
    (haT : a < T)
    (hInitial : H3AuditInitialStrongH3SpectralVelocityPath hH3) :
    ∃ b M : ℝ, 0 < b ∧ b < a ∧ 0 ≤ M ∧
      ∀ p : H3TerminalCurlGradientPair,
        H3AuditInitialComplementSpectralBound hH3 p b M := by
  obtain ⟨U, hContinuous, hMatches⟩ := hInitial
  obtain ⟨δ, hδ, hNear⟩ :=
    (Metric.continuousAt_iff.mp hContinuous) (1 : ℝ) (by norm_num)
  let b : ℝ := min (a / 2) (δ / 2)
  let M : ℝ := ‖U 0‖ + 1
  have hb : 0 < b := by
    dsimp [b]
    exact lt_min (by linarith) (by linarith)
  have hba : b < a := by
    dsimp [b]
    have h := min_le_left (a / 2) (δ / 2)
    linarith
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  refine ⟨b, M, hb, hba, hM, ?_⟩
  intro p t ht htb
  have hδsmall : t < δ := by
    have hBound : b ≤ δ / 2 := min_le_right _ _
    linarith
  have hDist : dist t (0 : ℝ) < δ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos ht.1] using hδsmall
  have hNearNorm : ‖U t - U 0‖ < 1 := by
    simpa only [dist_eq_norm] using hNear hDist
  have hUBound : ‖U t‖ ≤ M := by
    dsimp only [M]
    calc
      ‖U t‖ = ‖(U t - U 0) + U 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖U t - U 0‖ + ‖U 0‖ := norm_add_le _ _
      _ ≤ ‖U 0‖ + 1 := by linarith
  calc
    ‖h3TerminalComplementSpectralStateAt hH3 p t ht‖ =
        ‖(U t) (h3ClassicalizationFinOfAxis
          (h3TerminalComplementComponentAxisForPair p))‖ := by
            rw [hMatches p t ht]
    _ ≤ ‖U t‖ := h3SpectralFinVector_coordinate_norm_le (U t) _
    _ ≤ M := hUBound

/-- Strong initial spectral H³ continuity plus late homogeneous Fourier
square integrability gives the *actual physical* selected-component norm
in `L²(0,T; Ḣ^(3/2))`, with the full-time interval explicit. -/
theorem h3Audit_intrinsicThreeHalves_fullTime_of_initialStrongSpectralPath_and_terminal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a c : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (ha : 0 < a) (hac : a < c) (hcT : c < T)
    (hInitial : H3AuditInitialStrongH3SpectralVelocityPath hH3)
    (hTerminal : IntegrableOn
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      (Set.Ioo c T)) :
    MemLp (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3 p)
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  obtain ⟨b, M, hb, hba, _hM, hEarlyAll⟩ :=
    h3Audit_initialStrongSpectralPath_exists_commonEarlySpectralBounds
      hH3 ha (lt_trans hac hcT) hInitial
  have hbT : b < T := lt_trans hba (lt_trans hac hcT)
  have hEarly : IntegrableOn
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      (Set.Ioo (0 : ℝ) b) :=
    h3Audit_homogeneousThreeHalvesTimeDensity_integrableOn_initial_of_bound
      hH3 p hb hbT (hEarlyAll p)
  have hLater : IntegrableOn
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      (Set.Ioo b T) :=
    h3Audit_homogeneousThreeHalvesTimeDensity_integrableOn_positiveTail
      hH3 p hb (lt_trans hba hac) hcT hTerminal
  have hFull : IntegrableOn
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      (Set.Ioo (0 : ℝ) T) :=
    h3Audit_homogeneousThreeHalvesTimeDensity_integrableOn_fullTime_of_split
      hH3 p hb hbT hEarly hLater
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

/-- A strong spectral H³ initial path and one physical curl-component
terminal endpoint give the full-time physical one-component Sobolev
criterion, with no separate early energy-continuity hypothesis. -/
theorem h3Audit_onePhysicalEndpoint_oneIntrinsicThreeHalves_fullTime_of_initialStrongSpectralPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hInitial : H3AuditInitialStrongH3SpectralVelocityPath hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  obtain ⟨c, hc, hLate⟩ :=
    h3Audit_complementEndpoint_homogeneousThreeHalves_integrable
      hH3 hClass (h3TerminalActualVorticityPositiveComplementPair i)
      hPhysical.1
  exact
    h3Audit_intrinsicThreeHalves_fullTime_of_initialStrongSpectralPath_and_terminal
      hH3 _ hClass.terminal_start.1 hc.1 hc.2 hInitial hLate

/-- Both transverse actual physical velocity components have full-time
intrinsic homogeneous H^(3/2) seminorms in L² under the same single
initial strong spectral path and physical endpoint predicates. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialStrongSpectralPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hInitial : H3AuditInitialStrongH3SpectralVelocityPath hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  constructor
  · exact
      h3Audit_onePhysicalEndpoint_oneIntrinsicThreeHalves_fullTime_of_initialStrongSpectralPath
        hH3 hClass i hPhysical hInitial
  · obtain ⟨c, hc, hLate⟩ :=
      h3Audit_complementEndpoint_homogeneousThreeHalves_integrable
        hH3 hClass (h3TerminalActualVorticityNegativeComplementPair i)
        hPhysical.2
    exact
      h3Audit_intrinsicThreeHalves_fullTime_of_initialStrongSpectralPath_and_terminal
        hH3 _ hClass.terminal_start.1 hc.1 hc.2 hInitial hLate

end
end Euclidean
end Bridge
end PrimeTensor
