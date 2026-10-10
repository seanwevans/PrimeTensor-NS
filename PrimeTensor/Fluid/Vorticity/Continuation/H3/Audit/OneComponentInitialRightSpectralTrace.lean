import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentFullTimeSobolevInitialSpectralPath

/-!
# One-sided initial physical H³ trace suffices for full-time Ḣ^(3/2)

The previous module asks for a full three-coordinate H³ Fourier velocity
path continuous at time zero, agreeing with all physical velocity snapshots.
For the one-component continuation audit it is enough to know that the
*selected actual scalar velocity component* has a finite right H³ spectral
trace at time zero.

This module makes that weaker initial-data condition precise using a genuine
one-sided `Tendsto` at `𝓝[>] 0`. The underlying snapshot is the weighted H³
Fourier encoding of the actual velocity, not an unrelated spectral curve.
Its right limit bounds the component on a small interval `(0,b)`, and the
existing terminal integrability and compact interior regularity complete
`L²(0,T; Ḣ^(3/2))` for that physical velocity coordinate.

The existence of the right trace is an explicit, unproved initial-time
hypothesis. No local-strong-solution class equivalence, imported Liu--Zhang
continuation theorem, or unconditional Navier--Stokes continuation is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

/-- Extend the *actual* weighted Fourier H³ velocity-component snapshot by
zero away from the strict physical lifespan. Its restriction to `(0,T)` is
exactly the component supplied by the original Navier--Stokes path. -/
noncomputable def h3AuditActualComplementSpectralStateTotal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair) (t : ℝ) : H3SpectralScalarState :=
  if ht : t ∈ Set.Ioo (0 : ℝ) T then
    h3TerminalComplementSpectralStateAt hH3 p t ht
  else 0

/-- A one-sided H³ spectral trace for the **actual physical velocity
component**, rather than an arbitrary bounded Fourier-state path. -/
def H3AuditInitialRightComplementH3SpectralTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair) : Prop :=
  ∃ G₀ : H3SpectralScalarState,
    Tendsto (h3AuditActualComplementSpectralStateTotal hH3 p)
      (𝓝[>] (0 : ℝ)) (𝓝 G₀)

/-- The prior whole-line initial strong spectral path implies this
selected *one-sided* physical Fourier trace. Thus the new hypothesis is a
strictly less demanding interface for applying the analytic criterion. -/
theorem h3Audit_initialStrongSpectralPath_implies_rightComplementTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (p : H3TerminalCurlGradientPair)
    (hInitial : H3AuditInitialStrongH3SpectralVelocityPath hH3) :
    H3AuditInitialRightComplementH3SpectralTrace hH3 p := by
  obtain ⟨U, hContinuous, hMatches⟩ := hInitial
  let j : Fin 3 :=
    h3ClassicalizationFinOfAxis
      (h3TerminalComplementComponentAxisForPair p)
  refine ⟨(U 0) j, ?_⟩
  apply Metric.tendsto_nhdsWithin_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hNear⟩ :=
    (Metric.continuousAt_iff.mp hContinuous) ε hε
  refine ⟨min δ T, lt_min hδ hT, ?_⟩
  intro t htPos hDist
  have htSmall : t < min δ T := by
    have htPositive : 0 < t := htPos
    simpa only [Real.dist_eq, sub_zero, abs_of_pos htPositive] using hDist
  have ht : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨htPos, lt_of_lt_of_le htSmall (min_le_right δ T)⟩
  have hNearNorm : ‖U t - U 0‖ < ε := by
    have htδ : dist t (0 : ℝ) < δ :=
      lt_of_lt_of_le hDist (min_le_left δ T)
    simpa only [dist_eq_norm] using hNear htδ
  have hEq :
      h3AuditActualComplementSpectralStateTotal hH3 p t = (U t) j := by
    simp only [h3AuditActualComplementSpectralStateTotal, dif_pos ht]
    exact hMatches p t ht
  have hCoord : ‖(U t) j - (U 0) j‖ ≤ ‖U t - U 0‖ := by
    simpa only [Pi.sub_apply] using
      (h3SpectralFinVector_coordinate_norm_le (U t - U 0) j)
  rw [hEq]
  calc
    dist ((U t) j) ((U 0) j) = ‖(U t) j - (U 0) j‖ := by
      rw [dist_eq_norm]
    _ ≤ ‖U t - U 0‖ := hCoord
    _ < ε := hNearNorm

/-- Strong right convergence supplies an explicit early time interval and
spectral H³ norm bound for the actual selected velocity component. -/
theorem h3Audit_initialRightComplementTrace_exists_earlySpectralBound
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (ha : 0 < a) (haT : a < T)
    (hTrace : H3AuditInitialRightComplementH3SpectralTrace hH3 p) :
    ∃ b M : ℝ, 0 < b ∧ b < a ∧ 0 ≤ M ∧
      H3AuditInitialComplementSpectralBound hH3 p b M := by
  obtain ⟨G₀, hLimit⟩ := hTrace
  obtain ⟨δ, hδ, hNear⟩ :=
    (Metric.tendsto_nhdsWithin_nhds.mp hLimit) (1 : ℝ) (by norm_num)
  let b : ℝ := min (a / 2) (δ / 2)
  let M : ℝ := ‖G₀‖ + 1
  have hb : 0 < b := by
    dsimp only [b]
    exact lt_min (by linarith) (by linarith)
  have hba : b < a := by
    dsimp only [b]
    have h := min_le_left (a / 2) (δ / 2)
    linarith
  have hM : 0 ≤ M := by
    dsimp only [M]
    positivity
  refine ⟨b, M, hb, hba, hM, ?_⟩
  intro t ht htb
  have hδsmall : t < δ := by
    have hBound : b ≤ δ / 2 := min_le_right _ _
    linarith
  have hDist : dist t (0 : ℝ) < δ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos ht.1] using hδsmall
  have hNearNorm :
      ‖h3AuditActualComplementSpectralStateTotal hH3 p t - G₀‖ < 1 := by
    simpa only [dist_eq_norm] using (hNear ht.1 hDist)
  have hBound :
      ‖h3AuditActualComplementSpectralStateTotal hH3 p t‖ ≤ M := by
    dsimp only [M]
    calc
      ‖h3AuditActualComplementSpectralStateTotal hH3 p t‖ =
          ‖(h3AuditActualComplementSpectralStateTotal hH3 p t - G₀) + G₀‖ := by
            rw [sub_add_cancel]
      _ ≤ ‖h3AuditActualComplementSpectralStateTotal hH3 p t - G₀‖ + ‖G₀‖ :=
        norm_add_le _ _
      _ ≤ ‖G₀‖ + 1 := by linarith
  simpa only [h3AuditActualComplementSpectralStateTotal, dif_pos ht] using hBound

/-- Right H³ trace and a late homogeneous Fourier square-density integral
imply the full `(0,T)` intrinsic physical Ḣ^(3/2) time-L² condition. -/
theorem h3Audit_intrinsicThreeHalves_fullTime_of_initialRightTrace_and_terminal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a c : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (ha : 0 < a) (hac : a < c) (hcT : c < T)
    (hTrace : H3AuditInitialRightComplementH3SpectralTrace hH3 p)
    (hTerminal : IntegrableOn
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      (Set.Ioo c T)) :
    MemLp (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3 p)
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  obtain ⟨b, M, hb, hba, _hM, hEarlyBound⟩ :=
    h3Audit_initialRightComplementTrace_exists_earlySpectralBound
      hH3 p ha (lt_trans hac hcT) hTrace
  have hbT : b < T := lt_trans hba (lt_trans hac hcT)
  have hEarly : IntegrableOn
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      (Set.Ioo (0 : ℝ) b) :=
    h3Audit_homogeneousThreeHalvesTimeDensity_integrableOn_initial_of_bound
      hH3 p hb hbT hEarlyBound
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

/-- The single physical velocity component suffices for the full-time
analytic Sobolev criterion when its initial right H³ trace exists. -/
theorem h3Audit_onePhysicalEndpoint_oneIntrinsicThreeHalves_fullTime_of_initialRightTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hTrace : H3AuditInitialRightComplementH3SpectralTrace hH3
      (h3TerminalActualVorticityPositiveComplementPair i)) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  obtain ⟨c, hc, hLate⟩ :=
    h3Audit_complementEndpoint_homogeneousThreeHalves_integrable
      hH3 hClass (h3TerminalActualVorticityPositiveComplementPair i)
      hPhysical.1
  exact
    h3Audit_intrinsicThreeHalves_fullTime_of_initialRightTrace_and_terminal
      hH3 _ hClass.terminal_start.1 hc.1 hc.2 hTrace hLate

/-- Both transverse physical velocity components have full-time
Ḣ^(3/2) time-L² when the same physical endpoint holds and each selected
component has a finite initial right H³ trace. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialRightTraces
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hPositiveTrace : H3AuditInitialRightComplementH3SpectralTrace hH3
      (h3TerminalActualVorticityPositiveComplementPair i))
    (hNegativeTrace : H3AuditInitialRightComplementH3SpectralTrace hH3
      (h3TerminalActualVorticityNegativeComplementPair i)) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  constructor
  · exact h3Audit_onePhysicalEndpoint_oneIntrinsicThreeHalves_fullTime_of_initialRightTrace
      hH3 hClass i hPhysical hPositiveTrace
  · obtain ⟨c, hc, hLate⟩ :=
      h3Audit_complementEndpoint_homogeneousThreeHalves_integrable
        hH3 hClass (h3TerminalActualVorticityNegativeComplementPair i)
        hPhysical.2
    exact
      h3Audit_intrinsicThreeHalves_fullTime_of_initialRightTrace_and_terminal
        hH3 _ hClass.terminal_start.1 hc.1 hc.2 hNegativeTrace hLate

end
end Euclidean
end Bridge
end PrimeTensor
