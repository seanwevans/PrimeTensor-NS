import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentHomogeneousTimeL2
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Round.Trip

/-!
# Physical velocity Fourier identification for the homogeneous Ḣ^(3/2) criterion

For a genuine logged H³ Navier--Stokes path, the strict-time selected
spectral state is the weighted encoding of the *actual zeroth-order velocity
component*, not an unrelated solver amplitude. Deweighting recovers its
canonical Plancherel Fourier transform exactly in L².

Consequently the homogeneous Ḣ^(3/2) square density from the audit is
exactly the spatial-frequency integral of the Fourier transform of that
physical scalar velocity component. This is an internal Plancherel-level
identification, not a claim that the external Liu--Zhang continuation theorem
has been imported or that its local-strong-solution assumptions are verified.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

noncomputable local instance axisFintypeH3AuditPhysicalFourier
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- At a strict preterminal time, the deweighted pair-selected Fourier state
is the **actual** Fourier transform of the selected zeroth-order scalar
velocity jet, with no additional Fourier-representative assumption. -/
theorem h3Audit_complementRawFourierL2_eq_actualVelocityFourier
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    h3SpectralScalarRawFourierL2
        (h3TerminalComplementSpectralStateAt hH3 p t ht) =
      h3ScalarFourierL2
        (velocityH3L2JetAt u t
          (hH3.velocity_h3_integrable t ht)
          (velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
            hH3.navier_stokes ht)
          (h3JetSlot0
            (h3ClassicalizationFinOfAxis
              (h3TerminalComplementComponentAxisForPair p)))) := by
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t ht
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes ht
  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes ht hInt
  let j : Fin 3 :=
    h3ClassicalizationFinOfAxis
      (h3TerminalComplementComponentAxisForPair p)
  change
    h3SpectralScalarRawFourierL2
        (velocityH3SpectralScalarAt u t hInt hMeas hFourier j) =
      velocityH3BaseFourierAt u t hInt hMeas j
  exact h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
    hFourier j

/-- The raw Fourier representative of the genuine selected velocity
component agrees almost everywhere with its physical zeroth-order Fourier
jet. The identity is in the project's normalized Plancherel convention. -/
theorem h3Audit_complementRawFourier_ae_actualVelocityFourier
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    h3SpectralScalarRawFourier
        (h3TerminalComplementSpectralStateAt hH3 p t ht)
      =ᵐ[(volume : Measure H3FourierPoint3)]
      (h3ScalarFourierL2
        (velocityH3L2JetAt u t
          (hH3.velocity_h3_integrable t ht)
          (velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
            hH3.navier_stokes ht)
          (h3JetSlot0
            (h3ClassicalizationFinOfAxis
              (h3TerminalComplementComponentAxisForPair p)))) :
        H3FourierPoint3 → ℂ) := by
  have hAE :=
    (h3SpectralScalarRawFourierL2_ae
      (h3TerminalComplementSpectralStateAt hH3 p t ht)).symm
  rw [h3Audit_complementRawFourierL2_eq_actualVelocityFourier
    hH3 p t ht] at hAE
  exact hAE

/-- The actual homogeneous Fourier square energy is the literal weighted
spatial Fourier integral of the selected physical velocity component. -/
theorem h3Audit_homogeneousThreeHalvesTimeDensity_eq_actualVelocityFourier
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p t =
      ∫ ξ : H3FourierPoint3,
        Real.sqrt (h3FourierGradientSquare ξ ^ 3) *
          ‖(h3ScalarFourierL2
            (velocityH3L2JetAt u t
              (hH3.velocity_h3_integrable t ht)
              (velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
                hH3.navier_stokes ht)
              (h3JetSlot0
                (h3ClassicalizationFinOfAxis
                  (h3TerminalComplementComponentAxisForPair p))))) ξ‖ ^ 2 := by
  simp only [h3AuditHomogeneousThreeHalvesVelocityTimeDensity, dif_pos ht]
  apply integral_congr_ae
  filter_upwards [h3Audit_complementRawFourier_ae_actualVelocityFourier
    hH3 p t ht] with ξ hξ
  unfold h3AuditHomogeneousThreeHalvesFourierSquareDensity
  rw [hξ]

/-- The genuine physical Fourier integral, zero-extended off `(0,T)`. -/
noncomputable def h3AuditActualVelocityHomogeneousThreeHalvesFourierSquare
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair) (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Ioo (0 : ℝ) T then
    ∫ ξ : H3FourierPoint3,
      Real.sqrt (h3FourierGradientSquare ξ ^ 3) *
        ‖(h3ScalarFourierL2
          (velocityH3L2JetAt u t
            (hH3.velocity_h3_integrable t ht)
            (velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
              hH3.navier_stokes ht)
            (h3JetSlot0
              (h3ClassicalizationFinOfAxis
                (h3TerminalComplementComponentAxisForPair p))))) ξ‖ ^ 2
  else 0

/-- Physical Fourier square energy is the already-audited density, at every
time (including the zero extension outside the preterminal interval). -/
theorem h3Audit_actualVelocityFourierSquare_eq_timeDensity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair) (t : ℝ) :
    h3AuditActualVelocityHomogeneousThreeHalvesFourierSquare hH3 p t =
      h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p t := by
  by_cases ht : t ∈ Set.Ioo (0 : ℝ) T
  · simpa only [h3AuditActualVelocityHomogeneousThreeHalvesFourierSquare,
      dif_pos ht] using
      (h3Audit_homogeneousThreeHalvesTimeDensity_eq_actualVelocityFourier
        hH3 p t ht).symm
  · simp [h3AuditActualVelocityHomogeneousThreeHalvesFourierSquare,
      h3AuditHomogeneousThreeHalvesVelocityTimeDensity, ht]

/-- The physical Fourier seminorm is computed by the square root of the
actual zeroth-order velocity Fourier integral. -/
noncomputable def h3AuditActualVelocityHomogeneousThreeHalvesFourierSeminorm
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair) (t : ℝ) : ℝ :=
  Real.sqrt (h3AuditActualVelocityHomogeneousThreeHalvesFourierSquare hH3 p t)

/-- No extra identification premise: the newly named physical Fourier
seminorm agrees pointwise with the original spectral audit seminorm. -/
theorem h3Audit_actualVelocityFourierSeminorm_eq_timeSeminorm
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair) (t : ℝ) :
    h3AuditActualVelocityHomogeneousThreeHalvesFourierSeminorm hH3 p t =
      h3AuditHomogeneousThreeHalvesVelocityTimeSeminorm hH3 p t := by
  unfold h3AuditActualVelocityHomogeneousThreeHalvesFourierSeminorm
    h3AuditHomogeneousThreeHalvesVelocityTimeSeminorm
  rw [h3Audit_actualVelocityFourierSquare_eq_timeDensity hH3 p t]

/-- The physical zeroth-order Fourier velocity seminorms for both
transverse coordinates satisfy the exact `L²_t` estimate on one interval.
This still does not import an external continuation theorem. -/
theorem h3Audit_onePhysicalEndpoint_twoActualVelocityFourier_timeL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i) :
    ∃ c : ℝ, c ∈ Set.Ioo a T ∧
      MemLp
        (h3AuditActualVelocityHomogeneousThreeHalvesFourierSeminorm hH3
          (h3TerminalActualVorticityPositiveComplementPair i))
        2 (volume.restrict (Set.Ioo c T)) ∧
      MemLp
        (h3AuditActualVelocityHomogeneousThreeHalvesFourierSeminorm hH3
          (h3TerminalActualVorticityNegativeComplementPair i))
        2 (volume.restrict (Set.Ioo c T)) := by
  obtain ⟨c, hc, hPos, hNeg⟩ :=
    h3Audit_onePhysicalEndpoint_twoHomogeneousThreeHalves_timeL2
      hH3 hClass i hPhysical
  refine ⟨c, hc, ?_, ?_⟩
  · have hEq :
        h3AuditActualVelocityHomogeneousThreeHalvesFourierSeminorm hH3
          (h3TerminalActualVorticityPositiveComplementPair i) =
        h3AuditHomogeneousThreeHalvesVelocityTimeSeminorm hH3
          (h3TerminalActualVorticityPositiveComplementPair i) := by
      funext t
      exact h3Audit_actualVelocityFourierSeminorm_eq_timeSeminorm hH3 _ t
    rw [hEq]
    exact hPos
  · have hEq :
        h3AuditActualVelocityHomogeneousThreeHalvesFourierSeminorm hH3
          (h3TerminalActualVorticityNegativeComplementPair i) =
        h3AuditHomogeneousThreeHalvesVelocityTimeSeminorm hH3
          (h3TerminalActualVorticityNegativeComplementPair i) := by
      funext t
      exact h3Audit_actualVelocityFourierSeminorm_eq_timeSeminorm hH3 _ t
    rw [hEq]
    exact hNeg

end
end Euclidean
end Bridge
end PrimeTensor
