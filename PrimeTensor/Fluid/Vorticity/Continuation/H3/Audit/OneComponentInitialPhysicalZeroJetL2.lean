import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialRawL2WeakH3Trace

/-!
# Physical initial velocity L² trace and actual t=0 H³ Fourier datum

The previous initial-value interface still assumed the raw Fourier L² right
limit of each of the three actual velocity components against a separately
chosen spectral initial datum. This module instead starts with the genuine
zeroth-order physical L² velocity jet and a genuinely encoded H³ snapshot
AT t=0. Plancherel transfers its physical L² right trace to the raw Fourier
right trace, while the existing exact spectral encoder identifies the
initial Fourier datum and its normalized H³ energy without extra premises.

The open-time Navier--Stokes path supplies neither the initial H³ snapshot,
its physical L² right trace nor the one-sided H³ energy inequality. These
are explicitly retained as initial-value hypotheses. An optional more
physical input replaces Fourier compatibility at t=0 by spatial C³.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3AuditInitialPhysicalZeroJetL2
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Zeroth-order real physical L² velocity jet of the ACTUAL old solution.
The auxiliary zero extension is immaterial for the t -> 0+ right trace. -/
noncomputable def h3AuditActualPhysicalZeroJetL2Total
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (j : Fin 3) (t : ℝ) : H3ScalarL2 :=
  if ht : t ∈ Set.Ioo (0 : ℝ) T then
    velocityH3L2JetAt u t
      (hH3.velocity_h3_integrable t ht)
      (velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
        hH3.navier_stokes ht)
      (h3JetSlot0 j)
  else 0

/-- The totalized physical path agrees with its genuine velocity L² jet
at every strict physical time. -/
theorem h3AuditActualPhysicalZeroJetL2Total_eq_at
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (j : Fin 3) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    h3AuditActualPhysicalZeroJetL2Total hH3 j t =
      velocityH3L2JetAt u t
        (hH3.velocity_h3_integrable t ht)
        (velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
          hH3.navier_stokes ht)
        (h3JetSlot0 j) := by
  simp only [h3AuditActualPhysicalZeroJetL2Total, dite_eq_left ht]

/-- The physical L² jet at every strict time has precisely the raw Fourier
state of the actual H³ spectral encoder. -/
theorem h3Audit_actualRawFourier_eq_fourierPhysicalZeroJetL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (j : Fin 3) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    h3SpectralScalarRawFourierL2
      (h3AuditActualSpectralVelocityTotal hH3 t j) =
    h3ScalarFourierL2
      (h3AuditActualPhysicalZeroJetL2Total hH3 j t) := by
  rw [h3Audit_actualFullRawFourier_eq_physicalZeroJet hH3 j t ht]
  rw [h3AuditActualPhysicalZeroJetL2Total_eq_at hH3 j t ht]

/-- Strong physical L² right convergence of the actual velocity to its
actual t=0 jet implies the correct raw Fourier right convergence. The
initial Fourier datum is NOT chosen independently: it is the H³ encoder of
the same old velocity at t=0. -/
theorem h3Audit_initialPhysicalZeroJetL2_implies_rawFourierTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (j : Fin 3)
    (hPhysical : Tendsto
      (h3AuditActualPhysicalZeroJetL2Total hH3 j)
      (𝓝[>] (0 : ℝ))
      (𝓝 (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)))) :
    Tendsto
      (fun t : ℝ => h3SpectralScalarRawFourierL2
        (h3AuditActualSpectralVelocityTotal hH3 t j))
      (𝓝[>] (0 : ℝ))
      (𝓝 (h3SpectralScalarRawFourierL2
        (velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0 j))) := by
  have hFourierLimit : Tendsto
      (fun t : ℝ => h3ScalarFourierL2
        (h3AuditActualPhysicalZeroJetL2Total hH3 j t))
      (𝓝[>] (0 : ℝ))
      (𝓝 (h3ScalarFourierL2
        (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)))) :=
    continuous_h3ScalarFourierL2.continuousAt.tendsto.comp hPhysical
  have hPositive : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)), 0 < t :=
    self_mem_nhdsWithin
  have hBeforeT : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)), t < T :=
    nhdsWithin_le_nhds (Iio_mem_nhds hT)
  have hEq :
      (fun t : ℝ => h3ScalarFourierL2
        (h3AuditActualPhysicalZeroJetL2Total hH3 j t))
      =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => h3SpectralScalarRawFourierL2
        (h3AuditActualSpectralVelocityTotal hH3 t j)) := by
    filter_upwards [hPositive, hBeforeT] with t hp hlt
    exact (h3Audit_actualRawFourier_eq_fourierPhysicalZeroJetL2
      hH3 j t ⟨hp, hlt⟩).symm
  have hInitialFourier :
      h3ScalarFourierL2
        (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)) =
      h3SpectralScalarRawFourierL2
        (velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0 j) := by
    change h3ScalarFourierL2
        (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)) =
      h3SpectralScalarRawFourierL2
        (velocityH3SpectralScalarAt u 0 hInt0 hMeas0 hFourier0 j)
    exact (h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
      hFourier0 j).symm
  simpa only [hInitialFourier] using hFourierLimit.congr' hEq

/-- Natural physical t=0 data. In contrast to the preceding Fourier-side
interface, the datum is the actual encoded H³ velocity at t=0, and the
right trace is stated directly for the three real physical L² coordinates.
The one-sided physical H³ energy bound remains explicit. -/
def H3AuditInitialPhysicalZeroJetL2AndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0),
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
        velocityH3EnergyAt u t < velocityH3EnergyAt u 0 + ε) ∧
    (∀ j : Fin 3,
      Tendsto (h3AuditActualPhysicalZeroJetL2Total hH3 j)
        (𝓝[>] (0 : ℝ))
        (𝓝 (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j))))

/-- Exact Fourier and energy encodings eliminate the independently supplied
spectral initial datum and all three assumed raw Fourier limits. -/
theorem h3Audit_initialPhysicalZeroJetL2AndEnergyUpper_implies_rawL2Data
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hData : H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3) :
    H3AuditInitialRightPhysicalRawL2AndEnergyUpper hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, hEnergyUpper, hPhysical⟩ := hData
  let U₀ : H3SpectralVelocityState :=
    velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0
  have hExact :
      1 + h3SpectralVelocitySquareEnergy U₀ =
        velocityH3EnergyAt u 0 := by
    dsimp only [U₀]
    exact one_add_h3SpectralVelocitySquareEnergy_velocityH3SpectralStateAt_eq
      hFourier0
  refine ⟨U₀, ?_, ?_⟩
  · intro ε hε
    simpa only [hExact] using hEnergyUpper ε hε
  · intro j
    exact h3Audit_initialPhysicalZeroJetL2_implies_rawFourierTrace
      hH3 hT hInt0 hMeas0 hFourier0 j (hPhysical j)

/-- Strong initial H³ right trace of the actual physical velocity from
physical zeroth-order L² right-continuity and an H³ energy limsup ceiling. -/
theorem h3Audit_initialPhysicalZeroJetL2AndEnergyUpper_implies_strongH3Trace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hData : H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3) :
    ∃ U₀ : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
  exact h3Audit_initialPhysicalRawL2AndEnergyUpper_implies_strongVelocityTrace
    hH3 hT
    (h3Audit_initialPhysicalZeroJetL2AndEnergyUpper_implies_rawL2Data
      hH3 hT hData)

/-- The initial Fourier-compatibility proof can itself be obtained from
spatial C³ regularity of each of the actual initial velocity components. -/
def H3AuditInitialPhysicalZeroJetSpatialC3Data
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ)),
    (∀ j : PrimeTensor.Axis Depth.three,
      SpatialC3 (loggedVelocityComponent u 0 j)) ∧
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
        velocityH3EnergyAt u t < velocityH3EnergyAt u 0 + ε) ∧
    (∀ j : Fin 3,
      Tendsto (h3AuditActualPhysicalZeroJetL2Total hH3 j)
        (𝓝[>] (0 : ℝ))
        (𝓝 (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j))))

/-- The existing Fourier derivative compatibility theorem for spatial C³
snapshots supplies the required actual initial spectral encoder. -/
theorem h3Audit_initialPhysicalZeroJetSpatialC3_implies_physicalData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalZeroJetSpatialC3Data hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  obtain ⟨hInt0, hMeas0, hSpatial0, hUpper, hL2⟩ := hData
  let hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0 :=
    velocityH3FourierCompatibleAt_of_spatialC3
      hSpatial0 hInt0 hMeas0
  exact ⟨hInt0, hMeas0, hFourier0, hUpper, hL2⟩

/-- The two transverse physical velocity components have full-time intrinsic
L²_t Ḣ^(3/2)_x under this initial physical-data contract and the SEPARATE
actual terminal vorticity strong-H³ endpoint assumption. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialPhysicalZeroJetL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  have hT : 0 < T :=
    lt_trans hClass.terminal_start.1 hClass.terminal_start.2
  exact
    h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialPhysicalRawL2
      hH3 hClass i hPhysical
      (h3Audit_initialPhysicalZeroJetL2AndEnergyUpper_implies_rawL2Data
        hH3 hT hData)

end
end Euclidean
end Bridge
end PrimeTensor
