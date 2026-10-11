import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPositiveStrongDerivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.Energy.Path.Continuity

/-!
# Weak initial L² data suffice for physical H³ mild-data compatibility

The physical H³ mild-data contract already contains a strongly continuous
spectral path P and its equality with the actual old velocity at every small
strictly positive time. The real inverse-Fourier decoder is continuous from
weighted H³ spectra to the physical scalar L² carrier. Consequently that
mild path supplies an L²-strong initial *limit* automatically.

Only the ordinary weak L² initial condition is required to identify that
limit with the prescribed old initial velocity. No positive-time strong
temporal derivative, Bochner source, two-point evolution equation, or
zero-endpoint FTC identity is assumed here. The old-solution mild path
remains a genuine separate PDE-side hypothesis; the independent terminal
vorticity endpoint remains unchanged.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval

noncomputable section

/-- On strictly positive time slices, the physical L² velocity is precisely
the real inverse-Fourier decoder of its actual weighted H³ spectral state. -/
theorem h3Audit_actualPositivePhysicalZeroJet_eq_spectralRealDecode
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (j : Fin 3) :
    h3FromFourierRealL2
      (h3SpectralScalarDecodeRealL2
        ((h3AuditActualSpectralVelocityTotal hH3 t) j)) =
      h3AuditActualPhysicalZeroJetL2Total hH3 j t := by
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t ht
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes ht
  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes ht hInt
  rw [h3AuditActualSpectralVelocityTotal_eq_at hH3 t ht,
    h3AuditActualPhysicalZeroJetL2Total_eq_at hH3 j t ht]
  change h3FromFourierRealL2
      (h3SpectralVelocityDecodeRealL2
        (velocityH3SpectralStateAt u t hInt hMeas hFourier) j) =
      velocityH3L2JetAt u t hInt hMeas (h3JetSlot0 j)
  rw [h3SpectralVelocityDecodeRealL2_velocityH3SpectralStateAt_apply_eq
    hFourier j]
  exact h3FromFourierRealL2_h3ToFourierRealL2 _

/-- Every strong right H³ spectral trace gives a right *strong physical L²*
trace to its decoded state. Identification with u(0) is not assumed. -/
theorem h3Audit_initialStrongSpectralTrace_physicalDecodeRightLimit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (U₀ : H3SpectralVelocityState)
    (hTrace : Tendsto (h3AuditActualSpectralVelocityTotal hH3)
      (𝓝[>] (0 : ℝ)) (𝓝 U₀))
    (j : Fin 3) :
    Tendsto (h3AuditActualPhysicalZeroJetL2Total hH3 j)
      (𝓝[>] (0 : ℝ))
      (𝓝 (h3FromFourierRealL2 (h3SpectralScalarDecodeRealL2 (U₀ j)))) := by
  have hDecode : Tendsto
      (fun t : ℝ => h3FromFourierRealL2
        (h3SpectralScalarDecodeRealL2
          ((h3AuditActualSpectralVelocityTotal hH3 t) j)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (h3FromFourierRealL2
        (h3SpectralScalarDecodeRealL2 (U₀ j)))) := by
    have h :=
      (continuous_h3SelectedPhysicalL2CoordinateDecode j).continuousAt.tendsto.comp
        hTrace
    change Tendsto
      (fun t : ℝ => h3FromFourierRealL2
        (h3SpectralScalarDecodeRealL2
          ((h3AuditActualSpectralVelocityTotal hH3 t) j)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (h3FromFourierRealL2
        (h3SpectralScalarDecodeRealL2 (U₀ j)))) at h
    exact h
  have hEventual :
      (fun t : ℝ => h3FromFourierRealL2
        (h3SpectralScalarDecodeRealL2
          ((h3AuditActualSpectralVelocityTotal hH3 t) j)))
      =ᶠ[𝓝[>] (0 : ℝ)]
      (h3AuditActualPhysicalZeroJetL2Total hH3 j) := by
    filter_upwards [h3Audit_eventually_initialStrictPhysicalTime hT]
      with t ht
    exact h3Audit_actualPositivePhysicalZeroJet_eq_spectralRealDecode
      hH3 t ht j
  exact hDecode.congr' hEventual

/-- In a real Hilbert space, a strong right limit and a weak right limit
necessarily identify the same state. -/
theorem h3Audit_initialHilbertStrongAndWeakLimit_identify
    (F : ℝ → H3ScalarL2) (L L₀ : H3ScalarL2)
    (hStrong : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hWeak : ∀ ψ : H3ScalarL2,
      Tendsto (fun t : ℝ => inner ℝ (F t) ψ)
        (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ L₀ ψ))) :
    L = L₀ := by
  have hPairingContinuous :
      Continuous (fun z : H3ScalarL2 => inner ℝ z (L - L₀)) :=
    continuous_id.inner continuous_const
  have hPair : inner ℝ L (L - L₀) = inner ℝ L₀ (L - L₀) :=
    tendsto_nhds_unique
      (hPairingContinuous.continuousAt.tendsto.comp hStrong)
      (hWeak (L - L₀))
  have hZero : inner ℝ (L - L₀) (L - L₀) = 0 := by
    rw [inner_sub_left]
    exact sub_eq_zero.mpr hPair
  have hNormSq : ‖L - L₀‖ ^ 2 = 0 := by
    simpa only [real_inner_self_eq_norm_sq] using hZero
  have hNormZero : ‖L - L₀‖ = 0 := by
    nlinarith [norm_nonneg (L - L₀)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hNormZero)

/-- The weak initial condition alone identifies the physical decoded mild
limit with the old solution's prescribed initial L² velocity. No time
source is needed when a strong H³ mild trace is already available. -/
theorem h3Audit_initialMildStrongTrace_and_weakInitial_implies_physicalL2Trace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (U₀ : H3SpectralVelocityState)
    (hTrace : Tendsto (h3AuditActualSpectralVelocityTotal hH3)
      (𝓝[>] (0 : ℝ)) (𝓝 U₀))
    (hWeak : ∀ (j : Fin 3) (ψ : H3ScalarL2),
      Tendsto
        (fun t : ℝ =>
          inner ℝ (h3AuditActualPhysicalZeroJetL2Total hH3 j t) ψ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ
          (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)) ψ))) :
    ∀ j : Fin 3,
      Tendsto (h3AuditActualPhysicalZeroJetL2Total hH3 j)
        (𝓝[>] (0 : ℝ))
        (𝓝 (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j))) := by
  intro j
  let L : H3ScalarL2 :=
    h3FromFourierRealL2 (h3SpectralScalarDecodeRealL2 (U₀ j))
  let L₀ : H3ScalarL2 :=
    velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)
  have hDecoded : Tendsto (h3AuditActualPhysicalZeroJetL2Total hH3 j)
      (𝓝[>] (0 : ℝ)) (𝓝 L) :=
    h3Audit_initialStrongSpectralTrace_physicalDecodeRightLimit
      hH3 hT U₀ hTrace j
  have hIdentify : L = L₀ :=
    h3Audit_initialHilbertStrongAndWeakLimit_identify
      (h3AuditActualPhysicalZeroJetL2Total hH3 j) L L₀
      hDecoded (hWeak j)
  simpa only [hIdentify] using hDecoded

/-- Minimal physical mild input with actual prescribed weak initial L² trace.
No Bochner temporal source, no interior strong derivative, and no physical
strong initial trace is included in this contract. -/
def H3AuditInitialPhysicalEnergyMildWeakTraceData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (U₀ : H3SpectralVelocityState) (A : ℝ)
    (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A) (b : ℝ),
    H3AuditInitialPhysicalEnergyMildDataAt hH3 U₀ hA hU₀ b ∧
    ∀ (j : Fin 3) (ψ : H3ScalarL2),
      Tendsto
        (fun t : ℝ =>
          inner ℝ (h3AuditActualPhysicalZeroJetL2Total hH3 j t) ψ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ
          (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)) ψ))

/-- The strong spectral initial trace of a continuous old physical mild path
upgrades its *weak* initial L² data to the prior strong L² initial criterion. -/
theorem h3Audit_initialMildWeakTrace_implies_L2TraceData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildWeakTraceData hH3) :
    H3AuditInitialPhysicalEnergyMildL2TraceData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, U₀, A, hA, hU₀,
    b, hMild, hWeak⟩ := hData
  have hT : 0 < T :=
    (Classical.choose_spec hH3.navier_stokes).positive_terminal
  have hTrace :=
    h3Audit_initialPhysicalEnergyMildDataAt_fullStrongH3Trace
      hH3 U₀ hA hU₀ hMild
  exact ⟨hInt0, hMeas0, hFourier0, U₀, A, hA, hU₀, b,
    hMild,
    h3Audit_initialMildStrongTrace_and_weakInitial_implies_physicalL2Trace
      hH3 hT hInt0 hMeas0 U₀ hTrace hWeak⟩

/-- Weak initial L² data identify the initial mild datum with the actual
initial H³ spectral velocity encoder, without a temporal L¹ source. -/
theorem h3Audit_initialMildWeakTrace_identifies_initialSpectral
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildWeakTraceData hH3) :
    H3AuditInitialPhysicalEnergyMildZeroCompatibleData hH3 := by
  exact h3Audit_initialMildL2Trace_implies_zeroCompatibleData
    hH3 (h3Audit_initialMildWeakTrace_implies_L2TraceData hH3 hData)

/-- Recover actual initial physical H³ energy right continuity from the
strong mild spectral trace and a prescribed weak L² initial condition. -/
theorem h3Audit_initialMildWeakTrace_energyRightLimit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildWeakTraceData hH3) :
    Tendsto (velocityH3EnergyAt u)
      (𝓝[>] (0 : ℝ)) (𝓝 (velocityH3EnergyAt u 0)) := by
  exact h3Audit_initialMildL2Trace_energyRightLimit
    hH3 (h3Audit_initialMildWeakTrace_implies_L2TraceData hH3 hData)

/-- Both transverse full-time homogeneous Sobolev consequences retain the
independent terminal vorticity strong-H³ endpoint. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialMildWeakTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialPhysicalEnergyMildWeakTraceData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialMildL2Trace
    hH3 hClass i hPhysical
    (h3Audit_initialMildWeakTrace_implies_L2TraceData hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
