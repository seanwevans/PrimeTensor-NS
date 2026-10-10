import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialMildZeroCompatibility
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spectral.Fin.Heat.Leray.VariationOfConstants.State

/-!
# Identify the physical initial mild datum by its actual L² right trace

The previous initial mild criterion supplied an explicit equality between the
spectral initial state `U₀` and the independent H³ Fourier encoding of the
old velocity at time zero. This equality is not implied by open-time
Navier--Stokes admissibility.

Under a strong H³ right limit, however, this compatibility is EQUIVALENT to
the ordinary strong physical L² right trace of all three actual velocity
components to their prescribed initial data. The proof uses:

* exact scalar physical/Fourier Plancherel at strict positive times;
* continuity of the H³-to-raw-L² deweighting map;
* injectivity of that map (positive Sobolev frequency weight);
* uniqueness of right-sided L² limits.

Thus physical L² initial-value data replaces an otherwise independent
spectral identification hypothesis. It does not construct the physical L²
initial trace or the old-solution mild equation from open-time classical PDE
admissibility. No terminal regularity is inferred here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval

noncomputable section

/-- Strong right H³ convergence and the actual physical L² right trace
uniquely identify the limiting weighted spectral state with the H³ encoder
of the prescribed old velocity at time zero. No energy continuity at zero
is assumed, and no spectral equality is postulated. -/
theorem h3Audit_initialStrongH3Trace_identifies_initialSpectral_of_physicalL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (U₀ : H3SpectralVelocityState)
    (hTrace : Tendsto (h3AuditActualSpectralVelocityTotal hH3)
      (𝓝[>] (0 : ℝ)) (𝓝 U₀))
    (hPhysical : ∀ j : Fin 3,
      Tendsto (h3AuditActualPhysicalZeroJetL2Total hH3 j)
        (𝓝[>] (0 : ℝ))
        (𝓝 (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)))) :
    U₀ = velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0 := by
  funext j
  apply h3SpectralScalarRawFourierL2_injective
  let F : ℝ → H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3
  let L₀ : H3ScalarL2 :=
    velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)
  have hCoord : Tendsto (fun t : ℝ => F t j)
      (𝓝[>] (0 : ℝ)) (𝓝 (U₀ j)) :=
    (continuous_apply j).continuousAt.tendsto.comp hTrace
  have hRawContinuous : Continuous
      (fun G : H3SpectralScalarState => h3SpectralScalarRawFourierL2 G) :=
    continuous_h3SpectralScalarRawFourierL2_comp _ continuous_id
  have hRawLimit : Tendsto
      (fun t : ℝ => h3SpectralScalarRawFourierL2 (F t j))
      (𝓝[>] (0 : ℝ))
      (𝓝 (h3SpectralScalarRawFourierL2 (U₀ j))) := by
    have h := hRawContinuous.continuousAt.tendsto.comp hCoord
    change Tendsto
      (fun t : ℝ => h3SpectralScalarRawFourierL2 (F t j))
      (𝓝[>] (0 : ℝ))
      (𝓝 (h3SpectralScalarRawFourierL2 (U₀ j))) at h
    exact h
  have hPhysicalFourier : Tendsto
      (fun t : ℝ => h3ScalarFourierL2
        (h3AuditActualPhysicalZeroJetL2Total hH3 j t))
      (𝓝[>] (0 : ℝ))
      (𝓝 (h3ScalarFourierL2 L₀)) := by
    exact continuous_h3ScalarFourierL2.continuousAt.tendsto.comp
      (hPhysical j)
  have hStrict : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      t ∈ Set.Ioo (0 : ℝ) T := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hT)] with t ht0 htT
    exact ⟨ht0, htT⟩
  have hRawAgreement :
      (fun t : ℝ => h3SpectralScalarRawFourierL2 (F t j))
        =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => h3ScalarFourierL2
        (h3AuditActualPhysicalZeroJetL2Total hH3 j t)) := by
    filter_upwards [hStrict] with t ht
    exact h3Audit_actualRawFourier_eq_fourierPhysicalZeroJetL2
      hH3 j t ht
  have hRawPhysical : Tendsto
      (fun t : ℝ => h3SpectralScalarRawFourierL2 (F t j))
      (𝓝[>] (0 : ℝ)) (𝓝 (h3ScalarFourierL2 L₀)) :=
    hPhysicalFourier.congr' hRawAgreement.symm
  have hLimitEquality :
      h3SpectralScalarRawFourierL2 (U₀ j) =
      h3ScalarFourierL2 L₀ :=
    tendsto_nhds_unique hRawLimit hRawPhysical
  have hInitialRaw :
      h3SpectralScalarRawFourierL2
          ((velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0) j) =
      h3ScalarFourierL2 L₀ := by
    change h3SpectralScalarRawFourierL2
        (velocityH3SpectralScalarAt u 0 hInt0 hMeas0 hFourier0 j) =
      velocityH3BaseFourierAt u 0 hInt0 hMeas0 j
    exact h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
      hFourier0 j
  exact hLimitEquality.trans hInitialRaw.symm

/-- For an actual strong H³ mild right trace, spectral initial-value
compatibility is equivalent to the physical L² right trace of all three
old velocity components. This is not an equivalence under the open-time
PDE class alone: the strong H³ right trace is an explicit hypothesis. -/
theorem h3Audit_initialSpectralCompatibility_iff_physicalL2RightTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (U₀ : H3SpectralVelocityState)
    (hTrace : Tendsto (h3AuditActualSpectralVelocityTotal hH3)
      (𝓝[>] (0 : ℝ)) (𝓝 U₀)) :
    (U₀ = velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0) ↔
      ∀ j : Fin 3,
        Tendsto (h3AuditActualPhysicalZeroJetL2Total hH3 j)
          (𝓝[>] (0 : ℝ))
          (𝓝 (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j))) := by
  constructor
  · intro hCompatible j
    exact h3Audit_compatibleInitialStrongH3Trace_physicalL2RightTrace
      hH3 hT hInt0 hMeas0 hFourier0 U₀ hCompatible hTrace j
  · intro hPhysical
    exact h3Audit_initialStrongH3Trace_identifies_initialSpectral_of_physicalL2
      hH3 hT hInt0 hMeas0 hFourier0 U₀ hTrace hPhysical

/-- Initial old physical mild data with the ordinary strong physical L²
right trace, but WITHOUT any separately assumed spectral equality. -/
def H3AuditInitialPhysicalEnergyMildL2TraceData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (U₀ : H3SpectralVelocityState) (A : ℝ)
    (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A) (b : ℝ),
    H3AuditInitialPhysicalEnergyMildDataAt hH3 U₀ hA hU₀ b ∧
    ∀ j : Fin 3,
      Tendsto (h3AuditActualPhysicalZeroJetL2Total hH3 j)
        (𝓝[>] (0 : ℝ))
        (𝓝 (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)))

/-- The physical L² initial trace IDENTIFIES the mild spectral datum.
This eliminates the previous separately assumed spectral initial equality. -/
theorem h3Audit_initialMildL2Trace_implies_zeroCompatibleData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildL2TraceData hH3) :
    H3AuditInitialPhysicalEnergyMildZeroCompatibleData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, U₀, A, hA, hU₀, b,
    hMild, hPhysical⟩ := hData
  have hT : 0 < T :=
    (Classical.choose_spec hH3.navier_stokes).positive_terminal
  have hTrace :=
    h3Audit_initialPhysicalEnergyMildDataAt_fullStrongH3Trace
      hH3 U₀ hA hU₀ hMild
  have hCompatible :=
    h3Audit_initialStrongH3Trace_identifies_initialSpectral_of_physicalL2
      hH3 hT hInt0 hMeas0 hFourier0 U₀ hTrace hPhysical
  exact ⟨hInt0, hMeas0, hFourier0, U₀, A, hA, hU₀, b,
    hMild, hCompatible⟩

/-- Under the old mild equation, its actual physical L² initial trace
supplies the exact original physical H³ energy right limit without an
additional zero-time spectral compatibility premise. -/
theorem h3Audit_initialMildL2Trace_energyRightLimit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildL2TraceData hH3) :
    Tendsto (velocityH3EnergyAt u)
      (𝓝[>] (0 : ℝ)) (𝓝 (velocityH3EnergyAt u 0)) := by
  obtain ⟨hInt0, hMeas0, hFourier0, U₀, A, hA, hU₀, b,
    hMild, hPhysical⟩ := hData
  have hT : 0 < T :=
    (Classical.choose_spec hH3.navier_stokes).positive_terminal
  have hTrace :=
    h3Audit_initialPhysicalEnergyMildDataAt_fullStrongH3Trace
      hH3 U₀ hA hU₀ hMild
  have hCompatible :=
    h3Audit_initialStrongH3Trace_identifies_initialSpectral_of_physicalL2
      hH3 hT hInt0 hMeas0 hFourier0 U₀ hTrace hPhysical
  exact h3Audit_compatibleInitialPhysicalMild_energyRightLimit
    hH3 U₀ hA hU₀ hMild hInt0 hMeas0 hFourier0 hCompatible

/-- The new physical initial-value premise discharges the earlier minimal
zero-jet L² / one-sided H³-energy interface. -/
theorem h3Audit_initialMildL2Trace_implies_physicalL2AndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildL2TraceData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialMildZeroCompatible_implies_physicalL2AndEnergyUpper
    hH3 (h3Audit_initialMildL2Trace_implies_zeroCompatibleData hH3 hData)

/-- Complete right H³ trace, now obtained under actual mild data and
physical initial L² trace rather than a separately asserted Fourier equality. -/
theorem h3Audit_initialMildL2Trace_strongH3Trace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildL2TraceData hH3) :
    ∃ U₀ : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
  exact h3Audit_initialMildZeroCompatible_strongH3Trace_via_physicalL2
    hH3 (h3Audit_initialMildL2Trace_implies_zeroCompatibleData hH3 hData)

/-- Full-time two-transverse-velocity consequence remains conditional on
the separate actual physical strong-H³ terminal vorticity endpoint. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialMildL2Trace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialPhysicalEnergyMildL2TraceData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialPhysicalZeroJetL2
    hH3 hClass i hPhysical
    (h3Audit_initialMildL2Trace_implies_physicalL2AndEnergyUpper hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
