import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPhysicalMildStrongTrace
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Two.Selected.Velocity.Raw.Fourier.L2.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.RHS.Continuity

/-!
# Initial mild H³ trace and the actual time-zero physical velocity

The prior initial mild-path theorem produces strong H³ convergence of the
actual old *positive-time* velocity to a mild datum U₀, but does not identify
U₀ with the separately specified old field at time zero.

Here an explicit and necessary initial-value compatibility equality identifies
U₀ with the canonical H³ Fourier encoding of that actual time-zero field.
Under this equality, the full spectral strong right trace gives all three
physical L² velocity right traces by the exact scalar Plancherel isometry.
The exact H³ energy encoding similarly identifies the mild energy limit with
the actual initial physical energy.

The old mild equation and actual/selected compatibility remain independent
assumptions in `H3AuditInitialPhysicalEnergyMildDataAt`.  The present module
neither derives them from open-time Navier--Stokes admissibility nor assumes
any terminal regularity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval

noncomputable section

/-- Fourier compatibility for an actual H³ zero snapshot identifies the raw
initial weighted-spectrum deweighting with its actual zeroth physical jet. -/
theorem h3Audit_compatibleInitialSpectral_raw_eq_physicalZeroJet
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (U₀ : H3SpectralVelocityState)
    (hCompatible : U₀ = velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0)
    (j : Fin 3) :
    h3SpectralScalarRawFourierL2 (U₀ j) =
      h3ScalarFourierL2 (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)) := by
  rw [hCompatible]
  change h3SpectralScalarRawFourierL2
      (velocityH3SpectralScalarAt u 0 hInt0 hMeas0 hFourier0 j) =
    velocityH3BaseFourierAt u 0 hInt0 hMeas0 j
  exact h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
    hFourier0 j

/-- A full weighted H³ right trace whose limit is the genuine physical
initial H³ Fourier encoding gives the strong physical L² right trace of
each actual old velocity coordinate, using Plancherel *in reverse*. -/
theorem h3Audit_compatibleInitialStrongH3Trace_physicalL2RightTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (U₀ : H3SpectralVelocityState)
    (hCompatible : U₀ = velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0)
    (hTrace : Tendsto (h3AuditActualSpectralVelocityTotal hH3)
      (𝓝[>] (0 : ℝ)) (𝓝 U₀))
    (j : Fin 3) :
    Tendsto (h3AuditActualPhysicalZeroJetL2Total hH3 j)
      (𝓝[>] (0 : ℝ))
      (𝓝 (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j))) := by
  let L₀ : H3ScalarL2 :=
    velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)
  let F : ℝ → H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3
  have hCoord : Tendsto (fun t : ℝ => F t j)
      (𝓝[>] (0 : ℝ)) (𝓝 (U₀ j)) :=
    (continuous_apply j).continuousAt.tendsto.comp hTrace
  have hRawCont : Continuous
      (fun G : H3SpectralScalarState => h3SpectralScalarRawFourierL2 G) :=
    continuous_h3SpectralScalarRawFourierL2_comp _ continuous_id
  have hRaw : Tendsto (fun t : ℝ =>
      h3SpectralScalarRawFourierL2 (F t j))
      (𝓝[>] (0 : ℝ)) (𝓝 (h3ScalarFourierL2 L₀)) := by
    have hBase := hRawCont.continuousAt.tendsto.comp hCoord
    have hAtZero := h3Audit_compatibleInitialSpectral_raw_eq_physicalZeroJet
      hInt0 hMeas0 hFourier0 U₀ hCompatible j
    -- The composed function in `hBase` is definitionally the displayed lambda.
    -- Normalize that syntactic form before rewriting the target value.
    change Tendsto
      (fun t : ℝ => h3SpectralScalarRawFourierL2 (F t j))
      (𝓝[>] (0 : ℝ))
      (𝓝 (h3SpectralScalarRawFourierL2 (U₀ j))) at hBase
    simpa only [L₀, hAtZero] using hBase
  have hStrict : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      t ∈ Set.Ioo (0 : ℝ) T := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hT)] with t ht0 htT
    exact ⟨ht0, htT⟩
  have hFourierAgreement :
      (fun t : ℝ => h3SpectralScalarRawFourierL2 (F t j))
        =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => h3ScalarFourierL2
        (h3AuditActualPhysicalZeroJetL2Total hH3 j t)) := by
    filter_upwards [hStrict] with t ht
    exact h3Audit_actualRawFourier_eq_fourierPhysicalZeroJetL2 hH3 j t ht
  have hPhysicalFourier : Tendsto
      (fun t : ℝ => h3ScalarFourierL2
        (h3AuditActualPhysicalZeroJetL2Total hH3 j t))
      (𝓝[>] (0 : ℝ)) (𝓝 (h3ScalarFourierL2 L₀)) :=
    hRaw.congr' hFourierAgreement
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hNear := (Metric.tendsto_nhds.mp hPhysicalFourier) ε hε
  filter_upwards [hNear] with t ht
  simpa only [L₀, dist_h3ScalarFourierL2] using ht

/-- The corresponding H³ energy limit is the actual physical initial
energy, not merely the spectral energy of a potentially unrelated U₀. -/
theorem h3Audit_compatibleInitialPhysicalMild_energyRightLimit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T A b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A)
    (hData : H3AuditInitialPhysicalEnergyMildDataAt hH3 U₀ hA hU₀ b)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (hCompatible : U₀ = velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0) :
    Tendsto (velocityH3EnergyAt u)
      (𝓝[>] (0 : ℝ)) (𝓝 (velocityH3EnergyAt u 0)) := by
  apply h3Audit_initialPhysicalEnergyMildDataAt_energyRightLimit_of_compatibleZero
    hH3 U₀ hA hU₀ hData
  rw [hCompatible]
  exact (one_add_h3SpectralVelocitySquareEnergy_velocityH3SpectralStateAt_eq
    hFourier0).symm

/-- Precisely compatible initial physical mild data. The only extra bridge
relative to the previous mild-data interface is the equality between the
mild datum and the *actual* physical old velocity's H³ Fourier state at zero. -/
def H3AuditInitialPhysicalEnergyMildZeroCompatibleData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (U₀ : H3SpectralVelocityState) (A : ℝ)
    (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A) (b : ℝ),
    H3AuditInitialPhysicalEnergyMildDataAt hH3 U₀ hA hU₀ b ∧
    U₀ = velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0

/-- The mild equation plus *actual zero-time compatibility* supplies the
minimal physical right-trace and energy upper-bound interface with no
additional physical L²-continuity, FTC, or signed-transport hypothesis. -/
theorem h3Audit_initialMildZeroCompatible_implies_physicalL2AndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildZeroCompatibleData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, U₀, A, hA, hU₀,
    b, hMild, hCompatible⟩ := hData
  have hT : 0 < T :=
    (Classical.choose_spec hH3.navier_stokes).positive_terminal
  have hEnergy :=
    h3Audit_compatibleInitialPhysicalMild_energyRightLimit
      hH3 U₀ hA hU₀ hMild hInt0 hMeas0 hFourier0 hCompatible
  have hTrace :=
    h3Audit_initialPhysicalEnergyMildDataAt_fullStrongH3Trace
      hH3 U₀ hA hU₀ hMild
  refine ⟨hInt0, hMeas0, hFourier0, ?_, ?_⟩
  · intro ε hε
    exact hEnergy.eventually (Iio_mem_nhds (by linarith))
  · intro j
    exact h3Audit_compatibleInitialStrongH3Trace_physicalL2RightTrace
      hH3 hT hInt0 hMeas0 hFourier0 U₀ hCompatible hTrace j

/-- Initial mild data with genuine physical zero-value compatibility gives
the strong initial H³ trace through the independent physical Plancherel route. -/
theorem h3Audit_initialMildZeroCompatible_strongH3Trace_via_physicalL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildZeroCompatibleData hH3) :
    ∃ U₀ : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
  have hT : 0 < T :=
    (Classical.choose_spec hH3.navier_stokes).positive_terminal
  exact h3Audit_initialPhysicalZeroJetL2AndEnergyUpper_implies_strongH3Trace
    hH3 hT
    (h3Audit_initialMildZeroCompatible_implies_physicalL2AndEnergyUpper
      hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
