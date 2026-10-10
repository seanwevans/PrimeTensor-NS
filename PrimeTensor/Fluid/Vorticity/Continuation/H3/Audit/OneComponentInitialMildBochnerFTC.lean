import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialMildL2Identification
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Initial physical L² trace from an integrable Bochner time source

The initial mild/H³ trace does not require a bounded physical L² temporal
source. An interval-integrable Bochner source with the exact physical
initial-time evolution identity suffices: its primitive is continuous at
zero and hence vanishes as t tends to zero from above.

Combining this elementary absolute-continuity argument with the existing
strong H³ mild trace and initial Fourier injectivity theorem identifies the
mild datum with the actual prescribed initial velocity. No H³ energy FTC or
uniform initial temporal source estimate is added.

The physical integral identity and its initial-time Bochner integrability are
still explicit initial-value assumptions. They are NOT derived from a PDE
that is only specified on the open interval (0,T). This theorem also does
not remove the separate terminal vorticity endpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval

noncomputable section

/-- A Bochner-integrable source on a single initial interval has a primitive
which converges to zero from the right, without an L∞ temporal bound. -/
theorem h3Audit_initialBochnerPrimitive_tendsto_zero
    (V : ℝ → H3ScalarL2) (b : ℝ) (hb : 0 < b)
    (hV : IntervalIntegrable V volume 0 b) :
    Tendsto (fun t : ℝ => ∫ s in (0 : ℝ)..t, V s)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : H3ScalarL2)) := by
  have hContinuousU :
      ContinuousOn
        (fun t : ℝ => ∫ s in (0 : ℝ)..t, V s)
        (Set.uIcc (0 : ℝ) b) := by
    exact intervalIntegral.continuousOn_primitive_interval'
      hV left_mem_uIcc
  have hContinuous :
      ContinuousOn
        (fun t : ℝ => ∫ s in (0 : ℝ)..t, V s)
        (Set.Icc (0 : ℝ) b) := by
    simpa only [Set.uIcc_of_le hb.le] using hContinuousU
  have hRight :=
    h3Audit_rightTendsto_of_continuousOn_initialIcc
      (fun t : ℝ => ∫ s in (0 : ℝ)..t, V s)
      hb hContinuous
  simpa using hRight

/-- The exact physical L²-valued evolution identity with any Bochner
integrable source forces the genuine initial L² right trace. Boundedness of
that source and any separate energy estimate are unnecessary here. -/
theorem h3Audit_initialBochnerFTC_implies_physicalL2RightTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (b : ℝ) (hb : 0 < b)
    (V : Fin 3 → ℝ → H3ScalarL2)
    (hIntegrable : ∀ j : Fin 3, IntervalIntegrable (V j) volume 0 b)
    (hFTC : ∀ (j : Fin 3) (t : ℝ),
      t ∈ Set.Ioo (0 : ℝ) b →
      h3AuditActualPhysicalZeroJetL2Total hH3 j t -
        velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j) =
        ∫ s in (0 : ℝ)..t, V j s) :
    ∀ j : Fin 3,
      Tendsto (h3AuditActualPhysicalZeroJetL2Total hH3 j)
        (𝓝[>] (0 : ℝ))
        (𝓝 (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j))) := by
  intro j
  let L₀ : H3ScalarL2 :=
    velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)
  let G : ℝ → H3ScalarL2 :=
    h3AuditActualPhysicalZeroJetL2Total hH3 j
  have hPrim :
      Tendsto (fun t : ℝ => ∫ s in (0 : ℝ)..t, V j s)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : H3ScalarL2)) :=
    h3Audit_initialBochnerPrimitive_tendsto_zero
      (V j) b hb (hIntegrable j)
  have hStrict : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      t ∈ Set.Ioo (0 : ℝ) b := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hb)] with t ht0 htb
    exact ⟨ht0, htb⟩
  have hEq :
      (fun t : ℝ => G t - L₀) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => ∫ s in (0 : ℝ)..t, V j s) := by
    filter_upwards [hStrict] with t ht
    exact hFTC j t ht
  have hSub : Tendsto (fun t : ℝ => G t - L₀)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : H3ScalarL2)) :=
    hPrim.congr' hEq.symm
  have hNorm : Tendsto (fun t : ℝ => ‖G t - L₀‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hNorm' := continuous_norm.continuousAt.tendsto.comp hSub
    change Tendsto (fun t : ℝ => ‖G t - L₀‖)
      (𝓝[>] (0 : ℝ)) (𝓝 ‖(0 : H3ScalarL2)‖) at hNorm'
    simpa only [norm_zero] using hNorm'
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hNorm

/-- Replace the assumed physical L² initial trace in the mild-data contract
with an initial Bochner-integrable physical source and its true integral
identity on one nonempty initial interval. -/
def H3AuditInitialPhysicalEnergyMildBochnerFTCData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (U₀ : H3SpectralVelocityState) (A : ℝ)
    (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A) (b : ℝ)
    (V : Fin 3 → ℝ → H3ScalarL2),
    H3AuditInitialPhysicalEnergyMildDataAt hH3 U₀ hA hU₀ b ∧
    (∀ j : Fin 3, IntervalIntegrable (V j) volume 0 b) ∧
    (∀ (j : Fin 3) (t : ℝ), t ∈ Set.Ioo (0 : ℝ) b →
      h3AuditActualPhysicalZeroJetL2Total hH3 j t -
        velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j) =
        ∫ s in (0 : ℝ)..t, V j s)

/-- One Bochner-integrable initial velocity evolution source closes the
physical L² trace obligation required by the previous mild theorem. -/
theorem h3Audit_initialMildBochnerFTC_implies_L2TraceData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildBochnerFTCData hH3) :
    H3AuditInitialPhysicalEnergyMildL2TraceData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, U₀, A, hA, hU₀, b,
    V, hMild, hIntegrable, hFTC⟩ := hData
  have hb : 0 < b := by
    obtain ⟨_P, hb, _hRest⟩ := hMild
    exact hb
  refine ⟨hInt0, hMeas0, hFourier0, U₀, A, hA, hU₀,
    b, hMild, ?_⟩
  exact h3Audit_initialBochnerFTC_implies_physicalL2RightTrace
    hH3 hInt0 hMeas0 b hb V hIntegrable hFTC

/-- The actual initial physical L² Bochner evolution identifies the mild
initial state with the Fourier encoder of the prescribed physical datum. -/
theorem h3Audit_initialMildBochnerFTC_identifies_zeroSpectralDatum
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildBochnerFTCData hH3) :
    H3AuditInitialPhysicalEnergyMildZeroCompatibleData hH3 := by
  exact h3Audit_initialMildL2Trace_implies_zeroCompatibleData
    hH3 (h3Audit_initialMildBochnerFTC_implies_L2TraceData hH3 hData)

/-- No energy FTC is needed: spectral mild continuity and the zero datum
identification already yield the exact right H³ energy limit. -/
theorem h3Audit_initialMildBochnerFTC_energyRightLimit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildBochnerFTCData hH3) :
    Tendsto (velocityH3EnergyAt u)
      (𝓝[>] (0 : ℝ)) (𝓝 (velocityH3EnergyAt u 0)) := by
  exact h3Audit_initialMildL2Trace_energyRightLimit
    hH3 (h3Audit_initialMildBochnerFTC_implies_L2TraceData hH3 hData)

/-- Both actual transverse velocity Sobolev time estimates are still
conditional on a separate strong terminal vorticity endpoint. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialMildBochnerFTC
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialPhysicalEnergyMildBochnerFTCData hH3) :
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
    (h3Audit_initialMildBochnerFTC_implies_L2TraceData hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
