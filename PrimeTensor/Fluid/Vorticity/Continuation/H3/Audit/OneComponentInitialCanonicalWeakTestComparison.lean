import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialCanonicalCompactSubsequence
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Realizable.Decoder.Injective

/-!
# Canonical initial overlap from physical compact weak-test comparison

The old/selected initial H³ spectral overlap is an unusually strong hypothesis.
This module replaces it by exact physical L² pairings against the project's
compact smooth scalar tests, with the selected mild solution launched from
THE ACTUAL encoded H³ datum at zero.

The proof uses already-established density of compact smooth physical weak
tests, the exact old spectral/physical L² decoder, realizability of both the
actual old encoder and the canonical selected restart, and injectivity of the
real decoder on realizable H³ states. Thus equal compact weak pairings at an
interior time identify the FULL weighted Fourier H³ state at that time.

The PDE-side weak-test comparison remains an EXPLICIT hypothesis. No
Navier--Stokes weak--strong uniqueness or initial-time PDE theorem is asserted
here. The strong actual-vorticity terminal endpoint is also independent.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace

noncomputable section

/-- Physical compact weak tests at one strict positive time determine equality
of actual-old and canonical-selected weighted H³ spectra, provided the
selected solution was launched from the ACTUAL encoded H³ initial datum. -/
theorem h3Audit_initialCanonicalWeakTestComparison_fullVelocity_eq_selected
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T A : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (hA : 0 < A)
    (hU₀ : ‖velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0‖ ≤ A)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htR : t ≤ h3FinHeatLerayRestartRadius 1 A)
    (hWeak : ∀ (j : Fin 3) (φ : H3WeakTestFunction),
      inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
        (h3AuditActualPhysicalZeroJetL2Total hH3 j t) =
      inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
        (h3FromFourierRealL2 (h3SpectralScalarDecodeRealL2
          ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            (one_pos : (0 : ℝ) < 1)
            (velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0)
            hA hU₀ t) j)))) :
    h3AuditActualSpectralVelocityTotal hH3 t =
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        (one_pos : (0 : ℝ) < 1)
        (velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0)
        hA hU₀ t := by
  let U₀ : H3SpectralVelocityState :=
    velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0
  let W : H3SpectralVelocityState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1) U₀ hA hU₀ t
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t ht
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes ht
  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes ht hInt
  let q : Set.Icc (0 : ℝ) (h3FinHeatLerayRestartRadius 1 A) :=
    ⟨t, ht.1.le, htR⟩
  have hSelectedRealizable : H3SpectralVelocityRealizable W := by
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_encoded_realizable
        (one_pos : (0 : ℝ) < 1) hFourier0 hA hU₀ q
  rw [h3AuditActualSpectralVelocityTotal_eq_at hH3 t ht]
  change velocityH3SpectralStateAt u t hInt hMeas hFourier = W
  funext j
  have hOldPhysical :
      h3FromFourierRealL2
          (h3SpectralScalarDecodeRealL2
            ((velocityH3SpectralStateAt u t hInt hMeas hFourier) j)) =
        h3AuditActualPhysicalZeroJetL2Total hH3 j t := by
    have h :=
      h3Audit_actualPositivePhysicalZeroJet_eq_spectralRealDecode hH3 t ht j
    rw [h3AuditActualSpectralVelocityTotal_eq_at hH3 t ht] at h
    exact h
  have hPhysicalEq :
      h3FromFourierRealL2
          (h3SpectralScalarDecodeRealL2
            ((velocityH3SpectralStateAt u t hInt hMeas hFourier) j)) =
        h3FromFourierRealL2
          (h3SpectralScalarDecodeRealL2 (W j)) := by
    apply h3ScalarL2_eq_of_weakTest_inner_eq_orderOne
    intro φ
    rw [hOldPhysical]
    exact hWeak j φ
  have hDecoderEq :
      h3SpectralScalarDecodeRealL2
          ((velocityH3SpectralStateAt u t hInt hMeas hFourier) j) =
        h3SpectralScalarDecodeRealL2 (W j) := by
    have h := congrArg h3ToFourierRealL2 hPhysicalEq
    simpa only [h3ToFourierRealL2_h3FromFourierRealL2] using h
  exact h3SpectralScalarDecodeRealL2_eq_imp_eq_of_realizable
    (velocityH3SpectralScalarAt_realizable hFourier j)
    (hSelectedRealizable j) hDecoderEq

/-- PDE-facing weak--strong comparison on one initial physical-time interval.
The old H³ spectral state is not postulated to equal the selected H³ state:
only their *physical compact weak-test pairings* must agree. -/
def H3AuditInitialCanonicalCompactWeakComparisonAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T A : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {hInt0 : VelocityH3IntegrableAt u (0 : ℝ)}
    {hMeas0 : VelocityH3MeasurableAt u (0 : ℝ)}
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (hA : 0 < A)
    (hU₀ : ‖velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0‖ ≤ A)
    (b : ℝ) : Prop :=
  0 < b ∧ b < T ∧
  b ≤ h3FinHeatLerayRestartRadius 1 A ∧
  ∀ (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T),
    t < b → ∀ (j : Fin 3) (φ : H3WeakTestFunction),
      inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
        (h3AuditActualPhysicalZeroJetL2Total hH3 j t) =
      inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
        (h3FromFourierRealL2 (h3SpectralScalarDecodeRealL2
          ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            (one_pos : (0 : ℝ) < 1)
            (velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0)
            hA hU₀ t) j)))

/-- Spatially weak comparison identifies the entire canonical H³ old/selected
overlap, by Hilbert test density and REAL decoder injectivity. -/
theorem h3Audit_initialCanonicalCompactWeakComparisonAt_implies_overlap
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T A b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (hA : 0 < A)
    (hU₀ : ‖velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0‖ ≤ A)
    (hWeak : H3AuditInitialCanonicalCompactWeakComparisonAt
      hH3 hFourier0 hA hU₀ b) :
    H3AuditInitialCanonicalMildOverlapAt hH3
      (velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0)
      hA hU₀ b := by
  obtain ⟨hb, hbT, hbR, hCompare⟩ := hWeak
  refine ⟨hb, hbT, hbR, ?_⟩
  intro p t ht htb
  have htR : t ≤ h3FinHeatLerayRestartRadius 1 A :=
    (le_of_lt htb).trans hbR
  have hWhole :=
    h3Audit_initialCanonicalWeakTestComparison_fullVelocity_eq_selected
      hH3 hInt0 hMeas0 hFourier0 hA hU₀ t ht htR
      (hCompare t ht htb)
  have hCoord :=
    congrFun hWhole
      (h3ClassicalizationFinOfAxis
        (h3TerminalComplementComponentAxisForPair p))
  rw [h3AuditActualSpectralVelocityTotal_eq_at hH3 t ht] at hCoord
  exact (h3AuditActualSpectralVelocityAt_complement hH3 p t ht).symm.trans
    hCoord

/-- All data in the comparison are physical at zero: U₀ is constructed from
actual u(0), not supplied as an unrelated spectral initial datum. -/
def H3AuditInitialCanonicalCompactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (A : ℝ) (hA : 0 < A)
    (hU₀ : ‖velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0‖ ≤ A)
    (b : ℝ),
    H3AuditInitialCanonicalCompactWeakComparisonAt hH3 hFourier0 hA hU₀ b

/-- Physical compact weak-test comparison is sufficient for the actual
initial L² trace and H³ energy upper condition, without a separately
assumed compact initial distributional subsequence. -/
theorem h3Audit_initialCanonicalCompactWeakComparison_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalCompactWeakComparisonData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀, b, hWeak⟩ := hData
  let U₀ : H3SpectralVelocityState :=
    velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0
  have hOverlap : H3AuditInitialCanonicalMildOverlapAt hH3 U₀ hA hU₀ b :=
    h3Audit_initialCanonicalCompactWeakComparisonAt_implies_overlap
      hH3 hInt0 hMeas0 hFourier0 hA hU₀ hWeak
  have hTrace :=
    h3Audit_initialCanonicalOverlap_fullStrongH3Trace
      hH3 U₀ hA hU₀ hOverlap
  have hT : 0 < T := lt_trans hOverlap.1 hOverlap.2.1
  have hPhysical : ∀ j : Fin 3,
      Tendsto (h3AuditActualPhysicalZeroJetL2Total hH3 j)
        (𝓝[>] (0 : ℝ))
        (𝓝 (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j))) := by
    intro j
    have hDecoded :=
      h3Audit_initialStrongSpectralTrace_physicalDecodeRightLimit
        hH3 hT U₀ hTrace j
    have hZero :
        h3FromFourierRealL2 (h3SpectralScalarDecodeRealL2 (U₀ j)) =
          velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j) := by
      exact
        h3FromFourierRealL2_h3SpectralVelocityDecodeRealL2_velocityH3SpectralStateAt_eq
          hFourier0 j
    simpa only [hZero] using hDecoded
  have hEnergy : Tendsto (velocityH3EnergyAt u)
      (𝓝[>] (0 : ℝ)) (𝓝 (velocityH3EnergyAt u 0)) := by
    have hSpec :=
      h3Audit_initialStrongH3Trace_energyRightLimit_toSpectral
        hH3 hT U₀ hTrace
    have hZero :
        1 + h3SpectralVelocitySquareEnergy U₀ =
          velocityH3EnergyAt u 0 :=
      one_add_h3SpectralVelocitySquareEnergy_velocityH3SpectralStateAt_eq
        hFourier0
    simpa only [hZero] using hSpec
  refine ⟨hInt0, hMeas0, hFourier0, ?_, hPhysical⟩
  intro ε hε
  exact hEnergy.eventually
    (Iio_mem_nhds (by linarith :
      velocityH3EnergyAt u 0 < velocityH3EnergyAt u 0 + ε))

/-- The independent terminal-side full-time transverse estimate under the
physical compact weak-test old/selected comparison at initial time. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialCanonicalCompactWeakComparison
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalCompactWeakComparisonData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact
    h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialPhysicalZeroJetL2
      hH3 hClass i hPhysical
      (h3Audit_initialCanonicalCompactWeakComparison_implies_physicalZeroJetAndEnergyUpper
        hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
