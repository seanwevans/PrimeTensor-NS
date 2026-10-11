import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialScalarWeakSequenceDerivative

/-!
# Initial datum identification from compact-test cluster subsequences

Once an actual old velocity agrees on an initial positive interval with the
canonical selected H³ mild solution, the old velocity has an already proved
strong spectral H³ right trace. Its canonical real physical L² decoder also
has a strong right limit.

To identify that limit with the *prescribed* old velocity at time zero, we do
not need a scalar weak FTC equation, a scalar derivative, a temporal L¹ source,
or even full compact-test convergence. For each physical component and each
compact smooth scalar test, it is enough that SOME (test-dependent) sequence of
positive times converges to zero and its scalar pairing converges to the
prescribed initial pairing. The strong physical L² limit has the same pairing
limit along every such sequence. Density of compact tests then identifies the
physical limit with the prescribed initial state.

The canonical old/selected overlap and the testwise initial cluster property
are still explicit PDE-side assumptions. Neither is derived merely from
open-time Navier--Stokes admissibility. The independent terminal vorticity
strong H³ endpoint remains a separate hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace

noncomputable section

/-- Identify a strong scalar physical L² right limit using only one compact-test
right cluster sequence per test. Sequences may depend on the test. -/
theorem h3Audit_initialStrongL2Limit_identified_by_compactSubsequences
    (F : ℝ → H3ScalarL2)
    (L L₀ : H3ScalarL2)
    (hStrong : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hSubseq : ∀ φ : H3WeakTestFunction,
      ∃ τ : ℕ → ℝ,
        Tendsto τ atTop (𝓝[>] (0 : ℝ)) ∧
        Tendsto
          (fun n : ℕ =>
            inner ℝ (h3WeakTestFunctionPhysicalL2 φ) (F (τ n)))
          atTop
          (𝓝 (inner ℝ (h3WeakTestFunctionPhysicalL2 φ) L₀))) :
    L = L₀ := by
  apply h3ScalarL2_eq_of_weakTest_inner_eq_orderOne
  intro φ
  obtain ⟨τ, hτ, hInitial⟩ := hSubseq φ
  have hPairContinuous :
      Continuous (fun z : H3ScalarL2 =>
        inner ℝ (h3WeakTestFunctionPhysicalL2 φ) z) :=
    continuous_const.inner continuous_id
  have hDirect :=
    hPairContinuous.continuousAt.tendsto.comp hStrong
  have hAlong :
      Tendsto
        (fun n : ℕ =>
          inner ℝ (h3WeakTestFunctionPhysicalL2 φ) (F (τ n)))
        atTop
        (𝓝 (inner ℝ (h3WeakTestFunctionPhysicalL2 φ) L)) := by
    simpa only [Function.comp_def] using hDirect.comp hτ
  exact tendsto_nhds_unique hAlong hInitial

/-- A strong initial spectral H³ trace and compact-test initial *cluster*
values imply the genuine physical strong L² right trace. No derivative or
integral source is involved. -/
theorem h3Audit_initialStrongSpectralTrace_and_compactSubsequences_implies_physicalL2Trace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (U₀ : H3SpectralVelocityState)
    (hTrace : Tendsto (h3AuditActualSpectralVelocityTotal hH3)
      (𝓝[>] (0 : ℝ)) (𝓝 U₀))
    (hSubseq : ∀ (j : Fin 3) (φ : H3WeakTestFunction),
      ∃ τ : ℕ → ℝ,
        Tendsto τ atTop (𝓝[>] (0 : ℝ)) ∧
        Tendsto
          (fun n : ℕ => inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
            (h3AuditActualPhysicalZeroJetL2Total hH3 j (τ n)))
          atTop
          (𝓝 (inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
            (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j))))) :
    ∀ j : Fin 3,
      Tendsto (h3AuditActualPhysicalZeroJetL2Total hH3 j)
        (𝓝[>] (0 : ℝ))
        (𝓝 (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j))) := by
  intro j
  let L : H3ScalarL2 :=
    h3FromFourierRealL2 (h3SpectralScalarDecodeRealL2 (U₀ j))
  let L₀ : H3ScalarL2 :=
    velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)
  have hDecoded :
      Tendsto (h3AuditActualPhysicalZeroJetL2Total hH3 j)
        (𝓝[>] (0 : ℝ)) (𝓝 L) :=
    h3Audit_initialStrongSpectralTrace_physicalDecodeRightLimit
      hH3 hT U₀ hTrace j
  have hIdentify : L = L₀ :=
    h3Audit_initialStrongL2Limit_identified_by_compactSubsequences
      (h3AuditActualPhysicalZeroJetL2Total hH3 j)
      L L₀ hDecoded (hSubseq j)
  simpa only [hIdentify] using hDecoded

/-- Canonical old/selected initial overlap and a *testwise compact weak
cluster* initial condition. The temporal source and derivative obligations of
the preceding scalar FTC branch have been removed entirely from this route. -/
def H3AuditInitialCanonicalOverlapCompactSubsequenceData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (U₀ : H3SpectralVelocityState) (A : ℝ)
    (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A) (b : ℝ),
    H3AuditInitialCanonicalMildOverlapAt hH3 U₀ hA hU₀ b ∧
    ∀ (j : Fin 3) (φ : H3WeakTestFunction),
      ∃ τ : ℕ → ℝ,
        Tendsto τ atTop (𝓝[>] (0 : ℝ)) ∧
        Tendsto
          (fun n : ℕ => inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
            (h3AuditActualPhysicalZeroJetL2Total hH3 j (τ n)))
          atTop
          (𝓝 (inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
            (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j))))

/-- The compact initial-value right trace is a theorem rather than a premise:
selected mild overlap supplies the strong L² limit and compact test cluster
sequences identify it with the prescribed old physical initial state. -/
theorem h3Audit_initialCanonicalCompactSubsequence_implies_compactInitialData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalOverlapCompactSubsequenceData hH3) :
    H3AuditInitialCanonicalOverlapCompactInitialData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, U₀, A, hA, hU₀,
    b, hOverlap, hSubseq⟩ := hData
  have hT : 0 < T := lt_trans hOverlap.1 hOverlap.2.1
  have hTrace :=
    h3Audit_initialCanonicalOverlap_fullStrongH3Trace
      hH3 U₀ hA hU₀ hOverlap
  have hPhysical :=
    h3Audit_initialStrongSpectralTrace_and_compactSubsequences_implies_physicalL2Trace
      hH3 hT hInt0 hMeas0 U₀ hTrace hSubseq
  refine ⟨hInt0, hMeas0, hFourier0, U₀, A, hA, hU₀,
    b, hOverlap, ?_⟩
  intro j φ
  have hPairContinuous :
      Continuous (fun z : H3ScalarL2 =>
        inner ℝ (h3WeakTestFunctionPhysicalL2 φ) z) :=
    continuous_const.inner continuous_id
  exact hPairContinuous.continuousAt.tendsto.comp (hPhysical j)

/-- No scalar weak source or time derivative is needed to establish the
actual physical initial L² trace and H³ energy upper condition. -/
theorem h3Audit_initialCanonicalCompactSubsequence_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalOverlapCompactSubsequenceData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact
    h3Audit_initialCanonicalCompactOverlap_implies_physicalZeroJetAndEnergyUpper
      hH3
      (h3Audit_initialCanonicalCompactSubsequence_implies_compactInitialData
        hH3 hData)

/-- This independent terminal-side conclusion is still conditional on the
actual physical vorticity strong H³ endpoint. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialCanonicalCompactSubsequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalOverlapCompactSubsequenceData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact
    h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialCanonicalCompactOverlap
      hH3 hClass i hPhysical
      (h3Audit_initialCanonicalCompactSubsequence_implies_compactInitialData
        hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
