import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialCompactWeakFTC
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPositiveStrongDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Initial scalar weak FTC from interior derivatives and one weak trace sequence

An exact initial-endpoint scalar FTC identity need not be postulated for every
positive time. It follows from a single L¹ scalar temporal source, its genuine
ordinary derivative identity at strictly positive times, and a weak initial
value identified along ONE sequence approaching zero from the right.

The interior FTC determines the pairing up to a constant of integration.
Integrability makes the initial primitive vanish; convergence of the pairing
along the initial sequence identifies that constant with the prescribed initial
value. No continuity, differentiability, or FTC at t=0 is assumed.

This is an initial-value reduction, NOT a derivation of the scalar derivative or
weak initial sequence from the project's open-time Navier--Stokes admissibility.
The canonical old/selected overlap and terminal physical vorticity endpoint
remain independent assumptions.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace

noncomputable section

/-- One globally interval-integrable real source restricts to every initial
subinterval, without a separate family of integrability assumptions. -/
theorem h3Audit_initialScalarIntervalIntegrable_of_global
    (g : ℝ → ℝ) (b : ℝ) (hb : 0 < b)
    (hg : IntervalIntegrable g volume 0 b)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) b) :
    IntervalIntegrable g volume 0 t := by
  apply hg.mono_set
  intro x hx
  have hxt : x ∈ Set.Icc (0 : ℝ) t := by
    simpa only [Set.uIcc_of_le ht.1.le] using hx
  have hxb : x ∈ Set.Icc (0 : ℝ) b :=
    ⟨hxt.1, hxt.2.trans ht.2.le⟩
  simpa only [Set.uIcc_of_le hb.le] using hxb

/-- Interior differentiability identifies all scalar increments without any
initial-endpoint regularity or integral equation at time zero. -/
theorem h3Audit_initialScalarInteriorDerivative_increments
    (F g : ℝ → ℝ) (b : ℝ) (hb : 0 < b)
    (hg : IntervalIntegrable g volume 0 b)
    (hDerivative : ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) b →
      HasDerivAt F (g x) x)
    (s t : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) b)
    (ht : t ∈ Set.Ioo (0 : ℝ) b) :
    F t - F s = ∫ r in s..t, g r := by
  have hSub : Set.uIcc s t ⊆ Set.uIcc (0 : ℝ) b := by
    intro x hx
    have hxb := h3Audit_positiveUnorderedInterval_subset_initial
      b s t hs ht hx
    simpa only [Set.uIcc_of_le hb.le] using hxb
  have hLocal : IntervalIntegrable g volume s t := hg.mono_set hSub
  have hFTC : (∫ r in s..t, g r) = F t - F s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx =>
        hDerivative x
          (h3Audit_positiveUnorderedInterval_strict b s t hs ht hx))
      hLocal
  exact hFTC.symm

/-- The only initial information needed beyond the positive-time scalar
ODE is identification of its value along one right-approaching sequence.
The full family of initial-time FTC identities is DERIVED. -/
theorem h3Audit_initialScalarWeakFTC_of_interiorDerivative_and_sequence
    (F g : ℝ → ℝ) (L₀ b : ℝ) (hb : 0 < b)
    (hg : IntervalIntegrable g volume 0 b)
    (hDerivative : ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) b →
      HasDerivAt F (g x) x)
    (τ : ℕ → ℝ)
    (hτ : Tendsto τ atTop (𝓝[>] (0 : ℝ)))
    (hInitialSequence : Tendsto (fun n : ℕ => F (τ n)) atTop (𝓝 L₀)) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      F t - L₀ = ∫ s in (0 : ℝ)..t, g s := by
  let a : ℝ := b / 2
  have ha : a ∈ Set.Ioo (0 : ℝ) b := by
    dsimp only [a]
    constructor <;> linarith
  let C : ℝ := F a - ∫ s in (0 : ℝ)..a, g s
  have hRepresentation : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      F t = C + ∫ s in (0 : ℝ)..t, g s := by
    intro t ht
    have hIncrement :=
      h3Audit_initialScalarInteriorDerivative_increments
        F g b hb hg hDerivative a t ha ht
    have hSplit :
        (∫ s in a..t, g s) =
          (∫ s in (0 : ℝ)..t, g s) -
          (∫ s in (0 : ℝ)..a, g s) :=
      (intervalIntegral.integral_interval_sub_left
        (h3Audit_initialScalarIntervalIntegrable_of_global g b hb hg t ht)
        (h3Audit_initialScalarIntervalIntegrable_of_global g b hb hg a ha)).symm
    rw [hSplit] at hIncrement
    dsimp only [C]
    linarith only [hIncrement]
  have hPrimitive := h3Audit_initialScalarWeakPrimitive_tendsto_zero g b hb hg
  have hRepresentationLimit :
      Tendsto (fun t : ℝ => C + ∫ s in (0 : ℝ)..t, g s)
        (𝓝[>] (0 : ℝ)) (𝓝 C) := by
    have h :=
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => C)
        (𝓝[>] (0 : ℝ)) (𝓝 C)).add hPrimitive
    simpa only [add_zero] using h
  have hStrict : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      t ∈ Set.Ioo (0 : ℝ) b := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hb)] with t hPos hBefore
    exact ⟨hPos, hBefore⟩
  have hEventually : F =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => C + ∫ s in (0 : ℝ)..t, g s) := by
    filter_upwards [hStrict] with t ht
    exact hRepresentation t ht
  have hF : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 C) :=
    hRepresentationLimit.congr' hEventually.symm
  have hSeq : Tendsto (fun n : ℕ => F (τ n)) atTop (𝓝 C) := by
    simpa only [Function.comp_def] using hF.comp hτ
  have hC : C = L₀ := tendsto_nhds_unique hSeq hInitialSequence
  intro t ht
  have hAt := hRepresentation t ht
  rw [hC] at hAt
  linarith only [hAt]

/-- Derive the project-native compact-test weak initial FTC from strong
positive-time *scalar pairings* and only one prescribed weak test sequence.
The test-dependent temporal sources need not have any common L² bound. -/
theorem h3Audit_actualInitialScalarWeakFTC_of_interiorDerivative_and_sequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (b : ℝ) (hb : 0 < b)
    (hDerivativeSequence : ∀ (j : Fin 3) (φ : H3WeakTestFunction),
      ∃ (g : ℝ → ℝ) (τ : ℕ → ℝ),
        IntervalIntegrable g volume 0 b ∧
        (∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) b →
          HasDerivAt
            (fun t : ℝ => inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
              (h3AuditActualPhysicalZeroJetL2Total hH3 j t)) (g x) x) ∧
        Tendsto τ atTop (𝓝[>] (0 : ℝ)) ∧
        Tendsto (fun n : ℕ => inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
          (h3AuditActualPhysicalZeroJetL2Total hH3 j (τ n)))
          atTop
          (𝓝 (inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
            (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j))))) :
    ∀ (j : Fin 3) (φ : H3WeakTestFunction),
      ∃ g : ℝ → ℝ,
        IntervalIntegrable g volume 0 b ∧
        ∀ (t : ℝ), t ∈ Set.Ioo (0 : ℝ) b →
          inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
              (h3AuditActualPhysicalZeroJetL2Total hH3 j t) -
            inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
              (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)) =
              ∫ s in (0 : ℝ)..t, g s := by
  intro j φ
  obtain ⟨g, τ, hg, hDerivative, hτ, hSeq⟩ :=
    hDerivativeSequence j φ
  refine ⟨g, hg, ?_⟩
  exact h3Audit_initialScalarWeakFTC_of_interiorDerivative_and_sequence
    (fun t : ℝ => inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
      (h3AuditActualPhysicalZeroJetL2Total hH3 j t))
    g
    (inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
      (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)))
    b hb hg hDerivative τ hτ hSeq

/-- PDE-facing contract: positive-time scalar test-pairing derivatives,
L¹ temporal sources, and a single right-approaching initial distributional
sequence; NO initial-time scalar FTC family is postulated. -/
def H3AuditInitialCanonicalOverlapScalarWeakSequenceDerivativeData
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
      ∃ (g : ℝ → ℝ) (τ : ℕ → ℝ),
        IntervalIntegrable g volume 0 b ∧
        (∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) b →
          HasDerivAt
            (fun t : ℝ => inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
              (h3AuditActualPhysicalZeroJetL2Total hH3 j t)) (g x) x) ∧
        Tendsto τ atTop (𝓝[>] (0 : ℝ)) ∧
        Tendsto (fun n : ℕ => inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
          (h3AuditActualPhysicalZeroJetL2Total hH3 j (τ n)))
          atTop
          (𝓝 (inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
            (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j))))

/-- Positive-time scalar differentiation plus ONE weak initial sequence
closes the formerly assumed whole initial-time scalar weak FTC identity. -/
theorem h3Audit_initialScalarWeakSequenceDerivative_implies_scalarWeakFTCData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalOverlapScalarWeakSequenceDerivativeData hH3) :
    H3AuditInitialCanonicalOverlapScalarWeakFTCData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, U₀, A, hA, hU₀,
    b, hOverlap, hDerivativeSequence⟩ := hData
  have hb : 0 < b := hOverlap.1
  exact ⟨hInt0, hMeas0, hFourier0, U₀, A, hA, hU₀,
    b, hOverlap,
    h3Audit_actualInitialScalarWeakFTC_of_interiorDerivative_and_sequence
      hH3 hInt0 hMeas0 b hb hDerivativeSequence⟩

/-- Initial strong physical L² convergence and correct H³ energy right
continuity without postulating initial-time scalar FTC identities. -/
theorem h3Audit_initialScalarWeakSequenceDerivative_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalOverlapScalarWeakSequenceDerivativeData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialCanonicalScalarWeakFTC_implies_physicalZeroJetAndEnergyUpper
    hH3
    (h3Audit_initialScalarWeakSequenceDerivative_implies_scalarWeakFTCData
      hH3 hData)

/-- Full-time transverse physical homogeneous 3/2 estimates, still
conditional on the separate strong terminal physical-vorticity endpoint. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialScalarWeakSequenceDerivative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalOverlapScalarWeakSequenceDerivativeData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialCanonicalScalarWeakFTC
    hH3 hClass i hPhysical
    (h3Audit_initialScalarWeakSequenceDerivative_implies_scalarWeakFTCData
      hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
