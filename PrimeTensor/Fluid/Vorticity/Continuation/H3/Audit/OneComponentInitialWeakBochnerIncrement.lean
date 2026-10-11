import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialMildBochnerFTC
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Strong initial physical L² trace from weak initial data and interior Bochner evolution

The preceding initial Bochner criterion postulated a full initial-time FTC
identity. Here the evolution law is needed only between two *strictly positive*
times. An integrable Bochner source makes the actual physical velocity differ
from its primitive by a single constant over the initial interval. A weak
right L² trace identifies that constant with the prescribed initial velocity.
Thus strong L² right continuity follows without assuming it at t = 0.

The interior two-time evolution identities, local integrability, and weak
initial condition are explicit PDE-side obligations. Open-time H³ path
admissibility alone does not imply these initial-value conditions, nor is
any terminal endpoint proved.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval

noncomputable section

/-- Interior Bochner evolution plus a weak initial trace forces a *strong*
initial trace. The evolution identity is never applied with either time
argument equal to zero. -/
theorem h3Audit_weakInitialTrace_strong_of_positiveBochnerIncrements
    (F V : ℝ → H3ScalarL2) (L₀ : H3ScalarL2)
    (b : ℝ) (hb : 0 < b)
    (hV : IntervalIntegrable V volume 0 b)
    (hLocal : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      IntervalIntegrable V volume 0 t)
    (hIncrement : ∀ (s t : ℝ),
      s ∈ Set.Ioo (0 : ℝ) b →
      t ∈ Set.Ioo (0 : ℝ) b →
      F t - F s = ∫ r in s..t, V r)
    (hWeak : ∀ ψ : H3ScalarL2,
      Tendsto (fun t : ℝ => inner ℝ (F t) ψ)
        (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ L₀ ψ))) :
    Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 L₀) := by
  let q : ℝ := b / 2
  have hq : q ∈ Set.Ioo (0 : ℝ) b := by
    dsimp only [q]
    constructor <;> linarith
  let C : H3ScalarL2 := F q - ∫ r in (0 : ℝ)..q, V r
  have hPrimitive :
      Tendsto (fun t : ℝ => ∫ r in (0 : ℝ)..t, V r)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : H3ScalarL2)) :=
    h3Audit_initialBochnerPrimitive_tendsto_zero V b hb hV
  have hOn (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) b) :
      F t = C + ∫ r in (0 : ℝ)..t, V r := by
    have hInc := hIncrement q t hq ht
    have hInt :
        (∫ r in q..t, V r) =
          (∫ r in (0 : ℝ)..t, V r) -
          (∫ r in (0 : ℝ)..q, V r) :=
      (intervalIntegral.integral_interval_sub_left
        (hLocal t ht) (hLocal q hq)).symm
    rw [hInt] at hInc
    calc
      F t = (F t - F q) + F q := by abel
      _ = ((∫ r in (0 : ℝ)..t, V r) -
          (∫ r in (0 : ℝ)..q, V r)) + F q := by rw [hInc]
      _ = C + ∫ r in (0 : ℝ)..t, V r := by dsimp only [C]; abel
  have hStrict : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      t ∈ Set.Ioo (0 : ℝ) b := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hb)] with t ht0 htb
    exact ⟨ht0, htb⟩
  have hEq :
      F =ᶠ[𝓝[>] (0 : ℝ)]
        (fun t : ℝ => C + ∫ r in (0 : ℝ)..t, V r) := by
    filter_upwards [hStrict] with t ht
    exact hOn t ht
  have hC : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 C) := by
    have hPlus :
        Tendsto (fun t : ℝ => C + ∫ r in (0 : ℝ)..t, V r)
          (𝓝[>] (0 : ℝ)) (𝓝 (C + (0 : H3ScalarL2))) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => C)
        (𝓝[>] (0 : ℝ)) (𝓝 C)).add hPrimitive
    have hPlus' :
        Tendsto (fun t : ℝ => C + ∫ r in (0 : ℝ)..t, V r)
          (𝓝[>] (0 : ℝ)) (𝓝 C) := by
      simpa only [add_zero] using hPlus
    exact hPlus'.congr' hEq.symm
  have hInnerContinuous (ψ : H3ScalarL2) :
      Continuous (fun z : H3ScalarL2 => inner ℝ z ψ) := by
    exact continuous_id.inner continuous_const
  have hWeakC (ψ : H3ScalarL2) :
      inner ℝ C ψ = inner ℝ L₀ ψ := by
    exact tendsto_nhds_unique
      ((hInnerContinuous ψ).continuousAt.tendsto.comp hC)
      (hWeak ψ)
  have hZeroInner : inner ℝ (C - L₀) (C - L₀) = 0 := by
    rw [inner_sub_left]
    exact sub_eq_zero.mpr (hWeakC (C - L₀))
  have hNormSq : ‖C - L₀‖ ^ 2 = 0 := by
    simpa only [real_inner_self_eq_norm_sq] using hZeroInner
  have hNormZero : ‖C - L₀‖ = 0 := by
    nlinarith [norm_nonneg (C - L₀)]
  have hCeq : C = L₀ :=
    sub_eq_zero.mp (norm_eq_zero.mp hNormZero)
  simpa only [hCeq] using hC

/-- The old physical velocity has a strong zero-time trace under interior
Bochner increments and weak initial L² data. There is no zero-endpoint FTC
hypothesis and no uniform-in-time derivative bound. -/
theorem h3Audit_initialWeakBochnerIncrement_implies_physicalL2RightTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (b : ℝ) (hb : 0 < b)
    (V : Fin 3 → ℝ → H3ScalarL2)
    (hV : ∀ j : Fin 3, IntervalIntegrable (V j) volume 0 b)
    (hLocal : ∀ (j : Fin 3) (t : ℝ), t ∈ Set.Ioo (0 : ℝ) b →
      IntervalIntegrable (V j) volume 0 t)
    (hIncrement : ∀ (j : Fin 3) (s t : ℝ),
      s ∈ Set.Ioo (0 : ℝ) b → t ∈ Set.Ioo (0 : ℝ) b →
      h3AuditActualPhysicalZeroJetL2Total hH3 j t -
        h3AuditActualPhysicalZeroJetL2Total hH3 j s =
        ∫ r in s..t, V j r)
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
  exact h3Audit_weakInitialTrace_strong_of_positiveBochnerIncrements
    (h3AuditActualPhysicalZeroJetL2Total hH3 j) (V j)
    (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j))
    b hb (hV j) (hLocal j)
    (hIncrement j) (hWeak j)

/-- Actual mild data with a weak physical initial L² trace and a genuine
positive-time two-point Bochner evolution identity. The initial strong L²
trace and initial-time FTC identity are NOT assumed. -/
def H3AuditInitialPhysicalEnergyMildWeakBochnerIncrementData
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
      IntervalIntegrable (V j) volume 0 t) ∧
    (∀ (j : Fin 3) (s t : ℝ),
      s ∈ Set.Ioo (0 : ℝ) b → t ∈ Set.Ioo (0 : ℝ) b →
      h3AuditActualPhysicalZeroJetL2Total hH3 j t -
        h3AuditActualPhysicalZeroJetL2Total hH3 j s =
        ∫ r in s..t, V j r) ∧
    (∀ (j : Fin 3) (ψ : H3ScalarL2),
      Tendsto
        (fun t : ℝ =>
          inner ℝ (h3AuditActualPhysicalZeroJetL2Total hH3 j t) ψ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ
          (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)) ψ)))

/-- Weak initial condition plus interior L¹ evolution implies the previous
strong physical initial L² trace contract. -/
theorem h3Audit_initialMildWeakBochnerIncrement_implies_L2TraceData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildWeakBochnerIncrementData hH3) :
    H3AuditInitialPhysicalEnergyMildL2TraceData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, U₀, A, hA, hU₀, b,
    V, hMild, hV, hLocal, hIncrement, hWeak⟩ := hData
  have hb : 0 < b := by
    obtain ⟨_P, hb, _⟩ := hMild
    exact hb
  refine ⟨hInt0, hMeas0, hFourier0, U₀, A, hA, hU₀,
    b, hMild, ?_⟩
  exact h3Audit_initialWeakBochnerIncrement_implies_physicalL2RightTrace
    hH3 hInt0 hMeas0 b hb V hV hLocal hIncrement hWeak

/-- The mild spectral initial state equals the prescribed physical H³ datum
without assuming the initial spectral equality or an initial-endpoint FTC. -/
theorem h3Audit_initialMildWeakBochnerIncrement_identifies_initialSpectral
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildWeakBochnerIncrementData hH3) :
    H3AuditInitialPhysicalEnergyMildZeroCompatibleData hH3 := by
  exact h3Audit_initialMildL2Trace_implies_zeroCompatibleData
    hH3 (h3Audit_initialMildWeakBochnerIncrement_implies_L2TraceData hH3 hData)

/-- The actual H³ energy has the correct initial right limit. -/
theorem h3Audit_initialMildWeakBochnerIncrement_energyRightLimit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildWeakBochnerIncrementData hH3) :
    Tendsto (velocityH3EnergyAt u)
      (𝓝[>] (0 : ℝ)) (𝓝 (velocityH3EnergyAt u 0)) := by
  exact h3Audit_initialMildL2Trace_energyRightLimit
    hH3 (h3Audit_initialMildWeakBochnerIncrement_implies_L2TraceData hH3 hData)

/-- The existing two-component physical Sobolev criterion, retaining its
separate physical terminal-vorticity strong H³ endpoint hypothesis. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialMildWeakBochnerIncrement
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialPhysicalEnergyMildWeakBochnerIncrementData hH3) :
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
    (h3Audit_initialMildWeakBochnerIncrement_implies_L2TraceData hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
