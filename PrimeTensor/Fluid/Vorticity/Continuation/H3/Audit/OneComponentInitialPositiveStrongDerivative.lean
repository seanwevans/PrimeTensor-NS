import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialWeakBochnerIncrement
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Interior physical L² Bochner evolution from genuine strong derivatives

The previous weak-to-strong initial L² theorem required exact two-time
Bochner increment identities AND separately supplied local integrability
of the temporal source on every positive subinterval.

Both are consequences of just two positive-time analytical inputs:

* a single Bochner-integrable L² temporal source on one interval `(0,b)`;
* the **actual** physical zeroth-jet path has that source as its strong
  `HasDerivAt` derivative at every strictly positive time in `(0,b)`.

The ordinary unordered-interval FTC handles both orientations `s..t`, and
restriction of the original `IntervalIntegrable V volume 0 b` proves all
subinterval integrability. No derivative or continuity of the actual old
velocity at `t=0` is assumed. The weak initial L² trace and actual old
physical mild representation remain explicit hypotheses. This module does
not derive the strong temporal L² derivative from the pointwise NS PDE;
that PDE-to-Hilbert derivative bridge is the next genuine obligation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval

noncomputable section

/-- The single Bochner `L¹` bound on `(0,b)` yields integrability on each
`0..t` with `0 < t < b`; no extra local-integrability family is needed. -/
theorem h3Audit_initialIntervalIntegrable_of_globalBochner
    (V : ℝ → H3ScalarL2) (b : ℝ) (hb : 0 < b)
    (hV : IntervalIntegrable V volume 0 b)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) b) :
    IntervalIntegrable V volume 0 t := by
  apply hV.mono_set
  intro x hx
  have hx' : x ∈ Set.Icc (0 : ℝ) t := by
    simpa only [Set.uIcc_of_le ht.1.le] using hx
  have hxb : x ∈ Set.Icc (0 : ℝ) b :=
    ⟨hx'.1, hx'.2.trans ht.2.le⟩
  simpa only [Set.uIcc_of_le hb.le] using hxb

/-- Both arbitrarily ordered interior endpoints lie inside the same
initial Bochner interval, including their entire unordered closed span. -/
theorem h3Audit_positiveUnorderedInterval_subset_initial
    (b s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) b)
    (ht : t ∈ Set.Ioo (0 : ℝ) b) :
    Set.uIcc s t ⊆ Set.Icc (0 : ℝ) b := by
  intro x hx
  have hx' : x ∈ Set.Icc (min s t) (max s t) := hx
  have hLow : 0 ≤ min s t := le_min hs.1.le ht.1.le
  have hHigh : max s t ≤ b := max_le hs.2.le ht.2.le
  exact ⟨hLow.trans hx'.1, hx'.2.trans hHigh⟩

/-- The unordered closed span of two strictly positive interior times
stays strictly inside the physical interval `(0,b)`. -/
theorem h3Audit_positiveUnorderedInterval_strict
    (b s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) b)
    (ht : t ∈ Set.Ioo (0 : ℝ) b) :
    Set.uIcc s t ⊆ Set.Ioo (0 : ℝ) b := by
  intro x hx
  have hx' : x ∈ Set.Icc (min s t) (max s t) := hx
  have hLow : 0 < min s t := lt_min hs.1 ht.1
  have hHigh : max s t < b := max_lt hs.2 ht.2
  exact ⟨lt_of_lt_of_le hLow hx'.1, lt_of_le_of_lt hx'.2 hHigh⟩

/-- Exact interior Bochner increments from one actual strong L² temporal
derivative. No initial endpoint derivative, continuity, or FTC identity is
postulated, and `s,t` may occur in either order. -/
theorem h3Audit_positiveStrongDerivative_implies_interiorBochnerIncrements
    (F V : ℝ → H3ScalarL2)
    (b : ℝ) (hb : 0 < b)
    (hV : IntervalIntegrable V volume 0 b)
    (hDerivative : ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) b →
      HasDerivAt F (V x) x)
    (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) b)
    (ht : t ∈ Set.Ioo (0 : ℝ) b) :
    F t - F s = ∫ r in s..t, V r := by
  have hSub : Set.uIcc s t ⊆ Set.uIcc (0 : ℝ) b := by
    intro x hx
    have hxb := h3Audit_positiveUnorderedInterval_subset_initial b s t hs ht hx
    simpa only [Set.uIcc_of_le hb.le] using hxb
  have hIntegrable : IntervalIntegrable V volume s t :=
    hV.mono_set hSub
  have hFTC : (∫ r in s..t, V r) = F t - F s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx =>
        hDerivative x
          (h3Audit_positiveUnorderedInterval_strict b s t hs ht hx))
      hIntegrable
  exact hFTC.symm

/-- The actual physical old velocity needs just one integrable temporal
source plus interior strong time derivatives to satisfy the previous
weak-initial-Bochner criterion. -/
theorem h3Audit_initialPositiveStrongDerivative_implies_physicalL2RightTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (b : ℝ) (hb : 0 < b)
    (V : Fin 3 → ℝ → H3ScalarL2)
    (hV : ∀ j : Fin 3, IntervalIntegrable (V j) volume 0 b)
    (hDerivative : ∀ (j : Fin 3) (t : ℝ),
      t ∈ Set.Ioo (0 : ℝ) b →
      HasDerivAt (h3AuditActualPhysicalZeroJetL2Total hH3 j)
        (V j t) t)
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
  apply h3Audit_initialWeakBochnerIncrement_implies_physicalL2RightTrace
    hH3 hInt0 hMeas0 b hb V hV
  · intro j t ht
    exact h3Audit_initialIntervalIntegrable_of_globalBochner
      (V j) b hb (hV j) t ht
  · intro j s t hs ht
    exact h3Audit_positiveStrongDerivative_implies_interiorBochnerIncrements
      (h3AuditActualPhysicalZeroJetL2Total hH3 j)
      (V j) b hb (hV j) (hDerivative j) s t hs ht
  · exact hWeak

/-- The old physical mild condition, a weak initial L² trace, a single
initial interval Bochner bound, and genuine interior strong time derivatives.
Neither an initial strong trace nor any two-point FTC identities appear in
the definition. -/
def H3AuditInitialPhysicalEnergyMildWeakStrongDerivativeData
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
      HasDerivAt (h3AuditActualPhysicalZeroJetL2Total hH3 j)
        (V j t) t) ∧
    (∀ (j : Fin 3) (ψ : H3ScalarL2),
      Tendsto
        (fun t : ℝ =>
          inner ℝ (h3AuditActualPhysicalZeroJetL2Total hH3 j t) ψ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ
          (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)) ψ)))

/-- The genuine strong interior time derivative discharges the *assumed*
Bochner increment and every redundant subinterval-integrability premise. -/
theorem h3Audit_initialMildWeakStrongDerivative_implies_weakBochnerIncrementData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildWeakStrongDerivativeData hH3) :
    H3AuditInitialPhysicalEnergyMildWeakBochnerIncrementData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, U₀, A, hA, hU₀,
    b, V, hMild, hV, hDerivative, hWeak⟩ := hData
  have hb : 0 < b := by
    obtain ⟨_P, hb, _⟩ := hMild
    exact hb
  refine ⟨hInt0, hMeas0, hFourier0, U₀, A, hA, hU₀,
    b, V, hMild, hV, ?_, ?_, hWeak⟩
  · intro j t ht
    exact h3Audit_initialIntervalIntegrable_of_globalBochner
      (V j) b hb (hV j) t ht
  · intro j s t hs ht
    exact h3Audit_positiveStrongDerivative_implies_interiorBochnerIncrements
      (h3AuditActualPhysicalZeroJetL2Total hH3 j)
      (V j) b hb (hV j) (hDerivative j) s t hs ht

/-- Initial strong physical L² convergence without any initial-time
strong differentiability or endpoint FTC assumption. -/
theorem h3Audit_initialMildWeakStrongDerivative_implies_L2TraceData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildWeakStrongDerivativeData hH3) :
    H3AuditInitialPhysicalEnergyMildL2TraceData hH3 := by
  exact h3Audit_initialMildWeakBochnerIncrement_implies_L2TraceData
    hH3 (h3Audit_initialMildWeakStrongDerivative_implies_weakBochnerIncrementData
      hH3 hData)

/-- The prescribed actual H³ initial Fourier state is the mild initial
state; no Fourier-identification equality is assumed. -/
theorem h3Audit_initialMildWeakStrongDerivative_identifies_initialSpectral
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildWeakStrongDerivativeData hH3) :
    H3AuditInitialPhysicalEnergyMildZeroCompatibleData hH3 := by
  exact h3Audit_initialMildWeakBochnerIncrement_identifies_initialSpectral
    hH3 (h3Audit_initialMildWeakStrongDerivative_implies_weakBochnerIncrementData
      hH3 hData)

/-- The initial actual H³ energy has the correct one-sided trace. -/
theorem h3Audit_initialMildWeakStrongDerivative_energyRightLimit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildWeakStrongDerivativeData hH3) :
    Tendsto (velocityH3EnergyAt u)
      (𝓝[>] (0 : ℝ)) (𝓝 (velocityH3EnergyAt u 0)) := by
  exact h3Audit_initialMildWeakBochnerIncrement_energyRightLimit
    hH3 (h3Audit_initialMildWeakStrongDerivative_implies_weakBochnerIncrementData
      hH3 hData)

/-- Full-time selected physical Sobolev consequence, still conditional on
the genuinely independent strong terminal vorticity endpoint. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialMildWeakStrongDerivative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialPhysicalEnergyMildWeakStrongDerivativeData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialMildWeakBochnerIncrement
    hH3 hClass i hPhysical
    (h3Audit_initialMildWeakStrongDerivative_implies_weakBochnerIncrementData
      hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
