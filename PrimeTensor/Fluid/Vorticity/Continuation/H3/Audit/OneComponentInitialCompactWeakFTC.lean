import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialCanonicalCompactOverlap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Recover compact-test initial data from a scalar weak integral formulation

The canonical initial-overlap theorem used a separately stated right limit
against every compact smooth spatial test. This module instead accepts an
ordinary weak initial-time evolution identity for each physical velocity
coordinate and each compact test:

  <phi, u_j(t)> - <phi, u_j(0)> = integral_0^t g_{j,phi}(s) ds.

The scalar source may depend on the test, and is only interval-integrable on
one initial interval. Its integral vanishes as t tends to zero from above.
No L2-valued Bochner derivative, uniform-in-test source estimate, initial H3
energy FTC, or strong initial temporal derivative is needed to establish the
compact-test trace.

IMPORTANT: the initial-time weak integral identity is an explicit hypothesis,
not a consequence of the project's open-time Navier--Stokes admissibility.
The canonical old/selected mild overlap and terminal physical vorticity H3
endpoint remain independent obligations.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace

noncomputable section

/-- Every interval-integrable *scalar* source has vanishing initial right
primitive; no uniform scalar bound is required. -/
theorem h3Audit_initialScalarWeakPrimitive_tendsto_zero
    (g : ℝ → ℝ) (b : ℝ) (hb : 0 < b)
    (hg : IntervalIntegrable g volume 0 b) :
    Tendsto (fun t : ℝ => ∫ s in (0 : ℝ)..t, g s)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hContinuousU :
      ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, g s)
        (Set.uIcc (0 : ℝ) b) := by
    exact intervalIntegral.continuousOn_primitive_interval'
      hg left_mem_uIcc
  have hContinuous :
      ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, g s)
        (Set.Icc (0 : ℝ) b) := by
    simpa only [Set.uIcc_of_le hb.le] using hContinuousU
  have hRight :=
    h3Audit_rightTendsto_of_continuousOn_initialIcc
      (fun t : ℝ => ∫ s in (0 : ℝ)..t, g s)
      hb hContinuous
  simpa using hRight

/-- An exact initial weak FTC identity, with one integrable real source for
each compact test, implies the corresponding initial distributional trace. -/
theorem h3Audit_initialCompactWeakTrace_of_scalarIntegralEquation
    (F : ℝ → H3ScalarL2) (L₀ : H3ScalarL2)
    (b : ℝ) (hb : 0 < b)
    (hWeakFTC : ∀ φ : H3WeakTestFunction,
      ∃ g : ℝ → ℝ,
        IntervalIntegrable g volume 0 b ∧
        ∀ (t : ℝ), t ∈ Set.Ioo (0 : ℝ) b →
          inner ℝ (h3WeakTestFunctionPhysicalL2 φ) (F t) -
            inner ℝ (h3WeakTestFunctionPhysicalL2 φ) L₀ =
              ∫ s in (0 : ℝ)..t, g s) :
    ∀ φ : H3WeakTestFunction,
      Tendsto
        (fun t : ℝ => inner ℝ (h3WeakTestFunctionPhysicalL2 φ) (F t))
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (h3WeakTestFunctionPhysicalL2 φ) L₀)) := by
  intro φ
  obtain ⟨g, hg, hIdentity⟩ := hWeakFTC φ
  have hPrimitive := h3Audit_initialScalarWeakPrimitive_tendsto_zero g b hb hg
  have hStrict : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      t ∈ Set.Ioo (0 : ℝ) b := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hb)] with t ht0 htb
    exact ⟨ht0, htb⟩
  have hEq :
      (fun t : ℝ =>
        inner ℝ (h3WeakTestFunctionPhysicalL2 φ) (F t) -
          inner ℝ (h3WeakTestFunctionPhysicalL2 φ) L₀)
        =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => ∫ s in (0 : ℝ)..t, g s) := by
    filter_upwards [hStrict] with t ht
    exact hIdentity t ht
  have hDifference :
      Tendsto
        (fun t : ℝ =>
          inner ℝ (h3WeakTestFunctionPhysicalL2 φ) (F t) -
            inner ℝ (h3WeakTestFunctionPhysicalL2 φ) L₀)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    hPrimitive.congr' hEq.symm
  have hSum := hDifference.add
    (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => inner ℝ (h3WeakTestFunctionPhysicalL2 φ) L₀)
      (𝓝[>] (0 : ℝ))
      (𝓝 (inner ℝ (h3WeakTestFunctionPhysicalL2 φ) L₀)))
  simpa only [sub_add_cancel, zero_add] using hSum

/-- Actual-old scalar weak FTC at the prescribed initial velocity suffices
for the preceding compact-test initial-value hypothesis. -/
theorem h3Audit_actualInitialCompactWeakTrace_of_scalarIntegralEquation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (b : ℝ) (hb : 0 < b)
    (hWeakFTC : ∀ (j : Fin 3) (φ : H3WeakTestFunction),
      ∃ g : ℝ → ℝ,
        IntervalIntegrable g volume 0 b ∧
        ∀ (t : ℝ), t ∈ Set.Ioo (0 : ℝ) b →
          inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
              (h3AuditActualPhysicalZeroJetL2Total hH3 j t) -
            inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
              (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)) =
              ∫ s in (0 : ℝ)..t, g s) :
    ∀ (j : Fin 3) (φ : H3WeakTestFunction),
      Tendsto
        (fun t : ℝ => inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
          (h3AuditActualPhysicalZeroJetL2Total hH3 j t))
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
          (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)))) := by
  intro j
  exact h3Audit_initialCompactWeakTrace_of_scalarIntegralEquation
    (h3AuditActualPhysicalZeroJetL2Total hH3 j)
    (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j))
    b hb (hWeakFTC j)

/-- PDE-facing initial contract: replace an independently postulated compact
initial trace by the weak initial-time integral equation. The source is real
and test-dependent, not assumed to take values in physical L2. -/
def H3AuditInitialCanonicalOverlapScalarWeakFTCData
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
      ∃ g : ℝ → ℝ,
        IntervalIntegrable g volume 0 b ∧
        ∀ (t : ℝ), t ∈ Set.Ioo (0 : ℝ) b →
          inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
              (h3AuditActualPhysicalZeroJetL2Total hH3 j t) -
            inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
              (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j)) =
              ∫ s in (0 : ℝ)..t, g s

/-- The scalar distributional weak integral equation discharges the compact
initial trace requirement of the canonical overlap theorem. -/
theorem h3Audit_initialCanonicalScalarWeakFTC_implies_compactData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalOverlapScalarWeakFTCData hH3) :
    H3AuditInitialCanonicalOverlapCompactInitialData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, U₀, A, hA, hU₀,
    b, hOverlap, hWeakFTC⟩ := hData
  have hb : 0 < b := hOverlap.1
  exact ⟨hInt0, hMeas0, hFourier0, U₀, A, hA, hU₀,
    b, hOverlap,
    h3Audit_actualInitialCompactWeakTrace_of_scalarIntegralEquation
      hH3 hInt0 hMeas0 b hb hWeakFTC⟩

/-- The actual old velocity has the correct physical initial L2 trace and
H3 energy upper limit under the initial scalar weak integral formulation
and canonical overlap, without a vector-valued temporal source. -/
theorem h3Audit_initialCanonicalScalarWeakFTC_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalOverlapScalarWeakFTCData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialCanonicalCompactOverlap_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialCanonicalScalarWeakFTC_implies_compactData hH3 hData)

/-- Recover both transverse full-time intrinsic 3/2 Sobolev estimates. The
actual physical terminal vorticity strong H3 endpoint remains independent. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialCanonicalScalarWeakFTC
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalOverlapScalarWeakFTCData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialCanonicalCompactOverlap
    hH3 hClass i hPhysical
    (h3Audit_initialCanonicalScalarWeakFTC_implies_compactData hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
