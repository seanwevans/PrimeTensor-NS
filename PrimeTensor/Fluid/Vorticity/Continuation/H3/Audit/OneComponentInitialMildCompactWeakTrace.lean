import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialMildWeakTraceClosure
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.One.Selected.Relative.Strong.L2.Reduction

/-!
# Physical initial data from compact smooth weak tests

The preceding initial mild proof assumed convergence against every element of
physical scalar L². This is unnecessarily strong when the actual old velocity
has a strong physical L² right *limit* from a continuous weighted H³ mild path.

The project already proves that the images of compact smooth weak test
functions are dense in physical scalar L². Thus the mild limit is identified
with the prescribed initial physical velocity if their pairings agree just
against those compact smooth scalar weak tests. An ordinary Hilbert-space
limit and dense test uniqueness prove the conclusion; there is no assumed
strong L² initial condition or temporal derivative at t=0.

This strengthens the initial-data INTERFACE; it does not derive the weak
initial condition or the old/mild path agreement from the open-time PDE.
The terminal physical vorticity strong-H³ endpoint remains separate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace

noncomputable section

/-- Strong convergence to L together with the initial pairing limit against
only the project's compact smooth weak tests identifies L with L₀.
No boundedness hypothesis is needed: strong convergence is already known. -/
theorem h3Audit_initialHilbertStrongAndCompactWeakLimit_identify
    (F : ℝ → H3ScalarL2) (L L₀ : H3ScalarL2)
    (hStrong : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hWeakCompact : ∀ φ : H3WeakTestFunction,
      Tendsto
        (fun t : ℝ => inner ℝ (h3WeakTestFunctionPhysicalL2 φ) (F t))
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (h3WeakTestFunctionPhysicalL2 φ) L₀))) :
    L = L₀ := by
  apply h3ScalarL2_eq_of_weakTest_inner_eq_orderOne
  intro φ
  have hPairingContinuous :
      Continuous (fun z : H3ScalarL2 =>
        inner ℝ (h3WeakTestFunctionPhysicalL2 φ) z) :=
    continuous_const.inner continuous_id
  exact tendsto_nhds_unique
    (hPairingContinuous.continuousAt.tendsto.comp hStrong)
    (hWeakCompact φ)

/-- A strong old physical H³ spectral right limit and merely *compact-test*
weak initial-value convergence imply the actual three-component physical L²
right trace. The complete weak-L² topology is not an input. -/
theorem h3Audit_initialMildStrongTrace_and_compactWeakInitial_implies_physicalL2Trace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (U₀ : H3SpectralVelocityState)
    (hTrace : Tendsto (h3AuditActualSpectralVelocityTotal hH3)
      (𝓝[>] (0 : ℝ)) (𝓝 U₀))
    (hWeakCompact : ∀ (j : Fin 3) (φ : H3WeakTestFunction),
      Tendsto
        (fun t : ℝ =>
          inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
            (h3AuditActualPhysicalZeroJetL2Total hH3 j t))
        (𝓝[>] (0 : ℝ))
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
    h3Audit_initialHilbertStrongAndCompactWeakLimit_identify
      (h3AuditActualPhysicalZeroJetL2Total hH3 j)
      L L₀ hDecoded (hWeakCompact j)
  simpa only [hIdentify] using hDecoded

/-- The ordinary compact smooth weak initial-value condition. Unlike the
previous all-L²-pairings interface, only project-native compact smooth scalar
test functions are quantified. The physical old mild representation remains
explicit and is not inferred merely from positive-time classical regularity. -/
def H3AuditInitialPhysicalEnergyMildCompactWeakTraceData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (U₀ : H3SpectralVelocityState) (A : ℝ)
    (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A) (b : ℝ),
    H3AuditInitialPhysicalEnergyMildDataAt hH3 U₀ hA hU₀ b ∧
    ∀ (j : Fin 3) (φ : H3WeakTestFunction),
      Tendsto
        (fun t : ℝ =>
          inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
            (h3AuditActualPhysicalZeroJetL2Total hH3 j t))
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
          (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j))))

/-- Actual old mild continuity supplies the strong decoded L² limit, and
compact weak-test initial data identifies it with the prescribed old field.
This discharges the prior all-physical-L² right trace contract. -/
theorem h3Audit_initialMildCompactWeakTrace_implies_L2TraceData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildCompactWeakTraceData hH3) :
    H3AuditInitialPhysicalEnergyMildL2TraceData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, U₀, A, hA, hU₀,
    b, hMild, hWeakCompact⟩ := hData
  have hT : 0 < T :=
    (Classical.choose_spec hH3.navier_stokes).positive_terminal
  have hTrace :=
    h3Audit_initialPhysicalEnergyMildDataAt_fullStrongH3Trace
      hH3 U₀ hA hU₀ hMild
  exact ⟨hInt0, hMeas0, hFourier0, U₀, A, hA, hU₀, b,
    hMild,
    h3Audit_initialMildStrongTrace_and_compactWeakInitial_implies_physicalL2Trace
      hH3 hT hInt0 hMeas0 U₀ hTrace hWeakCompact⟩

/-- Compact-test weak initial data also produces the previous full weak L²
initial-data contract. Here the stronger pairings are a consequence, not an
assumption, of the newly proved strong physical right trace. -/
theorem h3Audit_initialMildCompactWeakTrace_implies_weakTraceData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildCompactWeakTraceData hH3) :
    H3AuditInitialPhysicalEnergyMildWeakTraceData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, U₀, A, hA, hU₀,
    b, hMild, hPhysical⟩ :=
    h3Audit_initialMildCompactWeakTrace_implies_L2TraceData hH3 hData
  refine ⟨hInt0, hMeas0, hFourier0, U₀, A, hA, hU₀,
    b, hMild, ?_⟩
  intro j ψ
  have hPairingContinuous :
      Continuous (fun z : H3ScalarL2 => inner ℝ z ψ) :=
    continuous_id.inner continuous_const
  exact hPairingContinuous.continuousAt.tendsto.comp (hPhysical j)

/-- The mild initial spectral datum is the canonical H³ encoding of the
prescribed physical t=0 velocity; no spectral equality was assumed. -/
theorem h3Audit_initialMildCompactWeakTrace_identifies_initialSpectral
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildCompactWeakTraceData hH3) :
    H3AuditInitialPhysicalEnergyMildZeroCompatibleData hH3 := by
  exact h3Audit_initialMildL2Trace_implies_zeroCompatibleData
    hH3 (h3Audit_initialMildCompactWeakTrace_implies_L2TraceData hH3 hData)

/-- The genuine initial H³ physical energy is the right limit of positive
physical-time energy, without an initial energy FTC hypothesis. -/
theorem h3Audit_initialMildCompactWeakTrace_energyRightLimit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialPhysicalEnergyMildCompactWeakTraceData hH3) :
    Tendsto (velocityH3EnergyAt u)
      (𝓝[>] (0 : ℝ)) (𝓝 (velocityH3EnergyAt u 0)) := by
  exact h3Audit_initialMildL2Trace_energyRightLimit
    hH3 (h3Audit_initialMildCompactWeakTrace_implies_L2TraceData hH3 hData)

/-- The full-time physical two-component homogeneous 3/2 Sobolev result,
conditional on the independent strong terminal physical vorticity endpoint. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialMildCompactWeakTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialPhysicalEnergyMildCompactWeakTraceData hH3) :
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
    (h3Audit_initialMildCompactWeakTrace_implies_L2TraceData hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
