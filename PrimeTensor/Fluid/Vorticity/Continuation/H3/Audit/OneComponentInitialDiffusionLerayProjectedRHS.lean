import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialProjectedRHSWeakFTCControl

/-!
# Initial projected momentum from diffusion minus Leray transport

The preceding initial-value theorem requested one interval-integrable physical
Hilbert-space projected RHS, its total `L¹` budget, and a two-time weak momentum
identity for every three-component physical Schwartz test.

This module reduces those three assumptions to two physical L²-valued source
paths, intended to represent the actual diffusion and projected nonlinear
transport terms, plus the positive-time scalar derivative identity:

  d/dt <old(t), Φ> = <diffusion(t) - transport(t), Φ>.

One global `L¹` integral for each source implies a global `L¹` projected-RHS
bound with no supplied constant. The ordinary interval FTC proves the two-time
weak identity, with both endpoints strictly positive. The preceding theorem
then supplies conditional initial kinetic control and weak uniqueness.

Important boundary: this file does NOT derive source integrability or the
scalar derivative identity from `LoggedPreterminalH3PathAdmissible` alone.
Identifying these sources with the physical Navier--Stokes terms, and deriving
the independent vanishing selected/old relative-energy residual, are genuine
remaining PDE obligations. The terminal actual-vorticity strong-H³ endpoint
remains a separate premise.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- Two physical `L¹_t L²_x` source paths produce an integrable projected
RHS and its exact, explicit integral upper budget. Neither a new constant
nor a separate integrability proof for their difference is assumed. -/
theorem h3Audit_initialDiffusionLeray_integrableProjectedRHS_and_mass
    (D N : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b : ℝ) (hb : 0 ≤ b)
    (hD : IntervalIntegrable D volume 0 b)
    (hN : IntervalIntegrable N volume 0 b) :
    IntervalIntegrable (fun s : ℝ => D s - N s) volume 0 b ∧
    (∫ s in (0 : ℝ)..b, ‖D s - N s‖) ≤
      (∫ s in (0 : ℝ)..b, ‖D s‖) +
      (∫ s in (0 : ℝ)..b, ‖N s‖) := by
  have hSplit :
      IntervalIntegrable (fun s : ℝ => D s - N s) volume 0 b :=
    hD.sub hN
  have hMajor :
      IntervalIntegrable (fun s : ℝ => ‖D s‖ + ‖N s‖)
        volume 0 b :=
    hD.norm.add hN.norm
  have hPoint : ∀ s ∈ Set.Icc (0 : ℝ) b,
      ‖D s - N s‖ ≤ ‖D s‖ + ‖N s‖ := by
    intro s _hs
    exact norm_sub_le (D s) (N s)
  have hIntegral :
      (∫ s in (0 : ℝ)..b, ‖D s - N s‖) ≤
      (∫ s in (0 : ℝ)..b, ‖D s‖ + ‖N s‖) :=
    intervalIntegral.integral_mono_on hb hSplit.norm hMajor hPoint
  refine ⟨hSplit, ?_⟩
  calc
    (∫ s in (0 : ℝ)..b, ‖D s - N s‖) ≤
        ∫ s in (0 : ℝ)..b, ‖D s‖ + ‖N s‖ := hIntegral
    _ = (∫ s in (0 : ℝ)..b, ‖D s‖) +
          (∫ s in (0 : ℝ)..b, ‖N s‖) :=
      intervalIntegral.integral_add hD.norm hN.norm

/-- The sum of the two physical source masses is automatically nonnegative;
it is the shared projected-RHS dual budget. -/
theorem h3Audit_initialDiffusionLeray_exists_projectedRHS_budget
    (D N : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b : ℝ) (hb : 0 ≤ b)
    (hD : IntervalIntegrable D volume 0 b)
    (hN : IntervalIntegrable N volume 0 b) :
    ∃ M : ℝ, 0 ≤ M ∧
      IntervalIntegrable (fun s : ℝ => D s - N s) volume 0 b ∧
      (∫ s in (0 : ℝ)..b, ‖D s - N s‖) ≤ M := by
  let M : ℝ :=
    (∫ s in (0 : ℝ)..b, ‖D s‖) +
    (∫ s in (0 : ℝ)..b, ‖N s‖)
  have hM : 0 ≤ M := by
    dsimp only [M]
    apply add_nonneg
    · exact intervalIntegral.integral_nonneg hb
        (fun s _hs => norm_nonneg (D s))
    · exact intervalIntegral.integral_nonneg hb
        (fun s _hs => norm_nonneg (N s))
  obtain ⟨hSplit, hMass⟩ :=
    h3Audit_initialDiffusionLeray_integrableProjectedRHS_and_mass
      D N b hb hD hN
  exact ⟨M, hM, hSplit, hMass⟩

/-- The positive-time weak momentum derivative and source `L¹`
integrability imply the exact weak two-time FTC for every Schwartz probe.
No identity at `t=0` is used, and the integral works in either time order. -/
theorem h3Audit_initialDiffusionLeray_scalarDerivative_implies_weakFTC
    (F D N : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b : ℝ) (hb : 0 < b)
    (hD : IntervalIntegrable D volume 0 b)
    (hN : IntervalIntegrable N volume 0 b)
    (hDeriv : ∀ (Φ : H3PhysicalRealFinVectorSchwartz)
      (t : ℝ), t ∈ Set.Ioo (0 : ℝ) b →
        HasDerivAt
          (fun x : ℝ =>
            ((innerSL ℝ) (F x))
              (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
          (((innerSL ℝ) (D t - N t))
            (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)) t) :
    ∀ (Φ : H3PhysicalRealFinVectorSchwartz)
      (s t : ℝ),
        s ∈ Set.Ioo (0 : ℝ) b →
        t ∈ Set.Ioo (0 : ℝ) b →
          ((innerSL ℝ) (F t))
              (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) -
            ((innerSL ℝ) (F s))
              (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) =
            ∫ r in s..t,
              ((innerSL ℝ) (D r - N r))
                (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) := by
  intro Φ s t hs ht
  let ψ : H3PhysicalRealFinVectorL2Hilbert :=
    h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ
  let g : ℝ → ℝ :=
    fun r => ((innerSL ℝ) (D r - N r)) ψ
  have hSplit :
      IntervalIntegrable (fun r : ℝ => D r - N r) volume 0 b :=
    hD.sub hN
  have hScalar : IntervalIntegrable g volume 0 b :=
    h3Audit_initialProjectedRHS_scalarPairing_intervalIntegrable
      (fun r : ℝ => D r - N r) b hb.le hSplit ψ
  have hSub : Set.uIcc s t ⊆ Set.uIcc (0 : ℝ) b := by
    intro x hx
    have hIn :=
      h3Audit_positiveUnorderedInterval_subset_initial b s t hs ht hx
    simpa only [Set.uIcc_of_le hb.le] using hIn
  have hLocal : IntervalIntegrable g volume s t :=
    hScalar.mono_set hSub
  have hFTC :
      (∫ r in s..t, g r) =
        ((innerSL ℝ) (F t)) ψ - ((innerSL ℝ) (F s)) ψ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx =>
        hDeriv Φ x
          (h3Audit_positiveUnorderedInterval_strict b s t hs ht hx))
      hLocal
  exact hFTC.symm

/-- The genuinely split diffusion/transport sources and strict-positive
weak momentum derivative discharge both source and weak-FTC inputs in the
preceding projected-RHS theorem. -/
theorem h3Audit_initialDiffusionLeray_implies_schwartzDualL1
    (F D N : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b : ℝ) (hb : 0 < b)
    (hD : IntervalIntegrable D volume 0 b)
    (hN : IntervalIntegrable N volume 0 b)
    (hDeriv : ∀ (Φ : H3PhysicalRealFinVectorSchwartz)
      (t : ℝ), t ∈ Set.Ioo (0 : ℝ) b →
        HasDerivAt
          (fun x : ℝ =>
            ((innerSL ℝ) (F x))
              (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
          (((innerSL ℝ) (D t - N t))
            (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)) t) :
    ∃ M : ℝ, 0 ≤ M ∧ H3AuditInitialSchwartzDualL1IncrementOn F b M := by
  obtain ⟨M, hM, hSplit, hMass⟩ :=
    h3Audit_initialDiffusionLeray_exists_projectedRHS_budget
      D N b hb.le hD hN
  refine ⟨M, hM, ?_⟩
  exact h3Audit_initialProjectedRHS_implies_schwartzDualL1
    F (fun r => D r - N r) b M hb hSplit hMass
    (h3Audit_initialDiffusionLeray_scalarDerivative_implies_weakFTC
      F D N b hb hD hN hDeriv)

/-- Initial-value contract: a physical diffusion path and Leray-transport
path are separately `L¹_tL²_x`; their difference is the actual strict-time
weak momentum derivative against every Schwartz vector. The vanishing
old/selected relative-energy comparison is deliberately kept independent. -/
def H3AuditInitialCanonicalDiffusionLerayRelativeEnergyData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (A : ℝ) (hA : 0 < A)
    (hU₀ : ‖velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0‖ ≤ A)
    (b : ℝ),
    0 < b ∧ b < T ∧
    b ≤ h3FinHeatLerayRestartRadius 1 A ∧
    ∃ (D N : ℝ → H3PhysicalRealFinVectorL2Hilbert) (K : ℝ),
      IntervalIntegrable D volume 0 b ∧
      IntervalIntegrable N volume 0 b ∧
      (∀ (Φ : H3PhysicalRealFinVectorSchwartz) (t : ℝ),
        t ∈ Set.Ioo (0 : ℝ) b →
          HasDerivAt
            (fun x : ℝ =>
              ((innerSL ℝ)
                (h3AuditInitialOldPhysicalHilbertTotal hH3 x))
                (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
            (((innerSL ℝ) (D t - N t))
              (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)) t) ∧
      (∀ ε : ℝ, 0 < ε →
        ∃ (κ R : ℝ → ℝ),
          ContinuousOn κ (Set.Icc (0 : ℝ) b) ∧
          (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b → κ s ≤ K) ∧
          IntervalIntegrable (fun s => |R s|) volume 0 b ∧
          (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
          ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
            ‖h3AuditInitialCanonicalPhysicalDifference
              hH3 hFourier0 A hA hU₀ t‖ ^ 2 ≤
              (∫ s in (0 : ℝ)..t,
                κ s * ‖h3AuditInitialCanonicalPhysicalDifference
                  hH3 hFourier0 A hA hU₀ s‖ ^ 2) +
              (∫ s in (0 : ℝ)..t, |R s|))

/-- Expose the original projected-RHS contract directly. The RHS is the
actual supplied diffusion-minus-transport path, the common mass constant is
derived from its two integrable factors, and the weak FTC is proved from
the scalar derivative on strictly positive intervals. -/
theorem h3Audit_initialDiffusionLeray_implies_projectedRHSData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalDiffusionLerayRelativeEnergyData hH3) :
    H3AuditInitialCanonicalProjectedRHSWeakFTCRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, D, N, K, hD, hN, hDeriv, hEpsilon⟩ := hData
  obtain ⟨M, hM, hSplit, hMass⟩ :=
    h3Audit_initialDiffusionLeray_exists_projectedRHS_budget
      D N b hb.le hD hN
  exact ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, (fun r => D r - N r), M, K,
    hM, hSplit, hMass,
    h3Audit_initialDiffusionLeray_scalarDerivative_implies_weakFTC
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      D N b hb hD hN hDeriv,
    hEpsilon⟩

/-- Both split-source `L¹` controls and the positive-time physical weak
momentum derivative imply the previous Schwartz dual initial-value contract. -/
theorem h3Audit_initialDiffusionLeray_implies_schwartzDualL1Data
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalDiffusionLerayRelativeEnergyData hH3) :
    H3AuditInitialCanonicalSchwartzDualL1RelativeEnergyData hH3 := by
  exact h3Audit_initialProjectedRHS_implies_schwartzDualL1Data hH3
    (h3Audit_initialDiffusionLeray_implies_projectedRHSData hH3 hData)

/-- Conditional compact weak-test initial uniqueness from the separated
projected physical diffusion and Leray forcing source conditions. -/
theorem h3Audit_initialDiffusionLeray_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalDiffusionLerayRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialSchwartzDualL1_implies_compactWeakComparisonData
    hH3 (h3Audit_initialDiffusionLeray_implies_schwartzDualL1Data hH3 hData)

/-- Physical initial L² and H³ upper traces, still conditional on the
independent vanishing old/selected relative-energy residual. -/
theorem h3Audit_initialDiffusionLeray_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalDiffusionLerayRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialSchwartzDualL1_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialDiffusionLeray_implies_schwartzDualL1Data hH3 hData)

/-- The transverse full-time Sobolev result retains the independent
strong-H³ actual-vorticity terminal condition. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialDiffusionLeray
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalDiffusionLerayRelativeEnergyData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialSchwartzDualL1
    hH3 hClass i hPhysical
    (h3Audit_initialDiffusionLeray_implies_schwartzDualL1Data hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
