import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialScalarRightTraceRelativeEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Initial scalar right trace follows from integrated relative energy

The previous comparison requires a separate right-zero trace for the scalar
old-minus-selected energy. Here that requirement is *derived* from an
integrable comparison energy and the exact relative-energy inequality.

An `L¹` scalar relative energy has a forward primitive tending to zero as
time decreases to zero. Since `0 ≤ e(t) ≤ K ∫₀ᵗ e`, the energy itself also
tends to zero (even if it was not assumed continuous at the initial time).
Combined with positive-time continuity, this provides the closed-interval
continuity needed by the already proved scalar Gronwall argument.

The PDE-facing contract still explicitly requires initial-interval
integrability, positive-time scalar continuity, and epsilon-accurate
relative-energy estimates. It does *not* derive those from the open-time
Navier--Stokes admissibility class. The terminal actual-vorticity strong-H³
hypothesis remains separate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- On an initial positive interval, the exact integral-energy bound and
integrability of the nonnegative energy force its right limit to be zero.
No continuity of the energy at time zero is assumed. -/
theorem h3Audit_initialScalarRightZero_of_integrableExactEnergy
    (e : ℝ → ℝ) (b K : ℝ) (hb : 0 < b)
    (heNonneg : ∀ s : ℝ, 0 ≤ e s)
    (heInt : IntervalIntegrable e volume 0 b)
    (hExact : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) b →
      e t ≤ K * ∫ s in (0 : ℝ)..t, e s) :
    Tendsto e (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  let H : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, e s
  have hContinuousU : ContinuousOn H (Set.uIcc (0 : ℝ) b) := by
    exact intervalIntegral.continuousOn_primitive_interval'
      heInt left_mem_uIcc
  have hContinuous : ContinuousOn H (Set.Icc (0 : ℝ) b) := by
    simpa only [Set.uIcc_of_le hb.le] using hContinuousU
  have hHTendsto : Tendsto H (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := h3Audit_rightTendsto_of_continuousOn_initialIcc
      H hb hContinuous
    simpa [H] using h
  have hUpper : Tendsto (fun t : ℝ => K * H t)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hConstant : Tendsto (fun _t : ℝ => K)
        (𝓝[>] (0 : ℝ)) (𝓝 K) := tendsto_const_nhds
    have hProduct := hConstant.mul hHTendsto
    simpa [Function.comp_def] using hProduct
  apply Metric.tendsto_nhdsWithin_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hNear⟩ :=
    (Metric.tendsto_nhdsWithin_nhds.mp hUpper) ε hε
  refine ⟨min δ b, lt_min hδ hb, ?_⟩
  intro t htPos htDist
  have htδ : dist t 0 < δ :=
    lt_of_lt_of_le htDist (min_le_left δ b)
  have htb : t < b := by
    have hDistLt : dist t 0 < b :=
      lt_of_lt_of_le htDist (min_le_right δ b)
    have htPosReal : (0 : ℝ) < t := Set.mem_Ioi.mp htPos
    simpa only [Real.dist_eq, sub_zero, abs_of_pos htPosReal] using hDistLt
  have heBound : e t ≤ K * H t := by
    simpa only [H] using hExact t ⟨htPos.le, htb.le⟩
  have hUpperDist : dist (K * H t) 0 < ε := hNear htPos htδ
  have hUpperAbs : |K * H t| < ε := by
    simpa only [Real.dist_eq, sub_zero] using hUpperDist
  have heSmall : e t < ε :=
    lt_of_le_of_lt heBound
      (lt_of_le_of_lt (le_abs_self _) hUpperAbs)
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (heNonneg t)]
    using heSmall

/-- The epsilon-accurate integrated-residual comparison gives the right
scalar zero trace as soon as the comparison energy is interval-integrable.
The initial trace is no longer an independent premise. -/
theorem h3Audit_initialScalarRightZero_of_integrableEpsilonResidual
    (e : ℝ → ℝ) (b K : ℝ) (hb : 0 < b)
    (heNonneg : ∀ s : ℝ, 0 ≤ e s)
    (heInt : IntervalIntegrable e volume 0 b)
    (hEpsilon : ∀ ε : ℝ, 0 < ε →
      ∃ (κ : ℝ) (R : ℝ → ℝ),
        κ ≤ K ∧
        IntervalIntegrable (fun s : ℝ => |R s|) volume 0 b ∧
        (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
        ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) b →
          e t ≤ (κ * ∫ s in (0 : ℝ)..t, e s) +
            (∫ s in (0 : ℝ)..t, |R s|)) :
    Tendsto e (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  exact h3Audit_initialScalarRightZero_of_integrableExactEnergy
    e b K hb heNonneg heInt
    (h3Audit_initialRelativeEnergy_exact_of_arbitrarySmallIntegratedResidual
      e b K heNonneg hEpsilon)

/-- A PDE-facing uniqueness contract requiring actual integrability of the
initial comparison energy, rather than directly assuming its right zero trace. -/
def H3AuditInitialCanonicalIntegrableScalarRelativeEnergyData
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
    ∃ K : ℝ,
      ContinuousOn
        (fun t => ‖h3AuditInitialCanonicalPhysicalDifference
          hH3 hFourier0 A hA hU₀ t‖ ^ 2)
        (Set.Ioc (0 : ℝ) b) ∧
      IntervalIntegrable
        (fun t => ‖h3AuditInitialCanonicalPhysicalDifference
          hH3 hFourier0 A hA hU₀ t‖ ^ 2)
        volume 0 b ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ (κ : ℝ) (R : ℝ → ℝ),
          κ ≤ K ∧
          IntervalIntegrable (fun s : ℝ => |R s|) volume 0 b ∧
          (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
          ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) b →
            ‖h3AuditInitialCanonicalPhysicalDifference
              hH3 hFourier0 A hA hU₀ t‖ ^ 2 ≤
              (κ * ∫ s in (0 : ℝ)..t,
                ‖h3AuditInitialCanonicalPhysicalDifference
                  hH3 hFourier0 A hA hU₀ s‖ ^ 2) +
              (∫ s in (0 : ℝ)..t, |R s|)

/-- Integrability plus the epsilon-dependent energy inequality discharge the
separately postulated scalar right-zero trace in the previous interface. -/
theorem h3Audit_initialIntegrableScalar_implies_epsilonResidualRightTraceData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalIntegrableScalarRelativeEnergyData hH3) :
    H3AuditInitialCanonicalEpsilonResidualRightTraceData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, hPositive, hInt, hEpsilon⟩ := hData
  refine ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, hPositive, ?_, hEpsilon⟩
  exact h3Audit_initialScalarRightZero_of_integrableEpsilonResidual
    (fun t => ‖h3AuditInitialCanonicalPhysicalDifference
      hH3 hFourier0 A hA hU₀ t‖ ^ 2)
    b K hb (fun t => sq_nonneg _) hInt hEpsilon

/-- Compact physical weak-test uniqueness follows from time-integrable
relative energy and arbitrarily small PDE approximation residuals. -/
theorem h3Audit_initialIntegrableScalar_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalIntegrableScalarRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialEpsilonResidualRightTrace_implies_compactWeakComparisonData
    hH3 (h3Audit_initialIntegrableScalar_implies_epsilonResidualRightTraceData
      hH3 hData)

/-- The same conditions identify the actual initial physical L² and H³
energy right traces; no assumption of these conclusions is made. -/
theorem h3Audit_initialIntegrableScalar_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalIntegrableScalarRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialEpsilonResidualRightTrace_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialIntegrableScalar_implies_epsilonResidualRightTraceData
      hH3 hData)

/-- Full-time transverse estimates remain conditional on a separate
actual-vorticity terminal strong-H³ endpoint path. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialIntegrableScalar
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalIntegrableScalarRelativeEnergyData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialEpsilonResidualRightTrace
    hH3 hClass i hPhysical
    (h3Audit_initialIntegrableScalar_implies_epsilonResidualRightTraceData
      hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
