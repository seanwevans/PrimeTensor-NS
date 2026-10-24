import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionOldPressureGlobalJoint244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPhysicalHilbertGlobalFTC
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Global positive-time physical Hilbert FTC and kinetic differential identity

The prior global old-pressure joint-continuity checkpoint derived actual physical
Hilbert HasDerivAt directly from LoggedPreterminalH3PathAdmissible. Previously,
the repository's global-positive-time FTC theorem required a separately assumed
old temporal derivative joint-continuity predicate. This file eliminates that
extra premise and derives the genuine all-positive-time Bochner FTC, including
reversed endpoints, by reusing the independently established source integrability.

The same strong derivative supplies an all-L²-test derivative identity, a
continuous physical Hilbert time derivative, and the actual L² norm-square
(kinetic energy) derivative. None of these is an endpoint continuation result.

Dependency warning: the preceding old-pressure theorem itself imports selected
physical evolution from the earlier curl weak-FTC branch. This is a genuine
interface strengthening, not an independent proof of physical evolution.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Topology Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 1800000

/-- The actual old physical L² Hilbert velocity obeys the full Bochner
fundamental theorem between arbitrary positive preterminal times, in either
order. No additional old temporal-joint-continuity hypothesis remains. -/
theorem h3Path_physicalHilbertFTC_betweenPositiveTimes244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    h3AuditInitialOldPhysicalHilbertTotal hH3 t -
      h3AuditInitialOldPhysicalHilbertTotal hH3 s =
        ∫ r in s..t, h3PathActualProjectedMomentumSource244 hH3 r := by
  have hIntegrable :
      IntervalIntegrable (h3PathActualProjectedMomentumSource244 hH3)
        volume s t := by
    change IntervalIntegrable
      (fun r : ℝ =>
        h3AuditInitialActualSpectralLaplacianTotal hH3 r -
          h3AuditInitialActualSpectralLerayTotal hH3 r)
        volume s t
    exact h3Audit_initialActualProjectedRHS_intervalIntegrable_between_positiveTimes
      hH3 s t hs ht
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r hr =>
        h3Path_physicalHilbertHasDerivAt_fromH3Admissible244
          hH3
          (h3Audit_positiveUnorderedInterval_strict T s t hs ht hr))
      hIntegrable
  exact hFTC.symm

/-- Positive-time physical Hilbert evolution with any interior anchor. -/
theorem h3Path_physicalHilbertEvolution_betweenPositiveTimes244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    h3AuditInitialOldPhysicalHilbertTotal hH3 t =
      h3AuditInitialOldPhysicalHilbertTotal hH3 s +
        ∫ r in s..t, h3PathActualProjectedMomentumSource244 hH3 r := by
  have hFTC := h3Path_physicalHilbertFTC_betweenPositiveTimes244 hH3 s t hs ht
  exact (sub_eq_iff_eq_add.mp hFTC).trans (add_comm _ _)

/-- The *same* actual physical FTC defect is zero for all ordered or reversed
pairs of positive times, without restricting to a prechosen closed window. -/
theorem h3Path_projectedFTCDefect_zero_betweenPositiveTimes244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    h3PathActualProjectedMomentumFTCDefect244 hH3 s t = 0 := by
  exact (h3Path_actualProjectedMomentumFTCDefect_eq_zero_iff244
    hH3 s t).2
      (h3Path_physicalHilbertFTC_betweenPositiveTimes244 hH3 s t hs ht)

/-- Strong Fréchet differentiability on the entire open positive-time interval.
This no longer requires separately assumed temporal-derivative joint continuity. -/
theorem h3Path_physicalHilbertDifferentiableOn_positiveTime244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) :
    DifferentiableOn ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (Set.Ioo (0 : ℝ) T) := by
  intro s hs
  exact (h3Path_physicalHilbertHasDerivAt_fromH3Admissible244
    hH3 hs).differentiableAt.differentiableWithinAt

/-- Actual physical L² derivative, not merely a weak or distributional one. -/
theorem h3Path_physicalHilbert_deriv_eq_projectedSource_positiveTime244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    deriv (h3AuditInitialOldPhysicalHilbertTotal hH3) s =
      h3PathActualProjectedMomentumSource244 hH3 s := by
  exact (h3Path_physicalHilbertHasDerivAt_fromH3Admissible244
    hH3 hs).deriv

/-- Physical Hilbert derivative is strongly continuous throughout (0,T).
This is the C¹-in-time conclusion, expressed without any endpoint assertion. -/
theorem h3Path_physicalHilbert_deriv_continuousOn_positiveTime244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) :
    ContinuousOn
      (fun s : ℝ => deriv (h3AuditInitialOldPhysicalHilbertTotal hH3) s)
      (Set.Ioo (0 : ℝ) T) := by
  have hSource :
      ContinuousOn (h3PathActualProjectedMomentumSource244 hH3)
        (Set.Ioo (0 : ℝ) T) := by
    change ContinuousOn
      (fun s : ℝ =>
        h3AuditInitialActualSpectralLaplacianTotal hH3 s -
          h3AuditInitialActualSpectralLerayTotal hH3 s)
        (Set.Ioo (0 : ℝ) T)
    exact h3Audit_initialActualProjectedRHS_continuousOn_positiveTime hH3
  apply hSource.congr
  intro s hs
  exact h3Path_physicalHilbert_deriv_eq_projectedSource_positiveTime244
    hH3 s hs

/-- Momentum differentiation against ANY fixed physical L² Hilbert test,
not just solenoidal compact tests: this follows from the strong Hilbert
identity and continuity of inner-product evaluation. -/
theorem h3Path_allHilbertTest_momentumHasDerivAt_positiveTime244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ψ : H3PhysicalRealFinVectorL2Hilbert)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun r : ℝ => inner ℝ ψ (h3AuditInitialOldPhysicalHilbertTotal hH3 r))
      (inner ℝ ψ (h3PathActualProjectedMomentumSource244 hH3 s)) s := by
  let U : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  have hStrong : HasDerivAt U (h3PathActualProjectedMomentumSource244 hH3 s) s :=
    h3Path_physicalHilbertHasDerivAt_fromH3Admissible244 hH3 hs
  have hMapped : HasDerivAt
      (fun r : ℝ => ((innerSL ℝ) ψ) (U r))
      (((innerSL ℝ) ψ) (h3PathActualProjectedMomentumSource244 hH3 s)) s :=
    (((innerSL ℝ) ψ).hasFDerivAt).comp_hasDerivAt s hStrong
  exact hMapped

/-- Actual quadratic physical kinetic energy has the expected L² Hilbert
product-rule derivative, with no new old-pressure time hypothesis. This is
not the higher-order H³ energy balance and does not control the terminal time. -/
theorem h3Path_physicalL2KineticHasDerivAt_positiveTime244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun r : ℝ => ‖h3AuditInitialOldPhysicalHilbertTotal hH3 r‖ ^ 2)
      (2 * inner ℝ
        (h3AuditInitialOldPhysicalHilbertTotal hH3 s)
        (h3PathActualProjectedMomentumSource244 hH3 s)) s := by
  exact (h3Path_physicalHilbertHasDerivAt_fromH3Admissible244
    hH3 hs).norm_sq

end
end PrimeTensor.FirstMonomialTriad
