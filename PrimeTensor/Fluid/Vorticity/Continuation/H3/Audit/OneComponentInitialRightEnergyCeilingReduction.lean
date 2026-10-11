import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialH3EnergyCeilingRelativeEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Extract a short initial energy ceiling from an independent right energy trace

The preceding initial comparison asks for a uniform actual H³-energy bound on
an initial interval. An independently established finite right energy trace
produces such a bound on a possibly shorter interval. The relative-energy
coefficient and arbitrarily small residual estimates can be restricted from
the original interval without modifying their physical integrands.

Crucially, the right trace is a separate PDE-side hypothesis. We do not use
the *conclusion* of initial relative-energy uniqueness, which also entails
an initial energy upper trace, as a premise in order to prove itself.
Neither the physical relative-energy inequality nor old-velocity temporal
measurability is derived from open-time Navier--Stokes admissibility here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- A finite right limit furnishes a bounded strict initial interval, which
can be placed inside any preassigned positive restart width. -/
theorem h3Audit_initialRightLimit_shortUpperBound
    (f : ℝ → ℝ) (L b₀ ε : ℝ)
    (hb₀ : 0 < b₀) (hε : 0 < ε)
    (hRight : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    ∃ b : ℝ, 0 < b ∧ b ≤ b₀ ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b → f t ≤ L + ε := by
  obtain ⟨δ, hδ, hNear⟩ :=
    (Metric.tendsto_nhdsWithin_nhds.mp hRight) ε hε
  refine ⟨min δ b₀, lt_min hδ hb₀, min_le_right _ _, ?_⟩
  intro t ht
  have htδ : dist t (0 : ℝ) < δ := by
    have htBound : t < δ := lt_of_lt_of_le ht.2 (min_le_left δ b₀)
    simpa only [Real.dist_eq, sub_zero, abs_of_pos ht.1] using htBound
  have hSmall : dist (f t) L < ε := hNear (Set.mem_Ioi.mpr ht.1) htδ
  have hAbs : |f t - L| < ε := by
    simpa only [Real.dist_eq] using hSmall
  have hUpper := (abs_lt.mp hAbs).2
  linarith

/-- Restrict a coefficient-inside-the-integral comparison and its L¹-small
residual to a smaller positive initial interval. The residual total mass
cannot increase under this restriction. -/
theorem h3Audit_initialIntegratedComparison_restrict_initialInterval
    (e : ℝ → ℝ) (b b₀ K : ℝ)
    (hb : 0 < b) (hbb₀ : b ≤ b₀)
    (hEpsilon : ∀ ε : ℝ, 0 < ε →
      ∃ (κ R : ℝ → ℝ),
        ContinuousOn κ (Set.Icc (0 : ℝ) b₀) ∧
        (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b₀ → κ s ≤ K) ∧
        IntervalIntegrable (fun s : ℝ => |R s|) volume 0 b₀ ∧
        (∫ s in (0 : ℝ)..b₀, |R s|) ≤ ε ∧
        ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b₀ →
          e t ≤ (∫ s in (0 : ℝ)..t, κ s * e s) +
            (∫ s in (0 : ℝ)..t, |R s|)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ (κ R : ℝ → ℝ),
        ContinuousOn κ (Set.Icc (0 : ℝ) b) ∧
        (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b → κ s ≤ K) ∧
        IntervalIntegrable (fun s : ℝ => |R s|) volume 0 b ∧
        (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
        ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
          e t ≤ (∫ s in (0 : ℝ)..t, κ s * e s) +
            (∫ s in (0 : ℝ)..t, |R s|) := by
  intro ε hε
  obtain ⟨κ, R, hκCont, hκBound, hRInt, hMass, hApprox⟩ :=
    hEpsilon ε hε
  have hClosedSubset : Set.Icc (0 : ℝ) b ⊆ Set.Icc (0 : ℝ) b₀ := by
    intro t ht
    exact ⟨ht.1, ht.2.trans hbb₀⟩
  have hIntervalSubset : Set.uIcc (0 : ℝ) b ⊆ Set.uIcc (0 : ℝ) b₀ := by
    rw [Set.uIcc_of_le hb.le,
      Set.uIcc_of_le (hb.le.trans hbb₀)]
    exact hClosedSubset
  have hRIntSmall :
      IntervalIntegrable (fun s : ℝ => |R s|) volume 0 b :=
    hRInt.mono_set hIntervalSubset
  have hMassSmall :
      (∫ s in (0 : ℝ)..b, |R s|) ≤ ε := by
    exact (h3Audit_initialResidualPrimitive_le_totalAbsMass
      R b₀ b ⟨hb.le, hbb₀⟩ hRInt).trans hMass
  refine ⟨κ, R, hκCont.mono hClosedSubset, ?_,
    hRIntSmall, hMassSmall, ?_⟩
  · intro s hs
    exact hκBound s (hClosedSubset hs)
  · intro t ht
    exact hApprox t ⟨ht.1, ht.2.trans hbb₀⟩

/-- An independent finite right `H³` energy trace provides a short uniform
actual energy ceiling, no matter how small the required restart radius is. -/
theorem h3Audit_initialActualH3Energy_rightTrace_shortCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    (b₀ L : ℝ) (hb₀ : 0 < b₀)
    (hRight : Tendsto (velocityH3EnergyAt u)
      (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    ∃ b : ℝ, 0 < b ∧ b ≤ b₀ ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        velocityH3EnergyAt u t ≤ L + 1 := by
  exact h3Audit_initialRightLimit_shortUpperBound
    (velocityH3EnergyAt u) L b₀ 1 hb₀ (by norm_num) hRight

/-- PDE-facing initial uniqueness interface with an independent right
`H³` energy limit instead of a separately stipulated uniform initial
energy ceiling. Comparison estimates and old-velocity measurability are
still required on the original restart interval. -/
def H3AuditInitialCanonicalRightEnergyTraceRelativeEnergyData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (A : ℝ) (hA : 0 < A)
    (hU₀ : ‖velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0‖ ≤ A)
    (b₀ : ℝ),
    0 < b₀ ∧ b₀ < T ∧
    b₀ ≤ h3FinHeatLerayRestartRadius 1 A ∧
    ∃ (L K : ℝ),
      Tendsto (velocityH3EnergyAt u) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
      AEStronglyMeasurable
        (h3AuditInitialOldPhysicalHilbertTotal hH3)
        ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) b₀)) ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ (κ R : ℝ → ℝ),
          ContinuousOn κ (Set.Icc (0 : ℝ) b₀) ∧
          (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b₀ → κ s ≤ K) ∧
          IntervalIntegrable (fun s => |R s|) volume 0 b₀ ∧
          (∫ s in (0 : ℝ)..b₀, |R s|) ≤ ε ∧
          ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b₀ →
            ‖h3AuditInitialCanonicalPhysicalDifference
              hH3 hFourier0 A hA hU₀ t‖ ^ 2 ≤
              (∫ s in (0 : ℝ)..t,
                κ s * ‖h3AuditInitialCanonicalPhysicalDifference
                  hH3 hFourier0 A hA hU₀ s‖ ^ 2) +
              (∫ s in (0 : ℝ)..t, |R s|)

/-- Shrink the restart interval to extract the actual uniform H³-energy
ceiling. All relative-energy coefficient and residual hypotheses restrict to
that interval, preserving the same approximation tolerance and `K`. -/
theorem h3Audit_initialRightEnergyTrace_implies_H3EnergyCeilingData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalRightEnergyTraceRelativeEnergyData hH3) :
    H3AuditInitialCanonicalH3EnergyCeilingRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b₀, hb₀, hb₀T, hb₀R, L, K, hRight, hOldMeas, hEpsilon⟩ := hData
  obtain ⟨b, hb, hbb₀, hEnergy⟩ :=
    h3Audit_initialActualH3Energy_rightTrace_shortCeiling
      b₀ L hb₀ hRight
  have hSmallSet : Set.Ioo (0 : ℝ) b ⊆ Set.Ioo (0 : ℝ) b₀ := by
    intro t ht
    exact ⟨ht.1, lt_of_lt_of_le ht.2 hbb₀⟩
  have hOldMeasB :
      AEStronglyMeasurable
        (h3AuditInitialOldPhysicalHilbertTotal hH3)
        ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) b)) :=
    hOldMeas.mono_measure (Measure.restrict_mono hSmallSet le_rfl)
  have hEpsilonB :=
    h3Audit_initialIntegratedComparison_restrict_initialInterval
      (fun t : ℝ =>
        ‖h3AuditInitialCanonicalPhysicalDifference
          hH3 hFourier0 A hA hU₀ t‖ ^ 2)
      b b₀ K hb hbb₀ hEpsilon
  exact ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, lt_of_le_of_lt hbb₀ hb₀T,
    hbb₀.trans hb₀R, L + 1, K, hOldMeasB, hEnergy, hEpsilonB⟩

/-- Initial compact weak-test uniqueness from an independently supplied
right physical energy trace and positive-time relative-energy estimates. -/
theorem h3Audit_initialRightEnergyTrace_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalRightEnergyTraceRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialH3EnergyCeiling_implies_compactWeakComparisonData
    hH3 (h3Audit_initialRightEnergyTrace_implies_H3EnergyCeilingData
      hH3 hData)

/-- Initial physical `L²` and upper `H³` traces from the same condition. -/
theorem h3Audit_initialRightEnergyTrace_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalRightEnergyTraceRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialH3EnergyCeiling_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialRightEnergyTrace_implies_H3EnergyCeilingData
      hH3 hData)

/-- Terminal strong-H³ actual vorticity remains a separate hypothesis. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialRightEnergyTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalRightEnergyTraceRelativeEnergyData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialH3EnergyCeiling
    hH3 hClass i hPhysical
    (h3Audit_initialRightEnergyTrace_implies_H3EnergyCeilingData
      hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
