import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionZeroMassPrimitiveGlobal244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionOuterPrimitive244
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# From physical momentum distributions to the genuine Hilbert weak FTC

The zero-derivative kernel theorem on a connected time interval is now
unconditional. This module combines it with the physical FTC-defect reduction
and the previously established outer-primitive-to-weak-FTC implication.

First we verify addition for the concrete regular-distribution constructor
used by the pinned mathlib revision. Next, a momentum distributional identity
on an outer strict window produces a source-primitive-plus-constant
representation against every compact solenoidal spatial test. Consequently
all physical Hilbert FTC defects vanish on interior closed time windows, and
the physical solenoidal weak FTC holds there.

The physical distributional momentum equation is an EXPLICIT premise. It
remains to derive this from the old physical PDE and justified time/spatial
testing; none of the present implications asserts that step unconditionally.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set TopologicalSpace
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology Distributions

noncomputable section
set_option maxHeartbeats 1800000

/-- The actual regular time-distribution constructor is additive on locally
integrable scalar functions, with no global integrability assumption. -/
theorem h3Path_regularTimeDistribution_add244
    (Ω : Opens ℝ) (f g : ℝ → ℝ)
    (hf : LocallyIntegrableOn f Ω (volume : Measure ℝ))
    (hg : LocallyIntegrableOn g Ω (volume : Measure ℝ)) :
    h3PathRegularTimeDistribution244 Ω (fun t => f t + g t) =
      h3PathRegularTimeDistribution244 Ω f +
        h3PathRegularTimeDistribution244 Ω g := by
  ext θ
  have hfi : Integrable (fun t : ℝ => θ t • f t) volume :=
    θ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hf
  have hgi : Integrable (fun t : ℝ => θ t • g t) volume :=
    θ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hg
  calc
    h3PathRegularTimeDistribution244 Ω (fun t => f t + g t) θ =
        ∫ t : ℝ, θ t • (f t + g t) :=
      h3Path_regularTimeDistribution_apply244 Ω
        (fun t => f t + g t) (hf.add hg) θ
    _ = (∫ t : ℝ, θ t • f t) + (∫ t : ℝ, θ t • g t) := by
      simp only [smul_add]
      exact integral_add hfi hgi
    _ = (h3PathRegularTimeDistribution244 Ω f +
          h3PathRegularTimeDistribution244 Ω g) θ := by
      -- The sum of two distributions acts pointwise on temporal tests.
      -- `map_add` concerns addition in an argument, not in the dual space.
      change (∫ t : ℝ, θ t • f t) + (∫ t : ℝ, θ t • g t) =
        h3PathRegularTimeDistribution244 Ω f θ +
          h3PathRegularTimeDistribution244 Ω g θ
      rw [h3Path_regularTimeDistribution_apply244 Ω f hf θ,
        h3Path_regularTimeDistribution_apply244 Ω g hg θ]

/-- On an outer strict time interval, the genuine distributional momentum
identity yields a primitive-plus-constant representation for every compact
solenoidal spatial test. There is no remaining compact-test-spanning premise. -/
theorem h3Path_outerPrimitiveDistributions_of_distributionalMomentum244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {c d : ℝ} (hc : 0 < c) (hcd : c < d) (hd : d < T)
    (hMomentum : h3PathSolenoidalDistributionalMomentumOn244 hH3 c d) :
    ∀ φ : H3WeakTestVector, H3WeakTestVectorDivergenceFree φ →
      ∃ K : ℝ,
        h3PathRegularTimeDistribution244 (h3PathStrictTimeOpen244 c d)
          (h3PathPhysicalTestMomentumTime244 hH3 φ) =
        h3PathRegularTimeDistribution244 (h3PathStrictTimeOpen244 c d)
          (h3PathPhysicalTestSourcePrimitiveAddConstant244 hH3 c φ K) := by
  intro φ hφ
  obtain ⟨K, hDefect⟩ :=
    h3Path_physicalFTCDefect_constantDistribution_onStrict244
      hH3 hc hcd hd hMomentum φ hφ
  let Ω : Opens ℝ := h3PathStrictTimeOpen244 c d
  let M : ℝ → ℝ := h3PathPhysicalTestMomentumTime244 hH3 φ
  let R : ℝ → ℝ := h3PathPhysicalTestProjectedSourceTime244 hH3 φ
  let J : ℝ → ℝ := fun t => ∫ s in c..t, R s
  have hRCont : ContinuousOn R (Set.Icc c d) := by
    have hSource := h3Path_actualProjectedMomentumSource_continuousOnStrict244
      hH3 hc hcd hd
    change ContinuousOn
      (fun t : ℝ => ((innerSL ℝ) (h3WeakTestVectorPhysicalL2Hilbert φ))
        (h3PathActualProjectedMomentumSource244 hH3 t)) (Set.Icc c d)
    exact ((innerSL ℝ) (h3WeakTestVectorPhysicalL2Hilbert φ)).continuous.comp_continuousOn
      hSource
  have hRInt : IntervalIntegrable R volume c d :=
    hRCont.intervalIntegrable_of_Icc hcd.le
  have hJCont : ContinuousOn J (Set.Icc c d) := by
    have h := intervalIntegral.continuousOn_primitive_interval'
      hRInt left_mem_uIcc
    simpa only [Set.uIcc_of_le hcd.le] using h
  have hJLoc : LocallyIntegrableOn J Ω (volume : Measure ℝ) :=
    (hJCont.mono Set.Ioo_subset_Icc_self).locallyIntegrableOn
      measurableSet_Ioo
  have hKLoc : LocallyIntegrableOn (fun _ : ℝ => K) Ω
      (volume : Measure ℝ) :=
    continuousOn_const.locallyIntegrableOn measurableSet_Ioo
  have hRegSum :
      h3PathRegularTimeDistribution244 Ω (fun t => J t + K) =
        h3PathRegularTimeDistribution244 Ω J +
          h3PathRegularTimeDistribution244 Ω (fun _ : ℝ => K) :=
    h3Path_regularTimeDistribution_add244 Ω J (fun _ : ℝ => K) hJLoc hKLoc
  change h3PathRegularTimeDistribution244 Ω M -
      h3PathRegularTimeDistribution244 Ω J =
        h3PathRegularTimeDistribution244 Ω (fun _ : ℝ => K) at hDefect
  refine ⟨K, ?_⟩
  change h3PathRegularTimeDistribution244 Ω M =
    h3PathRegularTimeDistribution244 Ω (fun t => J t + K)
  calc
    h3PathRegularTimeDistribution244 Ω M =
        h3PathRegularTimeDistribution244 Ω (fun _ : ℝ => K) +
          h3PathRegularTimeDistribution244 Ω J :=
      sub_eq_iff_eq_add.mp hDefect
    _ = h3PathRegularTimeDistribution244 Ω J +
          h3PathRegularTimeDistribution244 Ω (fun _ : ℝ => K) := by
      abel
    _ = h3PathRegularTimeDistribution244 Ω (fun t => J t + K) :=
      hRegSum.symm

/-- A distributional physical momentum equation on a larger preterminal
window forces the actual physical projected Hilbert FTC defect to vanish
between any two strictly interior times. -/
theorem h3Path_projectedFTCDefect_eq_zero_of_outerDistributionalMomentum244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {c a b d : ℝ}
    (hc : 0 < c) (hca : c < a) (hab : a < b) (hbd : b < d) (hd : d < T)
    (hMomentum : h3PathSolenoidalDistributionalMomentumOn244 hH3 c d) :
    h3PathActualProjectedMomentumFTCDefect244 hH3 a b = 0 := by
  exact h3Path_projectedFTCDefect_eq_zero_of_outerPrimitiveDistributions244
    hH3 hc hca hab hbd hd
    (h3Path_outerPrimitiveDistributions_of_distributionalMomentum244
      hH3 hc (hca.trans (hab.trans hbd)) hd hMomentum)

/-- **Distributional momentum implies actual physical solenoidal weak FTC**
on any smaller closed strict interval. The distributional momentum PDE remains
an explicit premise: this theorem is the completed scalar-analytic converse
to the already formalized weak-FTC-to-distribution direction. -/
theorem h3Path_solenoidalWeakFTC_of_outerDistributionalMomentum244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {c a b d : ℝ}
    (hc : 0 < c) (hca : c < a) (hab : a < b) (hbd : b < d) (hd : d < T)
    (hMomentum : h3PathSolenoidalDistributionalMomentumOn244 hH3 c d) :
    H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) a b := by
  exact h3Path_solenoidalWeakFTC_of_outerPrimitiveDistributions244
    hH3 hc hca hab hbd hd
    (h3Path_outerPrimitiveDistributions_of_distributionalMomentum244
      hH3 hc (hca.trans (hab.trans hbd)) hd hMomentum)

end
end PrimeTensor.FirstMonomialTriad
