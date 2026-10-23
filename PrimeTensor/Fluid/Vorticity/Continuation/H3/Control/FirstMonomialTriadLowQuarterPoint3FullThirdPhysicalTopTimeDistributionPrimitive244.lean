import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionInjectivity244
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# The projected physical momentum source has its expected time-distribution primitive

This is the analytic forward half of the distributional primitive argument.
On a strict preterminal window, a continuous scalar source R has an absolutely
continuous primitive J(t) = integral_a^t R(s) ds.

We prove more than an a.e. derivative: J has the ordinary derivative R at
each interior time and the genuine regular time distributions satisfy

   Distribution.lineDerivCLM 1 (T_J) = T_R.

The distribution identity follows via a global compact-support integration
by parts. Its integrability assumptions come from continuous functions on
the strict time interval and compactly supported smooth temporal tests,
NOT from global integrability of R or J. No assumption of the classical
preterminal PDE yielding the old momentum distributional equation is used.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set TopologicalSpace Filter
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology Distributions

noncomputable section
set_option maxHeartbeats 1800000

/-- A continuous scalar source has an everywhere differentiable canonical
primitive at interior strict times. In particular no time regularity of the
*old velocity* is assumed. -/
theorem h3Path_scalarSourcePrimitive_hasDerivAt_onStrict244
    {a b : ℝ} (hab : a < b)
    (R : ℝ → ℝ) (hRCont : ContinuousOn R (Set.Icc a b)) :
    ∀ t : ℝ, t ∈ Set.Ioo a b →
      HasDerivAt (fun y : ℝ => ∫ s in a..y, R s) (R t) t := by
  have hRAt : ∀ y ∈ Set.Ioo a b, ContinuousAt R y := by
    intro y hy
    exact ContinuousWithinAt.continuousAt
      (hRCont y ⟨hy.1.le, hy.2.le⟩)
      (Icc_mem_nhds hy.1 hy.2)
  intro t ht
  have hSub : Set.Icc a t ⊆ Set.Icc a b := by
    intro y hy
    exact ⟨hy.1, hy.2.trans ht.2.le⟩
  have hRInt : IntervalIntegrable R volume a t :=
    (hRCont.mono hSub).intervalIntegrable_of_Icc ht.1.le
  have hRMeas : StronglyMeasurableAtFilter
      R (𝓝 t) (volume : Measure ℝ) := by
    exact ContinuousAt.stronglyMeasurableAtFilter
      (μ := (volume : Measure ℝ)) isOpen_Ioo hRAt t ht
  exact intervalIntegral.integral_hasDerivAt_right
    hRInt hRMeas (hRAt t ht)

/-- The time distribution associated to the canonical integral of a continuous
source differentiates to the actual regular source distribution.

The proof uses global integration by parts with temporal test functions of
compact support. Integrability of products is proved independently using the
local integrability of the scalar primitive/source and the TestFunction API. -/
theorem h3Path_regularTimeDistribution_sourcePrimitive_deriv244
    {a b : ℝ} (hab : a < b)
    (R : ℝ → ℝ) (hRCont : ContinuousOn R (Set.Icc a b)) :
    Distribution.lineDerivCLM (1 : ℝ)
        (h3PathRegularTimeDistribution244 (h3PathStrictTimeOpen244 a b)
          (fun t : ℝ => ∫ s in a..t, R s)) =
      h3PathRegularTimeDistribution244 (h3PathStrictTimeOpen244 a b) R := by
  let Ω : Opens ℝ := h3PathStrictTimeOpen244 a b
  let J : ℝ → ℝ := fun t => ∫ s in a..t, R s
  have hRLoc : LocallyIntegrableOn R Ω (volume : Measure ℝ) := by
    exact (hRCont.mono Set.Ioo_subset_Icc_self).locallyIntegrableOn
      measurableSet_Ioo
  have hRInt : IntervalIntegrable R volume a b :=
    hRCont.intervalIntegrable_of_Icc hab.le
  have hJAC : AbsolutelyContinuousOnInterval J a b := by
    exact hRInt.absolutelyContinuousOnInterval_intervalIntegral
      (c := a) (by
        rw [Set.uIcc_of_le hab.le]
        exact ⟨le_rfl, hab.le⟩)
  have hJContIcc : ContinuousOn J (Set.Icc a b) := by
    have hCont := hJAC.continuousOn
    rw [Set.uIcc_of_le hab.le] at hCont
    exact hCont
  have hJLoc : LocallyIntegrableOn J Ω (volume : Measure ℝ) := by
    exact (hJContIcc.mono Set.Ioo_subset_Icc_self).locallyIntegrableOn
      measurableSet_Ioo
  have hJDeriv : ∀ t : ℝ, t ∈ Set.Ioo a b →
      HasDerivAt J (R t) t := by
    intro t ht
    exact h3Path_scalarSourcePrimitive_hasDerivAt_onStrict244
      hab R hRCont t ht
  ext θ
  let θ' : TestFunction Ω ℝ ⊤ :=
    TestFunction.lineDerivCLM (k := ⊤) ℝ (1 : ℝ) θ
  have hθDiff : Differentiable ℝ (fun t : ℝ => θ t) :=
    θ.contDiff.differentiable (by simp)
  have hθDeriv : ∀ t : ℝ,
      HasDerivAt (fun y : ℝ => θ y) (θ' t) t := by
    intro t
    have htDiff : DifferentiableAt ℝ (fun y : ℝ => θ y) t :=
      hθDiff.differentiableAt
    have htEq :
        θ' t = deriv (fun y : ℝ => θ y) t := by
      simp [θ', TestFunction.lineDerivCLM_apply,
        htDiff.lineDeriv_eq_fderiv, fderiv_apply_one_eq_deriv]
    simpa only [htEq] using htDiff.hasDerivAt
  have hIntJθ' : Integrable (fun t : ℝ => J t * θ' t) volume := by
    have h : Integrable (fun t : ℝ => θ' t • J t) volume :=
      θ'.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hJLoc
    simpa only [smul_eq_mul, mul_comm] using h
  have hIntRθ : Integrable (fun t : ℝ => R t * θ t) volume := by
    have h : Integrable (fun t : ℝ => θ t • R t) volume :=
      θ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hRLoc
    simpa only [smul_eq_mul, mul_comm] using h
  have hIntJθ : Integrable (fun t : ℝ => J t * θ t) volume := by
    have h : Integrable (fun t : ℝ => θ t • J t) volume :=
      θ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hJLoc
    simpa only [smul_eq_mul, mul_comm] using h
  have hIBP :
      (∫ t : ℝ, J t * θ' t) =
        -(∫ t : ℝ, R t * θ t) := by
    exact integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := J) (u' := R)
      (v := fun t : ℝ => θ t) (v' := fun t : ℝ => θ' t)
      (by
        intro t ht
        exact hJDeriv t (θ.tsupport_subset ht))
      (by
        intro t _ht
        exact hθDeriv t)
      hIntJθ' hIntRθ hIntJθ
  change
    Distribution.lineDerivCLM (1 : ℝ)
        (h3PathRegularTimeDistribution244 Ω J) θ =
      h3PathRegularTimeDistribution244 Ω R θ
  rw [Distribution.lineDerivCLM_apply,
    h3Path_regularTimeDistribution_apply244 Ω J hJLoc,
    h3Path_regularTimeDistribution_apply244 Ω R hRLoc]
  simpa only [smul_eq_mul, mul_comm, neg_neg] using congrArg Neg.neg hIBP

/-- Specialization to the actual continuous projected physical Navier--Stokes
source. This is a theorem about the source primitive, not yet a proof that the
old physical velocity satisfies the distributional momentum equation. -/
theorem h3Path_physicalProjectedSourcePrimitive_distributionalDerivative244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (φ : H3WeakTestVector) :
    Distribution.lineDerivCLM (1 : ℝ)
      (h3PathRegularTimeDistribution244 (h3PathStrictTimeOpen244 a b)
        (fun t : ℝ => ∫ s in a..t,
          h3PathPhysicalTestProjectedSourceTime244 hH3 φ s)) =
      h3PathRegularTimeDistribution244 (h3PathStrictTimeOpen244 a b)
        (h3PathPhysicalTestProjectedSourceTime244 hH3 φ) := by
  have hRCont : ContinuousOn
      (h3PathPhysicalTestProjectedSourceTime244 hH3 φ)
      (Set.Icc a b) := by
    have hSource :=
      h3Path_actualProjectedMomentumSource_continuousOnStrict244
        hH3 ha hab hb
    change ContinuousOn
      (fun t : ℝ => ((innerSL ℝ) (h3WeakTestVectorPhysicalL2Hilbert φ))
        (h3PathActualProjectedMomentumSource244 hH3 t)) (Set.Icc a b)
    exact ((innerSL ℝ) (h3WeakTestVectorPhysicalL2Hilbert φ)).continuous.comp_continuousOn
      hSource
  exact h3Path_regularTimeDistribution_sourcePrimitive_deriv244
    hab (h3PathPhysicalTestProjectedSourceTime244 hH3 φ) hRCont

end
end PrimeTensor.FirstMonomialTriad
