import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionOuterPrimitive244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopPointwiseSolenoidalMomentum244
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# Physical weak FTC implies the genuine compact-time distributional momentum PDE

The scalar source-primitive distribution theorem proved earlier uses a classical
integration-by-parts calculation with compact temporal tests. The same argument
works for ANY continuous scalar momentum path whose interior derivative is its
continuous source. We prove this more general result and specialize it to the
actual old physical H³ momentum using the existing weak-FTC-to-strong-Hilbert-
derivative bridge.

This is the previously missing REVERSE direction of the distributional-FTC
comparison: it does not assert physical weak FTC from the pointwise old PDE.
That forward direction still requires the distributional PDE and a genuine
connected-interval zero-derivative kernel theorem. No assumptions are inserted
into LoggedPreterminalH3PathAdmissible.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set TopologicalSpace Filter
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology Distributions

noncomputable section
set_option maxHeartbeats 1800000

/-- Compactly supported scalar integration by parts turns an everywhere
interior pointwise derivative into the corresponding regular distributional
derivative. No global time integrability of either scalar function is required. -/
theorem h3Path_regularTimeDistribution_deriv_of_hasDerivAt_onStrict244
    {a b : ℝ} (hab : a < b)
    (M R : ℝ → ℝ)
    (hMCont : ContinuousOn M (Set.Icc a b))
    (hRCont : ContinuousOn R (Set.Icc a b))
    (hDeriv : ∀ t : ℝ, t ∈ Set.Ioo a b → HasDerivAt M (R t) t) :
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℝ)
        (h3PathRegularTimeDistribution244 (h3PathStrictTimeOpen244 a b) M) =
      h3PathRegularTimeDistribution244 (h3PathStrictTimeOpen244 a b) R := by
  let Ω : Opens ℝ := h3PathStrictTimeOpen244 a b
  have hMLoc : LocallyIntegrableOn M Ω (volume : Measure ℝ) := by
    exact (hMCont.mono Set.Ioo_subset_Icc_self).locallyIntegrableOn
      measurableSet_Ioo
  have hRLoc : LocallyIntegrableOn R Ω (volume : Measure ℝ) := by
    exact (hRCont.mono Set.Ioo_subset_Icc_self).locallyIntegrableOn
      measurableSet_Ioo
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
    have htEq : θ' t = deriv (fun y : ℝ => θ y) t := by
      simp [θ', TestFunction.lineDerivCLM_apply,
        htDiff.lineDeriv_eq_fderiv, fderiv_apply_one_eq_deriv]
    simpa only [htEq] using htDiff.hasDerivAt
  have hIntMθ' : Integrable (fun t : ℝ => M t * θ' t) volume := by
    have h : Integrable (fun t : ℝ => θ' t • M t) volume :=
      θ'.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hMLoc
    simpa only [smul_eq_mul, mul_comm] using h
  have hIntRθ : Integrable (fun t : ℝ => R t * θ t) volume := by
    have h : Integrable (fun t : ℝ => θ t • R t) volume :=
      θ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hRLoc
    simpa only [smul_eq_mul, mul_comm] using h
  have hIntMθ : Integrable (fun t : ℝ => M t * θ t) volume := by
    have h : Integrable (fun t : ℝ => θ t • M t) volume :=
      θ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hMLoc
    simpa only [smul_eq_mul, mul_comm] using h
  have hIBP :
      (∫ t : ℝ, M t * θ' t) = -(∫ t : ℝ, R t * θ t) := by
    exact integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := M) (u' := R)
      (v := fun t : ℝ => θ t) (v' := fun t : ℝ => θ' t)
      (by
        intro t ht
        exact hDeriv t (θ.tsupport_subset ht))
      (by
        intro t _ht
        exact hθDeriv t)
      hIntMθ' hIntRθ hIntMθ
  change
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℝ)
        (h3PathRegularTimeDistribution244 Ω M) θ =
      h3PathRegularTimeDistribution244 Ω R θ
  rw [Distribution.lineDerivCLM_apply,
    h3Path_regularTimeDistribution_apply244 Ω M hMLoc,
    h3Path_regularTimeDistribution_apply244 Ω R hRLoc]
  simpa only [smul_eq_mul, mul_comm, neg_neg] using congrArg Neg.neg hIBP

/-- The actual physical solenoidal weak FTC, if established on a strict closed
window, implies the corresponding genuine scalar momentum distributional PDE.
This theorem makes no inference in the reverse direction. -/
theorem h3Path_distributionalMomentum_of_physicalSolenoidalWeakFTC244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hWeak : H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) a b) :
    h3PathSolenoidalDistributionalMomentumOn244 hH3 a b := by
  intro φ hφ
  have hInside : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hUCont : ContinuousOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3) (Set.Icc a b) :=
    (h3Audit_initialOldPhysicalHilbert_continuousOn hH3).mono hInside
  have hMCont : ContinuousOn
      (h3PathPhysicalTestMomentumTime244 hH3 φ) (Set.Icc a b) := by
    change ContinuousOn
      (fun t : ℝ => ((innerSL ℝ) (h3WeakTestVectorPhysicalL2Hilbert φ))
        (h3AuditInitialOldPhysicalHilbertTotal hH3 t)) (Set.Icc a b)
    exact ((innerSL ℝ) (h3WeakTestVectorPhysicalL2Hilbert φ)).continuous.comp_continuousOn
      hUCont
  have hSourceCont :=
    h3Path_actualProjectedMomentumSource_continuousOnStrict244 hH3 ha hab hb
  have hRCont : ContinuousOn
      (h3PathPhysicalTestProjectedSourceTime244 hH3 φ) (Set.Icc a b) := by
    change ContinuousOn
      (fun t : ℝ => ((innerSL ℝ) (h3WeakTestVectorPhysicalL2Hilbert φ))
        (h3PathActualProjectedMomentumSource244 hH3 t)) (Set.Icc a b)
    exact ((innerSL ℝ) (h3WeakTestVectorPhysicalL2Hilbert φ)).continuous.comp_continuousOn
      hSourceCont
  have hDeriv : ∀ t : ℝ, t ∈ Set.Ioo a b →
      HasDerivAt
        (h3PathPhysicalTestMomentumTime244 hH3 φ)
        (h3PathPhysicalTestProjectedSourceTime244 hH3 φ t) t := by
    intro t ht
    exact h3Path_pointwiseWeakMomentum_of_solenoidalWeakFTC244
      hH3 ha hab hb hWeak φ hφ t ht
  exact h3Path_regularTimeDistribution_deriv_of_hasDerivAt_onStrict244
    hab
    (h3PathPhysicalTestMomentumTime244 hH3 φ)
    (h3PathPhysicalTestProjectedSourceTime244 hH3 φ)
    hMCont hRCont hDeriv

/-- Physical weak FTC also implies the explicit compact-time-test momentum
identity, by the previously proved equivalence between temporal regular
distributions and time tests. -/
theorem h3Path_timeTestMomentum_of_physicalSolenoidalWeakFTC244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hWeak : H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) a b) :
    h3PathSolenoidalTimeTestMomentumOn244 hH3 a b := by
  exact (h3Path_distributionalMomentum_iff_timeTestMomentum244
    hH3 ha hab hb).mp
      (h3Path_distributionalMomentum_of_physicalSolenoidalWeakFTC244
        hH3 ha hab hb hWeak)

end
end PrimeTensor.FirstMonomialTriad
