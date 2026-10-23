import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionBridge244
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Tactic

/-!
# Injectivity of continuous physical time distributions and absolutely continuous primitives

The pinned mathlib distribution framework lacks a convenience theorem stating
that a regular scalar distribution determines its continuous representative.
We derive the required statement directly from the existing fundamental lemma
of distribution theory: a locally integrable function with vanishing integrals
against all compact smooth tests vanishes almost everywhere. Positivity of
Lebesgue measure on nonempty open sets upgrades a.e. equality to equality at
EVERY point of the open time window for continuous representatives.

We also prove that the scalar primitive of the actual projected physical source
is absolutely continuous on every strict compact preterminal time interval.
These are two analytic inputs for the next distributional-primitive uniqueness
step. Neither assumes an L2 pressure-gradient time derivative nor asserts that
the old preterminal PDE itself already supplies the distributional identity.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set TopologicalSpace
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology Distributions

noncomputable section
set_option maxHeartbeats 1800000

/-- The regular distribution is faithful on continuous scalar functions:
if two such distributions agree, their time-dependent representatives agree
pointwise on the whole open domain, not merely almost everywhere. -/
theorem h3Path_regularTimeDistribution_eqOn_of_eq244
    (Ω : Opens ℝ) (f g : ℝ → ℝ)
    (hf : LocallyIntegrableOn f Ω (volume : Measure ℝ))
    (hg : LocallyIntegrableOn g Ω (volume : Measure ℝ))
    (hfCont : ContinuousOn f Ω) (hgCont : ContinuousOn g Ω)
    (hEq : h3PathRegularTimeDistribution244 Ω f =
      h3PathRegularTimeDistribution244 Ω g) :
    Set.EqOn f g Ω := by
  have hDiffLoc : LocallyIntegrableOn (f - g) Ω (volume : Measure ℝ) :=
    hf.sub hg
  have hZero : ∀ᵐ t ∂(volume : Measure ℝ),
      t ∈ (Ω : Set ℝ) → (f - g) t = 0 := by
    apply Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hDiffLoc
    intro q hqDiff hqCompact hqSupport
    let θ : TestFunction Ω ℝ ⊤ :=
      ⟨q, by simpa using hqDiff, hqCompact, hqSupport⟩
    have hEqEval :
        (∫ t : ℝ, θ t • f t) = ∫ t : ℝ, θ t • g t := by
      have hApply := congrArg
        (fun D : Distribution Ω ℝ ⊤ => D θ) hEq
      rw [h3Path_regularTimeDistribution_apply244 Ω f hf θ,
        h3Path_regularTimeDistribution_apply244 Ω g hg θ] at hApply
      exact hApply
    have hFInt : Integrable (fun t : ℝ => θ t • f t) volume := by
      exact θ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hf
    have hGInt : Integrable (fun t : ℝ => θ t • g t) volume := by
      exact θ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hg
    change (∫ t : ℝ, θ t • (f - g) t) = 0
    simp_rw [Pi.sub_apply, smul_sub]
    rw [integral_sub hFInt hGInt]
    exact sub_eq_zero.mpr hEqEval
  have hAE : f =ᵐ[(volume : Measure ℝ).restrict Ω] g := by
    apply (ae_restrict_iff' Ω.isOpen.measurableSet).2
    filter_upwards [hZero] with t ht htΩ
    exact sub_eq_zero.mp (ht htΩ)
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hAE Ω.isOpen hfCont hgCont

/-- Actual old physical momentum, tested against any compact spatial test,
is pointwise determined on a strict positive-time interval by its regular
time distribution. The comparison representative need only be continuous
and locally time integrable on that interval. -/
theorem h3Path_physicalTestMomentum_eqOn_of_distribution_eq244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (φ : H3WeakTestVector)
    (f : ℝ → ℝ)
    (hf : LocallyIntegrableOn f (h3PathStrictTimeOpen244 a b)
      (volume : Measure ℝ))
    (hfCont : ContinuousOn f (Set.Ioo a b))
    (hEq : h3PathRegularTimeDistribution244
        (h3PathStrictTimeOpen244 a b)
        (h3PathPhysicalTestMomentumTime244 hH3 φ) =
      h3PathRegularTimeDistribution244 (h3PathStrictTimeOpen244 a b) f) :
    ∀ t : ℝ, t ∈ Set.Ioo a b →
      h3PathPhysicalTestMomentumTime244 hH3 φ t = f t := by
  have hLoc := h3Path_physicalTestMomentum_locallyIntegrableOnStrict244
    hH3 ha hab hb φ
  have hUCont : ContinuousOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3) (Set.Ioo a b) := by
    apply (h3Audit_initialOldPhysicalHilbert_continuousOn hH3).mono
    intro t ht
    exact ⟨ha.trans ht.1, ht.2.trans hb⟩
  have hMomCont : ContinuousOn
      (h3PathPhysicalTestMomentumTime244 hH3 φ) (Set.Ioo a b) := by
    change ContinuousOn
      (fun t : ℝ => ((innerSL ℝ) (h3WeakTestVectorPhysicalL2Hilbert φ))
        (h3AuditInitialOldPhysicalHilbertTotal hH3 t)) (Set.Ioo a b)
    exact ((innerSL ℝ) (h3WeakTestVectorPhysicalL2Hilbert φ)).continuous.comp_continuousOn
      hUCont
  exact h3Path_regularTimeDistribution_eqOn_of_eq244
    (h3PathStrictTimeOpen244 a b)
    (h3PathPhysicalTestMomentumTime244 hH3 φ) f
    hLoc hf hMomCont hfCont hEq

/-- The scalar projected physical source has an absolutely continuous
canonical primitive on every closed strict preterminal time interval. This
uses only already-proved physical L2 source continuity, not temporal
differentiability of the OLD physical velocity. -/
theorem h3Path_physicalProjectedSourcePrimitive_absolutelyContinuous244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (φ : H3WeakTestVector) :
    AbsolutelyContinuousOnInterval
      (fun t : ℝ => ∫ s in a..t,
        h3PathPhysicalTestProjectedSourceTime244 hH3 φ s) a b := by
  have hRCont : ContinuousOn
      (h3PathActualProjectedMomentumSource244 hH3) (Set.Icc a b) :=
    h3Path_actualProjectedMomentumSource_continuousOnStrict244 hH3 ha hab hb
  have hScalarCont : ContinuousOn
      (h3PathPhysicalTestProjectedSourceTime244 hH3 φ) (Set.Icc a b) := by
    change ContinuousOn
      (fun t : ℝ => ((innerSL ℝ) (h3WeakTestVectorPhysicalL2Hilbert φ))
        (h3PathActualProjectedMomentumSource244 hH3 t)) (Set.Icc a b)
    exact ((innerSL ℝ) (h3WeakTestVectorPhysicalL2Hilbert φ)).continuous.comp_continuousOn
      hRCont
  have hInt : IntervalIntegrable
      (h3PathPhysicalTestProjectedSourceTime244 hH3 φ)
      volume a b := hScalarCont.intervalIntegrable_of_Icc hab.le
  exact hInt.absolutelyContinuousOnInterval_intervalIntegral
    (c := a) (by
      rw [Set.uIcc_of_le hab.le]
      exact ⟨le_rfl, hab.le⟩)

end
end PrimeTensor.FirstMonomialTriad
