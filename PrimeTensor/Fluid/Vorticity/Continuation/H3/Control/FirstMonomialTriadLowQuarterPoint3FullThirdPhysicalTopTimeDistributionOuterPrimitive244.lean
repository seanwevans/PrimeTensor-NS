import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionDefect244
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Recovering physical weak FTC from a time-distribution primitive representation

On a slightly larger strict preterminal interval `(c,d)`, suppose the regular
scalar distribution of old physical momentum is the distribution of the
canonical projected-source primitive plus some spatial-test-dependent scalar
constant. The previously proved regular-distribution injectivity upgrades that
distribution equality to pointwise equality at every time in `(c,d)`.

Any smaller closed interval `[a,b]` contained in `(c,d)` then satisfies the
*actual physical Hilbert* FTC identity: the scalar integration constants cancel
in the increment, and Leray-fixed solenoidal weak-test density kills the Hilbert
defect. This gives weak FTC on the closed subwindow, not merely in distribution.

Crucial boundary: no zero-derivative distribution is asserted to be constant
here. Deriving that uniqueness result on connected intervals, and deriving the
original distributional momentum PDE from the spatially tested old PDE, remain
independent analytic steps. No new axioms, proof placeholders, or time-regularity hypotheses
are inserted into `LoggedPreterminalH3PathAdmissible`.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set TopologicalSpace
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology Distributions

noncomputable section
set_option maxHeartbeats 1800000

/-- The continuous scalar candidate for the old momentum pairing: the genuine
projected-source primitive with an arbitrary integration constant. -/
noncomputable def h3PathPhysicalTestSourcePrimitiveAddConstant244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (c : ℝ) (φ : H3WeakTestVector) (K : ℝ) : ℝ → ℝ :=
  fun t => (∫ s in c..t,
    h3PathPhysicalTestProjectedSourceTime244 hH3 φ s) + K

/-- Regular-distribution equality against the source primitive plus a scalar
constant determines the ACTUAL physical scalar momentum at every interior
time. The key input is continuous-distribution injectivity, not an a.e.
representative choice. -/
theorem h3Path_physicalTestMomentum_eq_sourcePrimitiveAddConstant_onStrict244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {c d : ℝ} (hc : 0 < c) (hcd : c < d) (hd : d < T)
    (φ : H3WeakTestVector) (K : ℝ)
    (hEq :
      h3PathRegularTimeDistribution244 (h3PathStrictTimeOpen244 c d)
        (h3PathPhysicalTestMomentumTime244 hH3 φ) =
      h3PathRegularTimeDistribution244 (h3PathStrictTimeOpen244 c d)
        (h3PathPhysicalTestSourcePrimitiveAddConstant244 hH3 c φ K)) :
    ∀ t : ℝ, t ∈ Set.Ioo c d →
      h3PathPhysicalTestMomentumTime244 hH3 φ t =
        h3PathPhysicalTestSourcePrimitiveAddConstant244 hH3 c φ K t := by
  let R : ℝ → ℝ := h3PathPhysicalTestProjectedSourceTime244 hH3 φ
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
  have hJCont : ContinuousOn
      (fun t : ℝ => ∫ s in c..t, R s) (Set.Icc c d) := by
    have h := intervalIntegral.continuousOn_primitive_interval'
      hRInt left_mem_uIcc
    simpa only [Set.uIcc_of_le hcd.le] using h
  have hCandidateCont : ContinuousOn
      (h3PathPhysicalTestSourcePrimitiveAddConstant244 hH3 c φ K)
      (Set.Ioo c d) := by
    change ContinuousOn (fun t : ℝ => (∫ s in c..t, R s) + K) (Set.Ioo c d)
    exact (hJCont.add continuousOn_const).mono Set.Ioo_subset_Icc_self
  have hCandidateLoc : LocallyIntegrableOn
      (h3PathPhysicalTestSourcePrimitiveAddConstant244 hH3 c φ K)
      (h3PathStrictTimeOpen244 c d) (volume : Measure ℝ) :=
    hCandidateCont.locallyIntegrableOn measurableSet_Ioo
  exact h3Path_physicalTestMomentum_eqOn_of_distribution_eq244
    hH3 hc hcd hd φ
    (h3PathPhysicalTestSourcePrimitiveAddConstant244 hH3 c φ K)
    hCandidateLoc hCandidateCont hEq

/-- A distributional primitive representation on a larger strict time window
forces the *actual* physical Hilbert momentum FTC defect to vanish on every
smaller closed interval. Constants depend on the spatial test and cancel. -/
theorem h3Path_projectedFTCDefect_eq_zero_of_outerPrimitiveDistributions244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {c a b d : ℝ}
    (hc : 0 < c) (hca : c < a) (hab : a < b) (hbd : b < d) (hd : d < T)
    (hRepresentation : ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      ∃ K : ℝ,
        h3PathRegularTimeDistribution244 (h3PathStrictTimeOpen244 c d)
          (h3PathPhysicalTestMomentumTime244 hH3 φ) =
        h3PathRegularTimeDistribution244 (h3PathStrictTimeOpen244 c d)
          (h3PathPhysicalTestSourcePrimitiveAddConstant244 hH3 c φ K)) :
    h3PathActualProjectedMomentumFTCDefect244 hH3 a b = 0 := by
  have ha : 0 < a := hc.trans hca
  have hb : b < T := hbd.trans hd
  apply (h3Path_projectedFTCDefect_eq_zero_iff_solenoidalPairings244
    hH3 ha hab hb).2
  intro φ hφ
  obtain ⟨K, hEq⟩ := hRepresentation φ hφ
  let M : ℝ → ℝ := h3PathPhysicalTestMomentumTime244 hH3 φ
  let R : ℝ → ℝ := h3PathPhysicalTestProjectedSourceTime244 hH3 φ
  have hPoint := h3Path_physicalTestMomentum_eq_sourcePrimitiveAddConstant_onStrict244
    hH3 hc (hca.trans (hab.trans hbd)) hd φ K hEq
  have hMa : M a = (∫ s in c..a, R s) + K := by
    simpa only [M, R, h3PathPhysicalTestSourcePrimitiveAddConstant244] using
      hPoint a ⟨hca, hab.trans hbd⟩
  have hMb : M b = (∫ s in c..b, R s) + K := by
    simpa only [M, R, h3PathPhysicalTestSourcePrimitiveAddConstant244] using
      hPoint b ⟨hca.trans hab, hbd⟩
  have hRCont : ContinuousOn R (Set.Icc c d) := by
    have hSource := h3Path_actualProjectedMomentumSource_continuousOnStrict244
      hH3 hc (hca.trans (hab.trans hbd)) hd
    change ContinuousOn
      (fun t : ℝ => ((innerSL ℝ) (h3WeakTestVectorPhysicalL2Hilbert φ))
        (h3PathActualProjectedMomentumSource244 hH3 t)) (Set.Icc c d)
    exact ((innerSL ℝ) (h3WeakTestVectorPhysicalL2Hilbert φ)).continuous.comp_continuousOn
      hSource
  have hCA : IntervalIntegrable R volume c a :=
    (hRCont.mono (by
      intro s hs
      exact ⟨hs.1, hs.2.trans (hab.trans hbd).le⟩)).intervalIntegrable_of_Icc hca.le
  have hAB : IntervalIntegrable R volume a b :=
    (hRCont.mono (by
      intro s hs
      exact ⟨hca.le.trans hs.1, hs.2.trans hbd.le⟩)).intervalIntegrable_of_Icc hab.le
  have hAdd :
      (∫ s in c..a, R s) + (∫ s in a..b, R s) =
        ∫ s in c..b, R s :=
    intervalIntegral.integral_add_adjacent_intervals hCA hAB
  rw [h3Path_projectedFTCDefect_solenoidalPairing_eq_residual244
    hH3 ha hab hb φ, inner_sub_right]
  change M b - M a - (∫ s in a..b, R s) = 0
  rw [hMa, hMb]
  linarith only [hAdd]

/-- The outer distributional primitive representation implies exact compact
solenoidal weak FTC on any smaller CLOSED strict physical time interval.
The Hilbert FTC defect is proved zero on every prefix, not only at its endpoint. -/
theorem h3Path_solenoidalWeakFTC_of_outerPrimitiveDistributions244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {c a b d : ℝ}
    (hc : 0 < c) (hca : c < a) (hab : a < b) (hbd : b < d) (hd : d < T)
    (hRepresentation : ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      ∃ K : ℝ,
        h3PathRegularTimeDistribution244 (h3PathStrictTimeOpen244 c d)
          (h3PathPhysicalTestMomentumTime244 hH3 φ) =
        h3PathRegularTimeDistribution244 (h3PathStrictTimeOpen244 c d)
          (h3PathPhysicalTestSourcePrimitiveAddConstant244 hH3 c φ K)) :
    H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) a b := by
  have ha : 0 < a := hc.trans hca
  have hb : b < T := hbd.trans hd
  apply (h3Path_projectedFTCDefect_zeroOn_iff_solenoidalWeakFTC244
    hH3 ha hab hb).1
  intro r hr
  by_cases heq : r = a
  · subst r
    simp [h3PathActualProjectedMomentumFTCDefect244]
  · have har : a < r := by
      have hle : a ≤ r := hr.1
      rcases lt_or_eq_of_le hle with hlt | hEq
      · exact hlt
      · exact (heq hEq.symm).elim
    exact h3Path_projectedFTCDefect_eq_zero_of_outerPrimitiveDistributions244
      hH3 hc hca har (lt_of_le_of_lt hr.2 hbd) hd hRepresentation

end
end PrimeTensor.FirstMonomialTriad
