import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralDuhamelIntegratedClosure
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Topology

/-!
# Closed convex realization of the physical heat--Leray Duhamel term

The preceding checkpoints give two complementary facts:

* exact complex decoding commutes with the Bochner interval integral; and
* at every strict retarded time, the decoded integrand lies in the physical
  `L²` closure of genuine Schwartz heat--Leray anchors for that positive lag.

Bochner integration preserves closed convex sets after normalization by the
length of the time interval.  We therefore collect all genuine positive-lag
heat--Leray anchors occurring up to time `t`, take their real convex hull and
then its metric closure.  The normalized decoded Duhamel term belongs to this
closed convex hull.

This is the first time-integrated realization theorem: the continuum of
retarded nonlinear interactions is reduced to the closed convex hull of the
genuine Schwartz anchor family.  No measurable selection of individual
Schwartz approximants is required.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-- All genuine physical Schwartz heat--Leray anchors with positive lag at
most the final time `t`. -/
def H3SchwartzHeatLerayDuhamelPhysicalAnchorRange
    (ν t : ℝ)
    (hν : 0 < ν) :
    Set H3ComplexPhysicalFinVectorL2 :=
  {u : H3ComplexPhysicalFinVectorL2 |
    ∃ τ : ℝ, ∃ hτ : 0 < τ,
      τ ≤ t ∧
        H3SchwartzHeatLerayPhysicalFinVectorL2Anchor
          ν τ hν hτ u}

/-- Closed real convex hull of all genuine positive-lag physical Schwartz
heat--Leray anchors available up to final time `t`. -/
def H3SchwartzHeatLerayDuhamelPhysicalClosedConvexHull
    (ν t : ℝ)
    (hν : 0 < ν) :
    Set H3ComplexPhysicalFinVectorL2 :=
  closure
    (convexHull ℝ
      (H3SchwartzHeatLerayDuhamelPhysicalAnchorRange ν t hν))

/-- The closure of the anchor family at any fixed positive lag `τ ≤ t` sits
inside the global Duhamel closed convex hull. -/
theorem closure_h3SchwartzHeatLerayPhysicalFinVectorL2Anchor_subset_duhamelClosedConvexHull
    {ν t τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (hτt : τ ≤ t) :
    closure
        {u : H3ComplexPhysicalFinVectorL2 |
          H3SchwartzHeatLerayPhysicalFinVectorL2Anchor ν τ hν hτ u}
      ⊆
    H3SchwartzHeatLerayDuhamelPhysicalClosedConvexHull ν t hν := by
  intro u hu
  unfold H3SchwartzHeatLerayDuhamelPhysicalClosedConvexHull
  apply closure_mono ?_ hu
  intro v hv
  apply subset_convexHull ℝ
  exact ⟨τ, hτ, hτt, hv⟩

/-- Contractive decoding preserves interval integrability of the spectral
retarded integrand. -/
theorem h3SpectralFinHeatLerayDuhamelIntegrand_decodeComplexL2_intervalIntegrable
    {ν t : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν U V)
        volume
        0
        t) :
    IntervalIntegrable
      (fun s : ℝ =>
        h3SpectralFinVectorDecodeComplexL2
          (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν U V s))
      volume
      0
      t := by
  let F : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayDuhamelIntegrand ν t hν U V

  have hMeas :
      AEStronglyMeasurable
        (fun s : ℝ => h3SpectralFinVectorDecodeComplexL2 (F s))
        (volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    simpa only [h3SpectralFinVectorDecodeComplexL2CLM_apply] using
      h3SpectralFinVectorDecodeComplexL2CLM.continuous.comp_aestronglyMeasurable
        hInt.aestronglyMeasurable_restrict_uIoc

  refine hInt.mono_fun hMeas ?_
  filter_upwards with s
  exact norm_h3SpectralFinVectorDecodeComplexL2_le (F s)

/-- A normalized Bochner interval integral belongs to the global closed convex
hull whenever its strict pre-endpoint values lie in the corresponding
positive-lag anchor closures. -/
theorem normalized_intervalIntegral_mem_h3SchwartzHeatLerayDuhamelPhysicalClosedConvexHull
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (k : ℝ → H3ComplexPhysicalFinVectorL2)
    (hInt : IntervalIntegrable k volume 0 t)
    (hk :
      ∀ (s : ℝ) (hs : s < t),
        k s ∈ closure
          {u : H3ComplexPhysicalFinVectorL2 |
            H3SchwartzHeatLerayPhysicalFinVectorL2Anchor
              ν (t - s) hν (sub_pos.mpr hs) u}) :
    t⁻¹ • (∫ s in (0 : ℝ)..t, k s)
      ∈ H3SchwartzHeatLerayDuhamelPhysicalClosedConvexHull ν t hν := by
  let A : Set H3ComplexPhysicalFinVectorL2 :=
    H3SchwartzHeatLerayDuhamelPhysicalAnchorRange ν t hν
  let C : Set H3ComplexPhysicalFinVectorL2 :=
    closure (convexHull ℝ A)

  have hCconv : Convex ℝ C := by
    dsimp [C]
    exact (convex_convexHull ℝ A).closure

  have hCclosed : IsClosed C := by
    dsimp [C]
    exact isClosed_closure

  have h0 : volume (Set.Ioc (0 : ℝ) t) ≠ 0 := by
    rw [Real.volume_Ioc]
    simpa using (ENNReal.ofReal_ne_zero_iff.mpr ht)

  have htop : volume (Set.Ioc (0 : ℝ) t) ≠ ∞ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top

  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [MeasureTheory.ae_iff]
    simpa using (Real.volume_singleton (a := t))

  have hmem :
      ∀ᵐ s : ℝ ∂volume.restrict (Set.Ioc (0 : ℝ) t),
        k s ∈ C := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hne] with s hst
    intro hsIoc
    have hslt : s < t := lt_of_le_of_ne hsIoc.2 hst
    have hlag : 0 < t - s := sub_pos.mpr hslt
    have hlag_le : t - s ≤ t := by
      linarith [hsIoc.1]
    dsimp [C, A]
    exact
      closure_h3SchwartzHeatLerayPhysicalFinVectorL2Anchor_subset_duhamelClosedConvexHull
        hν hlag hlag_le (hk s hslt)

  have havg :
      (⨍ s in Set.Ioc (0 : ℝ) t, k s)
        ∈ C :=
    hCconv.set_average_mem hCclosed h0 htop hmem hInt.1

  dsimp [C, A] at havg ⊢
  rw [MeasureTheory.setAverage_eq] at havg
  rw [Real.volume_real_Ioc_of_le (le_of_lt ht)] at havg
  simp only [sub_zero] at havg
  rw [← intervalIntegral.integral_of_le (le_of_lt ht)] at havg
  exact havg

/-- The normalized decoded spectral Duhamel term belongs to the closed real
convex hull of genuine physical Schwartz heat--Leray anchors with positive lag
at most `t`. -/
theorem h3SpectralFinHeatLerayDuhamel_decodeComplexL2_normalized_mem_closedConvexHull
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V : ℝ → H3SpectralFinVectorState)
    (hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν U V)
        volume
        0
        t) :
    t⁻¹ •
        h3SpectralFinVectorDecodeComplexL2
          (h3SpectralFinHeatLerayDuhamel ν t hν U V)
      ∈ H3SchwartzHeatLerayDuhamelPhysicalClosedConvexHull ν t hν := by
  let k : ℝ → H3ComplexPhysicalFinVectorL2 :=
    fun s =>
      h3SpectralFinVectorDecodeComplexL2
        (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν U V s)

  have hIntPhysical : IntervalIntegrable k volume 0 t := by
    dsimp [k]
    exact
      h3SpectralFinHeatLerayDuhamelIntegrand_decodeComplexL2_intervalIntegrable
        hν U V hInt

  have hk :
      ∀ (s : ℝ) (hs : s < t),
        k s ∈ closure
          {u : H3ComplexPhysicalFinVectorL2 |
            H3SchwartzHeatLerayPhysicalFinVectorL2Anchor
              ν (t - s) hν (sub_pos.mpr hs) u} := by
    intro s hs
    dsimp [k]
    exact
      h3SpectralFinHeatLerayDuhamelIntegrand_decodeComplexL2_mem_closure
        hν hs U V

  have hClosed :=
    normalized_intervalIntegral_mem_h3SchwartzHeatLerayDuhamelPhysicalClosedConvexHull
      hν ht k hIntPhysical hk

  rw [h3SpectralFinHeatLerayDuhamel_decodeComplexL2_eq_intervalIntegral
    hν U V hInt]
  exact hClosed

/-- Automatic closed-convex realization on the continuous globally bounded
restart-path class. -/
theorem h3SpectralFinHeatLerayDuhamel_decodeComplexL2_normalized_mem_closedConvexHull_of_continuous
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV) :
    t⁻¹ •
        h3SpectralFinVectorDecodeComplexL2
          (h3SpectralFinHeatLerayDuhamel ν t hν U V)
      ∈ H3SchwartzHeatLerayDuhamelPhysicalClosedConvexHull ν t hν := by
  have hUint :
      ∀ s ∈ Set.Ioc (0 : ℝ) t,
        ‖U s‖ ≤ MU := by
    intro s _hs
    exact hU s

  have hVint :
      ∀ s ∈ Set.Ioc (0 : ℝ) t,
        ‖V s‖ ≤ MV := by
    intro s _hs
    exact hV s

  have hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν U V)
        volume
        0
        t :=
    h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
      hν (le_of_lt ht) hMU hMV U V
      hUcont hVcont hUint hVint

  exact
    h3SpectralFinHeatLerayDuhamel_decodeComplexL2_normalized_mem_closedConvexHull
      hν ht U V hInt

end

end Euclidean
end Bridge
end PrimeTensor
