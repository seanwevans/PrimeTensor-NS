import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopProjectedFTCDefectWeakDetermination244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialAutomaticOldTimeMeasurability
import Mathlib.Tactic

/-!
# Continuous projected Hilbert FTC defect and dense-time weak determination

The actual old physical velocity is strongly continuous on the strictly
preterminal interval (proved in the initial-velocity audit).  The actual
projected physical source is strongly continuous and Bochner-integrable on
all compact strict-time intervals.  Therefore the *discrepancy* between the
physical velocity increment and the integrated projected source is itself
continuous in its upper endpoint.

The preceding module proved that a zero discrepancy on every prefix is
equivalent to the physical solenoidal weak FTC.  Here we show that it is
sufficient to verify zero discrepancy at only a DENSE family of endpoints,
by the actual strong continuity.  The endpoint family may be countable and
may depend on the interval.  This is a topological reduction, not a proof of
unconditional weak FTC: dense-endpoint defect zero remains an explicit
analytic requirement.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The physical Hilbert FTC defect is continuous in the upper endpoint on
any strictly positive compact time interval.  Both pieces are known to be
continuous independently of any scalar weak-FTC hypothesis. -/
theorem h3Path_projectedFTCDefect_continuousOnStrict244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T) :
    ContinuousOn
      (fun r : ℝ => h3PathActualProjectedMomentumFTCDefect244 hH3 a r)
      (Set.Icc a b) := by
  let F : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hSub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T := by
    intro r hr
    exact ⟨lt_of_lt_of_le ha hr.1, lt_of_le_of_lt hr.2 hb⟩
  have hF : ContinuousOn F (Set.Icc a b) :=
    (h3Audit_initialOldPhysicalHilbert_continuousOn hH3).mono hSub
  have hGInt : IntervalIntegrable G volume a b :=
    h3Path_actualProjectedMomentumSource_intervalIntegrableStrict244
      hH3 ha hab hb
  have hPrim : ContinuousOn
      (fun r : ℝ => ∫ s in a..r, G s)
      (Set.Icc a b) := by
    have h := intervalIntegral.continuousOn_primitive_interval'
      hGInt left_mem_uIcc
    simpa only [Set.uIcc_of_le hab.le] using h
  change ContinuousOn
    (fun r : ℝ => F r - F a - ∫ s in a..r, G s)
    (Set.Icc a b)
  exact (hF.sub continuousOn_const).sub hPrim

/-- The sampled physical evolution identity at a dense set of endpoints
extends to the entire strict-time interval by strong L² continuity. -/
theorem h3Path_projectedFTCDefect_zeroOn_of_denseEndpointZero244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    {D : Type*}
    (ι : D → Set.Icc a b)
    (hDense : DenseRange ι)
    (hSamples : ∀ d : D,
      h3PathActualProjectedMomentumFTCDefect244 hH3 a (ι d : ℝ) = 0) :
    ∀ r : ℝ, r ∈ Set.Icc a b →
      h3PathActualProjectedMomentumFTCDefect244 hH3 a r = 0 := by
  have hContinuous : Continuous
      (fun q : Set.Icc a b =>
        h3PathActualProjectedMomentumFTCDefect244 hH3 a (q : ℝ)) :=
    (h3Path_projectedFTCDefect_continuousOnStrict244
      hH3 ha hab hb).domRestrict
  have hAll :
      (fun q : Set.Icc a b =>
        h3PathActualProjectedMomentumFTCDefect244 hH3 a (q : ℝ)) =
      (fun _q : Set.Icc a b =>
        (0 : H3PhysicalRealFinVectorL2Hilbert)) := by
    apply hDense.equalizer hContinuous continuous_const
    funext d
    exact hSamples d
  intro r hr
  exact congrFun hAll ⟨r, hr⟩

/-- The strong Bochner weak FTC can be recovered from evolution identities
checked on a dense set of physical endpoint times, rather than everywhere. -/
theorem h3Path_solenoidalWeakFTC_of_denseEndpointDefectZero244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    {D : Type*}
    (ι : D → Set.Icc a b)
    (hDense : DenseRange ι)
    (hSamples : ∀ d : D,
      h3PathActualProjectedMomentumFTCDefect244 hH3 a (ι d : ℝ) = 0) :
    H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) a b := by
  apply (h3Path_projectedFTCDefect_zeroOn_iff_solenoidalWeakFTC244
    hH3 ha hab hb).1
  exact h3Path_projectedFTCDefect_zeroOn_of_denseEndpointZero244
    hH3 ha hab hb ι hDense hSamples

/-- On a strict physical time window, scalar solenoidal weak FTC is EXACTLY
equivalent to sampled Hilbert defect vanishing on ANY given dense family of
endpoint times. This does not claim the dense samples vanish without proof. -/
theorem h3Path_denseEndpointDefectZero_iff_solenoidalWeakFTC244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    {D : Type*}
    (ι : D → Set.Icc a b)
    (hDense : DenseRange ι) :
    (∀ d : D,
      h3PathActualProjectedMomentumFTCDefect244 hH3 a (ι d : ℝ) = 0) ↔
    H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) a b := by
  constructor
  · intro hSamples
    exact h3Path_solenoidalWeakFTC_of_denseEndpointDefectZero244
      hH3 ha hab hb ι hDense hSamples
  · intro hWeak d
    have hZero :=
      (h3Path_projectedFTCDefect_zeroOn_iff_solenoidalWeakFTC244
        hH3 ha hab hb).2 hWeak
    exact hZero (ι d : ℝ) (ι d).property

/-- A dense family of scalar compact-solenoidal evolution identities
already determines the full physical Hilbert evolution.  For each sampled
strict time the Leray-fixed weak-determination theorem upgrades scalar
pairings to an actual Hilbert identity; the initial endpoint is automatic. -/
theorem h3Path_solenoidalWeakFTC_of_denseEndpointWeakPairings244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    {D : Type*}
    (ι : D → Set.Icc a b)
    (hDense : DenseRange ι)
    (hPair : ∀ d : D, ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PathActualProjectedMomentumFTCDefect244 hH3 a (ι d : ℝ)) = 0) :
    H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) a b := by
  apply h3Path_solenoidalWeakFTC_of_denseEndpointDefectZero244
    hH3 ha hab hb ι hDense
  intro d
  rcases lt_or_eq_of_le (ι d).property.1 with hlt | heq
  · exact (h3Path_projectedFTCDefect_eq_zero_iff_solenoidalPairings244
      hH3 ha hlt (lt_of_le_of_lt (ι d).property.2 hb)).2 (hPair d)
  · have hr : (ι d : ℝ) = a := heq.symm
    simpa only [hr] using
      (by simp [h3PathActualProjectedMomentumFTCDefect244] :
        h3PathActualProjectedMomentumFTCDefect244 hH3 a a = 0)

end
end PrimeTensor.FirstMonomialTriad
