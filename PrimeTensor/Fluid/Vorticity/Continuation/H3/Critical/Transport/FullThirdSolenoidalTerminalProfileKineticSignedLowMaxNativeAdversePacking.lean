import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCertifiedFrequencyOccupancy
import Mathlib.Tactic

/-!
# Native signed sixth flux: select genuine annuli before global packing

The preceding global inverse-eleventh occupancy theorem took an arbitrary
`active` predicate equipped with physical annular peak/width/charge witnesses.
This module eliminates that separately supplied certificate hypothesis.

For a prescribed family of actual observation times t(k) and inner radii R(k),
we define activity by the ACTUAL adverse signed sixth-flux derivative, exclusion
of the previously proved tenth-power residual, and low relative H3 gap cost.
The established cofinal certified-eleventh theorem supplies an actual annulus
for every sufficiently late active k. Classical choice selects the same outer
Q(k) and persistence width w(k) in all subsequent physical statements.

The result is a native global occupancy inequality for genuinely adverse
observations, retaining each annular H3 peak, its exact persistence width,
and its genuine gap dissipation charge. It does not claim that adverse
observations occur, recur, or are dense. No extra PDE premise is introduced.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open Classical
open scoped BigOperators Interval ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The ACTUAL qualifying adverse signed-flux observation on the kth original
kinetic gap. Neither annular cutoff Q nor persistence width w is part of
this predicate: they will be obtained from the established physical theorem. -/
def ThirdFullKineticSignedLowMaxNativeAdverseGap244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (eta : ℝ) (J : ℕ) (E epsilon : ℝ)
    (tau delta : ℕ → ℝ) (v R : ℕ → ℕ) (t : ℕ → ℝ)
    (k : ℕ) : Prop :=
  let x : ℝ := tau (v k) + delta (v k)
  let y : ℝ := tau (v (k + 1))
  let h : ℝ := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
  let D : ℝ := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
  t k ∈ Set.Icc x y ∧
    eta < -velocityH3TransportDerivative3At u (t k) ∧
    ¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
      hH3 (R k) J E eta epsilon x y (t k) ∧
    16 * D < (y - x) * h

/-- Genuine physical data retained after selecting a finite annulus: the
outer radius, the exact kinetic persistence width, the actual annular peak,
and its original full-H3 gap cost are all tied to the SAME index. -/
def ThirdFullKineticSignedLowMaxNativeSelectedAnnulus244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (eta b : ℝ) (tau delta : ℕ → ℝ) (v R : ℕ → ℕ)
    (t : ℕ → ℝ) (k Q : ℕ) (w : ℝ) : Prop :=
  let x : ℝ := tau (v k) + delta (v k)
  let y : ℝ := tau (v (k + 1))
  let H : ℝ := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
    (R k) eta (velocityH3EnergyAt u (t k))
  let E0 : ℝ := velocityH3Energy0At u b
  let D : ℝ := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
  R k ≤ Q ∧ 0 < w ∧
    w = thirdFullKineticSignedLowMaxSymmetricGapWidth244
      (R k) Q E0 H x y ∧
    H / 2 <
      h3PathActualLowRadialDissipation244 ((Q : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (t k)) -
      h3PathActualLowRadialDissipation244 ((R k : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (t k)) ∧
    w * (H / 4) ≤ D

/-- NATIVE PHYSICAL PACKING. Starting with actual selected inner cutoffs
and observation times, the established cofinal signed-sixth-flux theorem
constructs the outer annulus and its width on EVERY sufficiently late
qualifying gap. The selected annuli are simultaneously charged to the
single terminal full-H3 dissipation budget. The activity predicate contains
only the signed-flux observation, residual exclusion, and low-density test;
no physical annular certificate is postulated in the premises. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_nativeAdverseCertifiedOccupancy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (tau : ℕ → ℝ) (N : ℕ → ℕ)
    (delta : ℕ → ℝ) (v : ℕ → ℕ)
    (hLimit : Tendsto (fun k => tau (v k)) atTop (𝓝 T))
    (hSeparated : ∀ k l : ℕ, k < l →
      tau (v k) + delta (v k) < tau (v l))
    (hWindows : ∀ k : ℕ,
      tau (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (tau (v k)) (v k) (N (v k))
        (M (v k)) (delta (v k)))
    (eta : ℝ) (hEta : 0 < eta)
    (J : ℕ) (E epsilon : ℝ) (hE : 0 ≤ E) (hEpsilon : 0 < epsilon)
    (R : ℕ → ℕ) (t : ℕ → ℝ) :
    ∃ (k0 : ℕ) (Q : ℕ → ℕ) (w : ℕ → ℝ),
      (∀ k : ℕ, k0 ≤ k →
        ThirdFullKineticSignedLowMaxNativeAdverseGap244
          hH3 eta J E epsilon tau delta v R t k →
        ThirdFullKineticSignedLowMaxGapPackingCertificate244
          hH3 eta b tau delta v R Q t w k) ∧
      (∀ (B m : ℕ),
        thirdFullKineticSignedLowMaxCertifiedLowFrequencyCount244
          (fun k => k0 ≤ k ∧
            ThirdFullKineticSignedLowMaxNativeAdverseGap244
              hH3 eta J E epsilon tau delta v R t k)
          Q B m *
          ((thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E) ^ 2 /
            (32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244
              (velocityH3Energy0At u b))) ≤
          ((B : ℝ) + 1) ^ 11 *
            (∫ r in a..T, velocityH3DissipationAt u r ∂volume)) := by
  classical
  let native : ℕ → Prop := fun k =>
    ThirdFullKineticSignedLowMaxNativeAdverseGap244
      hH3 eta J E epsilon tau delta v R t k
  have hEventually :=
    thirdFullPhysical_kineticGaps_signedLowMax_trueCertifiedEleventh244
      hH3 hClass hDInt b hb M tau N delta v
      hLimit hSeparated hWindows eta hEta J E epsilon hE hEpsilon
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.1 hEventually
  have hNativeSelect (k : ℕ) (hk : k0 ≤ k) (ha : native k) :
      ∃ (q : ℕ) (z : ℝ),
        ThirdFullKineticSignedLowMaxNativeSelectedAnnulus244
          hH3 eta b tau delta v R t k q z := by
    dsimp only [native, ThirdFullKineticSignedLowMaxNativeAdverseGap244] at ha
    obtain ⟨ht, hAdverse, hNoResidual, hLowDensity⟩ := ha
    obtain ⟨q, z, hRQ, hz, hzEq, hPeak, hCost, _hRate⟩ :=
      hk0 k hk (R k) (t k) ht hAdverse hNoResidual hLowDensity
    exact ⟨q, z, hRQ, hz, hzEq, hPeak, hCost⟩
  have hAny (k : ℕ) :
      ∃ (q : ℕ) (z : ℝ),
        (k0 ≤ k ∧ native k) →
          ThirdFullKineticSignedLowMaxNativeSelectedAnnulus244
            hH3 eta b tau delta v R t k q z := by
    by_cases ha : k0 ≤ k ∧ native k
    · obtain ⟨q, z, hSelection⟩ := hNativeSelect k ha.1 ha.2
      exact ⟨q, z, fun _ => hSelection⟩
    · refine ⟨0, 0, ?_⟩
      intro hContr
      exact False.elim (ha hContr)
  let Q : ℕ → ℕ := fun k => Classical.choose (hAny k)
  let w : ℕ → ℝ := fun k =>
    Classical.choose (Classical.choose_spec (hAny k))
  let active : ℕ → Prop := fun k => k0 ≤ k ∧ native k
  have hPicked (k : ℕ) (hk : active k) :
      ThirdFullKineticSignedLowMaxNativeSelectedAnnulus244
        hH3 eta b tau delta v R t k (Q k) (w k) := by
    exact (Classical.choose_spec (Classical.choose_spec (hAny k))) hk
  have hCertified (k : ℕ) (hk : active k) :
      ThirdFullKineticSignedLowMaxGapPackingCertificate244
        hH3 eta b tau delta v R Q t w k := by
    have hSelection := hPicked k hk
    rcases hSelection with ⟨hRQ, hwPos, hwEq, hPeak, hCost⟩
    have hNative : native k := hk.2
    have ht : t k ∈ Set.Icc
        (tau (v k) + delta (v k)) (tau (v (k + 1))) := by
      dsimp only [native, ThirdFullKineticSignedLowMaxNativeAdverseGap244]
        at hNative
      exact hNative.1
    exact ⟨ht, hRQ, hwPos, hwEq, hPeak, hCost⟩
  have hEnergyCap (k : ℕ) (hk : active k) :
      velocityH3EnergyAt u (t k) ≤ E := by
    have hNative : native k := hk.2
    dsimp only [native, ThirdFullKineticSignedLowMaxNativeAdverseGap244]
      at hNative
    obtain ⟨_ht, _hAdverse, hNoResidual, _hLowDensity⟩ := hNative
    by_contra hn
    apply hNoResidual
    unfold ThirdFullKineticSignedLowMaxTenthPowerResidual244
    exact Or.inr (Or.inl (Or.inr (Or.inl (lt_of_not_ge hn))))
  have hLowDensity (k : ℕ) (hk : active k) :
      16 * (∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
        velocityH3DissipationAt u r ∂volume) <
      (tau (v (k + 1)) - (tau (v k) + delta (v k))) *
        thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E := by
    have hNative : native k := hk.2
    dsimp only [native, ThirdFullKineticSignedLowMaxNativeAdverseGap244]
      at hNative
    exact hNative.2.2.2
  refine ⟨k0, Q, w, ?_, ?_⟩
  · intro k hk hAdverse
    exact hCertified k ⟨hk, hAdverse⟩
  · intro B m
    exact thirdFullPhysical_kineticGaps_signedLowMax_certifiedFrequencyOccupancy244
      hH3 hClass hDInt b hb M tau N delta v hSeparated hWindows
      eta E hEta hE active R Q t w hCertified hEnergyCap hLowDensity B m

end
end PrimeTensor.FirstMonomialTriad
