import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxSignedSurplusAnnularFork
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxNativeAdversePacking
import Mathlib.Tactic

/-!
# Integrated signed-gap surplus: select the actual witnesses into one global packing

The previous physical fork produced an adverse third-order transport sample
from a strict integrated signed gap surplus. The native-adverse packing theorem
selected physical annuli globally, but still took a time sequence as input.

Here a gap is marked active ONLY when its actual positive signed transport
surplus beats the verified lower-order budget, its true relative H3 gap cost
is below the fixed positive capped-height floor, and the previously established
tenth-power residual is excluded at ALL adverse third-order samples in that
gap for the prescribed inner cutoff. This uniform exclusion is substantive:
finite terminal dissipation by itself does not prove it.

The signed physical PDE chooses an adverse time on each active gap BEFORE
frequency selection. The accepted native theorem then supplies a real
finite-annular peak, exact persistence width and integrated gap charge.
The same chosen Q and width enter both the inverse-eleventh global ledger
and the finite-frequency occupancy bound. No recurrence, bounded outer
frequency, terminal H3 trace, or new Navier--Stokes axiom is assumed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology Classical
open scoped BigOperators Interval ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- A *physical* signed-surplus event on the original kth kinetic gap.
No adverse snapshot time or annular cutoff is provided in this hypothesis.
The residual exclusion is required for every possible PDE-selected adverse
sample at the prescribed natural inner radius. -/
def ThirdFullKineticSignedLowMaxSurplusPackingActive244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (eta : ℝ) (J : ℕ) (E epsilon : ℝ)
    (tau delta : ℕ → ℝ) (v R : ℕ → ℕ) (k : ℕ) : Prop :=
  let x : ℝ := tau (v k) + delta (v k)
  let y : ℝ := tau (v (k + 1))
  let h : ℝ := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
  let D : ℝ := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
  R k ≤ J ∧
    thirdFullKineticGapLowOrderMargin244 u eta x y <
      thirdFullKineticGapSignedSurplus244 u x y ∧
    16 * D < (y - x) * h ∧
    (∀ z : ℝ, z ∈ Set.Icc x y →
      eta < -velocityH3TransportDerivative3At u z →
      ¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
        hH3 (R k) J E eta epsilon x y z)

/-- Every active integrated-surplus gap has an actual adverse physical
third-order time, independent of how its Fourier outer radius is chosen.
This uses the original PDE signed-surplus integral, not an assumed sample. -/
theorem thirdFullPhysical_signedLowMax_surplusPackingActive_adverseTime244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (tau : ℕ → ℝ) (N : ℕ → ℕ)
    (delta : ℕ → ℝ) (v R : ℕ → ℕ)
    (hSeparated : ∀ k l : ℕ, k < l →
      tau (v k) + delta (v k) < tau (v l))
    (hWindows : ∀ k : ℕ,
      tau (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (tau (v k)) (v k) (N (v k))
        (M (v k)) (delta (v k)))
    (eta : ℝ) (hEta : 0 < eta) (J : ℕ) (E epsilon : ℝ)
    (k : ℕ)
    (hk : ThirdFullKineticSignedLowMaxSurplusPackingActive244
      hH3 eta J E epsilon tau delta v R k) :
    ∃ z : ℝ,
      z ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) ∧
      eta < -velocityH3TransportDerivative3At u z := by
  have hActive := hk
  dsimp only [ThirdFullKineticSignedLowMaxSurplusPackingActive244] at hActive
  obtain ⟨_hRJ, hSurplus, _hLow, _hNoResidual⟩ := hActive
  let x : ℝ := tau (v k) + delta (v k)
  let y : ℝ := tau (v (k + 1))
  have hx : x ∈ Set.Ioo a T := by
    obtain ⟨hTime, hw⟩ := hWindows k
    rcases hw with ⟨_, hdelta, _, hEnd, _, _⟩
    exact ⟨by dsimp only [x]; linarith only [hb.1, hTime.1, hdelta], hEnd⟩
  have hy : y ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (hWindows (k + 1)).1.1,
      (hWindows (k + 1)).1.2⟩
  have hxy : x < y :=
    hSeparated k (k + 1) (Nat.lt_succ_self k)
  exact thirdFullPhysical_gapSignedSurplus_producesCommonAdverseTime244
    hH3 hClass x y eta hx hy hxy hEta hSurplus

/-- GLOBAL PHYSICAL SURPLUS PACKING. On sufficiently late original gaps,
strict integrated surplus together with subcritical relative dissipation
and the explicit all-adverse-time tenth-power residual exclusion produces
ONE physical time and ONE genuine certified annulus per active gap.
The *same* selected annuli obey both the weighted global packing ledger
and the low-frequency occupancy bound, without assuming active gaps recur. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_surplusGlobalPacking244
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
    (R : ℕ → ℕ) :
    ∃ (k0 : ℕ) (t : ℕ → ℝ) (Q : ℕ → ℕ) (w : ℕ → ℝ),
      (∀ k : ℕ, k0 ≤ k →
        ThirdFullKineticSignedLowMaxSurplusPackingActive244
          hH3 eta J E epsilon tau delta v R k →
        t k ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) ∧
        eta < -velocityH3TransportDerivative3At u (t k) ∧
        ThirdFullKineticSignedLowMaxGapPackingCertificate244
          hH3 eta b tau delta v R Q t w k) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          if k0 ≤ k ∧
              ThirdFullKineticSignedLowMaxSurplusPackingActive244
                hH3 eta J E epsilon tau delta v R k then
            ((thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E) ^ 2 /
              (32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244
                (velocityH3Energy0At u b))) / (((Q k : ℝ) + 1) ^ 11)
          else 0) ≤
        ∫ r in a..T, velocityH3DissipationAt u r ∂volume) ∧
      (∀ (B m : ℕ),
        thirdFullKineticSignedLowMaxCertifiedLowFrequencyCount244
          (fun k => k0 ≤ k ∧
            ThirdFullKineticSignedLowMaxSurplusPackingActive244
              hH3 eta J E epsilon tau delta v R k)
          Q B m *
          ((thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E) ^ 2 /
            (32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244
              (velocityH3Energy0At u b))) ≤
          ((B : ℝ) + 1) ^ 11 *
            (∫ r in a..T, velocityH3DissipationAt u r ∂volume)) := by
  classical
  let active : ℕ → Prop := fun k =>
    ThirdFullKineticSignedLowMaxSurplusPackingActive244
      hH3 eta J E epsilon tau delta v R k
  have hSelect (k : ℕ) (hk : active k) :
      ∃ z : ℝ,
        z ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) ∧
        eta < -velocityH3TransportDerivative3At u z :=
    thirdFullPhysical_signedLowMax_surplusPackingActive_adverseTime244
      hH3 hClass b hb M tau N delta v R hSeparated hWindows
      eta hEta J E epsilon k hk
  have hAny (k : ℕ) : ∃ z : ℝ, active k →
      z ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) ∧
        eta < -velocityH3TransportDerivative3At u z := by
    by_cases hk : active k
    · obtain ⟨z, ht, hAdverse⟩ := hSelect k hk
      exact ⟨z, fun _ => ⟨ht, hAdverse⟩⟩
    · exact ⟨0, fun h => False.elim (hk h)⟩
  let t : ℕ → ℝ := fun k => Classical.choose (hAny k)
  have hTime (k : ℕ) (hk : active k) :
      t k ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) ∧
        eta < -velocityH3TransportDerivative3At u (t k) :=
    (Classical.choose_spec (hAny k)) hk
  have hNative (k : ℕ) (hk : active k) :
      ThirdFullKineticSignedLowMaxNativeAdverseGap244
        hH3 eta J E epsilon tau delta v R t k := by
    have hAt := hTime k hk
    have hActive := hk
    dsimp only [active, ThirdFullKineticSignedLowMaxSurplusPackingActive244]
      at hActive
    obtain ⟨_hRJ, _hSurplus, hLow, hReject⟩ := hActive
    change t k ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) ∧
      eta < -velocityH3TransportDerivative3At u (t k) ∧
      ¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
        hH3 (R k) J E eta epsilon
          (tau (v k) + delta (v k)) (tau (v (k + 1))) (t k) ∧
      16 * (∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
          velocityH3DissipationAt u r ∂volume) <
        (tau (v (k + 1)) - (tau (v k) + delta (v k))) *
          thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
    exact ⟨hAt.1, hAt.2, hReject (t k) hAt.1 hAt.2, hLow⟩
  obtain ⟨k0, Q, w, hNativeCert, _hNativeCount⟩ :=
    thirdFullPhysical_kineticGaps_signedLowMax_nativeAdverseCertifiedOccupancy244
      hH3 hClass hDInt b hb M tau N delta v
      hLimit hSeparated hWindows eta hEta J E epsilon hE hEpsilon R t
  let selected : ℕ → Prop := fun k => k0 ≤ k ∧ active k
  have hCert (k : ℕ) (hk : selected k) :
      ThirdFullKineticSignedLowMaxGapPackingCertificate244
        hH3 eta b tau delta v R Q t w k :=
    hNativeCert k hk.1 (hNative k hk.2)
  have hEnergyCap (k : ℕ) (hk : selected k) :
      velocityH3EnergyAt u (t k) ≤ E := by
    have hNativeAt := hNative k hk.2
    dsimp only [ThirdFullKineticSignedLowMaxNativeAdverseGap244] at hNativeAt
    obtain ⟨_ht, _hAdverse, hBad, _hLow⟩ := hNativeAt
    by_contra hn
    apply hBad
    unfold ThirdFullKineticSignedLowMaxTenthPowerResidual244
    exact Or.inr (Or.inl (Or.inr (Or.inl (lt_of_not_ge hn))))
  have hLowDensity (k : ℕ) (hk : selected k) :
      16 * (∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
        velocityH3DissipationAt u r ∂volume) <
      (tau (v (k + 1)) - (tau (v k) + delta (v k))) *
        thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E := by
    have hNativeAt := hNative k hk.2
    dsimp only [ThirdFullKineticSignedLowMaxNativeAdverseGap244] at hNativeAt
    exact hNativeAt.2.2.2
  refine ⟨k0, t, Q, w, ?_, ?_, ?_⟩
  · intro k hk ha
    have hAt := hTime k ha
    exact ⟨hAt.1, hAt.2, hCert k ⟨hk, ha⟩⟩
  · intro m
    have hPacked :=
      thirdFullPhysical_kineticGaps_signedLowMax_certifiedFinitePacking244
        hH3 hClass hDInt b hb M tau N delta v hSeparated hWindows
        eta E hEta hE selected R Q t w hCert hEnergyCap hLowDensity m
    -- Compare the two actual sums before using the packed inequality.
    -- Their proposition tests coincide, but Lean can synthesize distinct
    -- `Decidable` instances for those tests.  The transitivity midpoint is
    -- the EXACT sum in `hPacked`, retaining its original instance.
    refine (le_of_eq ?_).trans hPacked
    apply Finset.sum_congr rfl
    intro k _hk
    by_cases hs : selected k
    · have hc : k0 ≤ k ∧
          ThirdFullKineticSignedLowMaxSurplusPackingActive244
            hH3 eta J E epsilon tau delta v R k := hs
      simp only [if_pos hc, if_pos hs]
    · have hc : ¬(k0 ≤ k ∧
          ThirdFullKineticSignedLowMaxSurplusPackingActive244
            hH3 eta J E epsilon tau delta v R k) := hs
      simp only [if_neg hc, if_neg hs]
  · intro B m
    exact thirdFullPhysical_kineticGaps_signedLowMax_certifiedFrequencyOccupancy244
      hH3 hClass hDInt b hb M tau N delta v hSeparated hWindows
      eta E hEta hE selected R Q t w hCert hEnergyCap hLowDensity B m

end
end PrimeTensor.FirstMonomialTriad
