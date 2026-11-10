import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxNativeAdversePacking
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticOffshellGapExcess
import Mathlib.Tactic

/-!
# Signed sixth flux: from integrated physical gap surplus to a certified annular fork

The preceding packing theorem takes actual adverse observations as input.
Here the observation is derived from the integrated *physical signed gap
surplus*, using the already-proved low-order/third-order PDE split on the
same original kinetic gap. In particular the adverse time is selected
before (and independently of) the inner Fourier cutoff R.

On all sufficiently late original gaps, a strict integrated surplus
forces one common adverse time, and, for each R under the prescribed radius
cap J, at least one genuine physical obstruction:

* an explicit tenth-power baseline, radius/energy, or earlier viscous cost;
* a positive relative full-H3 dissipation density on the original gap;
* a certified finite annulus Q > B with a positive H3 dissipation peak,
  exact in-gap persistence charge and inverse-eleventh-power frequency cost.

The final alternative is NOT the vacuous existence of Q > B. No recurrence
of surplus, uniform removal of the residual, or continuation is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The SAME physical annulus Q both carries a dissipation peak and pays
its in-gap width/eleventh-power charge. This predicate does not forget the
actual selected time or replace its annulus by a free natural number. -/
def ThirdFullKineticSignedLowMaxSurplusCertifiedAnnulus244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b : ℝ) (R B : ℕ) (eta E x y t : ℝ) : Prop :=
  let H := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
    R eta (velocityH3EnergyAt u t)
  let h := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
  let E0 := velocityH3Energy0At u b
  let D := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
  ∃ (Q : ℕ) (w : ℝ), R ≤ Q ∧ B < Q ∧ 0 < w ∧
    w = thirdFullKineticSignedLowMaxSymmetricGapWidth244
      R Q E0 H x y ∧
    H / 2 <
      h3PathActualLowRadialDissipation244 ((Q : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) -
      h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) ∧
    w * (H / 4) ≤ D ∧
    h ^ 2 / (32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0) ≤
      ((Q : ℝ) + 1) ^ 11 * D

/-- The integrated gap surplus, rather than an externally chosen adverse
observation, produces an actual signed third-order PDE sample. The time
is independent of every Fourier radius and every annular cutoff. -/
theorem thirdFullPhysical_gapSignedSurplus_producesCommonAdverseTime244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (x y eta : ℝ) (hx : x ∈ Set.Ioo a T) (hy : y ∈ Set.Ioo a T)
    (hxy : x < y) (hEta : 0 < eta)
    (hSurplus : thirdFullKineticGapLowOrderMargin244 u eta x y <
      thirdFullKineticGapSignedSurplus244 u x y) :
    ∃ t : ℝ, t ∈ Set.Icc x y ∧
      eta < -velocityH3TransportDerivative3At u t :=
  thirdFullPhysical_gapLowOrderExcess_forces_adverseThird244
    hH3 hClass x y eta hx hy hxy hEta hSurplus

/-- HARD PHYSICAL PDE FORK, UNIFORM IN THE INNER RADIUS. A single adverse
third-order sample is first recovered from an actual positive signed gap
surplus. For EVERY R at or below J, either the original tenth-power residual
persists, or the physical gap itself has sufficient relative dissipation,
or a genuine peak-carrying annulus above B is forced. The original gap,
sample time, Fourier state, width and integral are unchanged. -/
theorem thirdFullPhysical_kineticGaps_signedSurplus_certifiedAnnularFork244
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
    (J B : ℕ) (E epsilon : ℝ)
    (hE : 0 ≤ E) (hEpsilon : 0 < epsilon) :
    ∀ᶠ k : ℕ in atTop,
      let x := tau (v k) + delta (v k)
      let y := tau (v (k + 1))
      let h := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
      let D := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
      thirdFullKineticGapLowOrderMargin244 u eta x y <
        thirdFullKineticGapSignedSurplus244 u x y →
      ∃ t : ℝ, t ∈ Set.Icc x y ∧
        eta < -velocityH3TransportDerivative3At u t ∧
        ∀ R : ℕ, R ≤ J →
          ThirdFullKineticSignedLowMaxTenthPowerResidual244
            hH3 R J E eta epsilon x y t ∨
          (y - x) * h ≤ 16 * D ∨
          ThirdFullKineticSignedLowMaxSurplusCertifiedAnnulus244
            hH3 b R B eta E x y t := by
  have hOld :=
    thirdFullPhysical_kineticGaps_signedLowMax_certifiedOuterBeyondFixed244
      hH3 hClass hDInt b hb M tau N delta v
      hLimit hSeparated hWindows eta hEta J B E epsilon hE hEpsilon
  filter_upwards [hOld] with k hk
  dsimp only
  intro hSurplus
  let x : ℝ := tau (v k) + delta (v k)
  let y : ℝ := tau (v (k + 1))
  let h : ℝ := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
  let D : ℝ := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
  have hx : x ∈ Set.Ioo a T := by
    obtain ⟨hTime, hWindow⟩ := hWindows k
    rcases hWindow with ⟨_, hDelta, _, hEnd, _, _⟩
    exact ⟨by dsimp only [x]; linarith only [hb.1, hTime.1, hDelta], hEnd⟩
  have hy : y ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (hWindows (k + 1)).1.1, (hWindows (k + 1)).1.2⟩
  have hxy : x < y :=
    hSeparated k (k + 1) (Nat.lt_succ_self k)
  obtain ⟨t, ht, hAdverse⟩ :=
    thirdFullPhysical_gapSignedSurplus_producesCommonAdverseTime244
      hH3 hClass x y eta hx hy hxy hEta hSurplus
  refine ⟨t, ht, hAdverse, ?_⟩
  intro R _hRJ
  by_cases hResidual :
      ThirdFullKineticSignedLowMaxTenthPowerResidual244
        hH3 R J E eta epsilon x y t
  · exact Or.inl hResidual
  right
  by_cases hDense : (y - x) * h ≤ 16 * D
  · exact Or.inl hDense
  right
  have hLowDensity : 16 * D < (y - x) * h :=
    lt_of_not_ge hDense
  have hCert := hk R t ht hAdverse hResidual hLowDensity
  exact hCert

/-- Under explicit removal of the two non-annular physical alternatives,
EVERY inner radius at or below the finite cap J has a genuine peak-carrying
outer annulus beyond any fixed B, all at a single PDE-selected signed-surplus
time. The residual exclusion is a substantive physical premise: in particular
it includes baseline and earlier viscous-window alternatives. -/
theorem thirdFullPhysical_kineticGaps_signedSurplus_forcesCertifiedOuter244
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
    (J B : ℕ) (E epsilon : ℝ)
    (hE : 0 ≤ E) (hEpsilon : 0 < epsilon) :
    ∀ᶠ k : ℕ in atTop,
      let x := tau (v k) + delta (v k)
      let y := tau (v (k + 1))
      let h := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
      let D := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
      thirdFullKineticGapLowOrderMargin244 u eta x y <
        thirdFullKineticGapSignedSurplus244 u x y →
      16 * D < (y - x) * h →
      (∀ (t : ℝ), t ∈ Set.Icc x y →
        eta < -velocityH3TransportDerivative3At u t →
        ∀ R : ℕ, R ≤ J →
          ¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
            hH3 R J E eta epsilon x y t) →
      ∃ t : ℝ, t ∈ Set.Icc x y ∧
        eta < -velocityH3TransportDerivative3At u t ∧
        ∀ R : ℕ, R ≤ J →
          ThirdFullKineticSignedLowMaxSurplusCertifiedAnnulus244
            hH3 b R B eta E x y t := by
  have hFork := thirdFullPhysical_kineticGaps_signedSurplus_certifiedAnnularFork244
    hH3 hClass hDInt b hb M tau N delta v
    hLimit hSeparated hWindows eta hEta J B E epsilon hE hEpsilon
  filter_upwards [hFork] with k hk
  dsimp only
  intro hSurplus hLow hNoResidual
  obtain ⟨t, ht, hAdverse, hAlt⟩ := hk hSurplus
  refine ⟨t, ht, hAdverse, ?_⟩
  intro R hRJ
  rcases hAlt R hRJ with hBad | hRest
  · exact False.elim ((hNoResidual t ht hAdverse R hRJ) hBad)
  rcases hRest with hDense | hCert
  · exact False.elim ((not_lt_of_ge hDense) hLow)
  · exact hCert

end
end PrimeTensor.FirstMonomialTriad
