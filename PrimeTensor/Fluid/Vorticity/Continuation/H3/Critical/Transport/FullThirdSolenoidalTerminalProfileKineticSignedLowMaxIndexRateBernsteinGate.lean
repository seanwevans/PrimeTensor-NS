import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxAdaptiveShellSaturation
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# Signed sixth flux: exact index-rate Bernstein gate

The accepted first-excluded-band result identifies the deficit at G(k)+1.
Here we expose an additional, genuinely quantitative consequence of the
MAXIMAL affordable gauge: if the kinetic rate at the full INDEX k is still
affordable, then G(k)=k. Thus the adverse sixth-flux annular cutoff must
exceed the actual gap index unless that index-rate budget, or the gap's
relative physical H3 dissipation, is paid.

The one-band rate is expanded into the accepted physical kinetic Bernstein
weight and projected-source ceiling, so the rate branch is a concrete
physical frequency-dependent payment, not an unspecified temporal modulus.
No uniform polynomial bound for the source Fourier ball volume is assumed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Expand the exact finite-band kinetic PDE dissipation rate into its
physical Bernstein weight and actual projected-source ceiling. -/
theorem thirdFullKinetic_signedLowMax_bandRate_eq_BernsteinSource244
    (j : ℕ) (E0 : ℝ) :
    thirdFullPhysicalKineticLowBandDissipationRate244 j E0 =
      6 * ((j : ℝ) + 2) ^ 2 *
        (thirdFullFiniteBandH3WeightCeiling244 j) ^ 2 *
        Real.sqrt E0 *
        thirdFullPhysicalKineticLowBandSourceCeiling244
          ((j : ℝ) + 1) E0 := by
  unfold thirdFullPhysicalKineticLowBandDissipationRate244
  ring

/-- An affordable rate budget AT THE INDEX k forces the greatest affordable
natural cutoff below k to equal k. This is stronger than mere divergence
of that cutoff, and uses no monotonicity of individual band rates. -/
theorem thirdFullKinetic_signedLowMax_indexAffordable_fullGauge244
    (C D : ℕ → ℝ) (h : ℝ) (k : ℕ)
    (hIndex : 32 * C k * D k < h ^ 2) :
    thirdFullKineticSignedLowMaxAdaptiveBudgetGauge244 C D h k = k := by
  classical
  have hAbove : k ≤ Nat.findGreatest
      (fun j : ℕ => 32 * C j * D k < h ^ 2) k :=
    Nat.le_findGreatest (Nat.le_refl k) hIndex
  have hBelow : Nat.findGreatest
      (fun j : ℕ => 32 * C j * D k < h ^ 2) k ≤ k :=
    Nat.findGreatest_le k
  change Nat.findGreatest
    (fun j : ℕ => 32 * C j * D k < h ^ 2) k = k
  exact Nat.le_antisymm hBelow hAbove

/-- If the adaptive cutoff has not reached k, then k's exact finite-band
kinetic rate budget is necessarily unaffordable. -/
theorem thirdFullKinetic_signedLowMax_indexRate_unaffordable_of_below244
    (C D : ℕ → ℝ) (h : ℝ) (k : ℕ)
    (hBelow : thirdFullKineticSignedLowMaxAdaptiveBudgetGauge244 C D h k < k) :
    h ^ 2 ≤ 32 * C k * D k := by
  by_contra hn
  have hAffordable : 32 * C k * D k < h ^ 2 := lt_of_not_ge hn
  have hEq := thirdFullKinetic_signedLowMax_indexAffordable_fullGauge244
    C D h k hAffordable
  omega

/-- Given an adaptive signed-flux fork, replace the moving outer threshold
G(k) by the actual kinetic-gap index k. If the index rate cannot be paid,
then the witness annulus has an outer radius STRICTLY greater than k. -/
theorem thirdFullKinetic_signedLowMax_indexRateOrOuter_scalar244
    (C D : ℕ → ℝ) (h : ℝ) (k R : ℕ) (P : Prop)
    (hFork : P ∨
      ∃ Q : ℕ, R ≤ Q ∧
        thirdFullKineticSignedLowMaxAdaptiveBudgetGauge244 C D h k < Q) :
    P ∨ h ^ 2 ≤ 32 * C k * D k ∨
      ∃ Q : ℕ, R ≤ Q ∧ k < Q := by
  rcases hFork with hClock | ⟨Q, hRQ, hOuter⟩
  · exact Or.inl hClock
  right
  by_cases hIndex : 32 * C k * D k < h ^ 2
  · right
    have hEq := thirdFullKinetic_signedLowMax_indexAffordable_fullGauge244
      C D h k hIndex
    rw [hEq] at hOuter
    exact ⟨Q, hRQ, hOuter⟩
  · exact Or.inl (le_of_not_gt hIndex)

/-- A paid positive index-rate budget forces a genuinely positive H3 gap
charge, and yields its exact reciprocal coefficient threshold. -/
theorem thirdFullKinetic_signedLowMax_indexRate_inverseGapCharge244
    (h C D : ℝ) (hh : 0 < h) (hC : 0 < C)
    (hRate : h ^ 2 ≤ 32 * C * D) :
    0 < D ∧ h ^ 2 / (32 * C) ≤ D := by
  have hCoeff : 0 < 32 * C := by positivity
  have hD : 0 < D := by
    by_contra hn
    have hDle : D ≤ 0 := le_of_not_gt hn
    have hProd : 32 * C * D ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hCoeff.le hDle
    have hSq : 0 < h ^ 2 := pow_pos hh 2
    linarith only [hRate, hProd, hSq]
  refine ⟨hD, ?_⟩
  apply (div_le_iff₀ hCoeff).mpr
  calc
    h ^ 2 ≤ 32 * C * D := hRate
    _ = D * (32 * C) := by ring

/-- Direct physical alternative on ORIGINAL cofinal kinetic gaps. The
adaptive gauge is still recorded as tending to infinity, but its moving
cutoff is eliminated from the flux conclusion. Each adverse physical
sample whose earlier tenth-power residual is ruled out must pay either
relative full-H3 gap dissipation, the exact INDEX-k Bernstein/source rate
budget, or a certified annular outer radius strictly exceeding k.

There is no assumption that C(k)D(k) tends to zero: that unproved estimate
is exposed as the second physical obstruction. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_tenthResidual_indexRateGate244
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
    (J : ℕ) (E epsilon : ℝ) (hE : 0 ≤ E) (hEpsilon : 0 < epsilon) :
    let h : ℝ := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
    let D : ℕ → ℝ := fun k =>
      ∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
        velocityH3DissipationAt u r ∂volume
    let G : ℕ → ℕ := thirdFullKineticSignedLowMaxPhysicalAdaptiveGauge244
      (velocityH3Energy0At u b) h D
    Tendsto G atTop atTop ∧
      (∀ᶠ k : ℕ in atTop,
        ∀ (R : ℕ) (t : ℝ),
          t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
          eta < -velocityH3TransportDerivative3At u t →
          ¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
            hH3 R J E eta epsilon
              (tau (v k) + delta (v k)) (tau (v (k + 1))) t →
          ((tau (v (k + 1)) - (tau (v k) + delta (v k))) * h ≤
              16 * D k) ∨
          (h ^ 2 ≤ 32 * thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244
              k (velocityH3Energy0At u b) * D k) ∨
          (∃ Q : ℕ, R ≤ Q ∧ k < Q)) := by
  let h : ℝ := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
  let D : ℕ → ℝ := fun k =>
    ∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
      velocityH3DissipationAt u r ∂volume
  let C : ℕ → ℝ := fun k =>
    thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244 k
      (velocityH3Energy0At u b)
  let G : ℕ → ℕ := thirdFullKineticSignedLowMaxPhysicalAdaptiveGauge244
    (velocityH3Energy0At u b) h D
  change Tendsto G atTop atTop ∧
    (∀ᶠ k : ℕ in atTop, ∀ (R : ℕ) (t : ℝ),
      t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
      eta < -velocityH3TransportDerivative3At u t →
      ¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
        hH3 R J E eta epsilon
          (tau (v k) + delta (v k)) (tau (v (k + 1))) t →
      ((tau (v (k + 1)) - (tau (v k) + delta (v k))) * h ≤ 16 * D k) ∨
      (h ^ 2 ≤ 32 * C k * D k) ∨
      (∃ Q : ℕ, R ≤ Q ∧ k < Q))
  have hPrevious :=
    thirdFullPhysical_kineticGaps_signedLowMax_tenthResidual_adaptiveGauge244
      hH3 hClass hDInt b hb M tau N delta v
      hLimit hSeparated hWindows eta hEta J E epsilon hE hEpsilon
  change Tendsto G atTop atTop ∧
    (∀ᶠ k : ℕ in atTop, ∀ (R : ℕ) (t : ℝ),
      t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
      eta < -velocityH3TransportDerivative3At u t →
      ¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
        hH3 R J E eta epsilon
          (tau (v k) + delta (v k)) (tau (v (k + 1))) t →
      ((tau (v (k + 1)) - (tau (v k) + delta (v k))) * h ≤ 16 * D k) ∨
      (∃ Q : ℕ, R ≤ Q ∧ G k < Q)) at hPrevious
  refine ⟨hPrevious.1, ?_⟩
  filter_upwards [hPrevious.2] with k hk
  intro R t ht hAdverse hNoResidual
  have hOld := hk R t ht hAdverse hNoResidual
  let P : Prop :=
    (tau (v (k + 1)) - (tau (v k) + delta (v k))) * h ≤ 16 * D k
  have hFork : P ∨
      (∃ Q : ℕ, R ≤ Q ∧
        thirdFullKineticSignedLowMaxAdaptiveBudgetGauge244 C D h k < Q) := by
    change P ∨ (∃ Q : ℕ, R ≤ Q ∧
      thirdFullKineticSignedLowMaxAdaptiveBudgetGauge244 C D h k < Q) at hOld
    exact hOld
  exact thirdFullKinetic_signedLowMax_indexRateOrOuter_scalar244
    C D h k R P hFork

/-- This precise sufficient-condition version avoids postulating a
rate-weighted dissipation limit. If BOTH index-rate and relative-density
payments fail on a selected late original gap, the annular outer radius
exceeds the actual gap INDEX k. -/
theorem thirdFullKinetic_signedLowMax_indexGate_forcesOuter244
    (C D : ℕ → ℝ) (h : ℝ) (k R : ℕ) (gap : ℝ)
    (hFork : gap * h ≤ 16 * D k ∨
      h ^ 2 ≤ 32 * C k * D k ∨
      ∃ Q : ℕ, R ≤ Q ∧ k < Q)
    (hLowDensity : 16 * D k < gap * h)
    (hLowRate : 32 * C k * D k < h ^ 2) :
    ∃ Q : ℕ, R ≤ Q ∧ k < Q := by
  rcases hFork with hDensity | hRest
  · exact False.elim ((not_lt_of_ge hDensity) hLowDensity)
  rcases hRest with hRate | hOuter
  · exact False.elim ((not_lt_of_ge hRate) hLowRate)
  · exact hOuter

end
end PrimeTensor.FirstMonomialTriad
