import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxBackwardGapCharge
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticGapLowBandPDEFreezing
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeDelayedViscousTail
import Mathlib.Tactic

/-!
# Signed sixth flux: cofinal original-gap dissipation compression

The preceding closed-gap signed-flux theorem charges adverse recoveries
within the SAME physical kinetic gap. This module proves that the full
physical H3 viscous integral on each of the ORIGINAL cofinal intervening gaps
converges to zero under finite H3 dissipation. It then transfers the exact
signed LowMax clock-or-viscous-charge alternative to indexed Schwartz recovery
pairs on those gaps, retaining each moving radius, cubic amplitude, and
positive width.

The resulting obstruction is width TIMES flux-dependent height compression,
not a claim that widths alone vanish. The adverse complex flux snapshots
and their weighted-H3 recoveries are explicit input data; the existing
arbitrary-radius gap tradeoff does NOT silently imply the two-snapshot adverse
flux difference assumed here. No new time or annulus selection is made.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators FourierTransform SchwartzMap LineDeriv Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

private abbrev CA3 := PrimeTensor.Axis Depth.three
private abbrev CV3 := H3FourierPoint3

noncomputable local instance axisFintypeSignedCofinalGap244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A nonnegative integrable real physical density spends vanishing mass on
ANY cofinal subinterval [x_k,y_k] contained in [a,T]. The result uses the
exact continuous terminal primitive, so no uniform pointwise ceiling or
spike-continuity assumption enters. -/
theorem thirdFull_scalar_cofinalSubintervalCost_tendsto_zero244
    (D : ℝ → ℝ) (a T : ℝ) (haT : a < T)
    (hD : IntervalIntegrable D volume a T)
    (hNonneg : ∀ r : ℝ, 0 ≤ D r)
    (x y : ℕ → ℝ)
    (hInside : ∀ k : ℕ, a ≤ x k ∧ x k ≤ y k ∧ y k ≤ T)
    (hCofinal : Tendsto x atTop (𝓝 T)) :
    Tendsto (fun k : ℕ => ∫ r in x k..y k, D r ∂volume)
      atTop (𝓝 (0 : ℝ)) := by
  have hTail : Tendsto (fun k : ℕ =>
      ∫ r in x k..T, D r ∂volume) atTop (𝓝 (0 : ℝ)) :=
    thirdFull_scalarTerminalTail_integral_tendsto_zero244
      D a T haT hD x hCofinal
      (Filter.Eventually.of_forall (fun k =>
        ⟨(hInside k).1, ((hInside k).2.1).trans (hInside k).2.2⟩))
  have hLower (k : ℕ) :
      0 ≤ ∫ r in x k..y k, D r ∂volume :=
    intervalIntegral.integral_nonneg (hInside k).2.1
      (fun r _ => hNonneg r)
  have hBound (k : ℕ) :
      (∫ r in x k..y k, D r ∂volume) ≤
        ∫ r in x k..T, D r ∂volume := by
    have hInt : IntervalIntegrable D volume (x k) T := by
      apply hD.mono_set
      intro r hr
      have hrIcc : r ∈ Set.Icc (x k) T := by
        simpa only [Set.uIcc_of_le
          (((hInside k).2.1).trans (hInside k).2.2)] using hr
      have hrAll : r ∈ Set.Icc a T :=
        ⟨(hInside k).1.trans hrIcc.1, hrIcc.2⟩
      simpa only [Set.uIcc_of_le haT.le] using hrAll
    exact intervalIntegral.integral_mono_interval
      le_rfl (hInside k).2.1 (hInside k).2.2
      (Filter.Eventually.of_forall hNonneg) hInt
  exact squeeze_zero'
    (Filter.Eventually.of_forall hLower)
    (Filter.Eventually.of_forall hBound) hTail

/-- The actual full physical H3 dissipation, not a model/source surrogate,
vanishes on the original gaps between cofinal natural-annulus windows.
The same tau,N,delta,v and their original strict separation are retained. -/
theorem thirdFullPhysical_kineticGaps_fullDissipation_tendsto_zero244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (τ : ℕ → ℝ) (N : ℕ → ℕ)
    (δ : ℕ → ℝ) (v : ℕ → ℕ)
    (hLimit : Tendsto (fun k => τ (v k)) atTop (𝓝 T))
    (hSeparated : ∀ k l : ℕ, k < l →
      τ (v k) + δ (v k) < τ (v l))
    (hWindows : ∀ k : ℕ,
      τ (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (τ (v k)) (v k) (N (v k))
        (M (v k)) (δ (v k))) :
    Tendsto (fun k : ℕ =>
      ∫ r in (τ (v k) + δ (v k))..τ (v (k + 1)),
        velocityH3DissipationAt u r ∂volume)
      atTop (𝓝 (0 : ℝ)) := by
  have hPositive (k : ℕ) :
      0 < δ (v k) ∧ τ (v k) + δ (v k) < T := by
    rcases (hWindows k).2 with ⟨_, hδ, _, hEnd, _, _⟩
    exact ⟨hδ, hEnd⟩
  have hRemaining : Tendsto (fun k : ℕ => T - τ (v k))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (T : ℝ))
        atTop (𝓝 T)).sub hLimit
  have hWidth : Tendsto (fun k : ℕ => δ (v k)) atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall (fun k => (hPositive k).1.le))
      (Filter.Eventually.of_forall (fun k => by
        linarith only [(hPositive k).2]))
      hRemaining
  have hStartT : Tendsto (fun k : ℕ => τ (v k) + δ (v k))
      atTop (𝓝 T) := by
    simpa only [add_zero] using hLimit.add hWidth
  let x : ℕ → ℝ := fun k => τ (v k) + δ (v k)
  let y : ℕ → ℝ := fun k => τ (v (k + 1))
  have hInside (k : ℕ) : a ≤ x k ∧ x k ≤ y k ∧ y k ≤ T := by
    dsimp only [x, y]
    exact ⟨by linarith only [hb.1, (hWindows k).1.1,
         (hPositive k).1],
      (hSeparated k (k + 1) (Nat.lt_succ_self k)).le,
      (hWindows (k + 1)).1.2.le⟩
  exact thirdFull_scalar_cofinalSubintervalCost_tendsto_zero244
    (velocityH3DissipationAt u) a T hClass.terminal_start.2
    hDInt (velocityH3DissipationAt_nonneg u)
    x y hInside hStartT

/-- Index-by-index exact adverse two-snapshot signed LowMax data on the
original closed kinetic gaps. All Schwarz Fourier identifications are
included: the arbitrary-radius single-snapshot tradeoff is NOT a source
for this additional hypothesis. -/
def ThirdFullKineticSignedLowMaxCofinalGapSamples244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (_hH3 : LoggedPreterminalH3PathAdmissible u T)
    (τ : ℕ → ℝ) (δ : ℕ → ℝ) (v R : ℕ → ℕ)
    (eta : ℝ) (s t : ℕ → ℝ)
    (p q : ℕ → CA3 → SchwartzMap CV3 ℂ)
    (V W : ℕ → H3SpectralVelocityState) : Prop :=
  ∀ k : ℕ,
    s k ∈ Set.Icc (τ (v k) + δ (v k)) (τ (v (k + 1))) ∧
    t k ∈ Set.Icc (τ (v k) + δ (v k)) (τ (v (k + 1))) ∧
    (∀ j : CA3,
      (V k (h3ClassicalizationFinOfAxis j) : CV3 → ℂ) =ᵐ[volume]
        (fun ξ : CV3 => (h3SobolevFrequencyWeight ξ : ℂ) *
          (𝓕 (p k j)) ξ)) ∧
    (∀ j : CA3,
      (W k (h3ClassicalizationFinOfAxis j) : CV3 → ℂ) =ᵐ[volume]
        (fun ξ : CV3 => (h3SobolevFrequencyWeight ξ : ℂ) *
          (𝓕 (q k j)) ξ)) ∧
    eta ≤ |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 (R k) (p k)).im -
      (thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 (R k) (q k)).im|

/-- COFINAL signed-flux obstruction on the ORIGINAL separated physical
kinetic gaps. For every requested small real cost epsilon, all sufficiently
late gaps obey one of two quantified outcomes:
(1) their amplitude-weighted recovery plus projected-source clock exceeds
half of the genuine signed imaginary excursion; or
(2) the SAME selected adverse time anchors a strictly positive physical
annular interval inside its original gap, whose exact width-times-height
charge is smaller than epsilon.

No bound on moving R, Schwartz H3 amplitude or width is inferred. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_clockOrCompressedCharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (τ : ℕ → ℝ) (N : ℕ → ℕ)
    (δ : ℕ → ℝ) (v R : ℕ → ℕ)
    (hLimit : Tendsto (fun k => τ (v k)) atTop (𝓝 T))
    (hSeparated : ∀ k l : ℕ, k < l →
      τ (v k) + δ (v k) < τ (v l))
    (hWindows : ∀ k : ℕ,
      τ (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (τ (v k)) (v k) (N (v k))
        (M (v k)) (δ (v k)))
    (eta : ℝ) (hEta : 0 < eta)
    (s t : ℕ → ℝ)
    (p q : ℕ → CA3 → SchwartzMap CV3 ℂ)
    (V W : ℕ → H3SpectralVelocityState)
    (hSamples : ThirdFullKineticSignedLowMaxCofinalGapSamples244
      hH3 τ δ v R eta s t p q V W)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∀ᶠ k : ℕ in atTop,
      (eta / 2 < thirdFullKineticSignedLowMaxFluxClockWeight244
        (R k) (V k) (W k) *
        (‖V k - h3AuditActualSpectralVelocityTotal hH3 (t k)‖ +
          thirdFullFiniteBandH3WeightCeiling244 (R k) *
            (∫ r in (τ (v k) + δ (v k))..τ (v (k + 1)),
              ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) +
          ‖h3AuditActualSpectralVelocityTotal hH3 (s k) - W k‖)) ∨
      (∃ (z width : ℝ), (z = t k ∨ z = s k) ∧ 0 < width ∧
        ((z + width < τ (v (k + 1))) ∨
          (z = τ (v (k + 1)) ∧ τ (v k) + δ (v k) < z - width)) ∧
        width * (thirdFullKineticSignedLowMaxPDEViscousHeight244
          (R k) (V k) (W k) eta / 4) < epsilon) := by
  have hDZero := thirdFullPhysical_kineticGaps_fullDissipation_tendsto_zero244
    hH3 hClass hDInt b hb M τ N δ v hLimit hSeparated hWindows
  have hSmall : ∀ᶠ k : ℕ in atTop,
      (∫ r in (τ (v k) + δ (v k))..τ (v (k + 1)),
        velocityH3DissipationAt u r ∂volume) < epsilon :=
    hDZero.eventually (eventually_lt_nhds hEpsilon)
  filter_upwards [hSmall] with k hk
  obtain ⟨hs, ht, hp, hq, hAdverse⟩ := hSamples k
  have hStart : τ (v k) + δ (v k) ∈ Set.Ioo b T := by
    have hWin := (hWindows k).2
    rcases hWin with ⟨_, hδ, _, hEnd, _, _⟩
    exact ⟨by linarith only [(hWindows k).1.1, hδ], hEnd⟩
  have hFinish : τ (v (k + 1)) ∈ Set.Ioo b T :=
    (hWindows (k + 1)).1
  have hGap : τ (v k) + δ (v k) < τ (v (k + 1)) :=
    hSeparated k (k + 1) (Nat.lt_succ_self k)
  have hAlt := thirdFullPhysical_strictGap_signedLowMax_clockOrFullGapCharge244
    hH3 hClass hDInt b hb (R k)
    (τ (v k) + δ (v k)) (τ (v (k + 1)))
    hStart hFinish hGap (s k) (t k) hs ht
    (p k) (q k) (V k) (W k) hp hq eta hEta hAdverse
  rcases hAlt with hClock | ⟨z, width, hz, hWidth, hInside, hCost⟩
  · exact Or.inl hClock
  · have hInside' :
        (z + width < τ (v (k + 1))) ∨
          (z = τ (v (k + 1)) ∧
            τ (v k) + δ (v k) < z - width) := by
      rcases hInside with hInterior | ⟨hRight, hBackward⟩
      · exact Or.inl hInterior
      · exact Or.inr ⟨hRight, by simpa only [hRight] using hBackward⟩
    exact Or.inr ⟨z, width, hz, hWidth, hInside',
      lt_of_le_of_lt hCost hk⟩

end
end PrimeTensor.FirstMonomialTriad
