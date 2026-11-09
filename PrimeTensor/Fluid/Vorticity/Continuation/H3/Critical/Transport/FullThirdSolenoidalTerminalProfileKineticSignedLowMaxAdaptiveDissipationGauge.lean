import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxRelativeDissipationGauge
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# Signed sixth flux: an adaptive unbounded gauge paid by actual gap dissipation

A FIXED natural gauge G has a finite physical kinetic rate coefficient C_G.
The earlier fixed-gauge obstruction was valid only beyond an index depending
on G. This module constructs one gauge G(k) on EVERY sufficiently late
original kinetic gap, without exchanging the quantifiers incorrectly:

  G(k) = max {G <= k : 32*C_G*D(k) < h^2},

where D(k) is the actual full H3 dissipation on that original kinetic gap
and h is the positive linear viscous-height floor from an actual energy cap.
A finite supremum is implemented by `Nat.findGreatest`; the fallback is zero.
For every fixed G, D(k) -> 0 eventually makes G affordable. Thus
G(k) -> infinity, G(k) <= k, and the SELECTED G(k) is itself affordable
on sufficiently late gaps. The previously proved local physical lemma then
forces either positive average gap dissipation or an annular cutoff ABOVE
this unbounded adaptive gauge.

No bound on D(k)/(gap length) or terminal H3 trace is asserted. The new gauge
is noncomputable because it selects from inequalities involving real integrals.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Largest affordable natural gauge below the current index. The rate
coefficient C need not be monotone in the gauge, positive, or bounded. -/
noncomputable def thirdFullKineticSignedLowMaxAdaptiveBudgetGauge244
    (C : ℕ → ℝ) (D : ℕ → ℝ) (h : ℝ) (k : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun G : ℕ => 32 * C G * D k < h ^ 2) k

/-- An adaptive gauge never anticipates a later index. -/
theorem thirdFullKinetic_signedLowMax_adaptiveBudgetGauge_le_index244
    (C : ℕ → ℝ) (D : ℕ → ℝ) (h : ℝ) (k : ℕ) :
    thirdFullKineticSignedLowMaxAdaptiveBudgetGauge244 C D h k ≤ k := by
  classical
  change Nat.findGreatest (fun G : ℕ => 32 * C G * D k < h ^ 2) k ≤ k
  exact Nat.findGreatest_le k

/-- Each fixed natural frequency gauge eventually becomes affordable when
actual gap dissipation tends to zero. No frequency-uniform rate is used. -/
theorem thirdFullKinetic_signedLowMax_fixedBudget_eventuallyAffordable244
    (C : ℕ → ℝ) (D : ℕ → ℝ) (h : ℝ) (hh : 0 < h)
    (hD : Tendsto D atTop (𝓝 (0 : ℝ))) (G : ℕ) :
    ∀ᶠ k : ℕ in atTop, 32 * C G * D k < h ^ 2 := by
  have hScaled : Tendsto (fun k : ℕ => 32 * C G * D k)
      atTop (𝓝 (0 : ℝ)) := by
    have hProduct := (tendsto_const_nhds.mul hD :
      Tendsto (fun k : ℕ => (32 * C G) * D k)
        atTop (𝓝 ((32 * C G) * (0 : ℝ))))
    simpa only [mul_zero] using hProduct
  exact hScaled.eventually (eventually_lt_nhds (pow_pos hh 2))

/-- Once gauge zero is affordable, the selected MAXIMUM itself is
physically affordable. No selection is left to a later theorem. -/
theorem thirdFullKinetic_signedLowMax_adaptiveBudgetGauge_affordable244
    (C : ℕ → ℝ) (D : ℕ → ℝ) (h : ℝ) (hh : 0 < h)
    (hD : Tendsto D atTop (𝓝 (0 : ℝ))) :
    ∀ᶠ k : ℕ in atTop,
      32 * C (thirdFullKineticSignedLowMaxAdaptiveBudgetGauge244 C D h k) *
        D k < h ^ 2 := by
  classical
  have hZero := thirdFullKinetic_signedLowMax_fixedBudget_eventuallyAffordable244
    C D h hh hD 0
  filter_upwards [hZero] with k hk
  change 32 * C (Nat.findGreatest
      (fun G : ℕ => 32 * C G * D k < h ^ 2) k) * D k < h ^ 2
  exact (Nat.findGreatest_spec
    (P := fun G : ℕ => 32 * C G * D k < h ^ 2)
    (m := 0) (n := k) (Nat.zero_le k) hk)

/-- The selected affordable gauge is genuinely UNBOUNDED. For each fixed
G the convergence D(k)->0 makes that G affordable, and the bounded greatest
selector must eventually exceed it. -/
theorem thirdFullKinetic_signedLowMax_adaptiveBudgetGauge_tendsto_atTop244
    (C : ℕ → ℝ) (D : ℕ → ℝ) (h : ℝ) (hh : 0 < h)
    (hD : Tendsto D atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun k : ℕ =>
      thirdFullKineticSignedLowMaxAdaptiveBudgetGauge244 C D h k)
      atTop atTop := by
  classical
  apply Filter.tendsto_atTop.2
  intro G
  have hFixed := thirdFullKinetic_signedLowMax_fixedBudget_eventuallyAffordable244
    C D h hh hD G
  filter_upwards [hFixed, eventually_ge_atTop G] with k hk hkG
  change G ≤ Nat.findGreatest
    (fun j : ℕ => 32 * C j * D k < h ^ 2) k
  exact Nat.le_findGreatest hkG hk

/-- The concrete gauge uses the already-proved physical finite-gauge
kinetic rate at the fixed early anchor; it is tailored to actual gap costs. -/
noncomputable def thirdFullKineticSignedLowMaxPhysicalAdaptiveGauge244
    (E0 h : ℝ) (D : ℕ → ℝ) (k : ℕ) : ℕ :=
  thirdFullKineticSignedLowMaxAdaptiveBudgetGauge244
    (fun G : ℕ => thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244 G E0)
    D h k

/-- Physical simultaneous diagonal: an actual gamma-free high-radial
carrier with a capped H3 energy either pays positive relative H3 dissipation
on the SAME kinetic gap, or its certified finite outer cutoff exceeds the
explicit unbounded, affordable, gap-dependent gauge G(k).

The quantifier `Tendsto G atTop atTop` is proved, not postulated, and the
rate-budget premise of the local gauge lemma is discharged by construction. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_tail_adaptiveDensityOrGauge244
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
    (eta E : ℝ) (hEta : 0 < eta) (hE : 0 ≤ E) :
    let h : ℝ := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
    let D : ℕ → ℝ := fun k =>
      ∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
        velocityH3DissipationAt u r ∂volume
    let G : ℕ → ℕ :=
      thirdFullKineticSignedLowMaxPhysicalAdaptiveGauge244
        (velocityH3Energy0At u b) h D
    Tendsto G atTop atTop ∧
      (∀ᶠ k : ℕ in atTop,
        ∀ (R : ℕ) (t : ℝ),
          t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
          eta / 2 ≤ thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
            (velocityH3EnergyAt u t) *
              ‖thirdFullSpectralVelocityHighRadialApply244 R
                (h3AuditActualSpectralVelocityTotal hH3 t)‖ ^ 2 →
          velocityH3EnergyAt u t ≤ E →
          (tau (v (k + 1)) - (tau (v k) + delta (v k))) * h ≤
            16 * D k ∨
          ∃ Q : ℕ, R ≤ Q ∧ G k < Q) := by
  let h : ℝ := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
  let D : ℕ → ℝ := fun k =>
    ∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
      velocityH3DissipationAt u r ∂volume
  let G : ℕ → ℕ :=
    thirdFullKineticSignedLowMaxPhysicalAdaptiveGauge244
      (velocityH3Energy0At u b) h D
  change Tendsto G atTop atTop ∧
    (∀ᶠ k : ℕ in atTop, ∀ (R : ℕ) (t : ℝ),
      t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
      eta / 2 ≤ thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
        (velocityH3EnergyAt u t) *
          ‖thirdFullSpectralVelocityHighRadialApply244 R
            (h3AuditActualSpectralVelocityTotal hH3 t)‖ ^ 2 →
      velocityH3EnergyAt u t ≤ E →
      (tau (v (k + 1)) - (tau (v k) + delta (v k))) * h ≤ 16 * D k ∨
      ∃ Q : ℕ, R ≤ Q ∧ G k < Q)
  have hFloorPos : 0 < h :=
    thirdFullKinetic_signedLowMax_cappedLinearFloor_pos244 eta E hEta hE
  have hDZero : Tendsto D atTop (𝓝 (0 : ℝ)) := by
    simpa only [D] using
      (thirdFullPhysical_kineticGaps_fullDissipation_tendsto_zero244
        hH3 hClass hDInt b hb M tau N delta v
        hLimit hSeparated hWindows)
  let C : ℕ → ℝ := fun j =>
    thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244 j
      (velocityH3Energy0At u b)
  have hAffordable : ∀ᶠ k : ℕ in atTop,
      32 * C (G k) * D k < h ^ 2 := by
    simpa only [G, C, thirdFullKineticSignedLowMaxPhysicalAdaptiveGauge244]
      using (thirdFullKinetic_signedLowMax_adaptiveBudgetGauge_affordable244
        C D h hFloorPos hDZero)
  constructor
  · change Tendsto (fun k : ℕ =>
        thirdFullKineticSignedLowMaxAdaptiveBudgetGauge244 C D h k)
        atTop atTop
    exact thirdFullKinetic_signedLowMax_adaptiveBudgetGauge_tendsto_atTop244
      C D h hFloorPos hDZero
  · filter_upwards [hAffordable] with k hk
    intro R t ht hTail hEnergy
    let x : ℝ := tau (v k) + delta (v k)
    let y : ℝ := tau (v (k + 1))
    have hx : x ∈ Set.Ioo b T := by
      obtain ⟨hTime, hw⟩ := hWindows k
      rcases hw with ⟨_, hdelta, _, hEnd, _, _⟩
      exact ⟨by linarith only [hTime.1, hdelta], hEnd⟩
    have hy : y ∈ Set.Ioo b T := (hWindows (k + 1)).1
    have hxy : x < y := hSeparated k (k + 1) (Nat.lt_succ_self k)
    have hRateSmall :
        32 * thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244 (G k)
          (velocityH3Energy0At u b) *
          (∫ r in x..y, velocityH3DissipationAt u r ∂volume) <
        (thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E) ^ 2 := by
      simpa only [C, D, h, x, y] using hk
    exact thirdFullPhysical_signedLowMax_tail_relativeDensityOrGauge244
      hH3 hClass hDInt b hb (G k) R x y t hx hy hxy ht
      eta E hEta hE hEnergy hTail hRateSmall

/-- If the physical annular witness is selected consistently above the
adaptive gauge on late low-density gaps, that witness must itself escape
all fixed Fourier radii. This is the precise order-theoretic consequence;
no unproved selection of adverse observations is made. -/
theorem thirdFullKinetic_signedLowMax_witnessAboveAdaptiveGauge_tendsto244
    (G Q : ℕ → ℕ)
    (hGauge : Tendsto G atTop atTop)
    (hWitness : ∀ᶠ k : ℕ in atTop, G k < Q k) :
    Tendsto Q atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro B
  have hG : ∀ᶠ k : ℕ in atTop, B ≤ G k :=
    (Filter.tendsto_atTop.1 hGauge) B
  filter_upwards [hG, hWitness] with k hk hQk
  exact hk.trans hQk.le

/-- The original adverse physical signed-sixth-flux observation now has
one moving, truly UNBOUNDED outer gauge, rather than a separate eventual
index for each fixed gauge. The earlier tenth-power residual remains visible.
Under its negation, the gamma-independent high-tail carrier and physical
energy cap follow from the previously accepted radius/energy theorem. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_tenthResidual_adaptiveGauge244
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
    let G : ℕ → ℕ :=
      thirdFullKineticSignedLowMaxPhysicalAdaptiveGauge244
        (velocityH3Energy0At u b) h D
    Tendsto G atTop atTop ∧
      (∀ᶠ k : ℕ in atTop,
        ∀ (R : ℕ) (t : ℝ),
          t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
          eta < -velocityH3TransportDerivative3At u t →
          ¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
            hH3 R J E eta epsilon
              (tau (v k) + delta (v k)) (tau (v (k + 1))) t →
          (tau (v (k + 1)) - (tau (v k) + delta (v k))) * h ≤
            16 * D k ∨
          ∃ Q : ℕ, R ≤ Q ∧ G k < Q) := by
  let h : ℝ := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
  let D : ℕ → ℝ := fun k =>
    ∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
      velocityH3DissipationAt u r ∂volume
  let G : ℕ → ℕ :=
    thirdFullKineticSignedLowMaxPhysicalAdaptiveGauge244
      (velocityH3Energy0At u b) h D
  change Tendsto G atTop atTop ∧
    (∀ᶠ k : ℕ in atTop, ∀ (R : ℕ) (t : ℝ),
      t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
      eta < -velocityH3TransportDerivative3At u t →
      ¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
        hH3 R J E eta epsilon
          (tau (v k) + delta (v k)) (tau (v (k + 1))) t →
      (tau (v (k + 1)) - (tau (v k) + delta (v k))) * h ≤
        16 * D k ∨ ∃ Q : ℕ, R ≤ Q ∧ G k < Q)
  have hAdaptive :=
    thirdFullPhysical_kineticGaps_signedLowMax_tail_adaptiveDensityOrGauge244
      hH3 hClass hDInt b hb M tau N delta v
      hLimit hSeparated hWindows eta E hEta hE
  change Tendsto G atTop atTop ∧
    (∀ᶠ k : ℕ in atTop, ∀ (R : ℕ) (t : ℝ),
      t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
      eta / 2 ≤ thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
        (velocityH3EnergyAt u t) *
          ‖thirdFullSpectralVelocityHighRadialApply244 R
            (h3AuditActualSpectralVelocityTotal hH3 t)‖ ^ 2 →
      velocityH3EnergyAt u t ≤ E →
      (tau (v (k + 1)) - (tau (v k) + delta (v k))) * h ≤
        16 * D k ∨ ∃ Q : ℕ, R ≤ Q ∧ G k < Q) at hAdaptive
  obtain ⟨hGTop, hAffordable⟩ := hAdaptive
  have hRadius := thirdFullPhysical_kineticGaps_signedLowMax_radiusEnergyEscape244
    hH3 hClass hDInt b hb M tau N delta v hLimit hSeparated
    hWindows eta hEta J E epsilon hE hEpsilon
  constructor
  · exact hGTop
  · filter_upwards [hRadius, hAffordable] with k hkRadius hkAffordable
    intro R t ht hAdverse hNoResidual
    let x : ℝ := tau (v k) + delta (v k)
    let y : ℝ := tau (v (k + 1))
    let X : H3SpectralVelocityState :=
      h3AuditActualSpectralVelocityTotal hH3 t
    let A : ℝ := thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
      (velocityH3EnergyAt u t)
    let H : ℝ := ‖thirdFullSpectralVelocityHighRadialApply244 R X‖
    let Bad : Prop := ThirdFullKineticSignedLowMaxTenthPowerResidual244
      hH3 R J E eta epsilon x y t
    have hCap : velocityH3EnergyAt u t ≤ E := by
      by_contra hn
      have hBadEnergy : E < velocityH3EnergyAt u t := lt_of_not_ge hn
      apply hNoResidual
      unfold ThirdFullKineticSignedLowMaxTenthPowerResidual244
      exact Or.inr (Or.inl (Or.inr (Or.inl hBadEnergy)))
    have hEach (gamma : ℝ) (hGamma : 0 < gamma) :
        eta / 2 < A * (H + gamma) ^ 2 ∨ Bad := by
      have hPrev := hkRadius R gamma hGamma t ht hAdverse
      change (eta / 2 < ((2 * Real.pi) ^ 7 / 3) *
        (1944 * h3SobolevFirstMomentDeweightingConstant *
          (velocityH3EnergyAt u t + 1) * (H + gamma) ^ 2)) ∨ Bad at hPrev
      rcases hPrev with hTail | hOther
      · left
        simpa only [A, H, thirdFullKineticSignedLowMaxPhysicalHighTailFactor244,
          mul_assoc] using hTail
      · exact Or.inr hOther
    have hZero := thirdFull_scalar_signedLowMax_removePositiveTailTolerance244
      (eta / 2) A H Bad hEach
    rcases hZero with hTail | hOther
    · have hTrueTail : eta / 2 ≤
          thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
            (velocityH3EnergyAt u t) *
            ‖thirdFullSpectralVelocityHighRadialApply244 R X‖ ^ 2 := by
        simpa only [A, H] using hTail
      exact hkAffordable R t ht (by simpa only [X] using hTrueTail) hCap
    · exact False.elim (hNoResidual hOther)

end
end PrimeTensor.FirstMonomialTriad
