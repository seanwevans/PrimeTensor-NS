import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxAdaptiveDissipationGauge
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# Signed sixth flux: saturation of the first excluded adaptive kinetic band

The previous theorem selected the largest G(k) ≤ k satisfying the genuine
integrated full-H3 gap budget 32 C(G(k)) D(k) < h², and proved G(k) → ∞.
Here maximality identifies the FIRST excluded frequency. If G(k) < k,
then the next finite kinetic-rate budget fails, and the entire deficit
is carried by the newly added single low-band kinetic PDE rate:

  0 < h² - 32 C(G(k)) D(k) ≤ 64 L(G(k)+1) D(k).

The identity C(G+1)=C(G)+2 L(G+1) is exact. No monotonicity of L(G)
with respect to frequency is postulated or used. Under the actual
signed sixth-flux hypotheses, each sufficiently late gap therefore has
an explicit saturated first-excluded shell or an index-saturated gauge;
a physical adverse observation still pays either positive relative
dissipation or a certified outer cutoff above that unbounded gauge.

This is a NECESSARY concentration/frequency alternative, not the missing
upper bound on the ratio D(k)/(y(k)-x(k)).
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- A bounded greatest affordable gauge below k cannot have an affordable
successor while the selector is strictly below k. The proof uses the
accepted `Nat.le_findGreatest`, so there is no assumed rate monotonicity. -/
theorem thirdFullKinetic_signedLowMax_adaptiveNextGauge_unaffordable244
    (C : ℕ → ℝ) (D : ℕ → ℝ) (h : ℝ) (k : ℕ)
    (hBelow : thirdFullKineticSignedLowMaxAdaptiveBudgetGauge244 C D h k < k) :
    h ^ 2 ≤ 32 * C
      (thirdFullKineticSignedLowMaxAdaptiveBudgetGauge244 C D h k + 1) * D k := by
  classical
  let g : ℕ := thirdFullKineticSignedLowMaxAdaptiveBudgetGauge244 C D h k
  have hStep : g + 1 ≤ k := Nat.succ_le_of_lt hBelow
  by_contra hBad
  have hAffordable : 32 * C (g + 1) * D k < h ^ 2 :=
    lt_of_not_ge hBad
  have hGreatest : g + 1 ≤
      Nat.findGreatest (fun j : ℕ => 32 * C j * D k < h ^ 2) k :=
    Nat.le_findGreatest hStep hAffordable
  change g + 1 ≤ g at hGreatest
  omega

/-- The exact difference between consecutive finite-gauge physical kinetic
rate ceilings is twice the single new frequency-band rate. -/
theorem thirdFullKinetic_signedLowMax_finiteGaugeRate_step244
    (G : ℕ) (E0 : ℝ) :
    thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244 (G + 1) E0 =
      thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244 G E0 +
        2 * thirdFullPhysicalKineticLowBandDissipationRate244 (G + 1) E0 := by
  unfold thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244
  rw [Finset.sum_range_succ]
  ring

/-- If adding one band closes a strictly positive kinetic-rate deficit,
that SINGLE band must pay at least the entire exact deficit. -/
theorem thirdFullKinetic_signedLowMax_oneShell_pays_deficit244
    (h C L D : ℝ)
    (hAffordable : 32 * C * D < h ^ 2)
    (hNext : h ^ 2 ≤ 32 * (C + 2 * L) * D) :
    0 < h ^ 2 - 32 * C * D ∧
      h ^ 2 - 32 * C * D ≤ 64 * L * D := by
  constructor
  · linarith only [hAffordable]
  · nlinarith only [hNext]

/-- On EVERY sufficiently late index, the physical adaptive gauge is
strictly affordable, lies below the index, and either saturates the index
or has a positive deficit paid by the very next single kinetic band.
The next-band payment is not inferred from an assumed monotone rate. -/
theorem thirdFullKinetic_signedLowMax_physicalAdaptive_shellSaturation244
    (E0 h : ℝ) (D : ℕ → ℝ) (hh : 0 < h)
    (hD : Tendsto D atTop (𝓝 (0 : ℝ))) :
    let C : ℕ → ℝ := fun j =>
      thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244 j E0
    let G : ℕ → ℕ :=
      thirdFullKineticSignedLowMaxPhysicalAdaptiveGauge244 E0 h D
    ∀ᶠ k : ℕ in atTop,
      G k ≤ k ∧
      32 * C (G k) * D k < h ^ 2 ∧
      (G k = k ∨
        (0 < h ^ 2 - 32 * C (G k) * D k ∧
         h ^ 2 - 32 * C (G k) * D k ≤
           64 * thirdFullPhysicalKineticLowBandDissipationRate244
             (G k + 1) E0 * D k)) := by
  let C : ℕ → ℝ := fun j =>
    thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244 j E0
  let G : ℕ → ℕ :=
    thirdFullKineticSignedLowMaxPhysicalAdaptiveGauge244 E0 h D
  change ∀ᶠ k : ℕ in atTop,
    G k ≤ k ∧ 32 * C (G k) * D k < h ^ 2 ∧
      (G k = k ∨
        (0 < h ^ 2 - 32 * C (G k) * D k ∧
         h ^ 2 - 32 * C (G k) * D k ≤
           64 * thirdFullPhysicalKineticLowBandDissipationRate244
             (G k + 1) E0 * D k))
  have hAffordable : ∀ᶠ k : ℕ in atTop,
      32 * C (G k) * D k < h ^ 2 := by
    simpa only [G, C, thirdFullKineticSignedLowMaxPhysicalAdaptiveGauge244]
      using (thirdFullKinetic_signedLowMax_adaptiveBudgetGauge_affordable244
        C D h hh hD)
  filter_upwards [hAffordable] with k hk
  have hIndex : G k ≤ k := by
    change thirdFullKineticSignedLowMaxAdaptiveBudgetGauge244 C D h k ≤ k
    exact thirdFullKinetic_signedLowMax_adaptiveBudgetGauge_le_index244 C D h k
  refine ⟨hIndex, hk, ?_⟩
  by_cases hTop : G k = k
  · exact Or.inl hTop
  · right
    have hBelow : G k < k := by omega
    have hNext : h ^ 2 ≤ 32 * C (G k + 1) * D k := by
      change h ^ 2 ≤ 32 *
        C (thirdFullKineticSignedLowMaxAdaptiveBudgetGauge244 C D h k + 1) * D k
      exact thirdFullKinetic_signedLowMax_adaptiveNextGauge_unaffordable244
        C D h k (by simpa only [G,
          thirdFullKineticSignedLowMaxPhysicalAdaptiveGauge244] using hBelow)
    have hStep : C (G k + 1) = C (G k) +
        2 * thirdFullPhysicalKineticLowBandDissipationRate244
          (G k + 1) E0 := by
      simpa only [C] using
        (thirdFullKinetic_signedLowMax_finiteGaugeRate_step244 (G k) E0)
    rw [hStep] at hNext
    exact thirdFullKinetic_signedLowMax_oneShell_pays_deficit244
      h (C (G k))
      (thirdFullPhysicalKineticLowBandDissipationRate244 (G k + 1) E0)
      (D k) hk hNext

/-- The previously constructed original kinetic gaps now carry a single
physical kinetic-rate saturation ledger, based on the SAME adaptive gauge
that appears in the signed-sixth-flux frequency alternative. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_adaptiveShellLedger244
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
    let G : ℕ → ℕ := thirdFullKineticSignedLowMaxPhysicalAdaptiveGauge244
      (velocityH3Energy0At u b) h D
    Tendsto G atTop atTop ∧
      (∀ᶠ k : ℕ in atTop,
        G k ≤ k ∧
        32 * thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244
          (G k) (velocityH3Energy0At u b) * D k < h ^ 2 ∧
        (G k = k ∨
          (0 < h ^ 2 - 32 *
            thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244
              (G k) (velocityH3Energy0At u b) * D k ∧
           h ^ 2 - 32 *
             thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244
               (G k) (velocityH3Energy0At u b) * D k ≤
             64 * thirdFullPhysicalKineticLowBandDissipationRate244
               (G k + 1) (velocityH3Energy0At u b) * D k))) := by
  let h : ℝ := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
  let D : ℕ → ℝ := fun k =>
    ∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
      velocityH3DissipationAt u r ∂volume
  let G : ℕ → ℕ := thirdFullKineticSignedLowMaxPhysicalAdaptiveGauge244
    (velocityH3Energy0At u b) h D
  change Tendsto G atTop atTop ∧
    (∀ᶠ k : ℕ in atTop,
      G k ≤ k ∧
      32 * thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244
        (G k) (velocityH3Energy0At u b) * D k < h ^ 2 ∧
      (G k = k ∨
        (0 < h ^ 2 - 32 *
          thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244
            (G k) (velocityH3Energy0At u b) * D k ∧
         h ^ 2 - 32 *
           thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244
             (G k) (velocityH3Energy0At u b) * D k ≤
           64 * thirdFullPhysicalKineticLowBandDissipationRate244
             (G k + 1) (velocityH3Energy0At u b) * D k)) )
  have hh : 0 < h :=
    thirdFullKinetic_signedLowMax_cappedLinearFloor_pos244 eta E hEta hE
  have hDZero : Tendsto D atTop (𝓝 (0 : ℝ)) := by
    simpa only [D] using
      (thirdFullPhysical_kineticGaps_fullDissipation_tendsto_zero244
        hH3 hClass hDInt b hb M tau N delta v
        hLimit hSeparated hWindows)
  have hGTop : Tendsto G atTop atTop := by
    change Tendsto (fun k : ℕ =>
      thirdFullKineticSignedLowMaxAdaptiveBudgetGauge244
        (fun j : ℕ => thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244 j
          (velocityH3Energy0At u b)) D h k) atTop atTop
    exact thirdFullKinetic_signedLowMax_adaptiveBudgetGauge_tendsto_atTop244
      (fun j : ℕ => thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244 j
        (velocityH3Energy0At u b)) D h hh hDZero
  refine ⟨hGTop, ?_⟩
  exact thirdFullKinetic_signedLowMax_physicalAdaptive_shellSaturation244
    (velocityH3Energy0At u b) h D hh hDZero

/-- The exact physical shell-saturation certificate for one original gap.
The second disjunct identifies the FIRST new kinetic band whose rate
closes the positive deficit of the largest affordable gauge. -/
def ThirdFullKineticSignedLowMaxAdaptiveShellCost244
    (E0 h : ℝ) (D : ℕ → ℝ) (G : ℕ → ℕ) (k : ℕ) : Prop :=
  G k ≤ k ∧
  32 * thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244 (G k) E0 *
    D k < h ^ 2 ∧
  (G k = k ∨
    (0 < h ^ 2 - 32 *
      thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244 (G k) E0 * D k ∧
     h ^ 2 - 32 *
       thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244 (G k) E0 * D k ≤
       64 * thirdFullPhysicalKineticLowBandDissipationRate244
         (G k + 1) E0 * D k))

/-- The PRECISE cofinal signed-sixth-flux obstruction with its own actual
kinetic shell-rate ledger: the affordable gauge tends to infinity, the
first excluded band is rate-saturated unless the index bound saturates,
and every adverse physical sample without the tenth-power residual either
pays positive relative full-H3 dissipation or forces a certified annular
outer cutoff above that SAME growing gauge. All statements concern the
original separated kinetic gaps. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_tenthResidual_adaptiveShell244
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
        ThirdFullKineticSignedLowMaxAdaptiveShellCost244
          (velocityH3Energy0At u b) h D G k ∧
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
  let G : ℕ → ℕ := thirdFullKineticSignedLowMaxPhysicalAdaptiveGauge244
    (velocityH3Energy0At u b) h D
  change Tendsto G atTop atTop ∧
    (∀ᶠ k : ℕ in atTop,
      ThirdFullKineticSignedLowMaxAdaptiveShellCost244
        (velocityH3Energy0At u b) h D G k ∧
      ∀ (R : ℕ) (t : ℝ),
        t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
        eta < -velocityH3TransportDerivative3At u t →
        ¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
          hH3 R J E eta epsilon
            (tau (v k) + delta (v k)) (tau (v (k + 1))) t →
        (tau (v (k + 1)) - (tau (v k) + delta (v k))) * h ≤
          16 * D k ∨ ∃ Q : ℕ, R ≤ Q ∧ G k < Q)
  have hLedger := thirdFullPhysical_kineticGaps_signedLowMax_adaptiveShellLedger244
    hH3 hClass hDInt b hb M tau N delta v
    hLimit hSeparated hWindows eta E hEta hE
  change Tendsto G atTop atTop ∧
    (∀ᶠ k : ℕ in atTop,
      ThirdFullKineticSignedLowMaxAdaptiveShellCost244
        (velocityH3Energy0At u b) h D G k) at hLedger
  have hAdverse :=
    thirdFullPhysical_kineticGaps_signedLowMax_tenthResidual_adaptiveGauge244
      hH3 hClass hDInt b hb M tau N delta v
      hLimit hSeparated hWindows eta hEta J E epsilon hE hEpsilon
  change Tendsto G atTop atTop ∧
    (∀ᶠ k : ℕ in atTop,
      ∀ (R : ℕ) (t : ℝ),
        t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
        eta < -velocityH3TransportDerivative3At u t →
        ¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
          hH3 R J E eta epsilon
            (tau (v k) + delta (v k)) (tau (v (k + 1))) t →
        (tau (v (k + 1)) - (tau (v k) + delta (v k))) * h ≤
          16 * D k ∨ ∃ Q : ℕ, R ≤ Q ∧ G k < Q) at hAdverse
  refine ⟨hLedger.1, ?_⟩
  filter_upwards [hLedger.2, hAdverse.2] with k hShell hFlux
  exact ⟨hShell, hFlux⟩

end
end PrimeTensor.FirstMonomialTriad
