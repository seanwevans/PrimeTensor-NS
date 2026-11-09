import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxTenthPowerGaugeCoupling
import Mathlib.Tactic

/-!
# Fixed-gauge relative dissipation or genuine signed sixth-flux spectral escape

The previous kinetic rate-or-clock obstruction has three branches. A finite
natural outer gauge G has a FINITE kinetic-only rate coefficient C_G, fixed
independently of the cofinal gap. Since the actual full H3 dissipation on
those disjoint gaps tends to zero, the C_G-rate-payment branch disappears
for every FIXED G after a G-dependent threshold.

The linear physical viscous height is bounded below by a fixed positive
number when the actual adverse-time H3 energy is capped. Thus the remaining
alternative is a G-escaping annular outer radius or a strictly positive
lower bound on the ratio of gap dissipation to gap duration.

Quantifier order matters: G is chosen BEFORE the eventual index. Nothing
here supplies a uniform index over all G, since C_G may grow with G.
The source-carrier version retains the original tenth-power residual;
without excluding it, it would be incorrect to assert an outer escape.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Finite kinetic-only rate payment at one fixed natural outer gauge.
No monotonicity of the one-cutoff kinetic rate is assumed. -/
noncomputable def thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244
    (G : ℕ) (E0 : ℝ) : ℝ :=
  2 * (∑ j ∈ Finset.range (G + 1),
    thirdFullPhysicalKineticLowBandDissipationRate244 j E0) + 1

/-- A fixed finite gauge has a strictly positive, finite physical rate
coefficient, regardless of the sign of the kinetic-energy argument. -/
theorem thirdFullKinetic_signedLowMax_finiteGaugeRate_pos244
    (G : ℕ) (E0 : ℝ) :
    0 < thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244 G E0 := by
  have hSum : 0 ≤ ∑ j ∈ Finset.range (G + 1),
      thirdFullPhysicalKineticLowBandDissipationRate244 j E0 := by
    apply Finset.sum_nonneg
    intro j _hj
    exact thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 j E0
  unfold thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244
  linarith only [hSum]

/-- Resolves the genuinely physical rate/clock/frequency fork at a fixed
positive physical viscous-height floor. Once the finite-gauge rate budget
is too small, the remaining possibilities are RELATIVE GAP DISSIPATION
or actual outer-cutoff escape. -/
theorem thirdFullKinetic_signedLowMax_relativeDensityOrGauge_scalar244
    (x y H h D C : ℝ) (G Q : ℕ)
    (hGap : 0 ≤ y - x) (hFloor : 0 ≤ h) (hHeight : h ≤ H)
    (hRateSmall : 32 * C * D < h ^ 2)
    (hFork : (y - x) * H ≤ 16 * D ∨ G < Q ∨
      H ^ 2 ≤ 32 * C * D) :
    (y - x) * h ≤ 16 * D ∨ G < Q := by
  rcases hFork with hClock | hRest
  · left
    exact (mul_le_mul_of_nonneg_left hHeight hGap).trans hClock
  rcases hRest with hGauge | hRate
  · exact Or.inr hGauge
  · have hSquare : h ^ 2 ≤ H ^ 2 :=
      pow_le_pow_left₀ hFloor hHeight 2
    have hContradiction : h ^ 2 ≤ 32 * C * D := hSquare.trans hRate
    exact False.elim ((not_lt_of_ge hContradiction) hRateSmall)

/-- The G-dependent finite rate can no longer pay a gamma-free signed
sixth-flux carrier once its integrated full H3 dissipation is small enough.
The other branch bounds the TRUE relative gap dissipation from below. -/
theorem thirdFullPhysical_signedLowMax_tail_relativeDensityOrGauge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (G R : ℕ) (x y t : ℝ)
    (hx : x ∈ Set.Ioo b T) (hy : y ∈ Set.Ioo b T)
    (hxy : x < y) (ht : t ∈ Set.Icc x y)
    (eta E : ℝ) (hEta : 0 < eta) (hE : 0 ≤ E)
    (hEnergy : velocityH3EnergyAt u t ≤ E)
    (hTail : eta / 2 ≤
      thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
        (velocityH3EnergyAt u t) *
        ‖thirdFullSpectralVelocityHighRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 t)‖ ^ 2)
    (hRateSmall :
      32 * thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244 G
        (velocityH3Energy0At u b) *
        (∫ r in x..y, velocityH3DissipationAt u r ∂volume) <
      (thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E) ^ 2) :
    (y - x) * thirdFullKineticSignedLowMaxCappedLinearHeightFloor244
      eta E ≤ 16 * (∫ r in x..y,
        velocityH3DissipationAt u r ∂volume) ∨
    ∃ Q : ℕ, R ≤ Q ∧ G < Q := by
  obtain ⟨Q, hRQ, hFork⟩ :=
    thirdFullPhysical_signedLowMax_gammaFreeTail_gaugeRateBarrier244
      hH3 hClass hDInt b hb R G x y t hx hy hxy ht eta hEta hTail
  let H : ℝ := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
    R eta (velocityH3EnergyAt u t)
  let h : ℝ := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
  let C : ℝ := thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244
    G (velocityH3Energy0At u b)
  let D : ℝ := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
  have hActualNonneg : 0 ≤ velocityH3EnergyAt u t := by
    have hOne := one_le_velocityH3EnergyAt u t
    linarith only [hOne]
  have hFloor : 0 ≤ h :=
    (thirdFullKinetic_signedLowMax_cappedLinearFloor_pos244
      eta E hEta hE).le
  have hHeight : h ≤ H :=
    thirdFullKinetic_signedLowMax_linearHeight_ge_cappedFloor244
      R eta (velocityH3EnergyAt u t) E hEta hActualNonneg hEnergy
  have hGap : 0 ≤ y - x := sub_nonneg.mpr hxy.le
  have hSmall : 32 * C * D < h ^ 2 := hRateSmall
  have hFork' : (y - x) * H ≤ 16 * D ∨ G < Q ∨
      H ^ 2 ≤ 32 * C * D := by
    change (y - x) * H ≤ 16 * D ∨ G < Q ∨
      H ^ 2 ≤ 32 * C * D at hFork
    exact hFork
  have hResolved := thirdFullKinetic_signedLowMax_relativeDensityOrGauge_scalar244
    x y H h D C G Q hGap hFloor hHeight hSmall hFork'
  rcases hResolved with hDensity | hEscape
  · exact Or.inl hDensity
  · exact Or.inr ⟨Q, hRQ, hEscape⟩

/-- For each FIXED outer gauge G, finite physical H3 dissipation eliminates
the finite-G rate branch on every sufficiently late original kinetic gap.
The threshold is UNIFORM in the inner radius and the adverse physical time,
but may depend on G, the signed margin and the physical H3 energy cap. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_tail_densityOrGauge244
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
    (eta E : ℝ) (hEta : 0 < eta) (hE : 0 ≤ E) (G : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      ∀ (R : ℕ) (t : ℝ),
        t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
        (eta / 2 ≤
          thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
            (velocityH3EnergyAt u t) *
            ‖thirdFullSpectralVelocityHighRadialApply244 R
              (h3AuditActualSpectralVelocityTotal hH3 t)‖ ^ 2) →
        velocityH3EnergyAt u t ≤ E →
        ((tau (v (k + 1)) - (tau (v k) + delta (v k))) *
          thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E ≤
          16 * (∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
            velocityH3DissipationAt u r ∂volume)) ∨
        ∃ Q : ℕ, R ≤ Q ∧ G < Q := by
  let h : ℝ := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
  let C : ℝ := thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244
    G (velocityH3Energy0At u b)
  have hPositive : 0 < h :=
    thirdFullKinetic_signedLowMax_cappedLinearFloor_pos244 eta E hEta hE
  have hThreshold : 0 < h ^ 2 := pow_pos hPositive 2
  have hDZero := thirdFullPhysical_kineticGaps_fullDissipation_tendsto_zero244
    hH3 hClass hDInt b hb M tau N delta v hLimit hSeparated hWindows
  have hScaled : Tendsto
      (fun k : ℕ => 32 * C *
        (∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
          velocityH3DissipationAt u r ∂volume))
      atTop (𝓝 (0 : ℝ)) := by
    have hLimitScaled := (tendsto_const_nhds.mul hDZero : Tendsto
      (fun k : ℕ => (32 * C) *
        (∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
          velocityH3DissipationAt u r ∂volume))
      atTop (𝓝 ((32 * C) * (0 : ℝ))))
    simpa only [mul_zero] using hLimitScaled
  have hSmall : ∀ᶠ k : ℕ in atTop,
      32 * C *
        (∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
          velocityH3DissipationAt u r ∂volume) < h ^ 2 :=
    hScaled.eventually (eventually_lt_nhds hThreshold)
  filter_upwards [hSmall] with k hk
  intro R t ht hTail hEnergy
  let x : ℝ := tau (v k) + delta (v k)
  let y : ℝ := tau (v (k + 1))
  have hx : x ∈ Set.Ioo b T := by
    obtain ⟨hTime, hw⟩ := hWindows k
    rcases hw with ⟨_, hdelta, _, hEnd, _, _⟩
    exact ⟨by linarith only [hTime.1, hdelta], hEnd⟩
  have hy : y ∈ Set.Ioo b T := (hWindows (k + 1)).1
  have hxy : x < y := hSeparated k (k + 1) (Nat.lt_succ_self k)
  have hRate :
      32 * thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244 G
        (velocityH3Energy0At u b) *
        (∫ r in x..y, velocityH3DissipationAt u r ∂volume) <
      (thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E) ^ 2 := hk
  exact thirdFullPhysical_signedLowMax_tail_relativeDensityOrGauge244
    hH3 hClass hDInt b hb G R x y t hx hy hxy ht
    eta E hEta hE hEnergy hTail hRate

/-- A direct test for genuine spectral escape: below the fixed-height
relative gap dissipation threshold, there is no possible fixed-G rate
payment. The cutoff Q may depend on the inner radius and adverse time. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_tail_lowDensity_forcesGauge244
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
    (eta E : ℝ) (hEta : 0 < eta) (hE : 0 ≤ E) (G : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      ∀ (R : ℕ) (t : ℝ),
        t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
        (eta / 2 ≤
          thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
            (velocityH3EnergyAt u t) *
            ‖thirdFullSpectralVelocityHighRadialApply244 R
              (h3AuditActualSpectralVelocityTotal hH3 t)‖ ^ 2) →
        velocityH3EnergyAt u t ≤ E →
        (16 * (∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
          velocityH3DissipationAt u r ∂volume) <
          (tau (v (k + 1)) - (tau (v k) + delta (v k))) *
            thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E) →
        ∃ Q : ℕ, R ≤ Q ∧ G < Q := by
  have hMain := thirdFullPhysical_kineticGaps_signedLowMax_tail_densityOrGauge244
    hH3 hClass hDInt b hb M tau N delta v hLimit hSeparated hWindows
    eta E hEta hE G
  filter_upwards [hMain] with k hk
  intro R t ht hTail hEnergy hLow
  rcases hk R t ht hTail hEnergy with hDensity | hGauge
  · exact False.elim ((not_lt_of_ge hDensity) hLow)
  · exact hGauge

/-- Full tenth-power coupling at genuinely adverse physical observations:
if the earlier baseline, radius/energy escape and quadratic-height viscous
alternative are all excluded, then the remaining gamma-free carrier pays
EITHER a fixed positive average H3 dissipation per unit kinetic-gap time
OR a certified annulus outside any preassigned FIXED frequency gauge G.

The physical H3 energy cap is extracted from the negated original residual,
not imposed as an additional independent hypothesis. The cofinal threshold
may depend on G, J, E, eta and epsilon, but not on R or the observation t. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_tenthResidual_densityOrGauge244
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
    (J G : ℕ) (E epsilon : ℝ) (hE : 0 ≤ E) (hEpsilon : 0 < epsilon) :
    ∀ᶠ k : ℕ in atTop,
      ∀ (R : ℕ) (t : ℝ),
        t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
        eta < -velocityH3TransportDerivative3At u t →
        (¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
          hH3 R J E eta epsilon
            (tau (v k) + delta (v k)) (tau (v (k + 1))) t) →
        ((tau (v (k + 1)) - (tau (v k) + delta (v k))) *
          thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E ≤
          16 * (∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
            velocityH3DissipationAt u r ∂volume)) ∨
        ∃ Q : ℕ, R ≤ Q ∧ G < Q := by
  have hRadius := thirdFullPhysical_kineticGaps_signedLowMax_radiusEnergyEscape244
    hH3 hClass hDInt b hb M tau N delta v hLimit hSeparated
    hWindows eta hEta J E epsilon hE hEpsilon
  have hDensity := thirdFullPhysical_kineticGaps_signedLowMax_tail_densityOrGauge244
    hH3 hClass hDInt b hb M tau N delta v hLimit hSeparated
    hWindows eta E hEta hE G
  filter_upwards [hRadius, hDensity] with k hkRadius hkDensity
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
    exact hkDensity R t ht (by simpa only [X] using hTrueTail) hCap
  · exact False.elim (hNoResidual hOther)

end
end PrimeTensor.FirstMonomialTriad
