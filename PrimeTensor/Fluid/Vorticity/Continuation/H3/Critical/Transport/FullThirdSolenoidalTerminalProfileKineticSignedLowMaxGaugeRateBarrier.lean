import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxSymmetricRateCompression
import Mathlib.Tactic

/-!
# Signed sixth flux: physical kinetic gauge-rate barrier

The symmetric in-gap rate/clock estimate is not itself a frequency escape:
its certified outer natural cutoff is free to move. Here we compare that
exact cutoff-dependent finite-annulus kinetic rate with a NONMONOTONIC
finite-gauge sum. This uses only nonnegativity of the already established
physical kinetic-rate coefficients, not an unproved monotonicity statement.

If the actual gap clock is too expensive and the entire prescribed gauge's
finite-rate budget is too small to absorb the squared physical height,
then the certified annular outer cutoff MUST exceed that gauge. The same
statement holds on all sufficiently late original kinetic gaps, uniformly
over all cutoffs, adverse times, and prescribed natural gauges. No rate or
width floor is silently asserted for a moving terminal-frequency profile.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- A finite sum controls BOTH natural-radius kinetic coefficients below
an arbitrary gauge, with no monotonicity in the radius required. -/
theorem thirdFullKinetic_signedLowMax_twoRates_le_gaugeSum244
    (L : ℕ → ℝ) (hL : ∀ j : ℕ, 0 ≤ L j)
    (R N G : ℕ) (hRN : R ≤ N) (hNG : N ≤ G) :
    L R + L N ≤ 2 * (∑ j ∈ Finset.range (G + 1), L j) := by
  have hR : R ∈ Finset.range (G + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hRN.trans hNG))
  have hN : N ∈ Finset.range (G + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hNG)
  have hRBound : L R ≤ ∑ j ∈ Finset.range (G + 1), L j :=
    Finset.single_le_sum (fun j _ => hL j) hR
  have hNBound : L N ≤ ∑ j ∈ Finset.range (G + 1), L j :=
    Finset.single_le_sum (fun j _ => hL j) hN
  linarith only [hRBound, hNBound]

/-- The symmetric clock/rate dichotomy becomes an exact three-way gauge
barrier. The annular rate must be paid by a finite-gauge sum unless the
actual outer cutoff passes the gauge. -/
theorem thirdFullKinetic_signedLowMax_clockOr_outerGauge_or_rate244
    (L : ℕ → ℝ) (hL : ∀ j : ℕ, 0 ≤ L j)
    (R N G : ℕ) (x y H D : ℝ)
    (hRN : R ≤ N) (hD : 0 ≤ D)
    (hFork : (y - x) * H ≤ 16 * D ∨
      H ^ 2 ≤ 32 * (L R + L N + 1) * D) :
    (y - x) * H ≤ 16 * D ∨ G < N ∨
      H ^ 2 ≤ 32 * (2 * (∑ j ∈ Finset.range (G + 1), L j) + 1) * D := by
  rcases hFork with hClock | hRate
  · exact Or.inl hClock
  right
  by_cases hGauge : G < N
  · exact Or.inl hGauge
  right
  have hNG : N ≤ G := Nat.le_of_not_gt hGauge
  have hSum := thirdFullKinetic_signedLowMax_twoRates_le_gaugeSum244
    L hL R N G hRN hNG
  have hCoeff :
      32 * (L R + L N + 1) ≤
        32 * (2 * (∑ j ∈ Finset.range (G + 1), L j) + 1) := by
    linarith only [hSum]
  have hScaled := mul_le_mul_of_nonneg_right hCoeff hD
  exact hRate.trans hScaled

/-- If neither the actual gap clock nor the prescribed finite-gauge
kinetic-rate budget can pay the annular charge, its outer cutoff crosses
the gauge. This is a conditional, quantitative spectral barrier. -/
theorem thirdFullKinetic_signedLowMax_gaugeBarrier_of_twoBudgets244
    (L : ℕ → ℝ) (hL : ∀ j : ℕ, 0 ≤ L j)
    (R N G : ℕ) (x y H D : ℝ)
    (hRN : R ≤ N) (hD : 0 ≤ D)
    (hFork : (y - x) * H ≤ 16 * D ∨
      H ^ 2 ≤ 32 * (L R + L N + 1) * D)
    (hClock : 16 * D < (y - x) * H)
    (hRate : 32 * (2 * (∑ j ∈ Finset.range (G + 1), L j) + 1) * D < H ^ 2) :
    G < N := by
  have hAlt := thirdFullKinetic_signedLowMax_clockOr_outerGauge_or_rate244
    L hL R N G x y H D hRN hD hFork
  rcases hAlt with hClockCost | hRest
  · exact False.elim ((not_lt_of_ge hClockCost) hClock)
  rcases hRest with hGauge | hRateCost
  · exact hGauge
  · exact False.elim ((not_lt_of_ge hRateCost) hRate)

/-- The certified gamma-free high-radial carrier gives a PHYSICAL
three-way local obstruction at every strict kinetic gap: short height clock,
outer-cutoff escape past G, or the exact finite-gauge kinetic-rate payment.
The kinetic anchor is the original physical low-energy value at b. -/
theorem thirdFullPhysical_signedLowMax_gammaFreeTail_gaugeRateBarrier244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R G : ℕ) (x y t : ℝ)
    (hx : x ∈ Set.Ioo b T) (hy : y ∈ Set.Ioo b T)
    (hxy : x < y) (ht : t ∈ Set.Icc x y)
    (eta : ℝ) (hEta : 0 < eta)
    (hTail : eta / 2 ≤
      thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
        (velocityH3EnergyAt u t) *
        ‖thirdFullSpectralVelocityHighRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 t)‖ ^ 2) :
    ∃ Q : ℕ, R ≤ Q ∧
      (let H := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
            R eta (velocityH3EnergyAt u t)
       let D := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
       (y - x) * H ≤ 16 * D ∨ G < Q ∨
       H ^ 2 ≤ 32 *
         (2 * (∑ j ∈ Finset.range (G + 1),
           thirdFullPhysicalKineticLowBandDissipationRate244 j
             (velocityH3Energy0At u b)) + 1) * D) := by
  obtain ⟨Q, hRQ, hFork⟩ :=
    thirdFullPhysical_signedLowMax_gammaFreeTail_kineticRateOrClock244
      hH3 hClass hDInt b hb R x y t hx hy hxy ht eta hEta hTail
  refine ⟨Q, hRQ, ?_⟩
  let L : ℕ → ℝ := fun j =>
    thirdFullPhysicalKineticLowBandDissipationRate244 j
      (velocityH3Energy0At u b)
  let H : ℝ := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
    R eta (velocityH3EnergyAt u t)
  let D : ℝ := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
  have hL (j : ℕ) : 0 ≤ L j :=
    thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 j _
  have hD : 0 ≤ D :=
    intervalIntegral.integral_nonneg hxy.le
      (fun r _ => velocityH3DissipationAt_nonneg u r)
  have hCoreQR : (y - x) * H ≤ 16 * D ∨
      H ^ 2 ≤ 32 * (L Q + L R + 1) * D := by
    simpa only [H, D, L,
      thirdFullKineticSignedLowMaxKineticAnnulusRate244] using hFork
  have hCore : (y - x) * H ≤ 16 * D ∨
      H ^ 2 ≤ 32 * (L R + L Q + 1) * D := by
    rcases hCoreQR with hClock | hRate
    · exact Or.inl hClock
    · right
      calc
        H ^ 2 ≤ 32 * (L Q + L R + 1) * D := hRate
        _ = 32 * (L R + L Q + 1) * D := by ring
  exact thirdFullKinetic_signedLowMax_clockOr_outerGauge_or_rate244
    L hL R Q G x y H D hRQ hD hCore

/-- UNIFORM COFINAL GAUGE BARRIER. A single late-index threshold works for
ALL natural gauges G, all inner cutoffs R and all real adverse observations
carrying the true gamma-free high-radial signed flux. For each such carrier
there is a physical finite annulus whose outer cutoff either crosses G,
or whose finite-gauge rate/clock cost is below the prescribed epsilon.
No uniform positive clock or height premise has been added. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_tailGaugeRateOrClock244
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
    (eta epsilon : ℝ) (hEta : 0 < eta) (hEpsilon : 0 < epsilon) :
    ∀ᶠ k : ℕ in atTop,
      ∀ (G R : ℕ) (t : ℝ),
        t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
        (eta / 2 ≤
          thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
            (velocityH3EnergyAt u t) *
            ‖thirdFullSpectralVelocityHighRadialApply244 R
              (h3AuditActualSpectralVelocityTotal hH3 t)‖ ^ 2) →
        ∃ Q : ℕ, R ≤ Q ∧
          (let H := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
                R eta (velocityH3EnergyAt u t)
           let C : ℝ := 2 * (∑ j ∈ Finset.range (G + 1),
             thirdFullPhysicalKineticLowBandDissipationRate244 j
               (velocityH3Energy0At u b)) + 1
           ((tau (v (k + 1)) - (tau (v k) + delta (v k))) * H <
             16 * epsilon) ∨ G < Q ∨ (H ^ 2 < 32 * C * epsilon)) := by
  have hOld := thirdFullPhysical_kineticGaps_signedLowMax_tailRateOrClock244
    hH3 hClass hDInt b hb M tau N delta v hLimit hSeparated hWindows
    eta hEta epsilon hEpsilon
  filter_upwards [hOld] with k hk
  intro G R t ht hTail
  obtain ⟨Q, hRQ, hAlt⟩ := hk R t ht hTail
  refine ⟨Q, hRQ, ?_⟩
  let L : ℕ → ℝ := fun j =>
    thirdFullPhysicalKineticLowBandDissipationRate244 j
      (velocityH3Energy0At u b)
  let H : ℝ := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
    R eta (velocityH3EnergyAt u t)
  let C : ℝ := 2 * (∑ j ∈ Finset.range (G + 1), L j) + 1
  change ((tau (v (k + 1)) - (tau (v k) + delta (v k))) * H <
      16 * epsilon) ∨
    H ^ 2 < 32 * (L Q + L R + 1) * epsilon at hAlt
  change ((tau (v (k + 1)) - (tau (v k) + delta (v k))) * H <
      16 * epsilon) ∨ G < Q ∨ H ^ 2 < 32 * C * epsilon
  rcases hAlt with hClock | hRate
  · exact Or.inl hClock
  right
  by_cases hGauge : G < Q
  · exact Or.inl hGauge
  right
  have hQG : Q ≤ G := Nat.le_of_not_gt hGauge
  have hL (j : ℕ) : 0 ≤ L j :=
    thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 j _
  have hBound := thirdFullKinetic_signedLowMax_twoRates_le_gaugeSum244
    L hL R Q G hRQ hQG
  have hCoeff :
      32 * (L Q + L R + 1) ≤ 32 * C := by
    dsimp only [C]
    linarith only [hBound]
  exact lt_of_lt_of_le hRate
    (mul_le_mul_of_nonneg_right hCoeff hEpsilon.le)

/-- Once the signed high-radial carrier has neither an epsilon-short
height clock nor an epsilon-affordable finite-gauge rate, the certified
physical annulus MUST cross any chosen natural cutoff G. The cofinal
index does not depend on G, R or t. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_tailOuterGaugeEscape244
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
    (eta epsilon : ℝ) (hEta : 0 < eta) (hEpsilon : 0 < epsilon) :
    ∀ᶠ k : ℕ in atTop,
      ∀ (G R : ℕ) (t : ℝ),
        t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
        (eta / 2 ≤
          thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
            (velocityH3EnergyAt u t) *
            ‖thirdFullSpectralVelocityHighRadialApply244 R
              (h3AuditActualSpectralVelocityTotal hH3 t)‖ ^ 2) →
        (16 * epsilon ≤
          (tau (v (k + 1)) - (tau (v k) + delta (v k))) *
            thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
              R eta (velocityH3EnergyAt u t)) →
        (32 * (2 * (∑ j ∈ Finset.range (G + 1),
          thirdFullPhysicalKineticLowBandDissipationRate244 j
            (velocityH3Energy0At u b)) + 1) * epsilon ≤
          (thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
            R eta (velocityH3EnergyAt u t)) ^ 2) →
        ∃ Q : ℕ, R ≤ Q ∧ G < Q := by
  have hOld := thirdFullPhysical_kineticGaps_signedLowMax_tailGaugeRateOrClock244
    hH3 hClass hDInt b hb M tau N delta v hLimit hSeparated hWindows
    eta epsilon hEta hEpsilon
  filter_upwards [hOld] with k hk
  intro G R t ht hTail hClock hRate
  obtain ⟨Q, hRQ, hAlt⟩ := hk G R t ht hTail
  refine ⟨Q, hRQ, ?_⟩
  rcases hAlt with hClockCost | hRest
  · exact False.elim ((not_lt_of_ge hClock) hClockCost)
  rcases hRest with hGauge | hRateCost
  · exact hGauge
  · exact False.elim ((not_lt_of_ge hRate) hRateCost)

end
end PrimeTensor.FirstMonomialTriad
