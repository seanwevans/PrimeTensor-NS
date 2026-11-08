import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxPhysicalBaselineAndViscous
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCofinalGapCompression
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticGapLowBandPDEFreezing
import Mathlib.Tactic

/-!
# Cofinal signed sixth flux: physical radius/energy escape or compressed gap cost

The previous four-cost theorem expresses the genuine adverse signed sixth flux
only in terms of physical spectral states, physical source, and dissipation.
The original separated kinetic gaps also have source-L1 and dissipation
integrals tending to zero. We synchronize these results without postulating
an endpoint-uniform Fourier cutoff or an endpoint H3 energy ceiling.

For any K >= 0 and epsilon > 0, on every sufficiently late original kinetic
gap, a physical adverse top-third transport snapshot must pay its high-radial
H3 tail, the earlier cubic physical baseline, a physical cutoff/energy clock
coefficient STRICTLY GREATER than K, or an actual annular width-times-height
charge LESS than epsilon. The time and cutoff may vary with the gap.

An additional corollary starts from the original signed integrated surplus,
not from an assumed adverse snapshot. These are necessary alternatives only.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology FourierTransform
open scoped BigOperators Interval ENNReal SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- A positive signed clock on an L1 interval of small mass forces its
nonnegative-free multiplicative coefficient beyond any prescribed bound.
The strict inequality uses K+1 in the denominator and works at K=0. -/
theorem thirdFull_scalar_signedLowMax_sourceCoefficient_escape244
    (mu K A S : ℝ) (hMu : 0 < mu) (hK : 0 ≤ K)
    (hS : 0 ≤ S)
    (hClock : mu / 8 < A * S)
    (hSmall : S < mu / (8 * (K + 1))) : K < A := by
  by_contra hNot
  have hAK : A ≤ K := le_of_not_gt hNot
  have hKOne : 0 < K + 1 := by linarith only [hK]
  have hMul : (K + 1) * S < mu / 8 := by
    calc
      (K + 1) * S < (K + 1) * (mu / (8 * (K + 1))) :=
        mul_lt_mul_of_pos_left hSmall hKOne
      _ = mu / 8 := by
        field_simp [ne_of_gt hKOne] <;> ring
  have hAS : A * S ≤ K * S :=
    mul_le_mul_of_nonneg_right hAK hS
  have hKS : K * S ≤ (K + 1) * S :=
    mul_le_mul_of_nonneg_right (by linarith only [hK]) hS
  linarith only [hClock, hAS, hKS, hMul]

/-- The four physical alternatives after taking the true cofinal source and
viscosity limits. Neither the cutoff nor the adverse observation time is fixed
across gaps. The reference baseline is the original physical left-endpoint
cubic term, not an assumed zero. -/
def ThirdFullKineticSignedLowMaxPhysicalCofinalEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R : ℕ) (gamma eta K epsilon x y t : ℝ) : Prop :=
  (eta / 2 < ((2 * Real.pi) ^ 7 / 3) *
    (1944 * h3SobolevFirstMomentDeweightingConstant *
      (velocityH3EnergyAt u t + 1) *
      (‖thirdFullSpectralVelocityHighRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 t)‖ + gamma) ^ 2)) ∨
  (let mu := thirdFullKineticSignedLowMaxPhysicalMargin244 eta
   let X := h3AuditActualSpectralVelocityTotal hH3 t
   let Y := h3AuditActualSpectralVelocityTotal hH3 x
   (mu / 2 ≤ thirdFullKineticSignedLowMaxPhysicalBaselineCeiling244 R Y) ∨
   (K < thirdFullKineticSignedLowMaxPhysicalClockCeiling244 R X Y *
     thirdFullFiniteBandH3WeightCeiling244 R) ∨
   (∃ z width : ℝ, (z = t ∨ z = x) ∧ 0 < width ∧
      ((z + width < y) ∨ (z = y ∧ x < y - width)) ∧
      width * (thirdFullKineticSignedLowMaxPhysicalViscousHeight244
        R X Y (mu / 2) / 4) < epsilon))

/-- On every sufficiently late ORIGINAL kinetic gap, the actual top-order
adverse flux has a physical high-tail, cubic earlier baseline, UNBOUNDED-in-K
source multiplier, or an epsilon-compressed physical annular viscous charge.
No terminal-uniform radius, energy ceiling or persistence width is assumed. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_physicalCofinalEscape244
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
    (K epsilon : ℝ) (hK : 0 ≤ K) (hEpsilon : 0 < epsilon) :
    ∀ᶠ k : ℕ in atTop,
      ∀ (R : ℕ) (gamma : ℝ), 0 < gamma →
        ∀ t : ℝ,
          t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
          eta < -velocityH3TransportDerivative3At u t →
          ThirdFullKineticSignedLowMaxPhysicalCofinalEscape244
            hH3 R gamma eta K epsilon
            (tau (v k) + delta (v k)) (tau (v (k + 1))) t := by
  let mu : ℝ := thirdFullKineticSignedLowMaxPhysicalMargin244 eta
  have hMu : 0 < mu :=
    thirdFullKineticSignedLowMaxPhysicalMargin_pos244 eta hEta
  have hKOne : 0 < K + 1 := by linarith only [hK]
  have hThreshold : 0 < mu / (8 * (K + 1)) :=
    div_pos hMu (mul_pos (by norm_num) hKOne)
  have hSource := thirdFullPhysical_kineticGaps_sourceL1_tendsto_zero244
    hH3 hClass hDInt b hb M tau N delta v hLimit hSeparated hWindows
  have hDiss := thirdFullPhysical_kineticGaps_fullDissipation_tendsto_zero244
    hH3 hClass hDInt b hb M tau N delta v hLimit hSeparated hWindows
  have hSourceSmall : ∀ᶠ k : ℕ in atTop,
      (∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
        ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) <
        mu / (8 * (K + 1)) :=
    hSource.eventually (eventually_lt_nhds hThreshold)
  have hDissSmall : ∀ᶠ k : ℕ in atTop,
      (∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
        velocityH3DissipationAt u r ∂volume) < epsilon :=
    hDiss.eventually (eventually_lt_nhds hEpsilon)
  filter_upwards [hSourceSmall, hDissSmall] with k hkSource hkDiss
  intro R gamma hGamma t ht hAdverse
  let x : ℝ := tau (v k) + delta (v k)
  let y : ℝ := tau (v (k + 1))
  have hx : x ∈ Set.Ioo b T := by
    have hWin := (hWindows k).2
    rcases hWin with ⟨_, hDelta, _, hEnd, _, _⟩
    exact ⟨by linarith only [(hWindows k).1.1, hDelta], hEnd⟩
  have hy : y ∈ Set.Ioo b T := (hWindows (k + 1)).1
  have hxy : x < y := hSeparated k (k + 1) (Nat.lt_succ_self k)
  have ht' : t ∈ Set.Icc x y := ht
  have hAlt := thirdFullPhysical_gapAdverseThird_physicalLowMaxFourCosts244
    hH3 hClass hDInt b hb R x y t hx hy hxy ht'
    eta gamma hEta hGamma hAdverse
  change ThirdFullKineticSignedLowMaxPhysicalCofinalEscape244
    hH3 R gamma eta K epsilon x y t
  rcases hAlt with hTail | hRest
  · exact Or.inl hTail
  right
  rcases hRest with hBaseline | hRest
  · exact Or.inl hBaseline
  right
  rcases hRest with hClock | ⟨z, width, hz, hWidth, hInside, hCharge⟩
  · left
    let X : H3SpectralVelocityState :=
      h3AuditActualSpectralVelocityTotal hH3 t
    let Y : H3SpectralVelocityState :=
      h3AuditActualSpectralVelocityTotal hH3 x
    let A : ℝ := thirdFullKineticSignedLowMaxPhysicalClockCeiling244 R X Y *
      thirdFullFiniteBandH3WeightCeiling244 R
    let S : ℝ :=
      ∫ r in x..y, ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume
    have hS : 0 ≤ S :=
      intervalIntegral.integral_nonneg hxy.le (fun r _ => norm_nonneg _)
    have hClock' : mu / 8 < A * S := by
      simpa only [A, S, mul_assoc] using hClock
    have hSsmall : S < mu / (8 * (K + 1)) := hkSource
    exact thirdFull_scalar_signedLowMax_sourceCoefficient_escape244
      mu K A S hMu hK hS hClock' hSsmall
  · right
    exact ⟨z, width, hz, hWidth, hInside,
      lt_of_le_of_lt hCharge hkDiss⟩

/-- The original positive signed *integrated* gap surplus automatically
provides the adverse observation needed by the cofinal physical alternative.
The excess is a per-gap conditional premise, not asserted at every index. -/
theorem thirdFullPhysical_kineticGaps_signedSurplus_physicalCofinalEscape244
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
    (K epsilon : ℝ) (hK : 0 ≤ K) (hEpsilon : 0 < epsilon) :
    ∀ᶠ k : ℕ in atTop,
      ∀ (R : ℕ) (gamma : ℝ), 0 < gamma →
        thirdFullKineticGapLowOrderMargin244 u eta
            (tau (v k) + delta (v k)) (tau (v (k + 1))) <
          thirdFullKineticGapSignedSurplus244 u
            (tau (v k) + delta (v k)) (tau (v (k + 1))) →
        ∃ t : ℝ,
          t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) ∧
          eta < -velocityH3TransportDerivative3At u t ∧
          ThirdFullKineticSignedLowMaxPhysicalCofinalEscape244
            hH3 R gamma eta K epsilon
            (tau (v k) + delta (v k)) (tau (v (k + 1))) t := by
  have hEventually :=
    thirdFullPhysical_kineticGaps_signedLowMax_physicalCofinalEscape244
      hH3 hClass hDInt b hb M tau N delta v
      hLimit hSeparated hWindows eta hEta K epsilon hK hEpsilon
  filter_upwards [hEventually] with k hk
  intro R gamma hGamma hExcess
  let x : ℝ := tau (v k) + delta (v k)
  let y : ℝ := tau (v (k + 1))
  have hx : x ∈ Set.Ioo a T := by
    have hWin := (hWindows k).2
    rcases hWin with ⟨_, hDelta, _, hEnd, _, _⟩
    exact ⟨by linarith only [hb.1, (hWindows k).1.1, hDelta], hEnd⟩
  have hy : y ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (hWindows (k + 1)).1.1,
      (hWindows (k + 1)).1.2⟩
  have hxy : x < y := hSeparated k (k + 1) (Nat.lt_succ_self k)
  obtain ⟨t, ht, hAdverse⟩ :=
    thirdFullPhysical_gapLowOrderExcess_forces_adverseThird244
      hH3 hClass x y eta hx hy hxy hEta hExcess
  exact ⟨t, ht, hAdverse, hk R gamma hGamma t ht hAdverse⟩

end
end PrimeTensor.FirstMonomialTriad
