import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousExactOverlapEnvelope
import Mathlib.Tactic

/-!
# Residual actual physical PDE rate after the exact overlapping H³ viscous clocks

The two-clock overlap envelope charges the entire primary clock before the
secondary excess peak can spend the REMAINING terminal H³ viscous action.

For A ≤ H, write L for the duration of the secondary interval outside the
primary one, and B for actual terminal H³ dissipation. The exact envelope
implies the residual bound

  theta*(H-A) ≤ B - eta*A - L*A.

Now use the genuine second projected-Navier--Stokes clock:

  theta = min ((T-s)/4) (H/(2*(Lambda2+1))).

It forces a temporal contraction OR the residual PDE-rate obstruction

  (T-s)*(H-A) ≤ 4*residual,
  H*(H-A) ≤ 2*(Lambda2+1)*residual.

Lambda2 is the ACTUAL attained source/state projected-PDE variation rate,
not an independent arbitrary Lipschitz bound. Its verified quintic physical
polynomial majorant yields a source-state-frequency amplification alternative.
This theorem is conditional on a strict secondary excess H>A and on the
same physical clock/exact envelope certificate. The existing cofinal theorem
has not yet retained J2 and the attained secondary PDE maxima, so we do NOT
claim an unconditional cofinal physical-rate bound here.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The actual action left after charging the full primary PDE window and
the primary floor on the nonoverlapping secondary extension. -/
noncomputable def thirdFullLateResidualTwoClockAction244
    (A B r s eta theta : ℝ) : ℝ :=
  B - eta * A -
    thirdFullLateSecondaryOutsidePrimaryDuration244 r s eta theta * A

/-- The exact two-clock floor envelope necessarily pays any SECONDARY
excess H-A entirely from the unspent terminal physical dissipation. -/
theorem thirdFull_scalar_exactOverlap_residualExcessCharge244
    (A B r s eta theta H : ℝ)
    (hAH : A ≤ H)
    (hExact : ThirdFullLateExactTwoClockOverlapEnvelope244
      A B r s eta theta H) :
    theta * (H - A) ≤
      thirdFullLateResidualTwoClockAction244 A B r s eta theta := by
  let L : ℝ := thirdFullLateSecondaryOutsidePrimaryDuration244 r s eta theta
  have hBase :
      eta * A + L * H + (theta - L) * max 0 (H - A) ≤ B := by
    exact hExact
  have hMax : max 0 (H - A) = H - A :=
    max_eq_right (sub_nonneg.mpr hAH)
  rw [hMax] at hBase
  dsimp only [thirdFullLateResidualTwoClockAction244]
  nlinarith only [hBase]

/-- Spend the SECOND clock's exact min-width from the residual tail, rather
than charging its full height against B a second time. The positive-rate
arm is a physical PDE variation demand, not a uniform clock bound. -/
theorem thirdFull_scalar_exactOverlap_residualPDEClockGate244
    (A B r s eta theta H T Lambda : ℝ)
    (hAH : A ≤ H) (htheta : 0 ≤ theta) (hLambda : 0 ≤ Lambda)
    (hExact : ThirdFullLateExactTwoClockOverlapEnvelope244
      A B r s eta theta H)
    (hClock : theta = min ((T - s) / 4) (H / (2 * (Lambda + 1)))) :
    0 ≤ thirdFullLateResidualTwoClockAction244 A B r s eta theta ∧
      ((T - s) * (H - A) ≤
        4 * thirdFullLateResidualTwoClockAction244 A B r s eta theta ∨
       H * (H - A) ≤
        2 * (Lambda + 1) *
          thirdFullLateResidualTwoClockAction244 A B r s eta theta) := by
  let E : ℝ := thirdFullLateResidualTwoClockAction244 A B r s eta theta
  have hCost : theta * (H - A) ≤ E :=
    thirdFull_scalar_exactOverlap_residualExcessCharge244
      A B r s eta theta H hAH hExact
  have hCostNonneg : 0 ≤ theta * (H - A) :=
    mul_nonneg htheta (sub_nonneg.mpr hAH)
  have hE : 0 ≤ E := le_trans hCostNonneg hCost
  refine ⟨hE, ?_⟩
  by_cases hTime : (T - s) / 4 ≤ H / (2 * (Lambda + 1))
  · left
    have hWidth : theta = (T - s) / 4 := by
      rw [hClock, min_eq_left hTime]
    calc
      (T - s) * (H - A) = 4 * (theta * (H - A)) := by
        rw [hWidth]
        ring
      _ ≤ 4 * E :=
        mul_le_mul_of_nonneg_left hCost (by norm_num)
  · right
    have hRateSide : H / (2 * (Lambda + 1)) ≤ (T - s) / 4 :=
      le_of_lt (lt_of_not_ge hTime)
    have hWidth : theta = H / (2 * (Lambda + 1)) := by
      rw [hClock, min_eq_right hRateSide]
    have hDen : 0 < 2 * (Lambda + 1) := by
      linarith only [hLambda]
    have hFraction : H * (H - A) / (2 * (Lambda + 1)) ≤ E := by
      calc
        H * (H - A) / (2 * (Lambda + 1)) =
            (H / (2 * (Lambda + 1))) * (H - A) := by ring
        _ = theta * (H - A) := by rw [hWidth]
        _ ≤ E := hCost
    have hMult := (div_le_iff₀ hDen).1 hFraction
    simpa only [mul_comm] using hMult

/-- The constructive source/state secondary floor is STRICTLY stronger
than the primary A precisely in the small R*B regime. This provides a
checkable scalar activation condition for the residual PDE gate. -/
theorem thirdFull_scalar_constructiveSqrtTail_activatesResidualExcess244
    (A R B : ℝ) (hA : 0 < A) (hRB : 0 < R * B)
    (hSmall : 24 * Real.sqrt (R * B) < 1) :
    A < (A / (12 * Real.sqrt (R * B))) / 2 := by
  let q : ℝ := Real.sqrt (R * B)
  have hq : 0 < q := Real.sqrt_pos.2 hRB
  have hFactor : 24 * q < 1 := by simpa only [q] using hSmall
  have hDen : 0 < 24 * q := by positivity
  have hProduct : A * (24 * q) < A := by
    have hMul := mul_lt_mul_of_pos_left hFactor hA
    simpa only [mul_one] using hMul
  have hDiv : A < A / (24 * q) :=
    (lt_div_iff₀ hDen).2 hProduct
  have hHeight : (A / (12 * q)) / 2 = A / (24 * q) := by
    field_simp [ne_of_gt hq]
    ring
  change A < (A / (12 * q)) / 2
  rw [hHeight]
  exact hDiv

/-- On an ACTUALLY SELECTED secondary physical clock, the rate branch must
amplify the attained projected momentum source, the spectral-state maximum,
or the secondary frequency cutoff. The full primary floor and secondary
exterior have already been deducted from the action available to pay it. -/
theorem thirdFullPhysical_selectedSecondaryClock_residualQuinticPDEGate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (A B r s eta1 eta2 h : ℝ)
    (J2 : ℕ) (zSource zState : ℝ)
    (hExcess : A ≤ h / 2) (heta2 : 0 < eta2)
    (hClock : eta2 = min ((T - s) / 4)
      ((h / 2) /
        (2 * (thirdFullLateViscousLowRadialPDERate244 J2
          ‖h3AuditActualSpectralVelocityTotal hH3 zState‖
          ‖h3PathActualProjectedMomentumSource244 hH3 zSource‖ + 1))))
    (hExact : ThirdFullLateExactTwoClockOverlapEnvelope244
      A B r s eta1 eta2 (h / 2)) :
    let E := thirdFullLateResidualTwoClockAction244 A B r s eta1 eta2
    0 ≤ E ∧
      ((T - s) * (h / 2 - A) ≤ 4 * E ∨
       (h / 2) * (h / 2 - A) ≤
         (48 * ‖h3AuditActualSpectralVelocityTotal hH3 zState‖ *
           ‖h3PathActualProjectedMomentumSource244 hH3 zSource‖ *
           (((J2 : ℝ) + 2) ^ 5) + 2) * E) := by
  let K : ℝ := ‖h3AuditActualSpectralVelocityTotal hH3 zState‖
  let C : ℝ := ‖h3PathActualProjectedMomentumSource244 hH3 zSource‖
  let S : ℝ := (((J2 : ℝ) + 2) ^ 5)
  let Lambda : ℝ := thirdFullLateViscousLowRadialPDERate244 J2 K C
  let E : ℝ := thirdFullLateResidualTwoClockAction244 A B r s eta1 eta2
  have hLambda : 0 ≤ Lambda := by
    dsimp only [Lambda, thirdFullLateViscousLowRadialPDERate244]
    positivity
  have hClock' : eta2 = min ((T - s) / 4)
      ((h / 2) / (2 * (Lambda + 1))) := by
    simpa only [Lambda, K, C] using hClock
  obtain ⟨hE, hAlternatives⟩ :=
    thirdFull_scalar_exactOverlap_residualPDEClockGate244
      A B r s eta1 eta2 (h / 2) T Lambda
      hExcess heta2.le hLambda hExact hClock'
  have hPoly : Lambda ≤ 24 * K * C * S := by
    dsimp only [Lambda, S, K, C]
    exact thirdFull_lateLowRadialPDERate_le_quinticPhysicalProduct244
      J2 _ _ (norm_nonneg _) (norm_nonneg _)
  have hMultiplier : 2 * (Lambda + 1) ≤ 48 * K * C * S + 2 := by
    nlinarith only [hPoly]
  change 0 ≤ E ∧
    ((T - s) * (h / 2 - A) ≤ 4 * E ∨
      (h / 2) * (h / 2 - A) ≤ (48 * K * C * S + 2) * E)
  refine ⟨hE, ?_⟩
  rcases hAlternatives with hTime | hRate
  · exact Or.inl hTime
  · right
    exact hRate.trans (mul_le_mul_of_nonneg_right hMultiplier hE)


/-- No extra overlap-envelope premise is needed when BOTH actual PDE clock
certificates are supplied. Destruct the secondary clock ONCE; use its SAME
selected s, eta2, cutoff, and physical maxima for the exact interval packing
and the residual quintic PDE-rate trilemma. -/
theorem thirdFullPhysical_dualSelectedClock_residualPDERate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (m r eta1 A sState sSource h : ℝ)
    (hm : m ∈ Set.Ioo a T) (hr : r ∈ Set.Ioo m T)
    (heta1 : 0 < eta1) (hend1 : r + eta1 < T)
    (hFloor1 : ∀ x : ℝ, x ∈ Set.Icc r (r + eta1) →
      A < velocityH3DissipationAt u x)
    (hPrimary : eta1 * A ≤
      ∫ x in m..T, velocityH3DissipationAt u x ∂volume)
    (hsState : sState ∈ Set.Icc r (r + (T - r) / 2))
    (hsSource : sSource ∈ Set.Icc r (r + (T - r) / 2))
    (hSecondary : ThirdFullLateSecondaryPDEClock244
      hH3 m sState sSource h)
    (hExcess : A ≤ h / 2) :
    ∃ (s eta2 : ℝ) (J2 : ℕ) (zSource zState : ℝ),
      (s = sState ∨ s = sSource) ∧ r ≤ s ∧
      0 < eta2 ∧ s + eta2 < T ∧
      zSource ∈ Set.Icc s (s + (T - s) / 2) ∧
      zState ∈ Set.Icc s (s + (T - s) / 2) ∧
      (let B : ℝ := ∫ x in m..T, velocityH3DissipationAt u x ∂volume
       let E : ℝ := thirdFullLateResidualTwoClockAction244
         A B r s eta1 eta2
       ThirdFullLateExactTwoClockOverlapEnvelope244
         A B r s eta1 eta2 (h / 2) ∧
       0 ≤ E ∧
       ((T - s) * (h / 2 - A) ≤ 4 * E ∨
        (h / 2) * (h / 2 - A) ≤
          (48 * ‖h3AuditActualSpectralVelocityTotal hH3 zState‖ *
            ‖h3PathActualProjectedMomentumSource244 hH3 zSource‖ *
            (((J2 : ℝ) + 2) ^ 5) + 2) * E)) := by
  rcases hSecondary with ⟨s, hChoice, J2, zSource, zState, eta2,
      hzSource, hzState, hEtaEq, heta2, hend2, hFloor2, _hCost2⟩
  have hrs : r ≤ s := by
    rcases hChoice with rfl | rfl
    · exact hsState.1
    · exact hsSource.1
  let D : ℝ → ℝ := velocityH3DissipationAt u
  let B : ℝ := ∫ x in m..T, D x ∂volume
  have hDtail : IntervalIntegrable D volume m T := by
    apply hDInt.mono_set
    intro x hx
    have hxIcc : x ∈ Set.Icc m T := by
      simpa only [Set.uIcc_of_le hm.2.le] using hx
    have hxMain : x ∈ Set.Icc a T :=
      ⟨hm.1.le.trans hxIcc.1, hxIcc.2⟩
    simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hxMain
  have hPrefix := thirdFull_scalar_orderedTwoClocks_trimmedPrefixCharge244
    D m T r s eta1 eta2 A (h / 2)
    hDtail hm.2.le (velocityH3DissipationAt_nonneg u)
    hr.1.le hrs heta1.le heta2.le hend2.le
    (fun x hx => (hFloor1 x hx).le)
    (fun x hx => (hFloor2 x hx).2.le)
  have hSuffix := thirdFull_scalar_orderedTwoClocks_secondarySuffixCharge244
    D m T r s eta1 eta2 A (h / 2)
    hDtail hm.2.le (velocityH3DissipationAt_nonneg u)
    hr.1.le hrs heta1.le heta2.le hend1.le hend2.le
    (fun x hx => (hFloor1 x hx).le)
    (fun x hx => (hFloor2 x hx).2.le)
  have hPack := thirdFull_scalar_orderedTwoClocks_threeWayMaxCharge244
    B r s eta1 eta2 A (h / 2)
    (by simpa only [B, D] using hPrimary) hPrefix hSuffix
  have hContained (hInside : s + eta2 ≤ r + eta1) :
      eta1 * A + eta2 * max 0 (h / 2 - A) ≤ B :=
    thirdFull_scalar_containedSecondary_positiveExcessCharge244
      D m T r s eta1 eta2 A (h / 2)
      hDtail hm.2.le (velocityH3DissipationAt_nonneg u)
      hr.1.le hrs heta1.le heta2.le hend1.le hInside
      (fun x hx => (hFloor1 x hx).le)
      (fun x hx => (hFloor2 x hx).2.le)
  have hEnvelope : ThirdFullLateExactTwoClockOverlapEnvelope244
      A B r s eta1 eta2 (h / 2) := by
    apply thirdFull_scalar_twoClock_exactOverlap_from_packing244
      A B r s eta1 eta2 (h / 2) hrs heta2.le
    · simpa only [thirdFullLateSecondaryOutsidePrimaryDuration244] using hPack
    · exact hContained
  obtain ⟨hResidual, hPDE⟩ :=
    thirdFullPhysical_selectedSecondaryClock_residualQuinticPDEGate244
      hH3 A B r s eta1 eta2 h J2 zSource zState
      hExcess heta2 hEtaEq hEnvelope
  exact ⟨s, eta2, J2, zSource, zState, hChoice, hrs, heta2, hend2,
    hzSource, hzState, hEnvelope, hResidual, hPDE⟩

end
end PrimeTensor.FirstMonomialTriad
