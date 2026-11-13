import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierKineticOnlySlope
import Mathlib.Tactic

/-!
# Two-radius signed source payment for selected outer H3 carriers

The earlier kinetic-only signed slope estimate bounded the source cost by
`2 * sigma^10 * ‖Vx‖² * A`. This discards the separate INNER highpass radius.
Retaining `w = rho^6` while using only `a ≤ sigma²` yields the sharper
`2 * rho^6 * sigma^4 * ‖Vx‖² * A`.

The signed cancellation remains exact and depends on the original positive
annular deficit. The physical L2 kinetic-energy antitonicity then provides a
fixed anchor E0(b). When the nonlinear Young cost fails to increase, the
actual projected-source tail must pay a FOURTH power of the outer frequency
if the inner cutoff remains bounded. No time-derivative hypothesis or
uniform nonlinear H3 envelope is introduced.

The source tail still needs frequency-weighted control for a continuation
argument; no terminal H3 trace or Navier--Stokes global regularity is claimed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Preserve the INNER highpass radius in the signed kinetic slope.
Only the mean annular frequency is bounded by the outer radius. -/
theorem thirdFullKinetic_earlyYoung_kineticSlope_twoRadiusCap244
    (a B mx rho sigma H : ℝ)
    (ha : 0 ≤ a) (haCap : a ≤ sigma ^ 2)
    (hB : 0 ≤ B) (hmx : 0 ≤ mx) (hmxCap : mx ≤ H)
    (hH : 0 ≤ H) :
    2 * (rho ^ 2) ^ 3 * a * (a * mx - B) ≤
      2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 * H := by
  have hInside : a * mx - B ≤ sigma ^ 2 * H := by
    calc
      a * mx - B ≤ a * mx := sub_le_self _ hB
      _ ≤ sigma ^ 2 * mx := mul_le_mul_of_nonneg_right haCap hmx
      _ ≤ sigma ^ 2 * H :=
        mul_le_mul_of_nonneg_left hmxCap (sq_nonneg sigma)
  have hCoeff : 0 ≤ 2 * (rho ^ 2) ^ 3 * a := by positivity
  have hCoeffBase : 0 ≤ 2 * (rho ^ 2) ^ 3 := by positivity
  have hOther : 0 ≤ sigma ^ 2 * H :=
    mul_nonneg (sq_nonneg sigma) hH
  calc
    2 * (rho ^ 2) ^ 3 * a * (a * mx - B) ≤
        (2 * (rho ^ 2) ^ 3 * a) * (sigma ^ 2 * H) :=
          mul_le_mul_of_nonneg_left hInside hCoeff
    _ ≤ (2 * (rho ^ 2) ^ 3 * (sigma ^ 2)) * (sigma ^ 2 * H) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left haCap hCoeffBase) hOther
    _ = 2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 * H := by ring

/-- The old sigma^10 estimate is a corollary of the two-radius estimate.
The gain is precisely (rho/sigma)^6 for positive radii. -/
theorem thirdFullKinetic_twoRadiusSlopeCap_le_outerRadiusCap244
    (rho sigma H : ℝ) (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma)
    (hH : 0 ≤ H) :
    2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 * H ≤
      2 * (sigma ^ 2) ^ 5 * H := by
  have hSq : rho ^ 2 ≤ sigma ^ 2 :=
    pow_le_pow_left₀ hRho hOrder 2
  have hCube : (rho ^ 2) ^ 3 ≤ (sigma ^ 2) ^ 3 :=
    pow_le_pow_left₀ (sq_nonneg rho) hSq 3
  calc
    2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 * H =
        (rho ^ 2) ^ 3 * (2 * (sigma ^ 2) ^ 2 * H) := by ring
    _ ≤ (sigma ^ 2) ^ 3 * (2 * (sigma ^ 2) ^ 2 * H) :=
      mul_le_mul_of_nonneg_right hCube (by positivity)
    _ = 2 * (sigma ^ 2) ^ 5 * H := by ring

/-- A fixed inner-radius ceiling converts the signed source payment into a
quartic, rather than tenth-power, outer-frequency condition. -/
theorem thirdFullKinetic_boundedInnerRadius_quarticSourcePayment244
    (rho sigma R E A epsilon : ℝ)
    (hRho : 0 ≤ rho) (hBound : rho ≤ R)
    (hE : 0 ≤ E) (hA : 0 ≤ A)
    (hPayment : epsilon <
      A * (2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 * E)) :
    epsilon < A * (2 * (R ^ 2) ^ 3 * (sigma ^ 2) ^ 2 * E) := by
  have hSq : rho ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ hRho hBound 2
  have hCube : (rho ^ 2) ^ 3 ≤ (R ^ 2) ^ 3 :=
    pow_le_pow_left₀ (sq_nonneg rho) hSq 3
  have hCoeff : 0 ≤ A * (2 * (sigma ^ 2) ^ 2 * E) := by positivity
  have hProduct :
      A * (2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 * E) ≤
        A * (2 * (R ^ 2) ^ 3 * (sigma ^ 2) ^ 2 * E) := by
    calc
      A * (2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 * E) =
          (rho ^ 2) ^ 3 * (A * (2 * (sigma ^ 2) ^ 2 * E)) := by ring
      _ ≤ (R ^ 2) ^ 3 * (A * (2 * (sigma ^ 2) ^ 2 * E)) :=
        mul_le_mul_of_nonneg_right hCube hCoeff
      _ = A * (2 * (R ^ 2) ^ 3 * (sigma ^ 2) ^ 2 * E) := by ring
  exact lt_of_lt_of_le hPayment hProduct

/-- Radius-separated physical slope coefficient: `rho^6 * sigma^4`.
There is NO H3 spectral Young/residual factor in this definition. -/
noncomputable def thirdFullPhysicalOuterTwoRadiusSlopeCap244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x rho sigma : ℝ) : ℝ :=
  2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 *
    ‖h3AuditInitialOldPhysicalHilbertTotal hH3 x‖ ^ 2

/-- The source slope coefficient is controlled by the FIXED physical kinetic
anchor E0(b), not by the potentially large H3 spectral state. -/
theorem thirdFullPhysical_outerTwoRadiusSlopeCap_le_kineticAnchor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (rho sigma : ℝ) :
    thirdFullPhysicalOuterTwoRadiusSlopeCap244 hH3 x rho sigma ≤
      2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 *
        velocityH3Energy0At u b := by
  have hb0 : b ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hb.1, hb.2⟩
  have hx0 : x ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hb0.1 hx.1, hx.2⟩
  have hEnergy : velocityH3Energy0At u x ≤ velocityH3Energy0At u b :=
    (h3Audit_initialKineticEnergy_antitoneOn_positiveInterval hH3)
      hb0 hx0 hx.1.le
  have hNormEq :
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 x‖ ^ 2 =
        velocityH3Energy0At u x := by
    rw [h3Audit_initialOldPhysicalHilbert_norm_eq_sqrt_kineticEnergy
      hH3 x hx0, Real.sq_sqrt (velocityH3Energy0At_nonneg u x)]
  have hBound : ‖h3AuditInitialOldPhysicalHilbertTotal hH3 x‖ ^ 2 ≤
      velocityH3Energy0At u b := by
    rw [hNormEq]
    exact hEnergy
  change (2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2) *
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 x‖ ^ 2 ≤
    (2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2) * velocityH3Energy0At u b
  exact mul_le_mul_of_nonneg_left hBound (by positivity)

theorem thirdFullPhysical_outerDeficitDrop_twoRadiusSlopeResidual244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (s : ℝ) (hxs : x ≤ s) (hsT : s < T)
    (rho sigma epsilon : ℝ)
    (hRho : 0 < rho) (hAspect : 2 * rho ≤ sigma)
    (hMargin : 0 < epsilon)
    (margin : ℝ) (hMarginPos : 0 < margin)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho)
    (hPeak : 2 * epsilon ≤
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma)
    (hDrop : epsilon <
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
        thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma) :
    let A := thirdFullPhysicalOuterSourceMassBudget244 hH3 b x
    let K := thirdFullPhysicalOuterTwoRadiusSlopeCap244 hH3 x rho sigma
    let Ms := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
    let Yx := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
    let Ys := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma
    epsilon - A * K < Ms * (Ys - Yx) := by
  let aMean : ℝ := (rho ^ 2 + sigma ^ 2) / 2
  let w : ℝ := (rho ^ 2) ^ 3
  let B : ℝ := Real.sqrt (velocityH3Energy0At u b) *
    (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
      rho (velocityH3Energy0At u b))
  let P : ℝ := thirdFullPhysicalOuterViscousCapBase244 u b aMean
  let Mx : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
  let Ms : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
  let Yx : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
  let Ys : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma
  let A : ℝ := thirdFullPhysicalOuterSourceMassBudget244 hH3 b x
  let K : ℝ := thirdFullPhysicalOuterTwoRadiusSlopeCap244 hH3 x rho sigma
  let Vx := h3AuditInitialOldPhysicalHilbertTotal hH3 x
  have hOrder : rho ≤ sigma := by linarith only [hRho, hAspect]
  have hRhoNonneg : 0 ≤ rho := hRho.le
  have hMean := thirdFullKinetic_annularMeanSquare_bound244
    rho sigma sigma hRhoNonneg hOrder le_rfl
  change 0 ≤ aMean ∧ aMean ≤ sigma ^ 2 at hMean
  have ha : 0 ≤ aMean := hMean.1
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (thirdFullPhysicalKineticLowBandSourceCeiling_nonneg244
          rho (velocityH3Energy0At u b)))
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hP : 0 ≤ P :=
    (thirdFullPhysical_outerViscousCapBase_boundedReal244
      u b aMean sigma ha hMean.2).1
  have hY : 0 ≤ Yx :=
    thirdFullPhysical_actualYoungWidth_nonneg244
      hH3 x rho sigma hRhoNonneg hOrder
  have hC : 0 ≤ Yx + w * P :=
    add_nonneg hY (mul_nonneg hw hP)
  have hMxNonneg : 0 ≤ Mx := sq_nonneg _
  have hEx : B + margin ≤ aMean * Mx := hExcess
  have hMx : 0 < Mx := by
    by_contra hn
    have hz : Mx = 0 := le_antisymm (le_of_not_gt hn) hMxNonneg
    rw [hz, mul_zero] at hEx
    linarith only [hEx, hB, hMarginPos]
  have hExNonneg : 0 ≤ aMean * Mx - B := by
    linarith only [hEx, hMarginPos]
  have hDef : 0 ≤
      w * (aMean * Mx - B) ^ 2 - Mx * (Yx + w * P) := by
    change 2 * epsilon ≤
      w * (aMean * Mx - B) ^ 2 - Mx * (Yx + w * P) at hPeak
    linarith only [hPeak, hMargin]
  have hMassOne : |Ms - Mx| ≤ A :=
    thirdFullPhysical_outerHighpassMassDrift_le_sourceBudget244
      hH3 hClass hDInt b hb x hx s hxs hsT rho
  have hMass : |Mx - Ms| ≤ A := by
    simpa only [abs_sub_comm] using hMassOne
  have hIdentity := thirdFullPhysical_outerDeficit_earlyYoungIdentity244
    hH3 b x s rho sigma
  change
    thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma =
        (Mx - Ms) * (w * aMean * (aMean * (Mx + Ms) - 2 * B) -
          (Yx + w * P)) + Ms * (Ys - Yx) at hIdentity
  have hDrop' : epsilon <
      (Mx - Ms) * (w * aMean * (aMean * (Mx + Ms) - 2 * B) -
        (Yx + w * P)) + Ms * (Ys - Yx) := by
    rw [hIdentity] at hDrop
    exact hDrop
  have hScalar :
      epsilon - A * (2 * w * aMean * (aMean * Mx - B)) <
        Ms * (Ys - Yx) :=
    thirdFullKinetic_earlyYoung_kineticOnlyResidual244
      aMean B w (Yx + w * P) Mx Ms Yx Ys epsilon A
      ha hB hw hC hMx hExNonneg hDef hMass hDrop'
  have hMxCap : Mx ≤ ‖Vx‖ ^ 2 := by
    change ‖Vx - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vx‖ ^ 2 ≤
      ‖Vx‖ ^ 2
    exact pow_le_pow_left₀ (norm_nonneg _)
      (thirdFullPhysical_sharpVectorHighpass_norm_le244 rho Vx) 2
  have hKCap : 2 * w * aMean * (aMean * Mx - B) ≤ K := by
    change 2 * (rho ^ 2) ^ 3 * aMean * (aMean * Mx - B) ≤
      2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 * ‖Vx‖ ^ 2
    exact thirdFullKinetic_earlyYoung_kineticSlope_twoRadiusCap244
      aMean B Mx rho sigma (‖Vx‖ ^ 2)
      ha hMean.2 hB hMxNonneg hMxCap (sq_nonneg _)
  have hA : 0 ≤ A := (abs_nonneg _).trans hMass
  have hPay : A * (2 * w * aMean * (aMean * Mx - B)) ≤ A * K :=
    mul_le_mul_of_nonneg_left hKCap hA
  change epsilon - A * K < Ms * (Ys - Yx)
  linarith only [hScalar, hPay]

/-- If the selected Young cost does NOT increase, the source-tail
    multiplier pays the full positive deficit drop. The absolute L2 energy
    ceiling is a FIXED kinetic anchor at b, not an H3 envelope. -/
theorem thirdFullPhysical_outerNoYoungGrowth_forcesTwoRadiusSourcePayment244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (s : ℝ) (hxs : x ≤ s) (hsT : s < T)
    (rho sigma epsilon : ℝ)
    (hRho : 0 < rho) (hAspect : 2 * rho ≤ sigma)
    (hMargin : 0 < epsilon)
    (margin : ℝ) (hMarginPos : 0 < margin)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho)
    (hPeak : 2 * epsilon ≤
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma)
    (hDrop : epsilon <
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
        thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma)
    (hNoGrowth :
      thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma ≤
        thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma) :
    epsilon < thirdFullPhysicalOuterSourceMassBudget244 hH3 b x *
      (2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 *
        velocityH3Energy0At u b) := by
  let A : ℝ := thirdFullPhysicalOuterSourceMassBudget244 hH3 b x
  let K : ℝ := thirdFullPhysicalOuterTwoRadiusSlopeCap244 hH3 x rho sigma
  let Ms : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
  let Yx : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
  let Ys : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma
  have hResidual : epsilon - A * K < Ms * (Ys - Yx) :=
    thirdFullPhysical_outerDeficitDrop_twoRadiusSlopeResidual244
      hH3 hClass hDInt b hb x hx s hxs hsT
      rho sigma epsilon hRho hAspect hMargin margin hMarginPos
      hExcess hPeak hDrop
  have hMs : 0 ≤ Ms := sq_nonneg _
  have hYoung : Ms * (Ys - Yx) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hMs (sub_nonpos.mpr hNoGrowth)
  have hPayment : epsilon < A * K := by
    linarith only [hResidual, hYoung]
  have hA : 0 ≤ A := by
    have hMass := thirdFullPhysical_outerHighpassMassDrift_le_sourceBudget244
      hH3 hClass hDInt b hb x hx x le_rfl hx.2 rho
    exact (abs_nonneg _).trans hMass
  have hKBound : K ≤
      2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 *
        velocityH3Energy0At u b :=
    thirdFullPhysical_outerTwoRadiusSlopeCap_le_kineticAnchor244
      hH3 hClass b hb x hx rho sigma
  have hBigger : A * K ≤ A *
      (2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 *
        velocityH3Energy0At u b) :=
    mul_le_mul_of_nonneg_left hKBound hA
  exact lt_of_lt_of_le hPayment hBigger

/-- When the highpass cutoff remains below R, an absent signed Young gain
    forces at least a quartic OUTER radius times the true projected source
    mass budget, with the physical initial kinetic anchor. -/
theorem thirdFullPhysical_outerNoYoungGrowth_boundedInner_quarticCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (s : ℝ) (hxs : x ≤ s) (hsT : s < T)
    (rho sigma R epsilon : ℝ)
    (hRho : 0 < rho) (hAspect : 2 * rho ≤ sigma)
    (hBound : rho ≤ R)
    (hMargin : 0 < epsilon)
    (margin : ℝ) (hMarginPos : 0 < margin)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho)
    (hPeak : 2 * epsilon ≤
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma)
    (hDrop : epsilon <
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
        thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma)
    (hNoGrowth :
      thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma ≤
        thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma) :
    epsilon < thirdFullPhysicalOuterSourceMassBudget244 hH3 b x *
      (2 * (R ^ 2) ^ 3 * (sigma ^ 2) ^ 2 *
        velocityH3Energy0At u b) := by
  have hPayment := thirdFullPhysical_outerNoYoungGrowth_forcesTwoRadiusSourcePayment244
    hH3 hClass hDInt b hb x hx s hxs hsT rho sigma epsilon
    hRho hAspect hMargin margin hMarginPos hExcess hPeak hDrop hNoGrowth
  have hA : 0 ≤ thirdFullPhysicalOuterSourceMassBudget244 hH3 b x := by
    have hMass := thirdFullPhysical_outerHighpassMassDrift_le_sourceBudget244
      hH3 hClass hDInt b hb x hx x le_rfl hx.2 rho
    exact (abs_nonneg _).trans hMass
  exact thirdFullKinetic_boundedInnerRadius_quarticSourcePayment244
    rho sigma R (velocityH3Energy0At u b)
    (thirdFullPhysicalOuterSourceMassBudget244 hH3 b x) epsilon
    hRho.le hBound (velocityH3Energy0At_nonneg u b) hA hPayment

theorem thirdFullPhysical_selectedOuter_lowHalfTail_twoRadiusYoungResidual244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (rho sigma margin epsilon : ℝ)
    (hRho : 0 < rho) (hAspect : 2 * rho ≤ sigma)
    (hMargin : 0 < margin) (hEps : 0 < epsilon)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho)
    (hPeak : 2 * epsilon ≤
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma)
    (hSmall :
      (∫ r in x..T, velocityH3DissipationAt u r) <
        119 * margin * sigma ^ 6 * (T - x) / 320) :
    let A := thirdFullPhysicalOuterSourceMassBudget244 hH3 b x
    let K := thirdFullPhysicalOuterTwoRadiusSlopeCap244 hH3 x rho sigma
    margin < (rho ^ 2 + sigma ^ 2) * A ∨
      (∃ s : ℝ, s ∈ Set.Ioc x ((x + T) / 2) ∧
        epsilon - A * K <
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho *
            (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma -
              thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma)) := by
  have hChoice :=
    thirdFullPhysical_selectedOuter_lowHalfTail_forcesViscousSourceOrYoung244
      hH3 hClass hDInt b hb x hx rho sigma margin epsilon
      hRho hAspect hMargin hEps hExcess hPeak hSmall
  dsimp only at hChoice ⊢
  rcases hChoice with hSource | ⟨s, hs, hDrop⟩
  · exact Or.inl hSource
  · right
    have hsT : s < T := by linarith only [hs.2, hx.2]
    exact ⟨s, hs,
      thirdFullPhysical_outerDeficitDrop_twoRadiusSlopeResidual244
        hH3 hClass hDInt b hb x hx s hs.1.le hsT
        rho sigma epsilon hRho hAspect hEps margin hMargin
        hExcess hPeak hDrop⟩

theorem thirdFullPhysical_selectedOuter_twoRadiusSlopeSmall_forcesYoungGrowth244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (rho sigma margin epsilon : ℝ)
    (hRho : 0 < rho) (hAspect : 2 * rho ≤ sigma)
    (hMargin : 0 < margin) (hEps : 0 < epsilon)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho)
    (hPeak : 2 * epsilon ≤
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma)
    (hSmall :
      (∫ r in x..T, velocityH3DissipationAt u r) <
        119 * margin * sigma ^ 6 * (T - x) / 320)
    (hSourceSmall :
      (rho ^ 2 + sigma ^ 2) *
        thirdFullPhysicalOuterSourceMassBudget244 hH3 b x ≤ margin)
    (hKineticSlopeSmall :
      thirdFullPhysicalOuterSourceMassBudget244 hH3 b x *
        thirdFullPhysicalOuterTwoRadiusSlopeCap244 hH3 x rho sigma ≤ epsilon) :
    ∃ s : ℝ, s ∈ Set.Ioc x ((x + T) / 2) ∧
      thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma <
        thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma := by
  obtain hSource | ⟨s, hs, hResidual⟩ :=
    thirdFullPhysical_selectedOuter_lowHalfTail_twoRadiusYoungResidual244
      hH3 hClass hDInt b hb x hx rho sigma margin epsilon
      hRho hAspect hMargin hEps hExcess hPeak hSmall
  · exact False.elim ((not_lt_of_ge hSourceSmall) hSource)
  · refine ⟨s, hs, ?_⟩
    exact thirdFullKinetic_earlyYoung_fullBudget_forcesIncrease244
      epsilon (thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho)
      (thirdFullPhysicalOuterSourceMassBudget244 hH3 b x)
      (thirdFullPhysicalOuterTwoRadiusSlopeCap244 hH3 x rho sigma)
      (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma)
      (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma)
      (sq_nonneg _) hKineticSlopeSmall hResidual

theorem thirdFullPhysical_cofinalOuter_twoRadiusYoungResidual244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x rho sigma margin epsilon : ℕ → ℝ)
    (hx : ∀ k : ℕ, x k ∈ Set.Ioo b T)
    (hCofinal : Tendsto x atTop (𝓝 T))
    (hRho : ∀ k : ℕ, 0 < rho k)
    (hAspect : ∀ k : ℕ, 2 * rho k ≤ sigma k)
    (hMargin : ∀ k : ℕ, 0 < margin k)
    (hEps : ∀ k : ℕ, 0 < epsilon k)
    (hExcess : ∀ k : ℕ,
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          (rho k) (velocityH3Energy0At u b)) + margin k ≤
      ((rho k ^ 2 + sigma k ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k) (rho k))
    (hPeak : ∀ k : ℕ, 2 * epsilon k ≤
      thirdFullPhysicalActualAnnularKineticDeficit244
        hH3 b (x k) (rho k) (sigma k))
    (c : ℝ) (hc : 0 < c)
    (hTerminalScale : ∀ᶠ k : ℕ in atTop,
      c ≤ margin k * sigma k ^ 6 * (T - x k)) :
    (∀ᶠ k : ℕ in atTop,
      let A := thirdFullPhysicalOuterSourceMassBudget244 hH3 b (x k)
      let K := thirdFullPhysicalOuterTwoRadiusSlopeCap244
        hH3 (x k) (rho k) (sigma k)
      margin k < (rho k ^ 2 + sigma k ^ 2) * A ∨
      (∃ s : ℝ, s ∈ Set.Ioc (x k) ((x k + T) / 2) ∧
        epsilon k - A * K <
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 s (rho k) *
            (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s
               (rho k) (sigma k) -
             thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 (x k)
               (rho k) (sigma k)))) ∧
    Tendsto (fun k : ℕ =>
      thirdFullPhysicalOuterTerminalSourceBudget244 u b (x k) T)
      atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨hChoice, _⟩ :=
    thirdFullPhysical_cofinalSelectedOuterMargins_forceSourceOrYoung244
      hH3 hClass hDInt b hb x rho sigma margin epsilon
      hx hCofinal hRho hAspect hMargin hEps hExcess hPeak
      c hc hTerminalScale
  refine ⟨?_, thirdFullPhysical_outerTerminalSourceBudget_cofinal_zero244
    hH3 hClass hDInt b hb x hx hCofinal⟩
  filter_upwards [hChoice] with k hk
  dsimp only at hk ⊢
  rcases hk with hSource | ⟨s, hs, hDrop⟩
  · exact Or.inl hSource
  · right
    have hsT : s < T := by linarith only [hs.2, (hx k).2]
    exact ⟨s, hs,
      thirdFullPhysical_outerDeficitDrop_twoRadiusSlopeResidual244
        hH3 hClass hDInt b hb (x k) (hx k) s hs.1.le hsT
        (rho k) (sigma k) (epsilon k)
        (hRho k) (hAspect k) (hEps k) (margin k) (hMargin k)
        (hExcess k) (hPeak k) hDrop⟩

end
end PrimeTensor.FirstMonomialTriad
