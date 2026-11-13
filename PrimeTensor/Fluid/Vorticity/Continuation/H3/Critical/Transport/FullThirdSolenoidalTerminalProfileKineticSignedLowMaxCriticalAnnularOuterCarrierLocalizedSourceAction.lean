import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierTwoRadiusSlope
import Mathlib.Tactic

/-!
# Localize the projected physical source payment at the actual highpass radius

The prior two-radius Young residual uses the full physical momentum-source
L¹ action, with a factor rho^6 sigma^4 times the total physical kinetic
mass.  The genuine physical Hilbert FTC permits a strictly finer payment:
apply the *actual sharp physical highpass* to the Bochner source increment.

For P_rho = I - sharpLow_rho and F = actual projected momentum source,
  S_rho(x,s) = ‖P_rho (∫_x^s F(t) dt)‖
is equal to the actual highpass-state increment.  Its quadratic mass payment
is S_rho (2‖P_rho u(x)‖ + S_rho).  The signed Young slope may be capped by
2 rho^6 sigma^4 ‖P_rho u(x)‖², rather than by the total kinetic anchor.

In particular, absent signed Young growth, the selected positive deficit
loss must pay a highpass-localized source action with *cubic* dependence
on the initial highpass amplitude when S_rho <= ‖P_rho u(x)‖.

These are real physical PDE statements, not a projected-source temporal
regularity assumption.  The highpass projection is applied after the time
integral, so no interchange of a sharp multiplier and a Bochner integral
is claimed here.  The frequency-weighted localized action remains a genuine
open analytic issue; no H3 continuation is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Exact sharp-highpass action of the physical projected Navier--Stokes
source, after integration over a prescribed interior time interval. -/
noncomputable def thirdFullPhysicalOuterHighpassSourceAction244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho : ℝ) : ℝ :=
  let J : H3PhysicalRealFinVectorL2Hilbert :=
    ∫ r in x..s, h3PathActualProjectedMomentumSource244 hH3 r
  ‖J - thirdFullPhysicalSharpLowCutoffHilbert244 rho J‖

/-- No new Fourier/Bochner commutation lemma is needed: first use the
unconditional strong physical FTC, then linearity of the sharp lowpass. -/
theorem thirdFullPhysical_outerHighpassIncrement_eq_sourceAction244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    ‖(h3AuditInitialOldPhysicalHilbertTotal hH3 s -
        thirdFullPhysicalSharpLowCutoffHilbert244 rho
          (h3AuditInitialOldPhysicalHilbertTotal hH3 s)) -
      (h3AuditInitialOldPhysicalHilbertTotal hH3 x -
        thirdFullPhysicalSharpLowCutoffHilbert244 rho
          (h3AuditInitialOldPhysicalHilbertTotal hH3 x))‖ =
      thirdFullPhysicalOuterHighpassSourceAction244 hH3 x s rho := by
  let Vs : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 s
  let Vx : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 x
  have hFTC : Vs - Vx =
      ∫ r in x..s, h3PathActualProjectedMomentumSource244 hH3 r :=
    h3Path_physicalHilbertFTC_betweenPositiveTimes244 hH3 x s hx hs
  have hFilter :
      (Vs - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vs) -
        (Vx - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vx) =
      (Vs - Vx) - thirdFullPhysicalSharpLowCutoffHilbert244 rho (Vs - Vx) := by
    rw [thirdFullPhysical_sharpVectorLowCutoff_sub244 rho Vs Vx]
    abel
  change ‖(Vs - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vs) -
    (Vx - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vx)‖ =
    ‖(∫ r in x..s, h3PathActualProjectedMomentumSource244 hH3 r) -
      thirdFullPhysicalSharpLowCutoffHilbert244 rho
        (∫ r in x..s, h3PathActualProjectedMomentumSource244 hH3 r)‖
  rw [hFilter, hFTC]

/-- The localized, time-integrated source action is at most the full
physical L¹ source action, for ordered interior times. -/
theorem thirdFullPhysical_outerHighpassSourceAction_le_globalAction244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho : ℝ) (hxs : x ≤ s) :
    thirdFullPhysicalOuterHighpassSourceAction244 hH3 x s rho ≤
      ∫ r in x..s, ‖h3PathActualProjectedMomentumSource244 hH3 r‖ := by
  let J : H3PhysicalRealFinVectorL2Hilbert :=
    ∫ r in x..s, h3PathActualProjectedMomentumSource244 hH3 r
  have hHigh : ‖J - thirdFullPhysicalSharpLowCutoffHilbert244 rho J‖ ≤ ‖J‖ :=
    thirdFullPhysical_sharpVectorHighpass_norm_le244 rho J
  calc
    thirdFullPhysicalOuterHighpassSourceAction244 hH3 x s rho =
        ‖J - thirdFullPhysicalSharpLowCutoffHilbert244 rho J‖ := rfl
    _ ≤ ‖J‖ := hHigh
    _ ≤ ∫ r in x..s,
        ‖h3PathActualProjectedMomentumSource244 hH3 r‖ :=
      intervalIntegral.norm_integral_le_integral_norm hxs

/-- The genuinely localized mass-change price.  It retains the sharp
highpass amplitude of the *initial* physical velocity, and both factors
use only the original physical projected momentum source and L² state. -/
noncomputable def thirdFullPhysicalOuterLocalizedSourceMassBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho : ℝ) : ℝ :=
  let S := thirdFullPhysicalOuterHighpassSourceAction244 hH3 x s rho
  let Vx := h3AuditInitialOldPhysicalHilbertTotal hH3 x
  let Hx := Vx - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vx
  S * (2 * ‖Hx‖ + S)

/-- An elementary Hilbert-space variation estimate with initial-state
size, rather than the possibly larger later-state size. -/
theorem thirdFullKinetic_highpassSquareDrift_fitted244
    (V W : H3PhysicalRealFinVectorL2Hilbert) :
    |‖V‖ ^ 2 - ‖W‖ ^ 2| ≤
      ‖V - W‖ * (2 * ‖W‖ + ‖V - W‖) := by
  have hSum : 0 ≤ ‖V‖ + ‖W‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hTriangle : ‖V‖ ≤ ‖V - W‖ + ‖W‖ := by
    calc
      ‖V‖ = ‖(V - W) + W‖ := by rw [sub_add_cancel]
      _ ≤ ‖V - W‖ + ‖W‖ := norm_add_le _ _
  have hSumBound : ‖V‖ + ‖W‖ ≤ 2 * ‖W‖ + ‖V - W‖ := by
    linarith only [hTriangle]
  calc
    |‖V‖ ^ 2 - ‖W‖ ^ 2| =
        |‖V‖ - ‖W‖| * (‖V‖ + ‖W‖) := by
          rw [sq_sub_sq, abs_mul, abs_of_nonneg hSum]
          ac_rfl
    _ ≤ ‖V - W‖ * (‖V‖ + ‖W‖) :=
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le V W) hSum
    _ ≤ ‖V - W‖ * (2 * ‖W‖ + ‖V - W‖) :=
      mul_le_mul_of_nonneg_left hSumBound (norm_nonneg _)

/-- Exact physical highpass kinetic-mass drift, controlled by the
highpass of the time-integrated physical projected momentum source. -/
theorem thirdFullPhysical_outerHighpassMassDrift_le_localizedSource244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    |thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho -
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho| ≤
      thirdFullPhysicalOuterLocalizedSourceMassBudget244 hH3 x s rho := by
  let Vs : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 s
  let Vx : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 x
  let Hs : H3PhysicalRealFinVectorL2Hilbert :=
    Vs - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vs
  let Hx : H3PhysicalRealFinVectorL2Hilbert :=
    Vx - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vx
  have hEq : ‖Hs - Hx‖ =
      thirdFullPhysicalOuterHighpassSourceAction244 hH3 x s rho :=
    thirdFullPhysical_outerHighpassIncrement_eq_sourceAction244
      hH3 x s rho hx hs
  have hDrift := thirdFullKinetic_highpassSquareDrift_fitted244 Hs Hx
  rw [hEq] at hDrift
  change |‖Hs‖ ^ 2 - ‖Hx‖ ^ 2| ≤
    thirdFullPhysicalOuterHighpassSourceAction244 hH3 x s rho *
      (2 * ‖Hx‖ + thirdFullPhysicalOuterHighpassSourceAction244 hH3 x s rho)
  exact hDrift

/-- Retain the actual initial highpass kinetic mass, rather than bounding
it by the full physical L² kinetic energy. -/
theorem thirdFullKinetic_earlyYoung_kineticSlope_initialHighpassCap244
    (a B mx rho sigma : ℝ)
    (ha : 0 ≤ a) (haCap : a ≤ sigma ^ 2)
    (hB : 0 ≤ B) (hmx : 0 ≤ mx) :
    2 * (rho ^ 2) ^ 3 * a * (a * mx - B) ≤
      2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 * mx := by
  exact thirdFullKinetic_earlyYoung_kineticSlope_twoRadiusCap244
    a B mx rho sigma mx ha haCap hB hmx le_rfl hmx

/-- The sharpened physical signed Young residual: both source-action
factors are highpass localized; the coefficient retains the actual
initial highpass mass, with no global kinetic or nonlinear H3 envelope. -/
theorem thirdFullPhysical_outerDeficitDrop_localizedSourceYoungResidual244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b x s rho sigma epsilon margin : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hRho : 0 < rho) (hAspect : 2 * rho ≤ sigma)
    (hEps : 0 < epsilon) (hMargin : 0 < margin)
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
    let A := thirdFullPhysicalOuterLocalizedSourceMassBudget244 hH3 x s rho
    let K := 2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 *
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
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
  let A : ℝ := thirdFullPhysicalOuterLocalizedSourceMassBudget244 hH3 x s rho
  let K : ℝ := 2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 * Mx
  have hOrder : rho ≤ sigma := by linarith only [hRho, hAspect]
  have hMean := thirdFullKinetic_annularMeanSquare_bound244
    rho sigma sigma hRho.le hOrder le_rfl
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
      hH3 x rho sigma hRho.le hOrder
  have hC : 0 ≤ Yx + w * P :=
    add_nonneg hY (mul_nonneg hw hP)
  have hMxNonneg : 0 ≤ Mx := sq_nonneg _
  have hEx : B + margin ≤ aMean * Mx := hExcess
  have hMx : 0 < Mx := by
    by_contra hn
    have hz : Mx = 0 := le_antisymm (le_of_not_gt hn) hMxNonneg
    rw [hz, mul_zero] at hEx
    linarith only [hEx, hB, hMargin]
  have hExNonneg : 0 ≤ aMean * Mx - B := by
    linarith only [hEx, hMargin]
  have hDef : 0 ≤
      w * (aMean * Mx - B) ^ 2 - Mx * (Yx + w * P) := by
    change 2 * epsilon ≤
      w * (aMean * Mx - B) ^ 2 - Mx * (Yx + w * P) at hPeak
    linarith only [hPeak, hEps]
  have hMassOne : |Ms - Mx| ≤ A :=
    thirdFullPhysical_outerHighpassMassDrift_le_localizedSource244
      hH3 x s rho hx hs
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
  have hKCap : 2 * w * aMean * (aMean * Mx - B) ≤ K := by
    change 2 * (rho ^ 2) ^ 3 * aMean * (aMean * Mx - B) ≤
      2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 * Mx
    exact thirdFullKinetic_earlyYoung_kineticSlope_initialHighpassCap244
      aMean B Mx rho sigma ha hMean.2 hB hMxNonneg
  have hA : 0 ≤ A := by
    let S := thirdFullPhysicalOuterHighpassSourceAction244 hH3 x s rho
    let Hx : H3PhysicalRealFinVectorL2Hilbert :=
      h3AuditInitialOldPhysicalHilbertTotal hH3 x -
        thirdFullPhysicalSharpLowCutoffHilbert244 rho
          (h3AuditInitialOldPhysicalHilbertTotal hH3 x)
    have hS : 0 ≤ S := by
      dsimp only [S, thirdFullPhysicalOuterHighpassSourceAction244]
      exact norm_nonneg _
    change 0 ≤ S * (2 * ‖Hx‖ + S)
    exact mul_nonneg hS
      (add_nonneg (mul_nonneg (by norm_num) (norm_nonneg Hx)) hS)
  have hPay : A * (2 * w * aMean * (aMean * Mx - B)) ≤ A * K :=
    mul_le_mul_of_nonneg_left hKCap hA
  change epsilon - A * K < Ms * (Ys - Yx)
  linarith only [hScalar, hPay]

/-- If the actual nonlinear Young width does not grow, the full deficit
loss is charged to the highpass-filtered Bochner momentum increment. -/
theorem thirdFullPhysical_outerNoYoungGrowth_forcesLocalizedSourcePayment244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b x s rho sigma epsilon margin : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hRho : 0 < rho) (hAspect : 2 * rho ≤ sigma)
    (hEps : 0 < epsilon) (hMargin : 0 < margin)
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
    (hNoGrowth : thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma ≤
      thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma) :
    epsilon < thirdFullPhysicalOuterLocalizedSourceMassBudget244 hH3 x s rho *
      (2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho) := by
  let A := thirdFullPhysicalOuterLocalizedSourceMassBudget244 hH3 x s rho
  let K := 2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 *
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
  let Ms := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
  let Yx := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
  let Ys := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma
  have hResidual : epsilon - A * K < Ms * (Ys - Yx) :=
    thirdFullPhysical_outerDeficitDrop_localizedSourceYoungResidual244
      hH3 b x s rho sigma epsilon margin hx hs
      hRho hAspect hEps hMargin hExcess hPeak hDrop
  have hMs : 0 ≤ Ms := sq_nonneg _
  have hYoung : Ms * (Ys - Yx) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hMs (sub_nonpos.mpr hNoGrowth)
  change epsilon < A * K
  linarith only [hResidual, hYoung]

/-- If the highpass-filtered source increment is smaller than the
initial highpass amplitude, the price is LINEAR in that increment and
CUBIC in the highpass amplitude (rather than quadratic in total L² mass). -/
theorem thirdFullPhysical_outerNoYoungGrowth_forcesCubicHighpassSource244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b x s rho sigma epsilon margin : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hRho : 0 < rho) (hAspect : 2 * rho ≤ sigma)
    (hEps : 0 < epsilon) (hMargin : 0 < margin)
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
    (hNoGrowth : thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma ≤
      thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma)
    (hSmallSource :
      thirdFullPhysicalOuterHighpassSourceAction244 hH3 x s rho ≤
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3 x -
          thirdFullPhysicalSharpLowCutoffHilbert244 rho
            (h3AuditInitialOldPhysicalHilbertTotal hH3 x)‖) :
    epsilon <
      (6 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2) *
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3 x -
          thirdFullPhysicalSharpLowCutoffHilbert244 rho
            (h3AuditInitialOldPhysicalHilbertTotal hH3 x)‖ ^ 3 *
        thirdFullPhysicalOuterHighpassSourceAction244 hH3 x s rho := by
  let Vx : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 x
  let Hx : H3PhysicalRealFinVectorL2Hilbert :=
    Vx - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vx
  let S : ℝ := thirdFullPhysicalOuterHighpassSourceAction244 hH3 x s rho
  have hPrice := thirdFullPhysical_outerNoYoungGrowth_forcesLocalizedSourcePayment244
    hH3 b x s rho sigma epsilon margin hx hs
    hRho hAspect hEps hMargin hExcess hPeak hDrop hNoGrowth
  have hS : 0 ≤ S := by
    dsimp [S, thirdFullPhysicalOuterHighpassSourceAction244]
    positivity
  have hH : 0 ≤ ‖Hx‖ := norm_nonneg _
  have hSH : S ≤ ‖Hx‖ := hSmallSource
  have hSsq : S * S ≤ S * ‖Hx‖ :=
    mul_le_mul_of_nonneg_left hSH hS
  have hA : S * (2 * ‖Hx‖ + S) ≤ 3 * S * ‖Hx‖ := by
    nlinarith only [hSsq]
  have hK : 0 ≤ 2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 * ‖Hx‖ ^ 2 := by
    positivity
  have hPayment :
      S * (2 * ‖Hx‖ + S) *
        (2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 * ‖Hx‖ ^ 2) ≤
      (6 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2) * ‖Hx‖ ^ 3 * S := by
    calc
      _ ≤ (3 * S * ‖Hx‖) *
          (2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 * ‖Hx‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hA hK
      _ = (6 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2) * ‖Hx‖ ^ 3 * S := by
        ring
  have hMxEq : thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho =
      ‖Hx‖ ^ 2 := rfl
  dsimp only [thirdFullPhysicalOuterLocalizedSourceMassBudget244] at hPrice
  rw [hMxEq] at hPrice
  change epsilon < S * (2 * ‖Hx‖ + S) *
    (2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 * ‖Hx‖ ^ 2) at hPrice
  change epsilon < (6 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2) * ‖Hx‖ ^ 3 * S
  exact lt_of_lt_of_le hPrice hPayment

/-- The selected half-terminal viscous compression now has an additional
quantitative conclusion: whenever the old global source arm cannot pay
the carrier margin, the remaining signed Young residual is charged to
the highpass of the *actual time-integrated* projected momentum source. -/
theorem thirdFullPhysical_selectedOuter_lowHalfTail_localizedYoungResidual244
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
        thirdFullPhysicalOuterSourceMassBudget244 hH3 b x ≤ margin) :
    ∃ s : ℝ, s ∈ Set.Ioc x ((x + T) / 2) ∧
      let A := thirdFullPhysicalOuterLocalizedSourceMassBudget244 hH3 x s rho
      let K := 2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
      epsilon - A * K <
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho *
          (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma -
            thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma) := by
  obtain hSource | ⟨s, hs, hDrop⟩ :=
    thirdFullPhysical_selectedOuter_lowHalfTail_forcesViscousSourceOrYoung244
      hH3 hClass hDInt b hb x hx rho sigma margin epsilon
      hRho hAspect hMargin hEps hExcess hPeak hSmall
  · exact False.elim ((not_lt_of_ge hSourceSmall) hSource)
  · refine ⟨s, hs, ?_⟩
    have hxAbs : x ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 hx.1), hx.2⟩
    have hsAbs : s ∈ Set.Ioo (0 : ℝ) T := by
      constructor
      · exact lt_trans hxAbs.1 hs.1
      · linarith only [hs.2, hx.2]
    exact thirdFullPhysical_outerDeficitDrop_localizedSourceYoungResidual244
      hH3 b x s rho sigma epsilon margin hxAbs hsAbs
      hRho hAspect hEps hMargin hExcess hPeak hDrop


/-- The highpass of the integrated projected source is bounded by the
actual full terminal physical source action, for ANY selected radius. -/
theorem thirdFullPhysical_outerHighpassSourceAction_le_terminalSourceTail244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (s : ℝ) (hxs : x ≤ s) (hsT : s < T)
    (rho : ℝ) :
    thirdFullPhysicalOuterHighpassSourceAction244 hH3 x s rho ≤
      ∫ r in x..T, ‖h3PathActualProjectedMomentumSource244 hH3 r‖ := by
  let Vs : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 s
  let Vx : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 x
  have hxAbs : x ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 hx.1), hx.2⟩
  have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le hxAbs.1 hxs, hsT⟩
  have hFTC : Vs - Vx =
      ∫ r in x..s, h3PathActualProjectedMomentumSource244 hH3 r :=
    h3Path_physicalHilbertFTC_betweenPositiveTimes244 hH3 x s hxAbs hsAbs
  have hHigh :
      ‖(Vs - Vx) - thirdFullPhysicalSharpLowCutoffHilbert244 rho (Vs - Vx)‖ ≤
        ‖Vs - Vx‖ :=
    thirdFullPhysical_sharpVectorHighpass_norm_le244 rho (Vs - Vx)
  have hTail : ‖Vs - Vx‖ ≤
      ∫ r in x..T, ‖h3PathActualProjectedMomentumSource244 hH3 r‖ :=
    thirdFullPhysical_outerSourceTail_controlsVelocityIncrement244
      hH3 hClass hDInt b hb x hx s hxs hsT
  calc
    thirdFullPhysicalOuterHighpassSourceAction244 hH3 x s rho =
        ‖(Vs - Vx) - thirdFullPhysicalSharpLowCutoffHilbert244 rho (Vs - Vx)‖ := by
          change ‖(∫ r in x..s, h3PathActualProjectedMomentumSource244 hH3 r) -
            thirdFullPhysicalSharpLowCutoffHilbert244 rho
              (∫ r in x..s, h3PathActualProjectedMomentumSource244 hH3 r)‖ = _
          rw [← hFTC]
    _ ≤ ‖Vs - Vx‖ := hHigh
    _ ≤ ∫ r in x..T,
        ‖h3PathActualProjectedMomentumSource244 hH3 r‖ := hTail

/-- Terminal physical source L¹ controls any moving sharp highpass action,
with no fixed-frequency or spatial tightness assumption. -/
theorem thirdFullPhysical_cofinalOuter_movingHighpassSourceAction_zero244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x s rho : ℕ → ℝ)
    (hx : ∀ k : ℕ, x k ∈ Set.Ioo b T)
    (hCofinal : Tendsto x atTop (𝓝 T))
    (hs : ∀ k : ℕ, x k ≤ s k ∧ s k < T) :
    Tendsto (fun k : ℕ =>
      thirdFullPhysicalOuterHighpassSourceAction244
        hH3 (x k) (s k) (rho k)) atTop (𝓝 (0 : ℝ)) := by
  have hTail : Tendsto (fun k : ℕ =>
      ∫ r in x k..T, ‖h3PathActualProjectedMomentumSource244 hH3 r‖)
      atTop (𝓝 (0 : ℝ)) :=
    thirdFullPhysical_cofinalOuterSourceTail_tendsto_zero244
      hH3 hClass hDInt b hb x hx hCofinal
  apply squeeze_zero'
    (Filter.Eventually.of_forall (fun k => by
      unfold thirdFullPhysicalOuterHighpassSourceAction244
      exact norm_nonneg _))
    (Filter.Eventually.of_forall (fun k =>
      thirdFullPhysical_outerHighpassSourceAction_le_terminalSourceTail244
        hH3 hClass hDInt b hb (x k) (hx k)
        (s k) (hs k).1 (hs k).2 (rho k)))
    hTail

/-- For cofinal selected margins, the full nonlinear Young residual is
now measured against a highpass-localized signed physical PDE payment.
The alternative still retains the original global source arm: removing
it requires an additional physical estimate rather than algebra alone. -/
theorem thirdFullPhysical_cofinalOuter_localizedSourceYoungResidual244
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
    ∀ᶠ k : ℕ in atTop,
      let H : ℝ := (3 + h3AuditInitialLerayEnergyCoefficient) *
        ((1 + 6 * velocityH3Energy0At u b) * (T - x k) +
          3 * (∫ r in x k..T, velocityH3DissipationAt u r))
      (margin k < (rho k ^ 2 + sigma k ^ 2) *
        (H * (2 * ‖h3AuditInitialOldPhysicalHilbertTotal hH3 (x k)‖ + H))) ∨
      (∃ s : ℝ, s ∈ Set.Ioc (x k) ((x k + T) / 2) ∧
        let A := thirdFullPhysicalOuterLocalizedSourceMassBudget244
          hH3 (x k) s (rho k)
        let K := 2 * (rho k ^ 2) ^ 3 * (sigma k ^ 2) ^ 2 *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k) (rho k)
        epsilon k - A * K <
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 s (rho k) *
            (thirdFullPhysicalActualAnnularYoungWidthCost244
              hH3 s (rho k) (sigma k) -
             thirdFullPhysicalActualAnnularYoungWidthCost244
              hH3 (x k) (rho k) (sigma k))) := by
  obtain ⟨hChoice, _⟩ :=
    thirdFullPhysical_cofinalSelectedOuterMargins_forceSourceOrYoung244
      hH3 hClass hDInt b hb x rho sigma margin epsilon
      hx hCofinal hRho hAspect hMargin hEps hExcess hPeak
      c hc hTerminalScale
  filter_upwards [hChoice] with k hk
  dsimp only at hk ⊢
  rcases hk with hSource | ⟨s, hs, hDrop⟩
  · exact Or.inl hSource
  · right
    have hxAbs : x k ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 (hx k).1),
       (hx k).2⟩
    have hsAbs : s ∈ Set.Ioo (0 : ℝ) T := by
      constructor
      · exact lt_trans hxAbs.1 hs.1
      · linarith only [hs.2, (hx k).2]
    exact ⟨s, hs,
      thirdFullPhysical_outerDeficitDrop_localizedSourceYoungResidual244
        hH3 b (x k) s (rho k) (sigma k) (epsilon k) (margin k)
        hxAbs hsAbs (hRho k) (hAspect k) (hEps k) (hMargin k)
        (hExcess k) (hPeak k) hDrop⟩

end
end PrimeTensor.FirstMonomialTriad
