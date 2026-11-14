import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierLocalizedSourceAction
import Mathlib.Tactic

/-!
# One-sided highpass mass loss and linear localized source drain

The previous localized source payment bounded the absolute mass change by
S_rho (2 * ||P_rho u(x)|| + S_rho). This loses the sign of the source.
Only a FALL in actual physical highpass mass can positively pay the selected
annular deficit drop. The one-sided squared-norm estimate removes S_rho^2:

   ||P_rho u(x)||^2 - ||P_rho u(s)||^2
       <= 2 ||P_rho u(x)|| S_rho(x,s).

The early-anchored signed Young slope then yields the exact linear action
barrier, with coefficient 4 rho^6 sigma^4 ||P_rho u(x)||^3.
No source-smallness or auxiliary time-Lipschitz assumption is made.

This does not assert endpoint regularity or H3 continuation: the remaining
critical obstruction is the moving-frequency weighted source action.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- A highpass energy LOSS has no positive quadratic error in the increment.
This is the one-sided refinement of the absolute squared-norm variation. -/
theorem thirdFullKinetic_highpassSquareLoss_oneSided244
    (V W : H3PhysicalRealFinVectorL2Hilbert) :
    ‖W‖ ^ 2 - ‖V‖ ^ 2 ≤ 2 * ‖W‖ * ‖V - W‖ := by
  have hAbs : |‖V‖ - ‖W‖| ≤ ‖V - W‖ :=
    abs_norm_sub_norm_le V W
  have hDiff : ‖W‖ - ‖V‖ ≤ ‖V - W‖ := by
    have hNeg := neg_abs_le (‖V‖ - ‖W‖)
    linarith only [hAbs, hNeg]
  have hV : 0 ≤ ‖V‖ := norm_nonneg _
  have hW : 0 ≤ ‖W‖ := norm_nonneg _
  have hS : 0 ≤ ‖V - W‖ := norm_nonneg _
  rcases le_total ‖W‖ ‖V‖ with hDown | hUp
  · have hSquare : ‖W‖ ^ 2 ≤ ‖V‖ ^ 2 :=
      pow_le_pow_left₀ hW hDown 2
    have hRight : 0 ≤ 2 * ‖W‖ * ‖V - W‖ := by positivity
    linarith only [hSquare, hRight]
  · have hSum : ‖W‖ + ‖V‖ ≤ 2 * ‖W‖ := by
      linarith only [hUp]
    have hProduct :
        (‖W‖ - ‖V‖) * (‖W‖ + ‖V‖) ≤
          ‖V - W‖ * (‖W‖ + ‖V‖) :=
      mul_le_mul_of_nonneg_right hDiff (add_nonneg hW hV)
    have hProduct2 :
        ‖V - W‖ * (‖W‖ + ‖V‖) ≤
          ‖V - W‖ * (2 * ‖W‖) :=
      mul_le_mul_of_nonneg_left hSum hS
    nlinarith only [hProduct, hProduct2]

/-- The one-sided actual highpass mass drain, paid only by the highpass of
physical time-integrated projected Navier--Stokes momentum source. -/
noncomputable def thirdFullPhysicalOuterLinearSourceMassBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho : ℝ) : ℝ :=
  let Vx := h3AuditInitialOldPhysicalHilbertTotal hH3 x
  let Hx := Vx - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vx
  2 * ‖Hx‖ * thirdFullPhysicalOuterHighpassSourceAction244 hH3 x s rho

theorem thirdFullPhysical_outerHighpassMassLoss_le_linearSource244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho ≤
      thirdFullPhysicalOuterLinearSourceMassBudget244 hH3 x s rho := by
  let Vs : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 s
  let Vx : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 x
  let Hs : H3PhysicalRealFinVectorL2Hilbert :=
    Vs - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vs
  let Hx : H3PhysicalRealFinVectorL2Hilbert :=
    Vx - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vx
  have hIncrement : ‖Hs - Hx‖ =
      thirdFullPhysicalOuterHighpassSourceAction244 hH3 x s rho :=
    thirdFullPhysical_outerHighpassIncrement_eq_sourceAction244
      hH3 x s rho hx hs
  have hLoss := thirdFullKinetic_highpassSquareLoss_oneSided244 Hs Hx
  rw [hIncrement] at hLoss
  change ‖Hx‖ ^ 2 - ‖Hs‖ ^ 2 ≤
    2 * ‖Hx‖ * thirdFullPhysicalOuterHighpassSourceAction244 hH3 x s rho
  exact hLoss

/-- The signed deficit slope needs only an UPPER BOUND on actual highpass
mass loss, not an absolute-variation budget. This is the key sign gain. -/
theorem thirdFullKinetic_earlyYoung_sourceSlope_oneSidedLoss244
    (a B w C mx ms L : ℝ)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hw : 0 ≤ w) (hC : 0 ≤ C)
    (hmx : 0 < mx) (hEx : 0 ≤ a * mx - B)
    (hDef : 0 ≤ w * (a * mx - B) ^ 2 - mx * C)
    (hLoss : mx - ms ≤ L) (hL : 0 ≤ L) :
    (mx - ms) * (w * a * (a * (mx + ms) - 2 * B) - C) ≤
      L * (2 * w * a * (a * mx - B)) := by
  have hWA : 0 ≤ w * a := mul_nonneg hw ha
  have hK : 0 ≤ 2 * w * a * (a * mx - B) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hw) ha) hEx
  rcases le_total ms mx with hDown | hUp
  · have hAS : a * ms ≤ a * mx := mul_le_mul_of_nonneg_left hDown ha
    have hInside : a * (mx + ms) - 2 * B ≤
        2 * (a * mx - B) := by
      nlinarith only [hAS]
    have hQ : w * a * (a * (mx + ms) - 2 * B) - C ≤
        2 * w * a * (a * mx - B) := by
      calc
        w * a * (a * (mx + ms) - 2 * B) - C ≤
            w * a * (a * (mx + ms) - 2 * B) := sub_le_self _ hC
        _ ≤ w * a * (2 * (a * mx - B)) :=
            mul_le_mul_of_nonneg_left hInside hWA
        _ = 2 * w * a * (a * mx - B) := by ring
    have hDelta : 0 ≤ mx - ms := sub_nonneg.mpr hDown
    calc
      (mx - ms) * (w * a * (a * (mx + ms) - 2 * B) - C) ≤
          (mx - ms) * (2 * w * a * (a * mx - B)) :=
        mul_le_mul_of_nonneg_left hQ hDelta
      _ ≤ L * (2 * w * a * (a * mx - B)) :=
        mul_le_mul_of_nonneg_right hLoss hK
  · have hQ : 0 ≤ w * a * (a * (mx + ms) - 2 * B) - C :=
      thirdFullKinetic_positiveDeficit_earlySlope_nonneg244
        a B w C mx ms ha hB hw hmx hUp hEx hDef
    have hNonpositive :
        (mx - ms) * (w * a * (a * (mx + ms) - 2 * B) - C) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hUp) hQ
    exact hNonpositive.trans (mul_nonneg hL hK)

/-- Exact signed Young residual with the linear, one-sided physical
highpass drain, retaining the FULL deficit loss without splitting epsilon. -/
theorem thirdFullKinetic_earlyYoung_linearResidual244
    (a B w C mx ms yx ys epsilon L : ℝ)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hw : 0 ≤ w) (hC : 0 ≤ C)
    (hmx : 0 < mx) (hEx : 0 ≤ a * mx - B)
    (hDef : 0 ≤ w * (a * mx - B) ^ 2 - mx * C)
    (hLoss : mx - ms ≤ L) (hL : 0 ≤ L)
    (hDrop : epsilon <
      (mx - ms) * (w * a * (a * (mx + ms) - 2 * B) - C) +
        ms * (ys - yx)) :
    epsilon - L * (2 * w * a * (a * mx - B)) < ms * (ys - yx) := by
  have hSlope := thirdFullKinetic_earlyYoung_sourceSlope_oneSidedLoss244
    a B w C mx ms L ha hB hw hC hmx hEx hDef hLoss hL
  linarith only [hSlope, hDrop]

theorem thirdFullPhysical_outerDeficitDrop_linearSourceYoungResidual244
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
    let A := thirdFullPhysicalOuterLinearSourceMassBudget244 hH3 x s rho
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
  let A : ℝ := thirdFullPhysicalOuterLinearSourceMassBudget244 hH3 x s rho
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
  have hMass : Mx - Ms ≤ A :=
    thirdFullPhysical_outerHighpassMassLoss_le_linearSource244
      hH3 x s rho hx hs
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
  have hANonneg : 0 ≤ A := by
    dsimp only [A, thirdFullPhysicalOuterLinearSourceMassBudget244]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (norm_nonneg _))
      (by
        unfold thirdFullPhysicalOuterHighpassSourceAction244
        exact norm_nonneg _)
  have hScalar :
      epsilon - A * (2 * w * aMean * (aMean * Mx - B)) <
        Ms * (Ys - Yx) :=
    thirdFullKinetic_earlyYoung_linearResidual244
      aMean B w (Yx + w * P) Mx Ms Yx Ys epsilon A
      ha hB hw hC hMx hExNonneg hDef hMass hANonneg hDrop'
  have hKCap : 2 * w * aMean * (aMean * Mx - B) ≤ K := by
    change 2 * (rho ^ 2) ^ 3 * aMean * (aMean * Mx - B) ≤
      2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 * Mx
    exact thirdFullKinetic_earlyYoung_kineticSlope_initialHighpassCap244
      aMean B Mx rho sigma ha hMean.2 hB hMxNonneg
  have hA : 0 ≤ A := hANonneg
  have hPay : A * (2 * w * aMean * (aMean * Mx - B)) ≤ A * K :=
    mul_le_mul_of_nonneg_left hKCap hA
  change epsilon - A * K < Ms * (Ys - Yx)
  linarith only [hScalar, hPay]

/-- The one-sided payment is EXACTLY linear in the localized projected
source action and cubic in the initial highpass amplitude. No relative
smallness of the source increment is needed. -/
theorem thirdFullPhysical_outerDeficitDrop_cubicLinearYoungResidual244
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
    let Vx := h3AuditInitialOldPhysicalHilbertTotal hH3 x
    let Hx := Vx - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vx
    let S := thirdFullPhysicalOuterHighpassSourceAction244 hH3 x s rho
    let Ms := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
    let Yx := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
    let Ys := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma
    epsilon -
        (4 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2) * ‖Hx‖ ^ 3 * S <
      Ms * (Ys - Yx) := by
  have hResidual := thirdFullPhysical_outerDeficitDrop_linearSourceYoungResidual244
    hH3 b x s rho sigma epsilon margin hx hs
    hRho hAspect hEps hMargin hExcess hPeak hDrop
  let Vx : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 x
  let Hx : H3PhysicalRealFinVectorL2Hilbert :=
    Vx - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vx
  let S : ℝ := thirdFullPhysicalOuterHighpassSourceAction244 hH3 x s rho
  let Ms : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
  let Yx : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
  let Ys : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma
  change epsilon -
      (2 * ‖Hx‖ * S) *
        (2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 * ‖Hx‖ ^ 2) <
      Ms * (Ys - Yx) at hResidual
  change epsilon -
      (4 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2) * ‖Hx‖ ^ 3 * S <
    Ms * (Ys - Yx)
  have hIdentity :
      (2 * ‖Hx‖ * S) *
          (2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 * ‖Hx‖ ^ 2) =
      (4 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2) * ‖Hx‖ ^ 3 * S := by
    ring
  rw [hIdentity] at hResidual
  exact hResidual

/-- With no positive signed Young-width growth, a selected deficit drop
must be paid by the improved factor-4 highpass source barrier, without
any hypothesis comparing source increment and initial highpass norm. -/
theorem thirdFullPhysical_outerNoYoungGrowth_forcesLinearCubicSource244
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
    epsilon <
      (4 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2) *
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3 x -
          thirdFullPhysicalSharpLowCutoffHilbert244 rho
            (h3AuditInitialOldPhysicalHilbertTotal hH3 x)‖ ^ 3 *
        thirdFullPhysicalOuterHighpassSourceAction244 hH3 x s rho := by
  have hResidual := thirdFullPhysical_outerDeficitDrop_cubicLinearYoungResidual244
    hH3 b x s rho sigma epsilon margin hx hs
    hRho hAspect hEps hMargin hExcess hPeak hDrop
  have hMs : 0 ≤ thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho :=
    sq_nonneg _
  have hYoung :
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho *
        (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma -
          thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hMs (sub_nonpos.mpr hNoGrowth)
  change epsilon -
      (4 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2) *
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3 x -
          thirdFullPhysicalSharpLowCutoffHilbert244 rho
            (h3AuditInitialOldPhysicalHilbertTotal hH3 x)‖ ^ 3 *
        thirdFullPhysicalOuterHighpassSourceAction244 hH3 x s rho <
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho *
        (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma -
          thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma)
    at hResidual
  linarith only [hResidual, hYoung]

/-- A no-growth deficit excursion necessarily drains the ACTUAL highpass
kinetic mass strictly; it cannot be caused by a highpass mass increase. -/
theorem thirdFullPhysical_outerNoYoungGrowth_forcesStrictHighpassDrain244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b x s rho sigma margin epsilon : ℝ)
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
    (hDrop : epsilon <
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
        thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma)
    (hNoGrowth : thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma ≤
      thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma) :
    thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho <
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho := by
  by_contra hNot
  have hIncrease : thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho ≤
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho :=
    le_of_not_gt hNot
  have hCharge := thirdFullPhysical_outerNondecreasingHighpass_fullYoungCharge244
    hH3 b x s rho sigma margin epsilon hRho hAspect
    hMargin hEps hExcess hPeak hIncrease hDrop
  have hMs : 0 ≤ thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho :=
    sq_nonneg _
  have hNoPay :
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho *
        (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma -
          thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hMs (sub_nonpos.mpr hNoGrowth)
  linarith only [hCharge, hNoPay, hEps]

/-- The cofinal selected outer PDE obstruction now uses the one-sided
factor-4 cubic highpass action with no smallness premise. Every highpass
frequency is allowed to move with the snapshot. -/
theorem thirdFullPhysical_cofinalOuter_cubicLinearYoungResidual244
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
        let Vx := h3AuditInitialOldPhysicalHilbertTotal hH3 (x k)
        let Hx := Vx - thirdFullPhysicalSharpLowCutoffHilbert244 (rho k) Vx
        let S := thirdFullPhysicalOuterHighpassSourceAction244
          hH3 (x k) s (rho k)
        epsilon k -
            (4 * (rho k ^ 2) ^ 3 * (sigma k ^ 2) ^ 2) * ‖Hx‖ ^ 3 * S <
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
      thirdFullPhysical_outerDeficitDrop_cubicLinearYoungResidual244
        hH3 b (x k) s (rho k) (sigma k) (epsilon k) (margin k)
        hxAbs hsAbs (hRho k) (hAspect k) (hEps k) (hMargin k)
        (hExcess k) (hPeak k) hDrop⟩

end
end PrimeTensor.FirstMonomialTriad
