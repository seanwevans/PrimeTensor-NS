import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierLinearSourceDrain
import Mathlib.Tactic

/-!
# Exact signed work of a selected outer highpass kinetic drain

The earlier one-sided source gate used the Cauchy bound
  M(x)-M(s) <= 2 ||P_high u(x)|| ||P_high integral_x^s F||.
We retain the *exact* polarization identity instead:
  M(x)-M(s) = 2 W_high(x,s) - S_high(x,s)^2,
where W_high = -<P_high u(x), P_high integral_x^s F> and S_high is the
previously defined highpass source action. Both use the actual physical
projected momentum source F and its unconditional strong Bochner FTC.

A selected positive deficit drop with no signed Young-width increase now
forces the exact directional source work, including the *favorable* negative
quadratic increment. The result distinguishes true highpass energy drain
from large highpass source action orthogonal to the carrier.

This does not separate Laplacian and Leray work, establish any positive
frequency-weighted tail limit, or prove H3 continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Exact polarization of a real Hilbert kinetic-mass LOSS. The increment
square appears with a negative sign, never as an error to be paid. -/
theorem thirdFullKinetic_highpassSquareLoss_exactWork244
    (H J : H3PhysicalRealFinVectorL2Hilbert) :
    ‖H‖ ^ 2 - ‖H + J‖ ^ 2 =
      -2 * inner ℝ H J - ‖J‖ ^ 2 := by
  rw [norm_add_sq_real]
  ring

/-- Highpass of the actual physical Bochner momentum increment is the
VECTOR difference of the two genuine physical highpass states. -/
theorem thirdFullPhysical_outerHighpassSourceVectorFTC244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    (h3AuditInitialOldPhysicalHilbertTotal hH3 s -
        thirdFullPhysicalSharpLowCutoffHilbert244 rho
          (h3AuditInitialOldPhysicalHilbertTotal hH3 s)) -
      (h3AuditInitialOldPhysicalHilbertTotal hH3 x -
        thirdFullPhysicalSharpLowCutoffHilbert244 rho
          (h3AuditInitialOldPhysicalHilbertTotal hH3 x)) =
      (∫ r in x..s, h3PathActualProjectedMomentumSource244 hH3 r) -
        thirdFullPhysicalSharpLowCutoffHilbert244 rho
          (∫ r in x..s, h3PathActualProjectedMomentumSource244 hH3 r) := by
  let Vs : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 s
  let Vx : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 x
  have hFTC : Vs - Vx =
      ∫ r in x..s, h3PathActualProjectedMomentumSource244 hH3 r :=
    h3Path_physicalHilbertFTC_betweenPositiveTimes244 hH3 x s hx hs
  change (Vs - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vs) -
      (Vx - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vx) =
      (∫ r in x..s, h3PathActualProjectedMomentumSource244 hH3 r) -
        thirdFullPhysicalSharpLowCutoffHilbert244 rho
          (∫ r in x..s, h3PathActualProjectedMomentumSource244 hH3 r)
  calc
    (Vs - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vs) -
        (Vx - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vx) =
      (Vs - Vx) - thirdFullPhysicalSharpLowCutoffHilbert244 rho (Vs - Vx) := by
        rw [thirdFullPhysical_sharpVectorLowCutoff_sub244 rho Vs Vx]
        abel
    _ = (∫ r in x..s, h3PathActualProjectedMomentumSource244 hH3 r) -
          thirdFullPhysicalSharpLowCutoffHilbert244 rho
            (∫ r in x..s, h3PathActualProjectedMomentumSource244 hH3 r) := by
      rw [hFTC]

/-- The signed physical source work of the OLD highpass against the
highpass of the time-integrated ACTUAL momentum source. -/
noncomputable def thirdFullPhysicalOuterHighpassSignedSourceWork244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho : ℝ) : ℝ :=
  let Vx := h3AuditInitialOldPhysicalHilbertTotal hH3 x
  let Hx := Vx - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vx
  let J : H3PhysicalRealFinVectorL2Hilbert :=
    ∫ r in x..s, h3PathActualProjectedMomentumSource244 hH3 r
  let Jh := J - thirdFullPhysicalSharpLowCutoffHilbert244 rho J
  show ℝ from -(inner ℝ Hx Jh)

/-- Exact physical highpass mass loss: signed projected-source work MINUS
its quadratic increment, with no Cauchy/triangle estimate. -/
theorem thirdFullPhysical_outerHighpassMassLoss_exactSourceWork244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho =
      2 * thirdFullPhysicalOuterHighpassSignedSourceWork244 hH3 x s rho -
        thirdFullPhysicalOuterHighpassSourceAction244 hH3 x s rho ^ 2 := by
  let Vx : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 x
  let Vs : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 s
  let Hx : H3PhysicalRealFinVectorL2Hilbert :=
    Vx - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vx
  let Hs : H3PhysicalRealFinVectorL2Hilbert :=
    Vs - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vs
  let J : H3PhysicalRealFinVectorL2Hilbert :=
    ∫ r in x..s, h3PathActualProjectedMomentumSource244 hH3 r
  let Jh : H3PhysicalRealFinVectorL2Hilbert :=
    J - thirdFullPhysicalSharpLowCutoffHilbert244 rho J
  have hDiff : Hs - Hx = Jh :=
    thirdFullPhysical_outerHighpassSourceVectorFTC244 hH3 x s rho hx hs
  have hHs : Hs = Hx + Jh := by
    calc
      Hs = (Hs - Hx) + Hx := by abel
      _ = Hx + Jh := by rw [hDiff]; abel
  change ‖Hx‖ ^ 2 - ‖Hs‖ ^ 2 =
    2 * (-(inner ℝ Hx Jh)) - ‖Jh‖ ^ 2
  calc
    ‖Hx‖ ^ 2 - ‖Hs‖ ^ 2 = ‖Hx‖ ^ 2 - ‖Hx + Jh‖ ^ 2 := by
      rw [hHs]
    _ = -2 * inner ℝ Hx Jh - ‖Jh‖ ^ 2 :=
      thirdFullKinetic_highpassSquareLoss_exactWork244 Hx Jh
    _ = 2 * (-(inner ℝ Hx Jh)) - ‖Jh‖ ^ 2 := by ring

/-- A genuine physical highpass drain must have strictly POSITIVE signed
source work (equivalently, negative projected-source alignment). -/
theorem thirdFullPhysical_outerPositiveDrain_forcesSignedSourceWork244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hDrain : thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho <
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho) :
    0 < thirdFullPhysicalOuterHighpassSignedSourceWork244 hH3 x s rho := by
  have hExact := thirdFullPhysical_outerHighpassMassLoss_exactSourceWork244
    hH3 x s rho hx hs
  have hSq : 0 ≤ thirdFullPhysicalOuterHighpassSourceAction244 hH3 x s rho ^ 2 :=
    sq_nonneg _
  have hDrop : 0 <
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho :=
    sub_pos.mpr hDrain
  rw [hExact] at hDrop
  linarith only [hDrop, hSq]

/-- Sharpen the earlier scalar early-Young gate by paying its slope with
ACTUAL kinetic loss, not a norm bound for the source action. -/
theorem thirdFullKinetic_earlyYoung_noGrowth_exactKineticDrain244
    (a B w C mx ms yx ys epsilon K : ℝ)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hw : 0 ≤ w) (hC : 0 ≤ C)
    (hmx : 0 < mx) (hEx : 0 ≤ a * mx - B)
    (hDef : 0 ≤ w * (a * mx - B) ^ 2 - mx * C)
    (hMs : 0 ≤ ms) (hStrict : ms < mx) (hNoGrowth : ys ≤ yx)
    (hK : 2 * w * a * (a * mx - B) ≤ K)
    (hDrop : epsilon <
      (mx - ms) * (w * a * (a * (mx + ms) - 2 * B) - C) +
        ms * (ys - yx)) :
    epsilon < (mx - ms) * K := by
  have hLoss : 0 ≤ mx - ms := sub_nonneg.mpr hStrict.le
  have hSlope := thirdFullKinetic_earlyYoung_sourceSlope_oneSidedLoss244
    a B w C mx ms (mx - ms)
    ha hB hw hC hmx hEx hDef le_rfl hLoss
  have hYoung : ms * (ys - yx) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hMs (sub_nonpos.mpr hNoGrowth)
  have hPartial : epsilon < (mx - ms) * (2 * w * a * (a * mx - B)) := by
    linarith only [hSlope, hDrop, hYoung]
  have hCap := mul_le_mul_of_nonneg_left hK hLoss
  exact lt_of_lt_of_le hPartial hCap

/-- Given a selected strict positive annular deficit drop without signed
Young-width growth, the exact one-sided physical source work MUST pay the
kinetic drain, including its negative quadratic correction. -/
theorem thirdFullPhysical_outerNoYoungGrowth_forcesSignedSourceWork244
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
    let Mx := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
    let K := 2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 * Mx
    epsilon < K *
      (2 * thirdFullPhysicalOuterHighpassSignedSourceWork244 hH3 x s rho -
       thirdFullPhysicalOuterHighpassSourceAction244 hH3 x s rho ^ 2) := by
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
  have hStrict : Ms < Mx :=
    thirdFullPhysical_outerNoYoungGrowth_forcesStrictHighpassDrain244
      hH3 b x s rho sigma margin epsilon hRho hAspect
      hMargin hEps hExcess hPeak hDrop hNoGrowth
  have hMs : 0 ≤ Ms := sq_nonneg _
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
  have hKCap : 2 * w * aMean * (aMean * Mx - B) ≤ K := by
    change 2 * (rho ^ 2) ^ 3 * aMean * (aMean * Mx - B) ≤
      2 * (rho ^ 2) ^ 3 * (sigma ^ 2) ^ 2 * Mx
    exact thirdFullKinetic_earlyYoung_kineticSlope_initialHighpassCap244
      aMean B Mx rho sigma ha hMean.2 hB hMxNonneg
  have hScalar : epsilon < (Mx - Ms) * K :=
    thirdFullKinetic_earlyYoung_noGrowth_exactKineticDrain244
      aMean B w (Yx + w * P) Mx Ms Yx Ys epsilon K
      ha hB hw hC hMx hExNonneg hDef hMs hStrict hNoGrowth
      hKCap hDrop'
  have hMassWork := thirdFullPhysical_outerHighpassMassLoss_exactSourceWork244
    hH3 x s rho hx hs
  change Mx - Ms =
      2 * thirdFullPhysicalOuterHighpassSignedSourceWork244 hH3 x s rho -
        thirdFullPhysicalOuterHighpassSourceAction244 hH3 x s rho ^ 2
    at hMassWork
  have hOrdered : epsilon < K * (Mx - Ms) := by
    calc
      epsilon < (Mx - Ms) * K := hScalar
      _ = K * (Mx - Ms) := mul_comm _ _
  rw [hMassWork] at hOrdered
  exact hOrdered

/-- Along a selected no-growth deficit excursion the signed projected
source work is genuinely positive, not merely norm-large. -/
theorem thirdFullPhysical_outerNoYoungGrowth_sourceWorkPositive244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b x s rho sigma margin epsilon : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
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
    0 < thirdFullPhysicalOuterHighpassSignedSourceWork244 hH3 x s rho := by
  have hDrain := thirdFullPhysical_outerNoYoungGrowth_forcesStrictHighpassDrain244
    hH3 b x s rho sigma margin epsilon hRho hAspect
    hMargin hEps hExcess hPeak hDrop hNoGrowth
  exact thirdFullPhysical_outerPositiveDrain_forcesSignedSourceWork244
    hH3 x s rho hx hs hDrain

/-- The physical Laplacian and nonlinear Leray source are individually
Bochner-integrable on every ORDERED strict interior interval. The projected
source was already known integrable as their difference; this proves the
individual facts required for an exact source-work decomposition. -/
theorem thirdFullPhysical_outerSourceComponents_intervalIntegrable244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hxs : x ≤ s) :
    IntervalIntegrable (h3AuditInitialActualSpectralLaplacianTotal hH3)
        volume x s ∧
      IntervalIntegrable (h3AuditInitialActualSpectralLerayTotal hH3)
        volume x s := by
  have hU : ContinuousOn
      (h3AuditActualSpectralVelocityTotal hH3)
      (Set.Ioo (0 : ℝ) T) :=
    h3Audit_initialActualSpectralVelocity_continuousOn hH3
  have hD : ContinuousOn
      (h3AuditInitialActualSpectralLaplacianTotal hH3)
      (Set.Ioo (0 : ℝ) T) := by
    have hComp :=
      continuous_h3AuditSpectralPhysicalLaplacian.comp_continuousOn hU
    apply hComp.congr
    intro r hr
    simp only [h3AuditInitialActualSpectralLaplacianTotal,
      dite_eq_left hr, Function.comp_apply]
  have hN : ContinuousOn
      (h3AuditInitialActualSpectralLerayTotal hH3)
      (Set.Ioo (0 : ℝ) T) := by
    have hComp :=
      continuous_h3AuditSpectralPhysicalLerayForcing.comp_continuousOn hU
    apply hComp.congr
    intro r hr
    simp only [h3AuditInitialActualSpectralLerayTotal,
      dite_eq_left hr, Function.comp_apply]
  have hSub : Set.Icc x s ⊆ Set.Ioo (0 : ℝ) T := by
    intro r hr
    exact ⟨lt_of_lt_of_le hx.1 hr.1, lt_of_le_of_lt hr.2 hs.2⟩
  exact ⟨(hD.mono hSub).intervalIntegrable_of_Icc hxs,
    (hN.mono hSub).intervalIntegrable_of_Icc hxs⟩

/-- Split the genuinely signed, time-integrated highpass physical source
work into its Laplacian and nonlinear Leray parts. This is NOT an
assumption about heat-flow positivity: the fixed-initial-state viscous
cross-time pairing can have either sign on its own. -/
theorem thirdFullPhysical_outerSignedSourceWork_viscousLeraySplit244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hxs : x ≤ s) :
    let Vx := h3AuditInitialOldPhysicalHilbertTotal hH3 x
    let Hx := Vx - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vx
    let JD : H3PhysicalRealFinVectorL2Hilbert :=
      ∫ r in x..s, h3AuditInitialActualSpectralLaplacianTotal hH3 r
    let JN : H3PhysicalRealFinVectorL2Hilbert :=
      ∫ r in x..s, h3AuditInitialActualSpectralLerayTotal hH3 r
    thirdFullPhysicalOuterHighpassSignedSourceWork244 hH3 x s rho =
      -(inner ℝ Hx (JD - thirdFullPhysicalSharpLowCutoffHilbert244 rho JD)) +
        inner ℝ Hx (JN - thirdFullPhysicalSharpLowCutoffHilbert244 rho JN) := by
  let Vx : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 x
  let Hx : H3PhysicalRealFinVectorL2Hilbert :=
    Vx - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vx
  let JD : H3PhysicalRealFinVectorL2Hilbert :=
    ∫ r in x..s, h3AuditInitialActualSpectralLaplacianTotal hH3 r
  let JN : H3PhysicalRealFinVectorL2Hilbert :=
    ∫ r in x..s, h3AuditInitialActualSpectralLerayTotal hH3 r
  let J : H3PhysicalRealFinVectorL2Hilbert :=
    ∫ r in x..s, h3PathActualProjectedMomentumSource244 hH3 r
  obtain ⟨hDInt, hNInt⟩ :=
    thirdFullPhysical_outerSourceComponents_intervalIntegrable244
      hH3 x s hx hs hxs
  have hJ : J = JD - JN := by
    dsimp only [J, JD, JN]
    change (∫ r in x..s,
      h3AuditInitialActualSpectralLaplacianTotal hH3 r -
        h3AuditInitialActualSpectralLerayTotal hH3 r) = _
    exact intervalIntegral.integral_sub hDInt hNInt
  have hHigh :
      J - thirdFullPhysicalSharpLowCutoffHilbert244 rho J =
        (JD - thirdFullPhysicalSharpLowCutoffHilbert244 rho JD) -
          (JN - thirdFullPhysicalSharpLowCutoffHilbert244 rho JN) := by
    rw [hJ, thirdFullPhysical_sharpVectorLowCutoff_sub244 rho JD JN]
    abel
  change -(inner ℝ Hx
      (J - thirdFullPhysicalSharpLowCutoffHilbert244 rho J)) =
    -(inner ℝ Hx (JD - thirdFullPhysicalSharpLowCutoffHilbert244 rho JD)) +
      inner ℝ Hx (JN - thirdFullPhysicalSharpLowCutoffHilbert244 rho JN)
  rw [hHigh, inner_sub_right]
  ring

/-- A positive physical highpass kinetic drain has to be paid by a
NEGATIVE projected viscous increment pairing, or by a POSITIVE nonlinear
Leray increment pairing. This is the exact source-work two-channel split,
not a sign assumption for either channel. -/
theorem thirdFullPhysical_outerPositiveDrain_forcesViscousOrLerayWork244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x s rho : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hxs : x ≤ s)
    (hDrain : thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho <
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho) :
    let Vx := h3AuditInitialOldPhysicalHilbertTotal hH3 x
    let Hx := Vx - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vx
    let JD : H3PhysicalRealFinVectorL2Hilbert :=
      ∫ r in x..s, h3AuditInitialActualSpectralLaplacianTotal hH3 r
    let JN : H3PhysicalRealFinVectorL2Hilbert :=
      ∫ r in x..s, h3AuditInitialActualSpectralLerayTotal hH3 r
    0 < -(inner ℝ Hx
      (JD - thirdFullPhysicalSharpLowCutoffHilbert244 rho JD)) ∨
    0 < inner ℝ Hx
      (JN - thirdFullPhysicalSharpLowCutoffHilbert244 rho JN) := by
  let Vx : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 x
  let Hx : H3PhysicalRealFinVectorL2Hilbert :=
    Vx - thirdFullPhysicalSharpLowCutoffHilbert244 rho Vx
  let JD : H3PhysicalRealFinVectorL2Hilbert :=
    ∫ r in x..s, h3AuditInitialActualSpectralLaplacianTotal hH3 r
  let JN : H3PhysicalRealFinVectorL2Hilbert :=
    ∫ r in x..s, h3AuditInitialActualSpectralLerayTotal hH3 r
  have hW : 0 < thirdFullPhysicalOuterHighpassSignedSourceWork244
      hH3 x s rho :=
    thirdFullPhysical_outerPositiveDrain_forcesSignedSourceWork244
      hH3 x s rho hx hs hDrain
  have hSplit := thirdFullPhysical_outerSignedSourceWork_viscousLeraySplit244
    hH3 x s rho hx hs hxs
  change thirdFullPhysicalOuterHighpassSignedSourceWork244 hH3 x s rho =
    -(inner ℝ Hx (JD - thirdFullPhysicalSharpLowCutoffHilbert244 rho JD)) +
      inner ℝ Hx (JN - thirdFullPhysicalSharpLowCutoffHilbert244 rho JN)
    at hSplit
  rw [hSplit] at hW
  change 0 < -(inner ℝ Hx
      (JD - thirdFullPhysicalSharpLowCutoffHilbert244 rho JD)) ∨
    0 < inner ℝ Hx
      (JN - thirdFullPhysicalSharpLowCutoffHilbert244 rho JN)
  by_contra hNot
  push_neg at hNot
  linarith only [hW, hNot.1, hNot.2]

end
end PrimeTensor.FirstMonomialTriad
