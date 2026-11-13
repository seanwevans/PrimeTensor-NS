import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierOneSidedYoung
import Mathlib.Tactic

/-!
# Signed highpass slope: remove the nonlinear H3 snapshot envelope

The exact early-anchored annular deficit has a one-sided cancellation. When
highpass mass falls, the early Young cost and viscous baseline are nonnegative;
they can only LOWER the positive mass-loss slope. When highpass mass rises,
the existing positive-deficit polarization makes the slope nonnegative,
so its contribution to a deficit drop is nonpositive.

Hence the entire signed physical source payment is bounded by the positive
kinetic-only coefficient `2*w*a*(a*Mx-B)` times the mass increment. In a
selected annulus this is at most `2*sigma^10*||Vx||²` times the physical
projected-source mass budget. There is no later-time nonlinear coefficient,
no H3 snapshot Young residual envelope, and no new temporal regularity premise.

This is a necessary conditional obstruction, not H3 continuation. The
frequency-weighted product sigma^10 * source-tail remains open.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Signed slope payment: the earlier Young/viscous cost cancels from
    the upper bound for both directions of the highpass-mass increment. -/
theorem thirdFullKinetic_earlyYoung_sourceSlope_kineticOnly244
    (a B w C mx ms : ℝ)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hw : 0 ≤ w) (hC : 0 ≤ C)
    (hmx : 0 < mx) (hEx : 0 ≤ a * mx - B)
    (hDef : 0 ≤ w * (a * mx - B) ^ 2 - mx * C) :
    (mx - ms) * (w * a * (a * (mx + ms) - 2 * B) - C) ≤
      (2 * w * a * (a * mx - B)) * |mx - ms| := by
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
      _ = (2 * w * a * (a * mx - B)) * |mx - ms| := by
        rw [abs_of_nonneg hDelta]
        ring
  · have hQ : 0 ≤ w * a * (a * (mx + ms) - 2 * B) - C :=
      thirdFullKinetic_positiveDeficit_earlySlope_nonneg244
        a B w C mx ms ha hB hw hmx hUp hEx hDef
    have hNonpositive :
        (mx - ms) * (w * a * (a * (mx + ms) - 2 * B) - C) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hUp) hQ
    exact hNonpositive.trans (mul_nonneg hK (abs_nonneg _))

/-- Exact signed residual, with a kinetic-only slope charge and no arbitrary
    factor-of-two split. -/
theorem thirdFullKinetic_earlyYoung_kineticOnlyResidual244
    (a B w C mx ms yx ys epsilon A : ℝ)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hw : 0 ≤ w) (hC : 0 ≤ C)
    (hmx : 0 < mx) (hEx : 0 ≤ a * mx - B)
    (hDef : 0 ≤ w * (a * mx - B) ^ 2 - mx * C)
    (hMass : |mx - ms| ≤ A)
    (hDrop : epsilon <
      (mx - ms) * (w * a * (a * (mx + ms) - 2 * B) - C) +
        ms * (ys - yx)) :
    epsilon - A * (2 * w * a * (a * mx - B)) < ms * (ys - yx) := by
  have hK : 0 ≤ 2 * w * a * (a * mx - B) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hw) ha) hEx
  have hSigned := thirdFullKinetic_earlyYoung_sourceSlope_kineticOnly244
    a B w C mx ms ha hB hw hC hmx hEx hDef
  have hTransport :
      (2 * w * a * (a * mx - B)) * |mx - ms| ≤
        (2 * w * a * (a * mx - B)) * A :=
    mul_le_mul_of_nonneg_left hMass hK
  have hUpper :
      (mx - ms) * (w * a * (a * (mx + ms) - 2 * B) - C) ≤
        A * (2 * w * a * (a * mx - B)) := by
    calc
      _ ≤ (2 * w * a * (a * mx - B)) * |mx - ms| := hSigned
      _ ≤ (2 * w * a * (a * mx - B)) * A := hTransport
      _ = A * (2 * w * a * (a * mx - B)) := by ring
  linarith only [hDrop, hUpper]

/-- Sharp radius-only bound. Positivity of the initial kinetic excess
    eliminates the nonlinear snapshot envelope entirely. -/
theorem thirdFullKinetic_earlyYoung_kineticSlope_radiusCap244
    (a B w mx R H : ℝ)
    (ha : 0 ≤ a) (haCap : a ≤ R ^ 2)
    (hw : 0 ≤ w) (hwCap : w ≤ (R ^ 2) ^ 3)
    (hB : 0 ≤ B) (hmx : 0 ≤ mx) (hmxCap : mx ≤ H)
    (hH : 0 ≤ H) (hEx : 0 ≤ a * mx - B) :
    2 * w * a * (a * mx - B) ≤ 2 * (R ^ 2) ^ 5 * H := by
  have hInside : a * mx - B ≤ R ^ 2 * H := by
    calc
      a * mx - B ≤ a * mx := sub_le_self _ hB
      _ ≤ R ^ 2 * mx := mul_le_mul_of_nonneg_right haCap hmx
      _ ≤ R ^ 2 * H := mul_le_mul_of_nonneg_left hmxCap (sq_nonneg R)
  have hWA : w * a ≤ (R ^ 2) ^ 3 * (R ^ 2) := by
    calc
      w * a ≤ (R ^ 2) ^ 3 * a := mul_le_mul_of_nonneg_right hwCap ha
      _ ≤ (R ^ 2) ^ 3 * (R ^ 2) :=
        mul_le_mul_of_nonneg_left haCap (by positivity)
  have hTwoWA : 2 * w * a ≤ 2 * ((R ^ 2) ^ 3 * (R ^ 2)) := by
    nlinarith only [hWA]
  have hTwoWANonneg : 0 ≤ 2 * w * a := by positivity
  have hInsideNonneg : 0 ≤ R ^ 2 * H := mul_nonneg (sq_nonneg R) hH
  calc
    2 * w * a * (a * mx - B) ≤
        (2 * w * a) * (R ^ 2 * H) :=
          mul_le_mul_of_nonneg_left hInside hTwoWANonneg
    _ ≤ (2 * ((R ^ 2) ^ 3 * (R ^ 2))) * (R ^ 2 * H) :=
      mul_le_mul_of_nonneg_right hTwoWA hInsideNonneg
    _ = 2 * (R ^ 2) ^ 5 * H := by ring

/-- Radius-only physical coefficient. No H3 spectral snapshot is used. -/
noncomputable def thirdFullPhysicalOuterKineticOnlySlopeCap244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x sigma : ℝ) : ℝ :=
  2 * (sigma ^ 2) ^ 5 *
    ‖h3AuditInitialOldPhysicalHilbertTotal hH3 x‖ ^ 2

/-- A selected annular deficit drop, charged ONLY to the initial L2
    kinetic mass and the actual projected source L1 tail. -/
theorem thirdFullPhysical_outerDeficitDrop_kineticOnlySlopeResidual244
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
    let K := thirdFullPhysicalOuterKineticOnlySlopeCap244 hH3 x sigma
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
  let K : ℝ := thirdFullPhysicalOuterKineticOnlySlopeCap244 hH3 x sigma
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
  have hRhoSq : rho ^ 2 ≤ sigma ^ 2 :=
    pow_le_pow_left₀ hRhoNonneg hOrder 2
  have hWCap : w ≤ (sigma ^ 2) ^ 3 := by
    dsimp only [w]
    exact pow_le_pow_left₀ (sq_nonneg rho) hRhoSq 3
  have hKCap : 2 * w * aMean * (aMean * Mx - B) ≤ K := by
    change 2 * w * aMean * (aMean * Mx - B) ≤
      2 * (sigma ^ 2) ^ 5 * ‖Vx‖ ^ 2
    exact thirdFullKinetic_earlyYoung_kineticSlope_radiusCap244
      aMean B w Mx sigma (‖Vx‖ ^ 2)
      ha hMean.2 hw hWCap hB hMxNonneg hMxCap
      (sq_nonneg _) hExNonneg
  have hA : 0 ≤ A := (abs_nonneg _).trans hMass
  have hPay : A * (2 * w * aMean * (aMean * Mx - B)) ≤ A * K :=
    mul_le_mul_of_nonneg_left hKCap hA
  change epsilon - A * K < Ms * (Ys - Yx)
  linarith only [hScalar, hPay]

/-- A selected terminal carrier must either spend physical source mass
    on the kinetic excess or grow the ORIGINAL Young-width cost after
    paying the radius^10 kinetic-only source slope. -/
theorem thirdFullPhysical_selectedOuter_lowHalfTail_kineticOnlyYoungResidual244
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
    let K := thirdFullPhysicalOuterKineticOnlySlopeCap244 hH3 x sigma
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
      thirdFullPhysical_outerDeficitDrop_kineticOnlySlopeResidual244
        hH3 hClass hDInt b hb x hx s hs.1.le hsT
        rho sigma epsilon hRho hAspect hEps margin hMargin
        hExcess hPeak hDrop⟩

/-- If the two physical payments are small, actual annular Young-width
    MUST grow, with no nonlinear H3 snapshot envelope assumption. -/
theorem thirdFullPhysical_selectedOuter_kineticOnlySlopeSmall_forcesYoungGrowth244
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
        thirdFullPhysicalOuterKineticOnlySlopeCap244 hH3 x sigma ≤ epsilon) :
    ∃ s : ℝ, s ∈ Set.Ioc x ((x + T) / 2) ∧
      thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma <
        thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma := by
  obtain hSource | ⟨s, hs, hResidual⟩ :=
    thirdFullPhysical_selectedOuter_lowHalfTail_kineticOnlyYoungResidual244
      hH3 hClass hDInt b hb x hx rho sigma margin epsilon
      hRho hAspect hMargin hEps hExcess hPeak hSmall
  · exact False.elim ((not_lt_of_ge hSourceSmall) hSource)
  · refine ⟨s, hs, ?_⟩
    exact thirdFullKinetic_earlyYoung_fullBudget_forcesIncrease244
      epsilon (thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho)
      (thirdFullPhysicalOuterSourceMassBudget244 hH3 b x)
      (thirdFullPhysicalOuterKineticOnlySlopeCap244 hH3 x sigma)
      (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma)
      (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma)
      (sq_nonneg _) hKineticSlopeSmall hResidual

/-- Cofinal carrier obstruction with the radius-only kinetic slope:
    no snapshot H3 Young envelope remains in the frequency payment. -/
theorem thirdFullPhysical_cofinalOuter_kineticOnlyYoungResidual244
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
      let K := thirdFullPhysicalOuterKineticOnlySlopeCap244
        hH3 (x k) (sigma k)
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
      thirdFullPhysical_outerDeficitDrop_kineticOnlySlopeResidual244
        hH3 hClass hDInt b hb (x k) (hx k) s hs.1.le hsT
        (rho k) (sigma k) (epsilon k)
        (hRho k) (hAspect k) (hEps k) (margin k) (hMargin k)
        (hExcess k) (hPeak k) hDrop⟩

end
end PrimeTensor.FirstMonomialTriad
