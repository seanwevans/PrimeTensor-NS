import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierAnchoredSlope
import Mathlib.Tactic

/-!
# One-sided Young-width obstruction and the full deficit-budget identity

The selected outer carrier's exact anchored identity has a hidden sign
structure. A *positive* initial deficit with a positive kinetic excess
forces its early-Young polynomial slope to be nonnegative whenever the
highpass kinetic mass does not decrease. Therefore a later deficit drop
cannot be financed by an increasing kinetic carrier: the entire drop must
be paid by strictly positive, signed Young-width growth.

Without monotonicity, the physical projected source has an explicit mass
variation budget A and the early-time snapshot envelope bounds |Q| by C.
The exact residual bound is

    epsilon - A*C < M(s) * (Y(s) - Y(x)),

which improves the previous epsilon/2 disjunction and removes an avoidable
factor of two in the condition forcing genuinely positive Young growth.

No time regularity beyond the proved physical momentum FTC is postulated;
no terminal continuation theorem is asserted. Moving-frequency A*C is not
proved to tend to zero.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Exact scalar residual: the whole deficit drop remains once the
SOURCE-weighted early polynomial slope has been paid. -/
theorem thirdFullKinetic_earlyYoung_fullResidual244
    (epsilon mx ms Q A C yx ys : ℝ)
    (hMass : |mx - ms| ≤ A) (hQ : |Q| ≤ C) (hA : 0 ≤ A)
    (hDrop : epsilon < (mx - ms) * Q + ms * (ys - yx)) :
    epsilon - A * C < ms * (ys - yx) := by
  have hSlope : (mx - ms) * Q ≤ A * C := by
    calc
      (mx - ms) * Q ≤ |(mx - ms) * Q| := le_abs_self _
      _ = |mx - ms| * |Q| := abs_mul _ _
      _ ≤ A * |Q| := mul_le_mul_of_nonneg_right hMass (abs_nonneg Q)
      _ ≤ A * C := mul_le_mul_of_nonneg_left hQ hA
  linarith only [hDrop, hSlope]

/-- When the original nonlinear Young-width cost does not increase,
ONE FULL deficit floor must be covered by the physical source-slope product.
No half-margin is lost. -/
theorem thirdFullKinetic_earlyYoung_noGrowth_fullSourcePayment244
    (epsilon ms A C yx ys : ℝ) (hMs : 0 ≤ ms)
    (hNoGrowth : ys ≤ yx)
    (hResidual : epsilon - A * C < ms * (ys - yx)) :
    epsilon < A * C := by
  have hY : ms * (ys - yx) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hMs (sub_nonpos.mpr hNoGrowth)
  linarith only [hResidual, hY]

/-- If the entire physical source-slope payment is no larger than the
observed deficit floor, the original Young-width cost MUST grow. -/
theorem thirdFullKinetic_earlyYoung_fullBudget_forcesIncrease244
    (epsilon ms A C yx ys : ℝ) (hMs : 0 ≤ ms)
    (hBudget : A * C ≤ epsilon)
    (hResidual : epsilon - A * C < ms * (ys - yx)) :
    yx < ys := by
  have hPos : 0 < ms * (ys - yx) :=
    lt_of_le_of_lt (sub_nonneg.mpr hBudget) hResidual
  by_contra hn
  have hY : ms * (ys - yx) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hMs
      (sub_nonpos.mpr (le_of_not_gt hn))
  exact (not_lt_of_ge hY) hPos

/-- A strictly positive starting mass and positive deficit make the
EARLY-anchored polynomial slope nonnegative whenever the highpass mass
is nondecreasing. The proof is an exact polarization, not an assumed
frequency-uniform slope estimate. -/
theorem thirdFullKinetic_positiveDeficit_earlySlope_nonneg244
    (a B w C mx ms : ℝ)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hw : 0 ≤ w)
    (hmx : 0 < mx) (hMass : mx ≤ ms)
    (hExcess : 0 ≤ a * mx - B)
    (hDeficit : 0 ≤ w * (a * mx - B) ^ 2 - mx * C) :
    0 ≤ w * a * (a * (mx + ms) - 2 * B) - C := by
  have hLaterExcess : 0 ≤ a * ms - B := by
    have hScaled := mul_le_mul_of_nonneg_left hMass ha
    linarith only [hScaled, hExcess]
  have hTermOne : 0 ≤ (a * mx - B) * (a * ms - B) :=
    mul_nonneg hExcess hLaterExcess
  have hTermTwo : 0 ≤ B * ((a * mx - B) + (a * ms - B)) :=
    mul_nonneg hB (add_nonneg hExcess hLaterExcess)
  have hTerm : 0 ≤ w * ((a * mx - B) * (a * ms - B) +
      B * ((a * mx - B) + (a * ms - B))) :=
    mul_nonneg hw (add_nonneg hTermOne hTermTwo)
  have hIdentity :
      mx * (w * a * (a * (mx + ms) - 2 * B) - C) =
        w * ((a * mx - B) * (a * ms - B) +
          B * ((a * mx - B) + (a * ms - B))) +
          (w * (a * mx - B) ^ 2 - mx * C) := by ring
  have hProduct : 0 ≤ mx * (w * a * (a * (mx + ms) - 2 * B) - C) := by
    rw [hIdentity]
    exact add_nonneg hTerm hDeficit
  by_contra hn
  have hNegative : w * a * (a * (mx + ms) - 2 * B) - C < 0 :=
    lt_of_not_ge hn
  have hBad : mx * (w * a * (a * (mx + ms) - 2 * B) - C) < 0 := by
    have h := mul_lt_mul_of_pos_left hNegative hmx
    simpa only [mul_zero] using h
  exact (not_lt_of_ge hProduct) hBad

/-- The earlier positive-deficit geometry makes any later *increase* in
highpass mass incapable of paying a positive deficit drop. The entire
strict loss must be paid by the signed Young-width increment. -/
theorem thirdFullKinetic_nondecreasingMass_fullYoungCharge244
    (a B w P mx ms yx ys epsilon : ℝ)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hw : 0 ≤ w)
    (hmx : 0 < mx) (hMass : mx ≤ ms)
    (hExcess : 0 ≤ a * mx - B)
    (hDeficit : 0 ≤ w * (a * mx - B) ^ 2 - mx * (yx + w * P))
    (hDrop : epsilon <
      (w * (a * mx - B) ^ 2 - mx * (yx + w * P)) -
        (w * (a * ms - B) ^ 2 - ms * (ys + w * P))) :
    epsilon < ms * (ys - yx) := by
  have hSlope : 0 ≤
      w * a * (a * (mx + ms) - 2 * B) - (yx + w * P) :=
    thirdFullKinetic_positiveDeficit_earlySlope_nonneg244
      a B w (yx + w * P) mx ms ha hB hw hmx hMass hExcess hDeficit
  have hNegative : (mx - ms) *
      (w * a * (a * (mx + ms) - 2 * B) - (yx + w * P)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hMass) hSlope
  have hIdentity := thirdFullKinetic_deficitPolynomial_earlyYoungIdentity244
    a B w P mx ms yx ys
  rw [hIdentity] at hDrop
  linarith only [hDrop, hNegative]

/-- Physical residual with NO factor-of-two loss. A is the genuine
projected-momentum-source budget; C is the real one-snapshot finite-radius
Fourier envelope, not a later Young-width surrogate. -/
theorem thirdFullPhysical_outerDeficitDrop_fullYoungResidual244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (s : ℝ) (hxs : x ≤ s) (hsT : s < T)
    (rho sigma R epsilon : ℝ)
    (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma) (hUpper : sigma ≤ R)
    (hDrop : epsilon <
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
        thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma) :
    let A := thirdFullPhysicalOuterSourceMassBudget244 hH3 b x
    let C := thirdFullPhysicalOuterDynamicSnapshotSlopeCeiling244 u b R A
      (h3AuditActualSpectralVelocityTotal hH3 x)
      (h3AuditInitialOldPhysicalHilbertTotal hH3 x)
    let Ms := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
    let Yx := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
    let Ys := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma
    epsilon - A * C < Ms * (Ys - Yx) := by
  let A : ℝ := thirdFullPhysicalOuterSourceMassBudget244 hH3 b x
  let C : ℝ := thirdFullPhysicalOuterDynamicSnapshotSlopeCeiling244 u b R A
    (h3AuditActualSpectralVelocityTotal hH3 x)
    (h3AuditInitialOldPhysicalHilbertTotal hH3 x)
  let Q : ℝ := thirdFullPhysicalOuterEarlyYoungSlope244 hH3 b x s rho sigma
  let Mx : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
  let Ms : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
  let Yx : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
  let Ys : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma
  have hMassOne : |Ms - Mx| ≤ A :=
    thirdFullPhysical_outerHighpassMassDrift_le_sourceBudget244
      hH3 hClass hDInt b hb x hx s hxs hsT rho
  have hMass : |Mx - Ms| ≤ A := by
    calc
      |Mx - Ms| = |Ms - Mx| := abs_sub_comm _ _
      _ ≤ A := hMassOne
  have hA : 0 ≤ A := (abs_nonneg _).trans hMass
  have hQ : |Q| ≤ C :=
    thirdFullPhysical_outerEarlyYoungSlope_le_dynamicSnapshotCeiling244
      hH3 hClass hDInt b hb x hx s hxs hsT
      rho sigma R hRho hOrder hUpper
  have hIdentity := thirdFullPhysical_outerDeficit_earlyYoungIdentity244
    hH3 b x s rho sigma
  change
    thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma =
        (Mx - Ms) * Q + Ms * (Ys - Yx) at hIdentity
  have hDrop' : epsilon < (Mx - Ms) * Q + Ms * (Ys - Yx) := by
    rw [hIdentity] at hDrop
    exact hDrop
  change epsilon - A * C < Ms * (Ys - Yx)
  exact thirdFullKinetic_earlyYoung_fullResidual244
    epsilon Mx Ms Q A C Yx Ys hMass hQ hA hDrop'

/-- The full physical source-slope cost (not half of it) is necessary
when the ORIGINAL nonlinear Young-width integral fails to rise. -/
theorem thirdFullPhysical_outerNoYoungIncrease_fullSourceSlope244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (s : ℝ) (hxs : x ≤ s) (hsT : s < T)
    (rho sigma R epsilon : ℝ)
    (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma) (hUpper : sigma ≤ R)
    (hDrop : epsilon <
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
        thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma)
    (hNoIncrease :
      thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma ≤
        thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma) :
    epsilon < thirdFullPhysicalOuterSourceMassBudget244 hH3 b x *
      thirdFullPhysicalOuterDynamicSnapshotSlopeCeiling244 u b R
        (thirdFullPhysicalOuterSourceMassBudget244 hH3 b x)
        (h3AuditActualSpectralVelocityTotal hH3 x)
        (h3AuditInitialOldPhysicalHilbertTotal hH3 x) := by
  have hResidual := thirdFullPhysical_outerDeficitDrop_fullYoungResidual244
    hH3 hClass hDInt b hb x hx s hxs hsT
    rho sigma R epsilon hRho hOrder hUpper hDrop
  dsimp only at hResidual
  exact thirdFullKinetic_earlyYoung_noGrowth_fullSourcePayment244
    epsilon (thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho)
    (thirdFullPhysicalOuterSourceMassBudget244 hH3 b x)
    (thirdFullPhysicalOuterDynamicSnapshotSlopeCeiling244 u b R
      (thirdFullPhysicalOuterSourceMassBudget244 hH3 b x)
      (h3AuditActualSpectralVelocityTotal hH3 x)
      (h3AuditInitialOldPhysicalHilbertTotal hH3 x))
    (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma)
    (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma)
    (sq_nonneg _) hNoIncrease hResidual

/-- Physical positive kinetic excess, initial annular deficit, and a
NONDECREASING actual highpass carrier force a FULL signed Young payment
for every deficit drop. The polynomial slope is proved nonnegative. -/
theorem thirdFullPhysical_outerNondecreasingHighpass_fullYoungCharge244
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
    (hMass :
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho ≤
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho)
    (hDrop : epsilon <
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
        thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma) :
    epsilon <
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho *
        (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma -
          thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma) := by
  let a : ℝ := (rho ^ 2 + sigma ^ 2) / 2
  let w : ℝ := (rho ^ 2) ^ 3
  let B : ℝ := Real.sqrt (velocityH3Energy0At u b) *
    (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
      rho (velocityH3Energy0At u b))
  let P : ℝ := thirdFullPhysicalOuterViscousCapBase244 u b a
  let Mx : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
  let Ms : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
  let Yx : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
  let Ys : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (thirdFullPhysicalKineticLowBandSourceCeiling_nonneg244
          rho (velocityH3Energy0At u b)))
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hmxNonneg : 0 ≤ Mx := sq_nonneg _
  have hEx : B + margin ≤ a * Mx := hExcess
  have hmx : 0 < Mx := by
    by_contra hn
    have hZero : Mx = 0 := le_antisymm (le_of_not_gt hn) hmxNonneg
    rw [hZero, mul_zero] at hEx
    linarith only [hEx, hB, hMargin]
  have hExcessPositive : 0 ≤ a * Mx - B := by
    linarith only [hEx, hMargin]
  have hDef : 0 ≤ w * (a * Mx - B) ^ 2 - Mx * (Yx + w * P) := by
    change 2 * epsilon ≤
      w * (a * Mx - B) ^ 2 - Mx * (Yx + w * P) at hPeak
    linarith only [hPeak, hEps]
  change Mx ≤ Ms at hMass
  have hResult := thirdFullKinetic_nondecreasingMass_fullYoungCharge244
    a B w P Mx Ms Yx Ys epsilon
    ha hB hw hmx hMass hExcessPositive hDef (by
      change epsilon <
        (w * (a * Mx - B) ^ 2 - Mx * (Yx + w * P)) -
          (w * (a * Ms - B) ^ 2 - Ms * (Ys + w * P))
      at hDrop
      exact hDrop)
  exact hResult

/-- The selected half-terminal PDE excursion, with the SHARP remaining
Young payment instead of an epsilon/2 disjunction. -/
theorem thirdFullPhysical_selectedOuter_lowHalfTail_fullYoungResidual244
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
    let C := thirdFullPhysicalOuterDynamicSnapshotSlopeCeiling244 u b sigma A
      (h3AuditActualSpectralVelocityTotal hH3 x)
      (h3AuditInitialOldPhysicalHilbertTotal hH3 x)
    margin < (rho ^ 2 + sigma ^ 2) * A ∨
      (∃ s : ℝ, s ∈ Set.Ioc x ((x + T) / 2) ∧
        epsilon - A * C <
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho *
            (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma -
              thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma)) := by
  have hChoice := thirdFullPhysical_selectedOuter_lowHalfTail_forcesViscousSourceOrYoung244
    hH3 hClass hDInt b hb x hx rho sigma margin epsilon
    hRho hAspect hMargin hEps hExcess hPeak hSmall
  dsimp only at hChoice ⊢
  rcases hChoice with hSource | ⟨s, hs, hDrop⟩
  · exact Or.inl hSource
  · right
    have hsT : s < T := by linarith only [hs.2, hx.2]
    have hOrder : rho ≤ sigma := by linarith only [hRho, hAspect]
    exact ⟨s, hs,
      thirdFullPhysical_outerDeficitDrop_fullYoungResidual244
        hH3 hClass hDInt b hb x hx s hs.1.le hsT
        rho sigma sigma epsilon hRho.le hOrder le_rfl hDrop⟩

/-- The source payment threshold for genuine signed Young growth is the
FULL deficit epsilon. Both eliminated channels use only actual physical
quantities and the original early-time snapshot Fourier envelope. -/
theorem thirdFullPhysical_selectedOuter_fullSlopeBudget_forcesYoungGrowth244
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
    (hFullSlopeSmall :
      thirdFullPhysicalOuterSourceMassBudget244 hH3 b x *
        thirdFullPhysicalOuterDynamicSnapshotSlopeCeiling244 u b sigma
          (thirdFullPhysicalOuterSourceMassBudget244 hH3 b x)
          (h3AuditActualSpectralVelocityTotal hH3 x)
          (h3AuditInitialOldPhysicalHilbertTotal hH3 x) ≤ epsilon) :
    ∃ s : ℝ, s ∈ Set.Ioc x ((x + T) / 2) ∧
      thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma <
        thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma := by
  have hChoice := thirdFullPhysical_selectedOuter_lowHalfTail_fullYoungResidual244
    hH3 hClass hDInt b hb x hx rho sigma margin epsilon
    hRho hAspect hMargin hEps hExcess hPeak hSmall
  dsimp only at hChoice
  rcases hChoice with hSource | ⟨s, hs, hResidual⟩
  · exact False.elim ((not_lt_of_ge hSourceSmall) hSource)
  · refine ⟨s, hs, ?_⟩
    exact thirdFullKinetic_earlyYoung_fullBudget_forcesIncrease244
      epsilon
      (thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho)
      (thirdFullPhysicalOuterSourceMassBudget244 hH3 b x)
      (thirdFullPhysicalOuterDynamicSnapshotSlopeCeiling244 u b sigma
        (thirdFullPhysicalOuterSourceMassBudget244 hH3 b x)
        (h3AuditActualSpectralVelocityTotal hH3 x)
        (h3AuditInitialOldPhysicalHilbertTotal hH3 x))
      (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma)
      (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma)
      (sq_nonneg _) hFullSlopeSmall hResidual

/-- Cofinal, full-deficit residual after the physical source-slope price:
no artificial loss of one-half and no later-time Young envelope. -/
theorem thirdFullPhysical_cofinalOuter_fullYoungResidual244
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
      let C := thirdFullPhysicalOuterDynamicSnapshotSlopeCeiling244 u b
        (sigma k) A (h3AuditActualSpectralVelocityTotal hH3 (x k))
        (h3AuditInitialOldPhysicalHilbertTotal hH3 (x k))
      margin k < (rho k ^ 2 + sigma k ^ 2) * A ∨
      (∃ s : ℝ, s ∈ Set.Ioc (x k) ((x k + T) / 2) ∧
        epsilon k - A * C <
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
    have hOrder : rho k ≤ sigma k := by
      linarith only [hRho k, hAspect k]
    exact ⟨s, hs,
      thirdFullPhysical_outerDeficitDrop_fullYoungResidual244
        hH3 hClass hDInt b hb (x k) (hx k) s hs.1.le hsT
        (rho k) (sigma k) (sigma k) (epsilon k)
        (hRho k).le hOrder le_rfl hDrop⟩

end
end PrimeTensor.FirstMonomialTriad
