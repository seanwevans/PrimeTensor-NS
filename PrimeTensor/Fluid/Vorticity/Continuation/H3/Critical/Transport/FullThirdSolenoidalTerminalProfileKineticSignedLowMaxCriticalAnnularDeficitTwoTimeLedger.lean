import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularUniformYoungWidthWindow
import Mathlib.Tactic

/-!
# Exact two-time annular deficit ledger and common kinetic-excess windows

The full physical annular deficit contains a *squared* kinetic excess and
its multiplication by the actual cubic-weighted Young-width integral. A
pointwise continuity theorem is insufficient for a family of varying radii.

We first factor the ORIGINAL deficit polynomial at two physical times. Its
variation is exactly a kinetic-mass increment times an explicit same-band
slope, minus the actual mass times the Young-width increment. This identifies
the additional coefficient that a uniform deficit-floor window must control.

Independently, the joint window from the preceding module yields a common
positive physical interval preserving an arbitrary strict kinetic-excess
margin for ALL 0 <= rho <= sigma <= R simultaneously. Neither conclusion
requires H4 or H6 regularity or an assumed source time derivative.

The final conditional ledger theorem records the exact sufficient criterion
for the deficit floor, rather than assuming an unproved cutoff-uniform bound
on the coefficient. Nothing here asserts a terminal H3 continuation theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeAnnularDeficitTwoTime244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceAnnularDeficitTwoTime244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The mean of two squared annular radii is nonnegative and bounded above
by the squared finite frequency ceiling. -/
theorem thirdFullKinetic_annularMeanSquare_bound244
    (rho sigma R : ℝ) (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma)
    (hUpper : sigma ≤ R) :
    0 ≤ (rho ^ 2 + sigma ^ 2) / 2 ∧
      (rho ^ 2 + sigma ^ 2) / 2 ≤ R ^ 2 := by
  have hSigma : 0 ≤ sigma := hRho.trans hOrder
  have hRhoSq : rho ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ hRho (hOrder.trans hUpper) 2
  have hSigmaSq : sigma ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ hSigma hUpper 2
  constructor
  · positivity
  · linarith only [hRhoSq, hSigmaSq]

/-- Exact algebraic factorization of the two-time kinetic deficit. The
baseline physical source term p is *fixed* between the two times; only
physical highpass mass m and genuine Young cost y change. -/
theorem thirdFullKinetic_deficitPolynomial_twoTimeIdentity244
    (a b w p m n y z : ℝ) :
    (w * (a * m - b) ^ 2 - m * (y + w * p)) -
      (w * (a * n - b) ^ 2 - n * (z + w * p)) =
    (m - n) * (w * a * (a * (m + n) - 2 * b) - (z + w * p)) -
      m * (y - z) := by
  ring

/-- The variation inequality is an algebraic consequence of the precise
factorization; it does not estimate the nonlinear Young term by a proxy. -/
theorem thirdFullKinetic_deficitPolynomial_twoTime_abs_bound244
    (a b w p m n y z : ℝ) (hm : 0 ≤ m) :
    |(w * (a * m - b) ^ 2 - m * (y + w * p)) -
      (w * (a * n - b) ^ 2 - n * (z + w * p))| ≤
      |m - n| *
        |w * a * (a * (m + n) - 2 * b) - (z + w * p)| +
      m * |y - z| := by
  rw [thirdFullKinetic_deficitPolynomial_twoTimeIdentity244]
  calc
    |(m - n) * (w * a * (a * (m + n) - 2 * b) - (z + w * p)) -
        m * (y - z)| ≤
        |(m - n) * (w * a * (a * (m + n) - 2 * b) - (z + w * p))| +
          |m * (y - z)| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              (abs_sub_le
                ((m - n) *
                  (w * a * (a * (m + n) - 2 * b) - (z + w * p)))
                (0 : ℝ) (m * (y - z)))
    _ = |m - n| *
          |w * a * (a * (m + n) - 2 * b) - (z + w * p)| +
        m * |y - z| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hm]

/-- The exact two-time identity for the ORIGINAL physical annular kinetic
deficit, including its kinetic-only Bernstein source and viscous baseline. -/
theorem thirdFullPhysical_actualAnnularDeficit_twoTimeIdentity244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b s t rho sigma : ℝ) :
    let a : ℝ := (rho ^ 2 + sigma ^ 2) / 2
    let w : ℝ := (rho ^ 2) ^ 3
    let B : ℝ := Real.sqrt (velocityH3Energy0At u b) *
      (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
        rho (velocityH3Energy0At u b))
    let P : ℝ := thirdFullPhysicalOuterViscousCapBase244 u b a
    let Ms : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
    let Mt : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho
    let Ys : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma
    let Yt : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 t rho sigma
    thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma -
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b t rho sigma =
      (Ms - Mt) * (w * a * (a * (Ms + Mt) - 2 * B) - (Yt + w * P)) -
        Ms * (Ys - Yt) := by
  change
    ((rho ^ 2) ^ 3 *
        (((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho -
          Real.sqrt (velocityH3Energy0At u b) *
            (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
              rho (velocityH3Energy0At u b))) ^ 2 -
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho *
        (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma +
          (rho ^ 2) ^ 3 * thirdFullPhysicalOuterViscousCapBase244 u b
            ((rho ^ 2 + sigma ^ 2) / 2))) -
    ((rho ^ 2) ^ 3 *
        (((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho -
          Real.sqrt (velocityH3Energy0At u b) *
            (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
              rho (velocityH3Energy0At u b))) ^ 2 -
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho *
        (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 t rho sigma +
          (rho ^ 2) ^ 3 * thirdFullPhysicalOuterViscousCapBase244 u b
            ((rho ^ 2 + sigma ^ 2) / 2))) = _
  exact thirdFullKinetic_deficitPolynomial_twoTimeIdentity244 _ _ _ _ _ _ _ _

/-- All coefficients are the original physical quantities. In particular
this bound isolates the ONLY extra annular-slope control needed after the
previous common mass/Young window theorem. -/
theorem thirdFullPhysical_actualAnnularDeficit_twoTimeAbsBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b s t rho sigma : ℝ) :
    let a : ℝ := (rho ^ 2 + sigma ^ 2) / 2
    let w : ℝ := (rho ^ 2) ^ 3
    let B : ℝ := Real.sqrt (velocityH3Energy0At u b) *
      (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
        rho (velocityH3Energy0At u b))
    let P : ℝ := thirdFullPhysicalOuterViscousCapBase244 u b a
    let Ms : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
    let Mt : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho
    let Ys : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma
    let Yt : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 t rho sigma
    |thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma -
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b t rho sigma| ≤
      |Ms - Mt| *
        |w * a * (a * (Ms + Mt) - 2 * B) - (Yt + w * P)| +
      Ms * |Ys - Yt| := by
  have hMs : 0 ≤ thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho :=
    sq_nonneg _
  change
    |((rho ^ 2) ^ 3 *
        (((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho -
          Real.sqrt (velocityH3Energy0At u b) *
            (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
              rho (velocityH3Energy0At u b))) ^ 2 -
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho *
        (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma +
          (rho ^ 2) ^ 3 * thirdFullPhysicalOuterViscousCapBase244 u b
            ((rho ^ 2 + sigma ^ 2) / 2))) -
    ((rho ^ 2) ^ 3 *
        (((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho -
          Real.sqrt (velocityH3Energy0At u b) *
            (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
              rho (velocityH3Energy0At u b))) ^ 2 -
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho *
        (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 t rho sigma +
          (rho ^ 2) ^ 3 * thirdFullPhysicalOuterViscousCapBase244 u b
            ((rho ^ 2 + sigma ^ 2) / 2)))| ≤ _
  exact thirdFullKinetic_deficitPolynomial_twoTime_abs_bound244 _ _ _ _ _ _ _ _ hMs

/-- The algebraic condition for preserving a positive deficit floor is
quantitative: a bounded two-time slope and the TWO independently controlled
actual increments suffice. Neither a new PDE hypothesis nor a uniform
cutoff-independent slope bound is smuggled into the conclusion. -/
theorem thirdFullKinetic_deficitPolynomial_floor_of_errors244
    (a b w p m n y z C H etaM etaY epsilon : ℝ)
    (hC : 0 ≤ C)
    (hm : 0 ≤ m) (hmCap : m ≤ H)
    (hMass : |m - n| ≤ etaM)
    (hYoung : |y - z| ≤ etaY)
    (hSlope : |w * a * (a * (m + n) - 2 * b) - (z + w * p)| ≤ C)
    (hEtaY : 0 ≤ etaY)
    (hPeak : 2 * epsilon ≤
      w * (a * n - b) ^ 2 - n * (z + w * p))
    (hBudget : etaM * C + H * etaY ≤ epsilon) :
    epsilon ≤ w * (a * m - b) ^ 2 - m * (y + w * p) := by
  have hD := thirdFullKinetic_deficitPolynomial_twoTime_abs_bound244
    a b w p m n y z hm
  have hTerm :
      |m - n| *
        |w * a * (a * (m + n) - 2 * b) - (z + w * p)| +
      m * |y - z| ≤ etaM * C + H * etaY := by
    apply add_le_add
    · exact (mul_le_mul_of_nonneg_left hSlope (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hMass hC)
    · exact (mul_le_mul_of_nonneg_left hYoung hm).trans
        (mul_le_mul_of_nonneg_right hmCap hEtaY)
  have hSmall := hD.trans (hTerm.trans hBudget)
  have hLow := (abs_le.mp hSmall).1
  linarith only [hLow, hPeak]

/-- The cutoff-independent physical highpass mass window preserves a
UNIFORM STRICT kinetic-excess margin for every annulus in a nondegenerate bounded family at once.
The positive lower radius excludes the zero-radius degenerate pair.
The same positive interval also retains the full nonlinear Young-width
variation bound, making it suitable for the exact deficit ledger. -/
theorem thirdFullPhysical_actualAnnularExcess_jointRightWindow244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b radiusMin R x margin toleranceY : ℝ)
    (hRadiusMin : 0 < radiusMin) (hRadiusMax : radiusMin ≤ R)
    (hx : x ∈ Set.Ioo (0 : ℝ) T)
    (hMargin : 0 < margin) (hTolY : 0 < toleranceY)
    (hExcess : ∀ rho sigma : ℝ,
      radiusMin ≤ rho → rho ≤ sigma → sigma ≤ R →
        Real.sqrt (velocityH3Energy0At u b) *
          (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
            rho (velocityH3Energy0At u b)) + 2 * margin ≤
        ((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho) :
    ∃ delta : ℝ, 0 < delta ∧ x + delta < T ∧
      ∀ s : ℝ, s ∈ Set.Icc x (x + delta) →
        (∀ rho sigma : ℝ, radiusMin ≤ rho → rho ≤ sigma → sigma ≤ R →
          Real.sqrt (velocityH3Energy0At u b) *
            (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
              rho (velocityH3Energy0At u b)) + margin ≤
          ((rho ^ 2 + sigma ^ 2) / 2) *
            thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho) ∧
        (∀ rho sigma : ℝ, radiusMin ≤ rho → rho ≤ sigma → sigma ≤ R →
          |thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma -
            thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma| <
            toleranceY) := by
  have hR : 0 ≤ R := hRadiusMin.le.trans hRadiusMax
  let C : ℝ := R ^ 2 + 1
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hEpsM : 0 < margin / C := div_pos hMargin hC
  obtain ⟨delta, hd, hEnd, hJoint⟩ :=
    thirdFullPhysical_actualAnnularCosts_jointRightWindow244
      hH3 R x toleranceY (margin / C) hR hx hTolY hEpsM
  refine ⟨delta, hd, hEnd, ?_⟩
  intro s hs
  constructor
  · intro rho sigma hRad hOrder hUpper
    have hRho : 0 ≤ rho := hRadiusMin.le.trans hRad
    let a : ℝ := (rho ^ 2 + sigma ^ 2) / 2
    have hA : 0 ≤ a ∧ a ≤ R ^ 2 :=
      thirdFullKinetic_annularMeanSquare_bound244 rho sigma R
        hRho hOrder hUpper
    have hDelta := (hJoint s hs).2 rho
    have hSmall :
        |thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho -
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho| <
          margin / C := hDelta
    have hMarginProd : R ^ 2 * (margin / C) < margin := by
      have hRaw : R ^ 2 * margin < margin * C := by
        dsimp only [C]
        nlinarith only [hMargin]
      have hEq : R ^ 2 * (margin / C) = (R ^ 2 * margin) / C := by ring
      rw [hEq]
      exact (div_lt_iff₀ hC).mpr hRaw
    have hAbsBound :
        a * |thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho -
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho| <
          margin := by
      calc
        a * |thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho -
            thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho| ≤
          a * (margin / C) :=
            mul_le_mul_of_nonneg_left hSmall.le hA.1
        _ ≤ R ^ 2 * (margin / C) :=
          mul_le_mul_of_nonneg_right hA.2 hEpsM.le
        _ < margin := hMarginProd
    have hMassSub :
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho ≤
        |thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho -
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho| := by
      have hAbs := neg_abs_le
        (thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho -
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho)
      linarith only [hAbs]
    have hLost :
        a * (thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho) <
        margin :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hMassSub hA.1)
        hAbsBound
    have hOld := hExcess rho sigma hRad hOrder hUpper
    let Ms : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
    let Mx : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
    let B : ℝ := Real.sqrt (velocityH3Energy0At u b) *
      (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
        rho (velocityH3Energy0At u b))
    change B + margin ≤ a * Ms
    change B + 2 * margin ≤ a * Mx at hOld
    -- Expose the linear cancellation instead of asking `nlinarith` to
    -- infer distributivity across the unexpanded frequency coefficient.
    rw [mul_sub] at hLost
    change a * Mx - a * Ms < margin at hLost
    have hBridge : B + margin ≤ a * Mx - margin := by
      linarith only [hOld]
    have hTransfer : a * Mx - margin ≤ a * Ms := by
      linarith only [hLost]
    exact hBridge.trans hTransfer
  · intro rho sigma hRad hOrder hUpper
    exact (hJoint s hs).1 rho sigma (hRadiusMin.le.trans hRad) hOrder hUpper

end
end PrimeTensor.FirstMonomialTriad
