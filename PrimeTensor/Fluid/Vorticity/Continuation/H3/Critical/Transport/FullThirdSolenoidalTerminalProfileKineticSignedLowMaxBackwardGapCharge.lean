import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxInGapAnnularCharge
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticAnnularDissipationRate
import Mathlib.Tactic

/-!
# Signed sixth-flux endpoint obstruction: backward kinetic PDE annular clock

The previous genuine physical in-gap charging theorem leaves an endpoint case:
its selected signed-flux observation may equal the RIGHT end of the original
kinetic gap. A forward annular interval rooted there cannot lie in that gap.

The preexisting kinetic-anchored finite-annulus dissipation Lipschitz modulus
works in BOTH time directions. At the original right endpoint y, retain the
same finite annulus N from the certified forward physical window, and propagate
its strict height BACKWARDS over

  epsilon = min ((y-x)/2) (H / (8*(Lambda+1))) > 0.

This supplies a physical integrated dissipation charge inside [x,y], with no
unproved backward full-H3 derivative, amplitude ceiling, terminal-uniform
width, or reselected observation time. The final closed-gap theorem removes
its earlier right-endpoint branch altogether, under explicit finite physical
H3 dissipation integrability and the kinetic anchor.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators FourierTransform SchwartzMap LineDeriv Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

private abbrev BA3 := PrimeTensor.Axis Depth.three
private abbrev BV3 := H3FourierPoint3

noncomputable local instance axisFintypeSignedBackwardGap244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The EXACT backward in-gap persistence width for a certified finite
annulus, using the existing kinetic-only finite-annulus physical PDE rate. -/
noncomputable def thirdFullKineticSignedLowMaxBackwardGapWidth244
    (R N : ℕ) (E H x y : ℝ) : ℝ :=
  min ((y - x) / 2)
    (H / (8 * (
      thirdFullPhysicalKineticLowBandDissipationRate244 N E +
      thirdFullPhysicalKineticLowBandDissipationRate244 R E + 1)))

/-- The kinetic clock has enough room on the original gap to preserve a
positive quarter-height annular mass, even when its anchor is y itself. -/
theorem thirdFullKineticSignedLowMaxBackwardGapWidth_budget244
    (R N : ℕ) (E H x y : ℝ)
    (hH : 0 < H) (hxy : x < y) :
    let Lambda : ℝ :=
      thirdFullPhysicalKineticLowBandDissipationRate244 N E +
      thirdFullPhysicalKineticLowBandDissipationRate244 R E
    let epsilon : ℝ :=
      thirdFullKineticSignedLowMaxBackwardGapWidth244 R N E H x y
    0 < epsilon ∧ x < y - epsilon ∧
      Lambda * epsilon ≤ H / 8 := by
  let Lambda : ℝ :=
    thirdFullPhysicalKineticLowBandDissipationRate244 N E +
    thirdFullPhysicalKineticLowBandDissipationRate244 R E
  let epsilon : ℝ :=
    thirdFullKineticSignedLowMaxBackwardGapWidth244 R N E H x y
  have hLambda : 0 ≤ Lambda :=
    add_nonneg
      (thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 N E)
      (thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 R E)
  have hOne : 0 < Lambda + 1 := by linarith only [hLambda]
  have hHalf : 0 < (y - x) / 2 := by linarith only [hxy]
  have hRatio : 0 < H / (8 * (Lambda + 1)) := by positivity
  have hPos : 0 < epsilon := by
    change 0 < min ((y - x) / 2) (H / (8 * (Lambda + 1)))
    exact lt_min hHalf hRatio
  have hHalfBound : epsilon ≤ (y - x) / 2 := by
    change min ((y - x) / 2) (H / (8 * (Lambda + 1))) ≤ _
    exact min_le_left _ _
  have hRateBound : epsilon ≤ H / (8 * (Lambda + 1)) := by
    change min ((y - x) / 2) (H / (8 * (Lambda + 1))) ≤ _
    exact min_le_right _ _
  have hCost : Lambda * epsilon ≤ H / 8 := by
    calc
      Lambda * epsilon ≤ (Lambda + 1) * epsilon :=
        mul_le_mul_of_nonneg_right (by linarith : Lambda ≤ Lambda + 1) hPos.le
      _ ≤ (Lambda + 1) * (H / (8 * (Lambda + 1))) :=
        mul_le_mul_of_nonneg_left hRateBound hOne.le
      _ = H / 8 := by
        field_simp [ne_of_gt hOne]
  exact ⟨hPos, by linarith only [hHalfBound, hxy], hCost⟩

/-- BACKWARD persistence at the SAME original kinetic right endpoint.
The already certified *forward* physical interval is used only to obtain
its finite outer radius and strict initial annulus. The actual persistence
in the preceding gap follows from the genuine kinetic-anchored bidirectional
finite-annulus PDE Lipschitz theorem, not from the forward window. -/
theorem thirdFullPhysical_signedLowMax_rightEndpoint_backwardGapCharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R : ℕ) (H x y : ℝ)
    (hH : 0 < H) (hx : x ∈ Set.Ioo b T)
    (hy : y ∈ Set.Ioo b T) (hxy : x < y)
    (hWindow : ThirdFullKineticSignedLowMaxCertifiedAnnularWindow244
      hH3 R H y) :
    ∃ (N : ℕ) (epsilon : ℝ), R ≤ N ∧
      epsilon = thirdFullKineticSignedLowMaxBackwardGapWidth244
        R N (velocityH3Energy0At u b) H x y ∧
      0 < epsilon ∧ x < y - epsilon ∧
      (∀ r : ℝ, r ∈ Set.Icc (y - epsilon) y →
        H / 4 <
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) -
          h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r)) ∧
      epsilon * (H / 4) ≤
        ∫ r in x..y, velocityH3DissipationAt u r ∂volume := by
  obtain ⟨N, K, C, delta, hRN, _hK, _hC, _hDelta, _hDeltaOne,
    _hDeltaT, _hState, _hSource, hAt, _hWidth, _hFloor, _hCost⟩ := hWindow
  let E : ℝ := velocityH3Energy0At u b
  let Lambda : ℝ :=
    thirdFullPhysicalKineticLowBandDissipationRate244 N E +
    thirdFullPhysicalKineticLowBandDissipationRate244 R E
  let epsilon : ℝ :=
    thirdFullKineticSignedLowMaxBackwardGapWidth244 R N E H x y
  obtain ⟨hEps, hLeft, hCostBound⟩ :=
    thirdFullKineticSignedLowMaxBackwardGapWidth_budget244
      R N E H x y hH hxy
  have hLambda : 0 ≤ Lambda :=
    add_nonneg
      (thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 N E)
      (thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 R E)
  let U : ℝ → H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3
  let Ann : ℝ → ℝ := fun r =>
    h3PathActualLowRadialDissipation244 ((N : ℝ) + 1) (U r) -
    h3PathActualLowRadialDissipation244 ((R : ℝ) + 1) (U r)
  have hAtAnn : H / 2 < Ann y := hAt
  have hFloor (r : ℝ) (hr : r ∈ Set.Icc (y - epsilon) y) :
      H / 4 < Ann r := by
    have hrTail : r ∈ Set.Ioo b T := by
      constructor
      · have hxLt : b < x := hx.1
        linarith only [hxLt, hLeft, hr.1]
      · exact lt_of_le_of_lt hr.2 hy.2
    have hLip := thirdFullPhysical_kineticNaturalAnnularDissipationLipschitz244
      hH3 hClass b hb R N r y hrTail hy hr.2
    change |Ann r - Ann y| ≤ Lambda * (y - r) at hLip
    have hDifference : Ann y - Ann r ≤ Lambda * (y - r) := by
      calc
        Ann y - Ann r ≤ |Ann y - Ann r| := le_abs_self _
        _ = |Ann r - Ann y| := abs_sub_comm _ _
        _ ≤ Lambda * (y - r) := hLip
    have hTime : y - r ≤ epsilon := by linarith only [hr.1]
    have hBound : Lambda * (y - r) ≤ H / 8 :=
      (mul_le_mul_of_nonneg_left hTime hLambda).trans hCostBound
    linarith only [hAtAnn, hDifference, hBound, hH]
  have hxClass : x ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hx.1, hx.2⟩
  have hyClass : y ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hy.1, hy.2⟩
  have hSub : Set.Icc (y - epsilon) y ⊆ Set.Ioo a T := by
    intro r hr
    exact ⟨lt_trans hxClass.1 (lt_of_lt_of_le hLeft hr.1),
      lt_of_le_of_lt hr.2 hyClass.2⟩
  have hAnnCont : ContinuousOn Ann (Set.Ioo a T) :=
    h3Path_finiteAnnularDissipation_continuousOn244
      hH3 hClass ((R : ℝ) + 1) ((N : ℝ) + 1)
      (by positivity) (by positivity)
  have hAnnInt : IntervalIntegrable Ann volume (y - epsilon) y :=
    (hAnnCont.mono hSub).intervalIntegrable_of_Icc
      (by linarith only [hEps])
  have hAnnCost : epsilon * (H / 4) ≤
      ∫ r in (y - epsilon)..y, Ann r ∂volume := by
    have h := h3Path_localPositiveHeight_forces_integratedCost244
      Ann (y - epsilon) y (H / 4)
      (by linarith only [hEps]) hAnnInt
      (fun r hr => (hFloor r hr).le)
    calc
      epsilon * (H / 4) = (y - (y - epsilon)) * (H / 4) := by ring
      _ ≤ ∫ r in (y - epsilon)..y, Ann r ∂volume := h
  let D : ℝ → ℝ := velocityH3DissipationAt u
  have hDGap : IntervalIntegrable D volume x y := by
    apply hDInt.mono_set
    intro r hr
    have hrIcc : r ∈ Set.Icc x y := by
      simpa only [Set.uIcc_of_le hxy.le] using hr
    have hrAll : r ∈ Set.Icc a T :=
      ⟨hxClass.1.le.trans hrIcc.1, hrIcc.2.trans hyClass.2.le⟩
    simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hrAll
  have hDWin : IntervalIntegrable D volume (y - epsilon) y := by
    apply hDInt.mono_set
    intro r hr
    have hrIcc : r ∈ Set.Icc (y - epsilon) y := by
      rcases Set.mem_uIcc.mp hr with hForward | hReverse
      · exact hForward
      · exfalso
        have hStrict : y - epsilon < y := by linarith only [hEps]
        exact (not_le_of_gt hStrict) (hReverse.1.trans hReverse.2)
    have hrAll : r ∈ Set.Icc a T :=
      ⟨hxClass.1.le.trans (hLeft.le.trans hrIcc.1),
        hrIcc.2.trans hyClass.2.le⟩
    simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hrAll
  have hAnnLeD : (∫ r in (y - epsilon)..y, Ann r ∂volume) ≤
      ∫ r in (y - epsilon)..y, D r ∂volume := by
    apply intervalIntegral.integral_mono_on
      (by linarith only [hEps]) hAnnInt hDWin
    intro r hr
    have hrClass : r ∈ Set.Ioo a T := hSub hr
    exact h3Path_actualFiniteAnnulusDissipation_le_fullAt244
      hH3 hClass r hrClass ((R : ℝ) + 1) ((N : ℝ) + 1)
  have hNonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc x y)] D := by
    filter_upwards [] with r
    exact velocityH3DissipationAt_nonneg u r
  have hGapCost : (∫ r in (y - epsilon)..y, D r ∂volume) ≤
      ∫ r in x..y, D r ∂volume :=
    intervalIntegral.integral_mono_interval
      hLeft.le (by linarith only [hEps]) le_rfl hNonneg hDGap
  refine ⟨N, epsilon, hRN, rfl, hEps, hLeft, ?_, ?_⟩
  · intro r hr
    exact hFloor r hr
  · exact (hAnnCost.trans hAnnLeD).trans hGapCost

/-- The previously open RIGHT-ENDPOINT case is now eliminated using the
physical kinetic finite-annulus PDE rate backwards in time. On EVERY closed
strict kinetic gap, the genuine signed sixth-flux excursion pays either
its correctly amplitude-weighted recovery/source clock OR the actual
integral of physical H3 dissipation on that VERY SAME gap.

The resulting width is positive but may depend on the selected radius,
state, observation time and gap. No radius-uniform continuation claim. -/
theorem thirdFullPhysical_strictGap_signedLowMax_clockOrFullGapCharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R : ℕ) (x y : ℝ)
    (hx : x ∈ Set.Ioo b T) (hy : y ∈ Set.Ioo b T) (hxy : x < y)
    (s t : ℝ) (hs : s ∈ Set.Icc x y) (ht : t ∈ Set.Icc x y)
    (v w : BA3 → SchwartzMap BV3 ℂ)
    (V W : H3SpectralVelocityState)
    (hv : ∀ j : BA3,
      (V (h3ClassicalizationFinOfAxis j) : BV3 → ℂ) =ᵐ[volume]
        (fun ξ : BV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (hw : ∀ j : BA3,
      (W (h3ClassicalizationFinOfAxis j) : BV3 → ℂ) =ᵐ[volume]
        (fun ξ : BV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (w j)) ξ))
    (eta : ℝ) (hEta : 0 < eta)
    (hAdverse : eta ≤
      |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v).im -
        (thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w).im|) :
    (eta / 2 < thirdFullKineticSignedLowMaxFluxClockWeight244 R V W *
      (‖V - h3AuditActualSpectralVelocityTotal hH3 t‖ +
        thirdFullFiniteBandH3WeightCeiling244 R *
          (∫ r in x..y,
            ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) +
        ‖h3AuditActualSpectralVelocityTotal hH3 s - W‖)) ∨
    (∃ z epsilon : ℝ, (z = t ∨ z = s) ∧ 0 < epsilon ∧
      ((z + epsilon < y) ∨ (z = y ∧ x < y - epsilon)) ∧
      epsilon *
        (thirdFullKineticSignedLowMaxPDEViscousHeight244 R V W eta / 4) ≤
        ∫ r in x..y, velocityH3DissipationAt u r ∂volume) := by
  have hxClass : x ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hx.1, hx.2⟩
  have hyClass : y ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hy.1, hy.2⟩
  have hCases :=
    thirdFullPhysical_strictGap_signedLowMax_clockOrEndpointOrInGap244
      hH3 hClass R x y hxClass hyClass hxy s t hs ht
      v w V W hv hw eta hEta hAdverse
  rcases hCases with hClock | hEndpoint | hInside
  · exact Or.inl hClock
  · right
    obtain ⟨z, hzTime, hzy, hWindow⟩ := hEndpoint
    subst z
    have hH : 0 < thirdFullKineticSignedLowMaxPDEViscousHeight244 R V W eta :=
      (thirdFullKineticSignedLowMaxPDEViscousHeight_budget244
        R V W eta hEta).1
    obtain ⟨N, epsilon, _hRN, _hWidth, hEps, hLeft, _hFloor, hCost⟩ :=
      thirdFullPhysical_signedLowMax_rightEndpoint_backwardGapCharge244
        hH3 hClass hDInt b hb R
        (thirdFullKineticSignedLowMaxPDEViscousHeight244 R V W eta)
        x y hH hx hy hxy hWindow
    exact ⟨y, epsilon, hzTime, hEps,
      Or.inr ⟨rfl, hLeft⟩, hCost⟩
  · right
    obtain ⟨z, hzTime, hzy, hInGap⟩ := hInside
    have hzGap : z ∈ Set.Icc x y := by
      rcases hzTime with rfl | rfl
      · exact ht
      · exact hs
    obtain ⟨epsilon, hEps, hEnd, hCost⟩ :=
      thirdFullPhysical_signedLowMax_inGapCharge_le_fullGapDissipation244
        hH3 hClass hDInt R
        (thirdFullKineticSignedLowMaxPDEViscousHeight244 R V W eta)
        x z y hxClass hyClass hxy.le hzGap hInGap
    exact ⟨z, epsilon, hzTime, hEps, Or.inl hEnd, hCost⟩

/-- A precise cofinal compression consequence, with the height kept.
Vanishing genuine physical gap dissipation implies vanishing width-times-height
cost for *any* selected flux-induced certified windows inside those gaps.
This does not imply widths vanish unless the height has a uniform positive
lower bound, which the growing radius/amplitude coefficient does not give. -/
theorem thirdFullKinetic_signedLowMax_cofinalWeightedWidthCompression244
    (epsilon height cost : ℕ → ℝ)
    (hEps : ∀ k : ℕ, 0 ≤ epsilon k)
    (hHeight : ∀ k : ℕ, 0 ≤ height k)
    (hCharge : ∀ k : ℕ, epsilon k * (height k / 4) ≤ cost k)
    (hCost : Tendsto cost atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun k : ℕ => epsilon k * (height k / 4))
      atTop (𝓝 (0 : ℝ)) := by
  apply squeeze_zero'
    (Filter.Eventually.of_forall (fun k =>
      mul_nonneg (hEps k) (div_nonneg (hHeight k) (by norm_num))))
    (Filter.Eventually.of_forall hCharge)
    hCost

end
end PrimeTensor.FirstMonomialTriad
