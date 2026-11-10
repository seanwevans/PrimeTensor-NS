import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCertifiedPolynomialEscape
import Mathlib.Tactic

/-!
# Signed sixth flux: an actual annular eleventh-power frequency charge

The certified annulus of the preceding theorem has an actual H3 dissipation
peak and a persistent positive in-gap charge at the SAME outer radius Q.
The earlier degree-twelve bound counts all finite low bands up to an INDEX.
A single certified annulus uses only the two endpoint kinetic rates. Here
we derive their sharper eleventh-power bound, and recover the corresponding
physical dissipation/frequency obstruction from the original in-gap width.

For energy anchor E0 >= 0, put
  K(E0) = 1 + 192 sqrt(E0) (sqrt(E0) + 54 E0).
If 16 D < (y-x) h, where h is the positive capped physical height floor,
then every certified annulus with its own width and gap charge satisfies
  h^2 / (32 K(E0)) <= (Q+1)^11 D.

The original separated kinetic gaps have D(k) -> 0. Therefore for EVERY
fixed B, sufficiently late adverse observations with the tenth-power
residual excluded and with subcritical relative density carry a CERTIFIED
annular physical peak at SOME Q > B. The witness keeps its in-gap integral
charge and its quantitative eleventh-power frequency bound.

No assumption that k^12 D(k) -> 0, no terminal H3 trace, and no naked
natural-number existential witness are introduced.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- A SINGLE kinetic Bernstein/source band costs one fewer radial power
than the sum over all bands below the moving index. -/
theorem thirdFullKinetic_signedLowMax_oneBand_le_eleventh244
    (Q : ℕ) (E0 : ℝ) (hE : 0 ≤ E0) :
    thirdFullKineticSignedLowMaxOneRadiusBandRate244 Q E0 ≤
      (96 * Real.sqrt E0 * (Real.sqrt E0 + 54 * E0)) *
        ((Q : ℝ) + 1) ^ 11 := by
  let r : ℝ := (Q : ℝ) + 1
  let s : ℝ := Real.sqrt E0
  let S : ℝ := thirdFullPhysicalKineticLowBandSourceCeiling244 r E0
  let F : ℝ := 24 * (r + 1) ^ 2 * r ^ 6 * s
  have hr : 1 ≤ r := by
    dsimp only [r]
    have hNat : 0 ≤ (Q : ℝ) := Nat.cast_nonneg Q
    linarith only [hNat]
  have hs : 0 ≤ s := Real.sqrt_nonneg E0
  have hF0 : 0 ≤ F := by dsimp only [F]; positivity
  have hSource : S ≤ r ^ 2 * s + 54 * r ^ 3 * E0 := by
    simpa only [S, r, s] using
      thirdFullKinetic_signedLowMax_sourceCeiling_le_polynomial244 r E0 hr hE
  have hSource0 : 0 ≤ r ^ 2 * s + 54 * r ^ 3 * E0 := by positivity
  have hDouble : r + 1 ≤ 2 * r := by linarith only [hr]
  have hQuad : (r + 1) ^ 2 ≤ 4 * r ^ 2 := by
    calc
      (r + 1) ^ 2 ≤ (2 * r) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hDouble 2
      _ = 4 * r ^ 2 := by ring
  have hF : F ≤ 96 * r ^ 8 * s := by
    dsimp only [F]
    calc
      24 * (r + 1) ^ 2 * r ^ 6 * s =
          (24 * r ^ 6 * s) * (r + 1) ^ 2 := by ring
      _ ≤ (24 * r ^ 6 * s) * (4 * r ^ 2) :=
        mul_le_mul_of_nonneg_left hQuad (by positivity)
      _ = 96 * r ^ 8 * s := by ring
  have hR23 : r ^ 2 ≤ r ^ 3 :=
    pow_le_pow_right₀ hr (by norm_num)
  have hS : r ^ 2 * s + 54 * r ^ 3 * E0 ≤
      r ^ 3 * (s + 54 * E0) := by
    calc
      r ^ 2 * s + 54 * r ^ 3 * E0 ≤
          r ^ 3 * s + 54 * r ^ 3 * E0 :=
        add_le_add (mul_le_mul_of_nonneg_right hR23 hs) le_rfl
      _ = r ^ 3 * (s + 54 * E0) := by ring
  have hCoeff0 : 0 ≤ 96 * r ^ 8 * s := by positivity
  calc
    thirdFullKineticSignedLowMaxOneRadiusBandRate244 Q E0 = F * S := by
      unfold thirdFullKineticSignedLowMaxOneRadiusBandRate244
      dsimp only [F, S, r, s]
      ring
    _ ≤ F * (r ^ 2 * s + 54 * r ^ 3 * E0) :=
      mul_le_mul_of_nonneg_left hSource hF0
    _ ≤ (96 * r ^ 8 * s) * (r ^ 2 * s + 54 * r ^ 3 * E0) :=
      mul_le_mul_of_nonneg_right hF hSource0
    _ ≤ (96 * r ^ 8 * s) * (r ^ 3 * (s + 54 * E0)) :=
      mul_le_mul_of_nonneg_left hS hCoeff0
    _ = (96 * s * (s + 54 * E0)) * r ^ 11 := by ring

/-- The TWO actual annular endpoint kinetic rates, including the positive
unit rate, are bounded by K(E0) times the ELEVENTH power of the chosen
outer radius. The actual peak-carrying outer cutoff Q is not arbitrary. -/
theorem thirdFullKinetic_signedLowMax_twoAnnularRates_le_eleventh244
    (R Q : ℕ) (E0 : ℝ) (hE : 0 ≤ E0) (hRQ : R ≤ Q) :
    thirdFullKineticSignedLowMaxKineticAnnulusRate244 R Q E0 + 1 ≤
      thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0 *
        ((Q : ℝ) + 1) ^ 11 := by
  let B : ℝ := thirdFullKineticSignedLowMaxOneRadiusBandRate244 Q E0
  let r : ℝ := (Q : ℝ) + 1
  let s : ℝ := Real.sqrt E0
  have hR : thirdFullPhysicalKineticLowBandDissipationRate244 R E0 ≤ B :=
    thirdFullKinetic_signedLowMax_bandRate_le_oneRadius244 R Q E0 hE hRQ
  have hQ : thirdFullPhysicalKineticLowBandDissipationRate244 Q E0 ≤ B :=
    thirdFullKinetic_signedLowMax_bandRate_le_oneRadius244 Q Q E0 hE le_rfl
  have hBand : B ≤ 96 * s * (s + 54 * E0) * r ^ 11 := by
    simpa only [B, r, s] using
      thirdFullKinetic_signedLowMax_oneBand_le_eleventh244 Q E0 hE
  have hTwo : 2 * B ≤ 192 * s * (s + 54 * E0) * r ^ 11 := by
    calc
      2 * B ≤ 2 * (96 * s * (s + 54 * E0) * r ^ 11) :=
        mul_le_mul_of_nonneg_left hBand (by norm_num)
      _ = 192 * s * (s + 54 * E0) * r ^ 11 := by ring
  have hr : 1 ≤ r := by
    dsimp only [r]
    have hNat : 0 ≤ (Q : ℝ) := Nat.cast_nonneg Q
    linarith only [hNat]
  have hOne : 1 ≤ r ^ 11 := one_le_pow₀ hr
  calc
    thirdFullKineticSignedLowMaxKineticAnnulusRate244 R Q E0 + 1 =
        thirdFullPhysicalKineticLowBandDissipationRate244 R E0 +
          thirdFullPhysicalKineticLowBandDissipationRate244 Q E0 + 1 := by
      unfold thirdFullKineticSignedLowMaxKineticAnnulusRate244
      ring
    _ ≤ 2 * B + 1 := by linarith only [hR, hQ]
    _ ≤ 192 * s * (s + 54 * E0) * r ^ 11 + r ^ 11 :=
      add_le_add hTwo hOne
    _ = thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0 *
        ((Q : ℝ) + 1) ^ 11 := by
      unfold thirdFullKineticSignedLowMaxCriticalTwelveCoeff244
      dsimp only [r, s]
      ring

/-- Under subcritical relative gap dissipation, a certified annulus's
ACTUAL symmetric persistence width is necessarily in its kinetic-rate
branch. The peak-carrying cutoff must pay the eleventh-power frequency
charge on the SAME original physical gap. -/
theorem thirdFullKinetic_signedLowMax_certifiedWidth_eleventhCharge244
    (R Q : ℕ) (E0 H h x y w D : ℝ)
    (hE : 0 ≤ E0) (hH : 0 < H) (hh : 0 < h)
    (hHeight : h ≤ H) (hxy : x < y) (hRQ : R ≤ Q)
    (hD : 0 ≤ D)
    (hw : w = thirdFullKineticSignedLowMaxSymmetricGapWidth244
      R Q E0 H x y)
    (hCost : w * (H / 4) ≤ D)
    (hLowDensity : 16 * D < (y - x) * h) :
    h ^ 2 / (32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0) ≤
      ((Q : ℝ) + 1) ^ 11 * D := by
  let L : ℝ := thirdFullKineticSignedLowMaxKineticAnnulusRate244 R Q E0
  have hL : 0 ≤ L :=
    thirdFullKinetic_signedLowMax_kineticAnnulusRate_nonneg244 R Q E0
  have hPeakCost :
      min ((y - x) / 4) (H / (8 * (L + 1))) * (H / 4) ≤ D := by
    rw [hw] at hCost
    simpa only [thirdFullKineticSignedLowMaxSymmetricGapWidth244, L] using hCost
  have hAlt := thirdFullKinetic_signedLowMax_symmetricCharge_clockOrRate244
    x y H L D hH hL hxy hPeakCost
  have hGap0 : 0 ≤ y - x := sub_nonneg.mpr hxy.le
  have hLowH : 16 * D < (y - x) * H :=
    lt_of_lt_of_le hLowDensity (mul_le_mul_of_nonneg_left hHeight hGap0)
  have hRate : H ^ 2 ≤ 32 * (L + 1) * D := by
    rcases hAlt with hClock | hRate
    · exact False.elim ((not_lt_of_ge hClock) hLowH)
    · exact hRate
  have hCap : L + 1 ≤
      thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0 *
        ((Q : ℝ) + 1) ^ 11 := by
    simpa only [L] using
      thirdFullKinetic_signedLowMax_twoAnnularRates_le_eleventh244 R Q E0 hE hRQ
  have hSquare : h ^ 2 ≤ H ^ 2 :=
    pow_le_pow_left₀ hh.le hHeight 2
  have hK : 0 < thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0 :=
    thirdFullKinetic_signedLowMax_criticalTwelveCoeff_pos244 E0 hE
  have hDen : 0 < 32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0 := by
    positivity
  apply (div_le_iff₀ hDen).mpr
  calc
    h ^ 2 ≤ H ^ 2 := hSquare
    _ ≤ 32 * (L + 1) * D := hRate
    _ ≤ 32 * (thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0 *
        ((Q : ℝ) + 1) ^ 11) * D := by
      have hMul := mul_le_mul_of_nonneg_right hCap hD
      nlinarith only [hMul]
    _ = (((Q : ℝ) + 1) ^ 11 * D) *
        (32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0) := by
      ring

/-- The original gamma-free physical carrier, under the actual energy cap
and subcritical relative gap dissipation, produces a genuine finite annular
peak whose selected outer radius pays an ELEVENTH-power frequency charge.
No twelfth-power rate-decay assumption or k-dependent threshold is used. -/
theorem thirdFullPhysical_signedLowMax_lowDensity_certifiedEleventh244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R : ℕ) (x y t : ℝ)
    (hx : x ∈ Set.Ioo b T) (hy : y ∈ Set.Ioo b T)
    (hxy : x < y) (ht : t ∈ Set.Icc x y)
    (eta E : ℝ) (hEta : 0 < eta) (hE : 0 ≤ E)
    (hEnergyCap : velocityH3EnergyAt u t ≤ E)
    (hTail : eta / 2 ≤
      thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
        (velocityH3EnergyAt u t) *
        ‖thirdFullSpectralVelocityHighRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 t)‖ ^ 2)
    (hLowDensity :
      16 * (∫ r in x..y, velocityH3DissipationAt u r ∂volume) <
        (y - x) * thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E) :
    let H := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
      R eta (velocityH3EnergyAt u t)
    let h := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
    let E0 := velocityH3Energy0At u b
    let D := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
    ∃ (Q : ℕ) (w : ℝ), R ≤ Q ∧ 0 < w ∧
      w = thirdFullKineticSignedLowMaxSymmetricGapWidth244 R Q E0 H x y ∧
      H / 2 <
        h3PathActualLowRadialDissipation244 ((Q : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) ∧
      w * (H / 4) ≤ D ∧
      h ^ 2 / (32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0) ≤
        ((Q : ℝ) + 1) ^ 11 * D := by
  let H := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
    R eta (velocityH3EnergyAt u t)
  let h := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
  let E0 := velocityH3Energy0At u b
  let D := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
  change ∃ (Q : ℕ) (w : ℝ), R ≤ Q ∧ 0 < w ∧
    w = thirdFullKineticSignedLowMaxSymmetricGapWidth244 R Q E0 H x y ∧
    H / 2 <
      h3PathActualLowRadialDissipation244 ((Q : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) -
      h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) ∧
    w * (H / 4) ≤ D ∧
    h ^ 2 / (32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0) ≤
      ((Q : ℝ) + 1) ^ 11 * D
  obtain ⟨Q, w, hRQ, hw, hwEq, _hSide, hPeak, hCost, _hFork⟩ :=
    thirdFullPhysical_signedLowMax_gammaFreeTail_certifiedCriticalTwelve244
      hH3 hClass hDInt b hb R 0 x y t hx hy hxy ht
      eta E hEta hE hEnergyCap hTail
  have hh : 0 < h :=
    thirdFullKinetic_signedLowMax_cappedLinearFloor_pos244 eta E hEta hE
  have hEnergy : 0 ≤ velocityH3EnergyAt u t := by
    have hOne := one_le_velocityH3EnergyAt u t
    linarith only [hOne]
  have hHeight : h ≤ H :=
    thirdFullKinetic_signedLowMax_linearHeight_ge_cappedFloor244
      R eta (velocityH3EnergyAt u t) E hEta hEnergy hEnergyCap
  have hH : 0 < H := lt_of_lt_of_le hh hHeight
  have hD : 0 ≤ D :=
    intervalIntegral.integral_nonneg hxy.le
      (fun r _ => velocityH3DissipationAt_nonneg u r)
  have hE0 : 0 ≤ E0 := velocityH3Energy0At_nonneg u b
  have hCharge :=
    thirdFullKinetic_signedLowMax_certifiedWidth_eleventhCharge244
      R Q E0 H h x y w D hE0 hH hh hHeight hxy hRQ hD hwEq hCost
      hLowDensity
  exact ⟨Q, w, hRQ, hw, hwEq, hPeak, hCost, hCharge⟩


/-- The genuine signed-sixth-flux cofinal conclusion now contains an
ELEVENTH-power frequency charge for the SAME certified annular peak.
Only low relative gap density is imposed; no twelfth-power rate decay or
index-dependent cutoff condition is required. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_trueCertifiedEleventh244
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
    (J : ℕ) (E epsilon : ℝ) (hE : 0 ≤ E) (hEpsilon : 0 < epsilon) :
    ∀ᶠ k : ℕ in atTop, ∀ (R : ℕ) (t : ℝ),
      let x := tau (v k) + delta (v k)
      let y := tau (v (k + 1))
      let H := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
        R eta (velocityH3EnergyAt u t)
      let h := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
      let E0 := velocityH3Energy0At u b
      let D := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
      t ∈ Set.Icc x y →
      eta < -velocityH3TransportDerivative3At u t →
      ¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
        hH3 R J E eta epsilon x y t →
      16 * D < (y - x) * h →
      ∃ (Q : ℕ) (w : ℝ), R ≤ Q ∧ 0 < w ∧
        w = thirdFullKineticSignedLowMaxSymmetricGapWidth244
          R Q E0 H x y ∧
        H / 2 <
          h3PathActualLowRadialDissipation244 ((Q : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) -
          h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) ∧
        w * (H / 4) ≤ D ∧
        h ^ 2 / (32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0) ≤
          ((Q : ℝ) + 1) ^ 11 * D := by
  have hRadius := thirdFullPhysical_kineticGaps_signedLowMax_radiusEnergyEscape244
    hH3 hClass hDInt b hb M tau N delta v hLimit hSeparated
    hWindows eta hEta J E epsilon hE hEpsilon
  filter_upwards [hRadius] with k hkRadius
  intro R t
  dsimp only
  intro ht hAdverse hNoResidual hLowDensity
  let x : ℝ := tau (v k) + delta (v k)
  let y : ℝ := tau (v (k + 1))
  let X : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let A : ℝ := thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
    (velocityH3EnergyAt u t)
  let H : ℝ := ‖thirdFullSpectralVelocityHighRadialApply244 R X‖
  let Bad : Prop := ThirdFullKineticSignedLowMaxTenthPowerResidual244
    hH3 R J E eta epsilon x y t
  have hCap : velocityH3EnergyAt u t ≤ E := by
    by_contra hn
    have hBadEnergy : E < velocityH3EnergyAt u t := lt_of_not_ge hn
    apply hNoResidual
    unfold ThirdFullKineticSignedLowMaxTenthPowerResidual244
    exact Or.inr (Or.inl (Or.inr (Or.inl hBadEnergy)))
  have hEach (gamma : ℝ) (hGamma : 0 < gamma) :
      eta / 2 < A * (H + gamma) ^ 2 ∨ Bad := by
    have hPrev := hkRadius R gamma hGamma t ht hAdverse
    change (eta / 2 < ((2 * Real.pi) ^ 7 / 3) *
      (1944 * h3SobolevFirstMomentDeweightingConstant *
        (velocityH3EnergyAt u t + 1) * (H + gamma) ^ 2)) ∨ Bad at hPrev
    rcases hPrev with hTail | hOther
    · left
      simpa only [A, H, thirdFullKineticSignedLowMaxPhysicalHighTailFactor244,
        mul_assoc] using hTail
    · exact Or.inr hOther
  have hZero := thirdFull_scalar_signedLowMax_removePositiveTailTolerance244
    (eta / 2) A H Bad hEach
  have hTail : eta / 2 ≤
      thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
        (velocityH3EnergyAt u t) *
        ‖thirdFullSpectralVelocityHighRadialApply244 R X‖ ^ 2 := by
    rcases hZero with hHigh | hOther
    · simpa only [A, H] using hHigh
    · exact False.elim (hNoResidual hOther)
  have hx : x ∈ Set.Ioo b T := by
    obtain ⟨hTime, hw⟩ := hWindows k
    rcases hw with ⟨_, hdelta, _, hEnd, _, _⟩
    exact ⟨by linarith only [hTime.1, hdelta], hEnd⟩
  have hy : y ∈ Set.Ioo b T := (hWindows (k + 1)).1
  have hxy : x < y := hSeparated k (k + 1) (Nat.lt_succ_self k)
  exact thirdFullPhysical_signedLowMax_lowDensity_certifiedEleventh244
    hH3 hClass hDInt b hb R x y t hx hy hxy ht
    eta E hEta hE hCap (by simpa only [X] using hTail)
    hLowDensity

/-- A fixed outer cutoff cannot pay a positive eleventh-power charge
on a sequence of actual gap costs converging to zero. The conclusion
uses the SAME selected radius Q as the given quantitative certificate. -/
theorem thirdFullKinetic_signedLowMax_eleventhCharge_forcesCofinalRadius244
    (D : ℕ → ℝ) (K h : ℝ) (hK : 0 < K) (hh : 0 < h)
    (hDZero : Tendsto D atTop (𝓝 (0 : ℝ))) (B : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ Q : ℕ,
      0 ≤ D k →
      h ^ 2 / (32 * K) ≤ ((Q : ℝ) + 1) ^ 11 * D k →
      B < Q := by
  have hDen : 0 < 32 * K := by positivity
  have hTarget : 0 < h ^ 2 / (32 * K) :=
    div_pos (pow_pos hh 2) hDen
  have hScaled :
      Tendsto (fun k : ℕ => ((B : ℝ) + 1) ^ 11 * D k)
        atTop (𝓝 (0 : ℝ)) := by
    have hMul := (tendsto_const_nhds.mul hDZero :
      Tendsto (fun k : ℕ => ((B : ℝ) + 1) ^ 11 * D k)
        atTop (𝓝 (((B : ℝ) + 1) ^ 11 * (0 : ℝ))))
    simpa only [mul_zero] using hMul
  have hSmall : ∀ᶠ k : ℕ in atTop,
      ((B : ℝ) + 1) ^ 11 * D k < h ^ 2 / (32 * K) :=
    hScaled.eventually (eventually_lt_nhds hTarget)
  filter_upwards [hSmall] with k hk
  intro Q hD hCharge
  by_contra hn
  have hQB : Q ≤ B := Nat.le_of_not_gt hn
  have hRad : (Q : ℝ) + 1 ≤ (B : ℝ) + 1 := by
    have hCast : (Q : ℝ) ≤ (B : ℝ) := Nat.cast_le.mpr hQB
    linarith only [hCast]
  have hPower : ((Q : ℝ) + 1) ^ 11 ≤ ((B : ℝ) + 1) ^ 11 :=
    pow_le_pow_left₀ (by positivity) hRad 11
  have hPaid : ((Q : ℝ) + 1) ^ 11 * D k ≤
      ((B : ℝ) + 1) ^ 11 * D k :=
    mul_le_mul_of_nonneg_right hPower hD
  exact (not_lt_of_ge (hCharge.trans hPaid)) hk


/-- TRUE COFINAL PHYSICAL FREQUENCY ESCAPE. At every fixed B, on all
sufficiently late original separated kinetic gaps, any adverse signed-sixth
flux observation with its tenth-power residual excluded and with low
relative H3 dissipation produces a CERTIFIED annular peak at Q > B.
The same Q retains its width, integrated physical gap charge, and sharp
one-annulus eleventh-power frequency bound. The eventual index depends on B
but is UNIFORM in the adverse sample time and inner cutoff R. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_certifiedOuterBeyondFixed244
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
    (J B : ℕ) (E epsilon : ℝ) (hE : 0 ≤ E) (hEpsilon : 0 < epsilon) :
    ∀ᶠ k : ℕ in atTop, ∀ (R : ℕ) (t : ℝ),
      let x := tau (v k) + delta (v k)
      let y := tau (v (k + 1))
      let H := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
        R eta (velocityH3EnergyAt u t)
      let h := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
      let E0 := velocityH3Energy0At u b
      let D := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
      t ∈ Set.Icc x y →
      eta < -velocityH3TransportDerivative3At u t →
      ¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
        hH3 R J E eta epsilon x y t →
      16 * D < (y - x) * h →
      ∃ (Q : ℕ) (w : ℝ), R ≤ Q ∧ B < Q ∧ 0 < w ∧
        w = thirdFullKineticSignedLowMaxSymmetricGapWidth244
          R Q E0 H x y ∧
        H / 2 <
          h3PathActualLowRadialDissipation244 ((Q : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) -
          h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) ∧
        w * (H / 4) ≤ D ∧
        h ^ 2 / (32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0) ≤
          ((Q : ℝ) + 1) ^ 11 * D := by
  let h : ℝ := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
  let E0 : ℝ := velocityH3Energy0At u b
  let D : ℕ → ℝ := fun k =>
    ∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
      velocityH3DissipationAt u r ∂volume
  have hh : 0 < h :=
    thirdFullKinetic_signedLowMax_cappedLinearFloor_pos244 eta E hEta hE
  have hK : 0 < thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0 :=
    thirdFullKinetic_signedLowMax_criticalTwelveCoeff_pos244 E0
      (velocityH3Energy0At_nonneg u b)
  have hDZero : Tendsto D atTop (𝓝 (0 : ℝ)) := by
    simpa only [D] using
      (thirdFullPhysical_kineticGaps_fullDissipation_tendsto_zero244
        hH3 hClass hDInt b hb M tau N delta v
        hLimit hSeparated hWindows)
  have hBeyond := thirdFullKinetic_signedLowMax_eleventhCharge_forcesCofinalRadius244
    D (thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0) h
    hK hh hDZero B
  have hPhysical := thirdFullPhysical_kineticGaps_signedLowMax_trueCertifiedEleventh244
    hH3 hClass hDInt b hb M tau N delta v
    hLimit hSeparated hWindows eta hEta J E epsilon hE hEpsilon
  filter_upwards [hPhysical, hBeyond] with k hkPhysical hkBeyond
  intro R t
  dsimp only
  intro ht hAdverse hNoResidual hLowDensity
  obtain ⟨Q, w, hRQ, hw, hwEq, hPeak, hCost, hCharge⟩ :=
    hkPhysical R t ht hAdverse hNoResidual hLowDensity
  have hxy : tau (v k) + delta (v k) < tau (v (k + 1)) :=
    hSeparated k (k + 1) (Nat.lt_succ_self k)
  have hD : 0 ≤ D k := by
    change 0 ≤ ∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
      velocityH3DissipationAt u r ∂volume
    exact intervalIntegral.integral_nonneg hxy.le
      (fun r _ => velocityH3DissipationAt_nonneg u r)
  have hQB : B < Q := hkBeyond Q hD hCharge
  exact ⟨Q, w, hRQ, hQB, hw, hwEq, hPeak, hCost, hCharge⟩

end
end PrimeTensor.FirstMonomialTriad
