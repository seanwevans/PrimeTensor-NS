import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxPolynomialSourceGate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxSymmetricRateCompression
import Mathlib.Tactic

/-!
# Signed sixth flux: repair the certified annular-frequency obstruction

The later signed LowMax gauge theorems reduced their physical annular conclusion
merely to `∃ Q, R ≤ Q ∧ G < Q`. That proposition holds for *every* R and G,
and on its own contains no physical information. The actual in-gap symmetric
kinetic-rate proof constructs much more: an annular H3 dissipation peak at
the SAME chosen Q, positive persistence width, and a real integrated charge.

We retain that peak in the original symmetric in-gap proof instead of
forgetting it when eliminating the kinetic clock/rate fork. We then attach
the accepted degree-twelve Fourier-source envelope to THIS physical Q.
The resulting outer-frequency conclusion is genuine: it carries the actual
annular peak and the nonzero integrated cost, not a freely chosen integer.

The rate ceiling is compressed further to K(E0)*(k+1)^12, with
K(E0) = 1 + 192 sqrt(E0)*(sqrt(E0) + 54 E0).
No new Navier--Stokes axiom or terminal H3 trace is assumed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The naked natural-number outer-frequency disjunct of the previous
interfaces is tautological; a genuine spectral claim must retain a physical
annular witness at the same chosen outer frequency. -/
theorem thirdFullKinetic_signedLowMax_bareOuterNumber_trivial244
    (R G : ℕ) : ∃ Q : ℕ, R ≤ Q ∧ G < Q := by
  refine ⟨max R (G + 1), le_max_left _ _, ?_⟩
  exact lt_of_lt_of_le (Nat.lt_succ_self G) (le_max_right _ _)

/-- The kinetic-anchor coefficient of the critical twelfth-power rate. -/
noncomputable def thirdFullKineticSignedLowMaxCriticalTwelveCoeff244
    (E0 : ℝ) : ℝ :=
  1 + 192 * Real.sqrt E0 * (Real.sqrt E0 + 54 * E0)

/-- Strict positivity even when the kinetic energy anchor is zero. -/
theorem thirdFullKinetic_signedLowMax_criticalTwelveCoeff_pos244
    (E0 : ℝ) (hE : 0 ≤ E0) :
    0 < thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0 := by
  have hs : 0 ≤ Real.sqrt E0 := Real.sqrt_nonneg _
  have hSum : 0 ≤ Real.sqrt E0 + 54 * E0 := by positivity
  have hProduct :
      0 ≤ 192 * Real.sqrt E0 * (Real.sqrt E0 + 54 * E0) := by positivity
  unfold thirdFullKineticSignedLowMaxCriticalTwelveCoeff244
  linarith only [hProduct]

/-- The exact polynomial source rate is bounded by one critical power,
with NO further frequency dependence in its coefficient. The exponent
12 comes from 2 (Bernstein), 6 (H3 multiplier), 3 (Fourier source),
and one extra frequency count. -/
theorem thirdFullKinetic_signedLowMax_polynomialRate_le_criticalTwelve244
    (k : ℕ) (E0 : ℝ) (hE : 0 ≤ E0) :
    thirdFullKineticSignedLowMaxPolynomialIndexRate244 k E0 ≤
      thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0 *
        ((k : ℝ) + 1) ^ 12 := by
  let r : ℝ := (k : ℝ) + 1
  let s : ℝ := Real.sqrt E0
  have hr : 1 ≤ r := by
    dsimp only [r]
    have hNat : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith only [hNat]
  have hr0 : 0 ≤ r := le_trans (by norm_num) hr
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hSum : 0 ≤ s + 54 * E0 := by positivity
  have hDouble : r + 1 ≤ 2 * r := by linarith only [hr]
  have hQuad : (r + 1) ^ 2 ≤ 4 * r ^ 2 := by
    calc
      (r + 1) ^ 2 ≤ (2 * r) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hDouble 2
      _ = 4 * r ^ 2 := by ring
  have hBase : 0 ≤ 48 * r * r ^ 6 * s := by positivity
  have hCoef :
      48 * r * (r + 1) ^ 2 * r ^ 6 * s ≤ 192 * r ^ 9 * s := by
    calc
      48 * r * (r + 1) ^ 2 * r ^ 6 * s =
          (48 * r * r ^ 6 * s) * (r + 1) ^ 2 := by ring
      _ ≤ (48 * r * r ^ 6 * s) * (4 * r ^ 2) :=
        mul_le_mul_of_nonneg_left hQuad hBase
      _ = 192 * r ^ 9 * s := by ring
  have hR23 : r ^ 2 ≤ r ^ 3 :=
    pow_le_pow_right₀ hr (by norm_num)
  have hSource :
      r ^ 2 * s + 54 * r ^ 3 * E0 ≤
        r ^ 3 * (s + 54 * E0) := by
    calc
      r ^ 2 * s + 54 * r ^ 3 * E0 ≤
          r ^ 3 * s + 54 * r ^ 3 * E0 :=
        add_le_add (mul_le_mul_of_nonneg_right hR23 hs) le_rfl
      _ = r ^ 3 * (s + 54 * E0) := by ring
  have hSource0 : 0 ≤ r ^ 2 * s + 54 * r ^ 3 * E0 := by positivity
  have hCoef0 : 0 ≤ 192 * r ^ 9 * s := by positivity
  have hTerm :
      (48 * r * (r + 1) ^ 2 * r ^ 6 * s) *
          (r ^ 2 * s + 54 * r ^ 3 * E0) ≤
        (192 * s * (s + 54 * E0)) * r ^ 12 := by
    calc
      _ ≤ (192 * r ^ 9 * s) *
          (r ^ 2 * s + 54 * r ^ 3 * E0) :=
        mul_le_mul_of_nonneg_right hCoef hSource0
      _ ≤ (192 * r ^ 9 * s) * (r ^ 3 * (s + 54 * E0)) :=
        mul_le_mul_of_nonneg_left hSource hCoef0
      _ = (192 * s * (s + 54 * E0)) * r ^ 12 := by ring
  have hPower : 1 ≤ r ^ 12 := one_le_pow₀ hr
  have hBound :
      1 + (48 * r * (r + 1) ^ 2 * r ^ 6 * s) *
          (r ^ 2 * s + 54 * r ^ 3 * E0) ≤
        (1 + 192 * s * (s + 54 * E0)) * r ^ 12 := by
    calc
      _ ≤ 1 + (192 * s * (s + 54 * E0)) * r ^ 12 :=
        add_le_add le_rfl hTerm
      _ ≤ r ^ 12 + (192 * s * (s + 54 * E0)) * r ^ 12 :=
        add_le_add hPower le_rfl
      _ = (1 + 192 * s * (s + 54 * E0)) * r ^ 12 := by ring
  calc
    thirdFullKineticSignedLowMaxPolynomialIndexRate244 k E0 =
        1 + (48 * r * (r + 1) ^ 2 * r ^ 6 * s) *
          (r ^ 2 * s + 54 * r ^ 3 * E0) := by
      unfold thirdFullKineticSignedLowMaxPolynomialIndexRate244
      dsimp only [r, s]
      ring
    _ ≤ (1 + 192 * s * (s + 54 * E0)) * r ^ 12 := hBound
    _ = thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0 *
        ((k : ℝ) + 1) ^ 12 := by
      unfold thirdFullKineticSignedLowMaxCriticalTwelveCoeff244
      dsimp only [r, s]

/-- A paid polynomial kinetic index rate forces a nonzero *normalized*
H3 dissipation charge at the critical twelfth-power frequency scale. -/
theorem thirdFullKinetic_signedLowMax_criticalTwelve_inverseCharge244
    (k : ℕ) (E0 h D : ℝ) (hE : 0 ≤ E0) (hD : 0 ≤ D)
    (hRate : h ^ 2 ≤
      32 * thirdFullKineticSignedLowMaxPolynomialIndexRate244 k E0 * D) :
    h ^ 2 / (32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0) ≤
      ((k : ℝ) + 1) ^ 12 * D := by
  have hCap := thirdFullKinetic_signedLowMax_polynomialRate_le_criticalTwelve244
    k E0 hE
  have hCoeff : 0 < 32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0 :=
    mul_pos (by norm_num)
      (thirdFullKinetic_signedLowMax_criticalTwelveCoeff_pos244 E0 hE)
  apply (div_le_iff₀ hCoeff).mpr
  calc
    h ^ 2 ≤ 32 * thirdFullKineticSignedLowMaxPolynomialIndexRate244 k E0 * D := hRate
    _ = thirdFullKineticSignedLowMaxPolynomialIndexRate244 k E0 * (32 * D) := by ring
    _ ≤ (thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0 *
        ((k : ℝ) + 1) ^ 12) * (32 * D) :=
      mul_le_mul_of_nonneg_right hCap (by positivity)
    _ = (((k : ℝ) + 1) ^ 12 * D) *
          (32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0) := by ring

/-- Preserved-peak version of the accepted symmetric in-gap annular charge.
Any certified high-radial annulus at a time in the closed kinetic gap
persists at quarter height on the longer available side. The original
symmetric width depends only on the two kinetic cutoff rates. Unlike the
compressed downstream interface, the conclusion retains the actual positive
finite-annular H3 dissipation peak at the same selected outer cutoff. -/
theorem thirdFullPhysical_signedLowMax_symmetricKineticInGapCharge_withPeak244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R : ℕ) (H x y t : ℝ)
    (hH : 0 < H) (hx : x ∈ Set.Ioo b T)
    (hy : y ∈ Set.Ioo b T) (hxy : x < y)
    (ht : t ∈ Set.Icc x y)
    (hWindow : ThirdFullKineticSignedLowMaxCertifiedAnnularWindow244
      hH3 R H t) :
    ∃ (N : ℕ) (w : ℝ), R ≤ N ∧
      w = thirdFullKineticSignedLowMaxSymmetricGapWidth244 R N
        (velocityH3Energy0At u b) H x y ∧
      0 < w ∧
      ((t + w < y) ∨ (x < t - w)) ∧
      w * (H / 4) ≤
        ∫ r in x..y, velocityH3DissipationAt u r ∂volume ∧
      H / 2 <
        h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) := by
  obtain ⟨N, K, C, delta, hRN, _hK, _hC, _hDelta, _hDeltaOne,
    _hDeltaT, _hState, _hSource, hAt, _hWidth, _hFloor, _hCost⟩ := hWindow
  let E : ℝ := velocityH3Energy0At u b
  let L : ℝ := thirdFullKineticSignedLowMaxKineticAnnulusRate244 R N E
  let w : ℝ := thirdFullKineticSignedLowMaxSymmetricGapWidth244 R N E H x y
  obtain ⟨hw, hQuarter, hRate⟩ :=
    thirdFullKinetic_signedLowMax_symmetricWidth_budget244 R N E H x y hH hxy
  have hL : 0 ≤ L := thirdFullKinetic_signedLowMax_kineticAnnulusRate_nonneg244 R N E
  let U : ℝ → H3SpectralVelocityState := h3AuditActualSpectralVelocityTotal hH3
  let Ann : ℝ → ℝ := fun r =>
    h3PathActualLowRadialDissipation244 ((N : ℝ) + 1) (U r) -
      h3PathActualLowRadialDissipation244 ((R : ℝ) + 1) (U r)
  let D : ℝ → ℝ := velocityH3DissipationAt u
  have hPeak : H / 2 < Ann t := hAt
  have hxClass : x ∈ Set.Ioo a T := ⟨lt_trans hb.1 hx.1, hx.2⟩
  have hyClass : y ∈ Set.Ioo a T := ⟨lt_trans hb.1 hy.1, hy.2⟩
  have htTail : t ∈ Set.Ioo b T :=
    ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
  have hCont : ContinuousOn Ann (Set.Ioo a T) :=
    h3Path_finiteAnnularDissipation_continuousOn244
      hH3 hClass ((R : ℝ) + 1) ((N : ℝ) + 1)
      (by positivity) (by positivity)
  have hDGap : IntervalIntegrable D volume x y := by
    apply hDInt.mono_set
    intro r hr
    have hrIcc : r ∈ Set.Icc x y := by
      simpa only [Set.uIcc_of_le hxy.le] using hr
    have hrAll : r ∈ Set.Icc a T :=
      ⟨hxClass.1.le.trans hrIcc.1, hrIcc.2.trans hyClass.2.le⟩
    simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hrAll
  have hNonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc x y)] D := by
    filter_upwards [] with r
    exact velocityH3DissipationAt_nonneg u r
  refine ⟨N, w, hRN, rfl, hw, ?_⟩
  by_cases hSide : t ≤ (x + y) / 2
  · have hForward : t + w < y := by
      linarith only [hSide, hQuarter, hxy]
    have hSub : Set.Icc t (t + w) ⊆ Set.Ioo a T := by
      intro r hr
      exact ⟨lt_of_lt_of_le hxClass.1 (ht.1.trans hr.1),
        lt_of_le_of_lt hr.2 (lt_trans hForward hyClass.2)⟩
    have hFloor (r : ℝ) (hr : r ∈ Set.Icc t (t + w)) : H / 4 < Ann r := by
      have hrTail : r ∈ Set.Ioo b T :=
        ⟨lt_of_lt_of_le htTail.1 hr.1,
         lt_of_le_of_lt hr.2 (lt_trans hForward hy.2)⟩
      have hLip := thirdFullPhysical_kineticNaturalAnnularDissipationLipschitz244
        hH3 hClass b hb R N t r htTail hrTail hr.1
      change |Ann t - Ann r| ≤ L * (r - t) at hLip
      have hDifference : Ann t - Ann r ≤ L * (r - t) :=
        (le_abs_self (Ann t - Ann r)).trans hLip
      have hTime : r - t ≤ w := by linarith only [hr.2]
      have hBound : L * (r - t) ≤ H / 8 :=
        (mul_le_mul_of_nonneg_left hTime hL).trans hRate
      linarith only [hPeak, hDifference, hBound, hH]
    have hAnnInt : IntervalIntegrable Ann volume t (t + w) :=
      (hCont.mono hSub).intervalIntegrable_of_Icc (by linarith only [hw])
    have hDWin : IntervalIntegrable D volume t (t + w) := by
      apply hDInt.mono_set
      intro r hr
      have hrIcc : r ∈ Set.Icc t (t + w) := by
        rcases Set.mem_uIcc.mp hr with hForward | hReverse
        · exact hForward
        · exfalso
          have hStrict : t < t + w := by linarith only [hw]
          exact (not_le_of_gt hStrict) (hReverse.1.trans hReverse.2)
      have hrAll : r ∈ Set.Icc a T :=
        ⟨hxClass.1.le.trans (ht.1.trans hrIcc.1),
          hrIcc.2.trans (lt_trans hForward hyClass.2).le⟩
      simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hrAll
    have hAnnCost : w * (H / 4) ≤ ∫ r in t..(t + w), Ann r ∂volume := by
      have hCost := h3Path_localPositiveHeight_forces_integratedCost244
        Ann t (t + w) (H / 4) (by linarith only [hw]) hAnnInt
        (fun r hr => (hFloor r hr).le)
      calc
        w * (H / 4) = ((t + w) - t) * (H / 4) := by ring
        _ ≤ _ := hCost
    have hAnnLeD : (∫ r in t..(t + w), Ann r ∂volume) ≤
        ∫ r in t..(t + w), D r ∂volume := by
      apply intervalIntegral.integral_mono_on
        (le_add_of_nonneg_right hw.le) hAnnInt hDWin
      intro r hr
      exact h3Path_actualFiniteAnnulusDissipation_le_fullAt244
        hH3 hClass r (hSub hr) ((R : ℝ) + 1) ((N : ℝ) + 1)
    have hGapCost : (∫ r in t..(t + w), D r ∂volume) ≤
        ∫ r in x..y, D r ∂volume :=
      intervalIntegral.integral_mono_interval
        ht.1 (le_add_of_nonneg_right hw.le) hForward.le hNonneg hDGap
    exact ⟨Or.inl hForward, (hAnnCost.trans hAnnLeD).trans hGapCost, hPeak⟩
  · have hBeyond : (x + y) / 2 < t := lt_of_not_ge hSide
    have hBackward : x < t - w := by
      linarith only [hBeyond, hQuarter, hxy]
    have hSub : Set.Icc (t - w) t ⊆ Set.Ioo a T := by
      intro r hr
      exact ⟨lt_trans hxClass.1 (lt_of_lt_of_le hBackward hr.1),
        lt_of_le_of_lt hr.2 (lt_of_le_of_lt ht.2 hyClass.2)⟩
    have hFloor (r : ℝ) (hr : r ∈ Set.Icc (t - w) t) : H / 4 < Ann r := by
      have hrTail : r ∈ Set.Ioo b T :=
        ⟨lt_trans hx.1 (lt_of_lt_of_le hBackward hr.1),
         lt_of_le_of_lt hr.2 htTail.2⟩
      have hLip := thirdFullPhysical_kineticNaturalAnnularDissipationLipschitz244
        hH3 hClass b hb R N r t hrTail htTail hr.2
      change |Ann r - Ann t| ≤ L * (t - r) at hLip
      have hDifference : Ann t - Ann r ≤ L * (t - r) := by
        calc
          Ann t - Ann r ≤ |Ann t - Ann r| := le_abs_self _
          _ = |Ann r - Ann t| := abs_sub_comm _ _
          _ ≤ L * (t - r) := hLip
      have hTime : t - r ≤ w := by linarith only [hr.1]
      have hBound : L * (t - r) ≤ H / 8 :=
        (mul_le_mul_of_nonneg_left hTime hL).trans hRate
      linarith only [hPeak, hDifference, hBound, hH]
    have hAnnInt : IntervalIntegrable Ann volume (t - w) t :=
      (hCont.mono hSub).intervalIntegrable_of_Icc (by linarith only [hw])
    have hDWin : IntervalIntegrable D volume (t - w) t := by
      apply hDInt.mono_set
      intro r hr
      have hrIcc : r ∈ Set.Icc (t - w) t := by
        simpa only [Set.uIcc_of_le (by linarith only [hw] : t - w ≤ t)] using hr
      have hrAll : r ∈ Set.Icc a T :=
        ⟨hxClass.1.le.trans (hBackward.le.trans hrIcc.1),
          hrIcc.2.trans (ht.2.trans hyClass.2.le)⟩
      simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hrAll
    have hAnnCost : w * (H / 4) ≤ ∫ r in (t - w)..t, Ann r ∂volume := by
      have hCost := h3Path_localPositiveHeight_forces_integratedCost244
        Ann (t - w) t (H / 4) (by linarith only [hw]) hAnnInt
        (fun r hr => (hFloor r hr).le)
      calc
        w * (H / 4) = (t - (t - w)) * (H / 4) := by ring
        _ ≤ _ := hCost
    have hAnnLeD : (∫ r in (t - w)..t, Ann r ∂volume) ≤
        ∫ r in (t - w)..t, D r ∂volume := by
      apply intervalIntegral.integral_mono_on
        (by linarith only [hw] : t - w ≤ t) hAnnInt hDWin
      intro r hr
      exact h3Path_actualFiniteAnnulusDissipation_le_fullAt244
        hH3 hClass r (hSub hr) ((R : ℝ) + 1) ((N : ℝ) + 1)
    have hGapCost : (∫ r in (t - w)..t, D r ∂volume) ≤
        ∫ r in x..y, D r ∂volume :=
      intervalIntegral.integral_mono_interval
        hBackward.le (by linarith only [hw] : t - w ≤ t) ht.2
        hNonneg hDGap
    exact ⟨Or.inr hBackward, (hAnnCost.trans hAnnLeD).trans hGapCost, hPeak⟩

/-- The actual gamma-free signed sixth-flux carrier admits an annulus N whose
PEAK at the adverse time and in-gap dissipation charge are retained while its
kinetic rate is compared with an arbitrary finite gauge G. This is stronger
than a naked existential `R ≤ N ∧ G < N`, which is always satisfiable. -/
theorem thirdFullPhysical_signedLowMax_gammaFreeTail_certifiedGaugeRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R G : ℕ) (x y t : ℝ)
    (hx : x ∈ Set.Ioo b T) (hy : y ∈ Set.Ioo b T)
    (hxy : x < y) (ht : t ∈ Set.Icc x y)
    (eta : ℝ) (hEta : 0 < eta)
    (hTail : eta / 2 ≤
      thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
        (velocityH3EnergyAt u t) *
        ‖thirdFullSpectralVelocityHighRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 t)‖ ^ 2) :
    let H := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
      R eta (velocityH3EnergyAt u t)
    let E0 := velocityH3Energy0At u b
    let D := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
    ∃ (N : ℕ) (w : ℝ),
      R ≤ N ∧ 0 < w ∧
      w = thirdFullKineticSignedLowMaxSymmetricGapWidth244 R N E0 H x y ∧
      ((t + w < y) ∨ (x < t - w)) ∧
      H / 2 <
        h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) ∧
      w * (H / 4) ≤ D ∧
      ((y - x) * H ≤ 16 * D ∨ G < N ∨
        H ^ 2 ≤ 32 * thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244
          G E0 * D) := by
  let H : ℝ := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
    R eta (velocityH3EnergyAt u t)
  let E0 : ℝ := velocityH3Energy0At u b
  let D : ℝ := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
  change ∃ (N : ℕ) (w : ℝ), R ≤ N ∧ 0 < w ∧
    w = thirdFullKineticSignedLowMaxSymmetricGapWidth244 R N E0 H x y ∧
    ((t + w < y) ∨ (x < t - w)) ∧
    H / 2 <
      h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) -
      h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) ∧
    w * (H / 4) ≤ D ∧
    ((y - x) * H ≤ 16 * D ∨ G < N ∨
      H ^ 2 ≤ 32 * thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244
        G E0 * D)
  have hxClass : x ∈ Set.Ioo a T := ⟨lt_trans hb.1 hx.1, hx.2⟩
  have hyClass : y ∈ Set.Ioo a T := ⟨lt_trans hb.1 hy.1, hy.2⟩
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hxClass.1 ht.1, lt_of_le_of_lt ht.2 hyClass.2⟩
  obtain ⟨hH, hHigh⟩ :=
    thirdFullPhysical_signedLowMax_gammaFreeTail_linearHighRadialFloor244
      hH3 hClass R t htClass eta hEta hTail
  have hWindow : ThirdFullKineticSignedLowMaxCertifiedAnnularWindow244
      hH3 R H t :=
    thirdFullPhysical_highRadialHeight_to_signedCertifiedWindow244
      hH3 hClass t htClass R H hH hHigh
  obtain ⟨N, w, hRN, hwEq, hw, hSide, hCost, hPeak⟩ :=
    thirdFullPhysical_signedLowMax_symmetricKineticInGapCharge_withPeak244
      hH3 hClass hDInt b hb R H x y t hH hx hy hxy ht hWindow
  refine ⟨N, w, hRN, hw, hwEq, hSide, hPeak, hCost, ?_⟩
  let L : ℕ → ℝ := fun j =>
    thirdFullPhysicalKineticLowBandDissipationRate244 j E0
  let A : ℝ := thirdFullKineticSignedLowMaxKineticAnnulusRate244 R N E0
  have hL (j : ℕ) : 0 ≤ L j :=
    thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 j E0
  have hA : 0 ≤ A :=
    thirdFullKinetic_signedLowMax_kineticAnnulusRate_nonneg244 R N E0
  have hD : 0 ≤ D :=
    intervalIntegral.integral_nonneg hxy.le
      (fun r _ => velocityH3DissipationAt_nonneg u r)
  have hCharge :
      min ((y - x) / 4) (H / (8 * (A + 1))) * (H / 4) ≤ D := by
    simpa only [hwEq,
      thirdFullKineticSignedLowMaxSymmetricGapWidth244, A, D] using hCost
  have hRaw := thirdFullKinetic_signedLowMax_symmetricCharge_clockOrRate244
    x y H A D hH hA hxy hCharge
  have hCore : (y - x) * H ≤ 16 * D ∨
      H ^ 2 ≤ 32 * (L R + L N + 1) * D := by
    rcases hRaw with hClock | hRate
    · exact Or.inl hClock
    · right
      calc
        H ^ 2 ≤ 32 * (A + 1) * D := hRate
        _ = 32 * (L R + L N + 1) * D := by
          dsimp only [A, L]
          unfold thirdFullKineticSignedLowMaxKineticAnnulusRate244
          ring
  have hGaugeFork := thirdFullKinetic_signedLowMax_clockOr_outerGauge_or_rate244
    L hL R N G x y H D hRN hD hCore
  simpa only [L, E0, thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244]
    using hGaugeFork

/-- A real high-tail observation under an actual physical H3 energy cap
forces a true annular H3 dissipation peak. Either its gap has positive
relative density, its index has a critical twelfth-power rate payment, or
THE SAME peak-carrying annular cutoff N exceeds the natural gap index k. -/
theorem thirdFullPhysical_signedLowMax_gammaFreeTail_certifiedCriticalTwelve244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R k : ℕ) (x y t : ℝ)
    (hx : x ∈ Set.Ioo b T) (hy : y ∈ Set.Ioo b T)
    (hxy : x < y) (ht : t ∈ Set.Icc x y)
    (eta E : ℝ) (hEta : 0 < eta) (hE : 0 ≤ E)
    (hEnergyCap : velocityH3EnergyAt u t ≤ E)
    (hTail : eta / 2 ≤
      thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
        (velocityH3EnergyAt u t) *
        ‖thirdFullSpectralVelocityHighRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 t)‖ ^ 2) :
    let H := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
      R eta (velocityH3EnergyAt u t)
    let h := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
    let E0 := velocityH3Energy0At u b
    let D := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
    ∃ (N : ℕ) (w : ℝ), R ≤ N ∧ 0 < w ∧
      w = thirdFullKineticSignedLowMaxSymmetricGapWidth244 R N E0 H x y ∧
      ((t + w < y) ∨ (x < t - w)) ∧
      H / 2 <
        h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) ∧
      w * (H / 4) ≤ D ∧
      ((y - x) * h ≤ 16 * D ∨
        h ^ 2 ≤ 32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0 *
          ((k : ℝ) + 1) ^ 12 * D ∨ k < N) := by
  let H : ℝ := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
    R eta (velocityH3EnergyAt u t)
  let h : ℝ := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
  let E0 : ℝ := velocityH3Energy0At u b
  let D : ℝ := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
  change ∃ (N : ℕ) (w : ℝ), R ≤ N ∧ 0 < w ∧
    w = thirdFullKineticSignedLowMaxSymmetricGapWidth244 R N E0 H x y ∧
    ((t + w < y) ∨ (x < t - w)) ∧
    H / 2 <
      h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) -
      h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) ∧
    w * (H / 4) ≤ D ∧
    ((y - x) * h ≤ 16 * D ∨
      h ^ 2 ≤ 32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0 *
        ((k : ℝ) + 1) ^ 12 * D ∨ k < N)
  obtain ⟨N, w, hRN, hw, hwEq, hSide, hPeak, hCost, hFork⟩ :=
    thirdFullPhysical_signedLowMax_gammaFreeTail_certifiedGaugeRate244
      hH3 hClass hDInt b hb R k x y t hx hy hxy ht eta hEta hTail
  refine ⟨N, w, hRN, hw, hwEq, hSide, hPeak, hCost, ?_⟩
  have hEt0 : 0 ≤ velocityH3EnergyAt u t := by
    have hOne := one_le_velocityH3EnergyAt u t
    linarith only [hOne]
  have hHeight : h ≤ H :=
    thirdFullKinetic_signedLowMax_linearHeight_ge_cappedFloor244
      R eta (velocityH3EnergyAt u t) E hEta hEt0 hEnergyCap
  have hFloor : 0 ≤ h :=
    (thirdFullKinetic_signedLowMax_cappedLinearFloor_pos244 eta E hEta hE).le
  have hSquare : h ^ 2 ≤ H ^ 2 :=
    pow_le_pow_left₀ hFloor hHeight 2
  have hGap : 0 ≤ y - x := sub_nonneg.mpr hxy.le
  have hD : 0 ≤ D :=
    intervalIntegral.integral_nonneg hxy.le
      (fun r _ => velocityH3DissipationAt_nonneg u r)
  have hC :
      thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244 k E0 ≤
      thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0 *
        ((k : ℝ) + 1) ^ 12 :=
    (thirdFullKinetic_signedLowMax_finiteRate_le_polynomial244
      k E0 (velocityH3Energy0At_nonneg u b)).trans
      (thirdFullKinetic_signedLowMax_polynomialRate_le_criticalTwelve244
        k E0 (velocityH3Energy0At_nonneg u b))
  rcases hFork with hClock | hRest
  · left
    exact (mul_le_mul_of_nonneg_left hHeight hGap).trans hClock
  rcases hRest with hOuter | hRate
  · exact Or.inr (Or.inr hOuter)
  · right; left
    calc
      h ^ 2 ≤ H ^ 2 := hSquare
      _ ≤ 32 * thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244 k E0 * D := hRate
      _ = thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244 k E0 *
          (32 * D) := by ring
      _ ≤ (thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0 *
          ((k : ℝ) + 1) ^ 12) * (32 * D) :=
        mul_le_mul_of_nonneg_right hC (by positivity)
      _ = 32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0 *
          ((k : ℝ) + 1) ^ 12 * D := by ring

/-- Under a subcritical relative gap cost and a subcritical twelfth-power
rate cost, the SAME finite annulus is forced above the gap index, and it
has a proved positive physical dissipation peak and in-gap charge. -/
theorem thirdFullPhysical_signedLowMax_lowCost_forcesCertifiedOuter244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R k : ℕ) (x y t : ℝ)
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
        (y - x) * thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E)
    (hLowRate :
      32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244
          (velocityH3Energy0At u b) * ((k : ℝ) + 1) ^ 12 *
        (∫ r in x..y, velocityH3DissipationAt u r ∂volume) <
        (thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E) ^ 2) :
    ∃ (N : ℕ) (w : ℝ), R ≤ N ∧ k < N ∧ 0 < w ∧
      thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
          R eta (velocityH3EnergyAt u t) / 2 <
        h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) ∧
      w * (thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
          R eta (velocityH3EnergyAt u t) / 4) ≤
        ∫ r in x..y, velocityH3DissipationAt u r ∂volume := by
  obtain ⟨N, w, hRN, hw, _hwEq, _hSide, hPeak, hCost, hFork⟩ :=
    thirdFullPhysical_signedLowMax_gammaFreeTail_certifiedCriticalTwelve244
      hH3 hClass hDInt b hb R k x y t hx hy hxy ht
      eta E hEta hE hEnergyCap hTail
  rcases hFork with hClock | hRest
  · exact False.elim ((not_lt_of_ge hClock) hLowDensity)
  rcases hRest with hRate | hOuter
  · exact False.elim ((not_lt_of_ge hRate) hLowRate)
  exact ⟨N, w, hRN, hOuter, hw, hPeak, hCost⟩

/-- Cofinal repair of the ACTUAL adverse signed-sixth-flux conclusion.
The original tenth-power residual is explicitly excluded. When both
physical gap payments are subcritical, the returned outer annulus exceeds
the gap index AND has a nonzero actual H3 dissipation peak and real
integrated in-gap charge. No arbitrary existential cutoff can discharge
this strengthened conclusion. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_trueCertifiedCriticalTwelve244
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
      let D := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
      t ∈ Set.Icc x y →
      eta < -velocityH3TransportDerivative3At u t →
      ¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
        hH3 R J E eta epsilon x y t →
      16 * D < (y - x) * h →
      32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244
        (velocityH3Energy0At u b) * ((k : ℝ) + 1) ^ 12 * D < h ^ 2 →
      ∃ (Q : ℕ) (w : ℝ), R ≤ Q ∧ k < Q ∧ 0 < w ∧
        H / 2 <
          h3PathActualLowRadialDissipation244 ((Q : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) -
          h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) ∧
        w * (H / 4) ≤ D := by
  have hRadius := thirdFullPhysical_kineticGaps_signedLowMax_radiusEnergyEscape244
    hH3 hClass hDInt b hb M tau N delta v hLimit hSeparated
    hWindows eta hEta J E epsilon hE hEpsilon
  filter_upwards [hRadius] with k hkRadius
  intro R t
  dsimp only
  intro ht hAdverse hNoResidual hLowDensity hLowRate
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
  exact thirdFullPhysical_signedLowMax_lowCost_forcesCertifiedOuter244
    hH3 hClass hDInt b hb R k x y t hx hy hxy ht
    eta E hEta hE hCap (by simpa only [X] using hTail)
    hLowDensity hLowRate

end
end PrimeTensor.FirstMonomialTriad
