import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierExplicitTemporalRate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularDeficitTwoTimeLedger
import Mathlib.Tactic

/-!
# Outer carrier: exact two-channel temporal rates and necessary rate amplification

The previous explicit-window theorem gives

  min(m/(2 LM), epsilon/LG, (T-x)/2) * (119*m*sigma^6/160)
     <= integral_x^T D_H3.

The first result below derives LG from *separate changes of the actual highpass
mass and actual nonlinear Young/width integral*, using the exact two-time
annular-deficit polynomial, rather than treating LG as an opaque rate.

The second result gives a sharp three-way price for a selected outer carrier:
  - highpass-margin rate must pay 119*m^2*sigma^6 <= 320 LM V;
  - deficit rate must pay 119*m*epsilon*sigma^6 <= 160 LG V;
  - or terminal-time compression must pay 119*m*sigma^6*(T-x) <= 320 V.

For cofinal snapshots V = integral_x^T D_H3 tends to zero. If the third arm
has a positive lower bound, then for EVERY fixed C > 0 eventually
  C*m^2*sigma^6 < LM  OR  C*m*epsilon*sigma^6 < LG.
This is a necessary temporal rate acceleration, not a claim that the PDE
actually provides either quantitative derivative bound or continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The exact deficit polynomial inherits a rate from independent mass and
Young-width rates and the *true* two-time slope. No assumption about a
higher-order time derivative is hidden in this scalar estimate. -/
theorem thirdFullKinetic_deficitPolynomial_rateFromTwoChannels244
    (a b w p m n y z lm ly M S delta : ℝ)
    (hm : 0 ≤ m) (hM : m ≤ M)
    (hlm : 0 ≤ lm) (hly : 0 ≤ ly) (hd : 0 ≤ delta)
    (hMass : |m - n| ≤ lm * delta)
    (hYoung : |y - z| ≤ ly * delta)
    (hSlope : |w * a * (a * (m + n) - 2 * b) - (z + w * p)| ≤ S) :
    |(w * (a * m - b) ^ 2 - m * (y + w * p)) -
      (w * (a * n - b) ^ 2 - n * (z + w * p))| ≤
      (lm * S + M * ly) * delta := by
  have hFirst :
      |m - n| * |w * a * (a * (m + n) - 2 * b) - (z + w * p)| ≤
        (lm * delta) * S := by
    calc
      _ ≤ (lm * delta) *
          |w * a * (a * (m + n) - 2 * b) - (z + w * p)| :=
            mul_le_mul_of_nonneg_right hMass (abs_nonneg _)
      _ ≤ (lm * delta) * S :=
        mul_le_mul_of_nonneg_left hSlope (mul_nonneg hlm hd)
  have hSecond : m * |y - z| ≤ M * (ly * delta) := by
    calc
      _ ≤ m * (ly * delta) := mul_le_mul_of_nonneg_left hYoung hm
      _ ≤ M * (ly * delta) :=
        mul_le_mul_of_nonneg_right hM (mul_nonneg hly hd)
  calc
    |(w * (a * m - b) ^ 2 - m * (y + w * p)) -
        (w * (a * n - b) ^ 2 - n * (z + w * p))| ≤
        |m - n| *
          |w * a * (a * (m + n) - 2 * b) - (z + w * p)| +
          m * |y - z| :=
            thirdFullKinetic_deficitPolynomial_twoTime_abs_bound244
              a b w p m n y z hm
    _ ≤ (lm * delta) * S + M * (ly * delta) := add_le_add hFirst hSecond
    _ = (lm * S + M * ly) * delta := by ring

/-- Application of the exact polynomial-rate lemma to the ORIGINAL physical
annular deficit. The raw mass rate, genuine Young-width rate, and exact
polynomial slope are all displayed as distinct analytic inputs. -/
theorem thirdFullPhysical_actualAnnularDeficit_rateFromTwoChannels244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b x rho sigma lm ly M S : ℝ)
    (hlm : 0 ≤ lm) (hly : 0 ≤ ly)
    (hMassBound : ∀ s : ℝ, s ∈ Set.Ico x T →
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho ≤ M)
    (hMassRate : ∀ s : ℝ, s ∈ Set.Ico x T →
      |thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho -
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho| ≤ lm * (s - x))
    (hYoungRate : ∀ s : ℝ, s ∈ Set.Ico x T →
      |thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma -
        thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma| ≤
          ly * (s - x))
    (hSlope : ∀ s : ℝ, s ∈ Set.Ico x T →
      let a : ℝ := (rho ^ 2 + sigma ^ 2) / 2
      let w : ℝ := (rho ^ 2) ^ 3
      let B : ℝ := Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b))
      let P : ℝ := thirdFullPhysicalOuterViscousCapBase244 u b a
      let Ms : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
      let Mt : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
      let Yt : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
      |w * a * (a * (Ms + Mt) - 2 * B) - (Yt + w * P)| ≤ S) :
    ∀ s : ℝ, s ∈ Set.Ico x T →
      |thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma -
        thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma| ≤
        (lm * S + M * ly) * (s - x) := by
  intro s hs
  let a : ℝ := (rho ^ 2 + sigma ^ 2) / 2
  let w : ℝ := (rho ^ 2) ^ 3
  let B : ℝ := Real.sqrt (velocityH3Energy0At u b) *
    (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
      rho (velocityH3Energy0At u b))
  let P : ℝ := thirdFullPhysicalOuterViscousCapBase244 u b a
  let Ms : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
  let Mt : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
  let Ys : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma
  let Yt : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
  have hm : 0 ≤ Ms := sq_nonneg _
  have hPoly := thirdFullKinetic_deficitPolynomial_rateFromTwoChannels244
    a B w P Ms Mt Ys Yt lm ly M S (s - x)
    hm (hMassBound s hs) hlm hly (sub_nonneg.mpr hs.1)
    (hMassRate s hs) (hYoungRate s hs) (hSlope s hs)
  change
    |(w * (a * Ms - B) ^ 2 - Ms * (Ys + w * P)) -
      (w * (a * Mt - B) ^ 2 - Mt * (Yt + w * P))| ≤
      (lm * S + M * ly) * (s - x)
  exact hPoly

/-- Multiplying away one positive temporal rate denominator is valid
without postulating any nonzero terminal dissipation. -/
private theorem thirdFullKinetic_divRate_clear244
    (z L A V : ℝ) (hL : 0 < L) (h : (z / L) * A ≤ V) :
    z * A ≤ L * V := by
  have hMul := mul_le_mul_of_nonneg_right h hL.le
  calc
    z * A = (z / L) * A * L := by
      field_simp [ne_of_gt hL]
      <;> ring
    _ ≤ V * L := hMul
    _ = L * V := by ring

/-- A selected physical sixth-power outer-carrier charge can only be paid
by one of two temporal rate costs or by the remaining terminal-time gap.
The constants 119, 160 and 320 are inherited exactly from the physical
viscous-spike theorem and its half-margin window. -/
theorem thirdFullKinetic_explicitOuterRate_threeWayBarrier244
    (m epsilon sigma LM LG gap V : ℝ)
    (hLM : 0 < LM) (hLG : 0 < LG)
    (hCharge :
      min (m / (2 * LM)) (min (epsilon / LG) (gap / 2)) *
        (119 * m * sigma ^ 6 / 160) ≤ V) :
    119 * m ^ 2 * sigma ^ 6 ≤ 320 * LM * V ∨
    119 * m * epsilon * sigma ^ 6 ≤ 160 * LG * V ∨
    119 * m * sigma ^ 6 * gap ≤ 320 * V := by
  let A : ℝ := 119 * m * sigma ^ 6 / 160
  have hCost :
      min (m / (2 * LM)) (min (epsilon / LG) (gap / 2)) * A ≤ V :=
    hCharge
  rcases le_total (m / (2 * LM)) (min (epsilon / LG) (gap / 2)) with
    hFirst | hRemainder
  · have hSelected : (m / (2 * LM)) * A ≤ V := by
      simpa only [min_eq_left hFirst] using hCost
    have hCleared := thirdFullKinetic_divRate_clear244
      m (2 * LM) A V (by positivity) hSelected
    left
    calc
      119 * m ^ 2 * sigma ^ 6 = 160 * (m * A) := by
        dsimp only [A]
        ring
      _ ≤ 160 * ((2 * LM) * V) :=
        mul_le_mul_of_nonneg_left hCleared (by norm_num)
      _ = 320 * LM * V := by ring
  · have hRest : min (epsilon / LG) (gap / 2) * A ≤ V := by
      simpa only [min_eq_right hRemainder] using hCost
    rcases le_total (epsilon / LG) (gap / 2) with hSecond | hThird
    · have hSelected : (epsilon / LG) * A ≤ V := by
        simpa only [min_eq_left hSecond] using hRest
      have hCleared := thirdFullKinetic_divRate_clear244
        epsilon LG A V hLG hSelected
      exact Or.inr (Or.inl (by
        calc
          119 * m * epsilon * sigma ^ 6 = 160 * (epsilon * A) := by
            dsimp only [A]
            ring
          _ ≤ 160 * (LG * V) :=
            mul_le_mul_of_nonneg_left hCleared (by norm_num)
          _ = 160 * LG * V := by ring))
    · have hSelected : (gap / 2) * A ≤ V := by
        simpa only [min_eq_right hThird] using hRest
      right
      right
      calc
        119 * m * sigma ^ 6 * gap = 320 * ((gap / 2) * A) := by
          dsimp only [A]
          ring
        _ ≤ 320 * V := mul_le_mul_of_nonneg_left hSelected (by norm_num)

/-- A non-collapsing terminal-time sixth-power scale eliminates the third
arm once the genuine physical viscous terminal integral becomes small. -/
theorem thirdFullKinetic_outerRate_threeWay_noTimeArm244
    (m epsilon sigma LM LG gap V c : ℝ)
    (hc : 0 < c) (hFloor : c ≤ m * sigma ^ 6 * gap)
    (hSmall : V < 119 * c / 320)
    (hThree :
      119 * m ^ 2 * sigma ^ 6 ≤ 320 * LM * V ∨
      119 * m * epsilon * sigma ^ 6 ≤ 160 * LG * V ∨
      119 * m * sigma ^ 6 * gap ≤ 320 * V) :
    119 * m ^ 2 * sigma ^ 6 ≤ 320 * LM * V ∨
      119 * m * epsilon * sigma ^ 6 ≤ 160 * LG * V := by
  rcases hThree with hMass | hYoung | hTime
  · exact Or.inl hMass
  · exact Or.inr hYoung
  · exfalso
    have hLow : 119 * c ≤ 119 * m * sigma ^ 6 * gap := by
      calc
        119 * c ≤ 119 * (m * sigma ^ 6 * gap) :=
          mul_le_mul_of_nonneg_left hFloor
            (by norm_num : (0 : ℝ) ≤ 119)
        _ = 119 * m * sigma ^ 6 * gap := by ring
    have hHigh : 320 * V < 119 * c := by
      have h := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 320)).mp hSmall
      linarith only [h]
    linarith only [hLow, hHigh, hTime]

/-- As the terminal viscous tail vanishes, either physical rate must become
arbitrarily large relative to its OWN natural sixth-power carrier scale.
The proof makes no choice of which rate dominates along the cofinal family. -/
theorem thirdFullKinetic_outerRate_smallTail_amplification244
    (m epsilon sigma LM LG V C : ℝ)
    (hm : 0 < m) (he : 0 < epsilon) (hs : 0 < sigma)
    (hLM : 0 < LM) (hLG : 0 < LG) (hC : 0 < C)
    (hSmallM : V < 119 / (320 * C))
    (hSmallY : V < 119 / (160 * C))
    (hTwo :
      119 * m ^ 2 * sigma ^ 6 ≤ 320 * LM * V ∨
      119 * m * epsilon * sigma ^ 6 ≤ 160 * LG * V) :
    C * m ^ 2 * sigma ^ 6 < LM ∨
      C * m * epsilon * sigma ^ 6 < LG := by
  have hCne : C ≠ 0 := ne_of_gt hC
  rcases hTwo with hMass | hYoung
  · left
    have hUpper : 320 * LM * V <
        320 * LM * (119 / (320 * C)) :=
      mul_lt_mul_of_pos_left hSmallM (by positivity)
    have hBoth := lt_of_le_of_lt hMass hUpper
    have hTimes := mul_lt_mul_of_pos_left hBoth hC
    have hFinal : 119 * (C * m ^ 2 * sigma ^ 6) < 119 * LM := by
      calc
        _ = C * (119 * m ^ 2 * sigma ^ 6) := by ring
        _ < C * (320 * LM * (119 / (320 * C))) := hTimes
        _ = 119 * LM := by
          field_simp [hCne]
          <;> ring
    nlinarith only [hFinal]
  · right
    have hUpper : 160 * LG * V <
        160 * LG * (119 / (160 * C)) :=
      mul_lt_mul_of_pos_left hSmallY (by positivity)
    have hBoth := lt_of_le_of_lt hYoung hUpper
    have hTimes := mul_lt_mul_of_pos_left hBoth hC
    have hFinal : 119 * (C * m * epsilon * sigma ^ 6) < 119 * LG := by
      calc
        _ = C * (119 * m * epsilon * sigma ^ 6) := by ring
        _ < C * (160 * LG * (119 / (160 * C))) := hTimes
        _ = 119 * LG := by
          field_simp [hCne]
          <;> ring
    nlinarith only [hFinal]

/-- Consequence for the ORIGINAL actual Navier--Stokes selected outer
carriers. If the physical terminal distance is large enough in the
margin-weighted sixth-power scaling, one of the two quantitative rates
must accelerate beyond every prescribed multiple of its natural scale.
The rates remain hypotheses; their existence is not inferred from H3. -/
theorem thirdFullPhysical_cofinalSelectedOuterMargins_forceRateAmplification244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x rho sigma margin epsilon LM LG : ℕ → ℝ)
    (hx : ∀ k : ℕ, x k ∈ Set.Ioo b T)
    (hCofinal : Tendsto x atTop (𝓝 T))
    (hRho : ∀ k : ℕ, 0 < rho k)
    (hAspect : ∀ k : ℕ, 2 * rho k ≤ sigma k)
    (hMargin : ∀ k : ℕ, 0 < margin k)
    (hEps : ∀ k : ℕ, 0 < epsilon k)
    (hLM : ∀ k : ℕ, 0 < LM k)
    (hLG : ∀ k : ℕ, 0 < LG k)
    (hExcess : ∀ k : ℕ,
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          (rho k) (velocityH3Energy0At u b)) + margin k ≤
      ((rho k ^ 2 + sigma k ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k) (rho k))
    (hPeak : ∀ k : ℕ, 2 * epsilon k ≤
      thirdFullPhysicalActualAnnularKineticDeficit244
        hH3 b (x k) (rho k) (sigma k))
    (hMassRate : ∀ k : ℕ, ∀ s : ℝ, s ∈ Set.Ico (x k) T →
      |((rho k ^ 2 + sigma k ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 s (rho k) -
        ((rho k ^ 2 + sigma k ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k) (rho k)| ≤
        LM k * (s - x k))
    (hDeficitRate : ∀ k : ℕ, ∀ s : ℝ, s ∈ Set.Ico (x k) T →
      |thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s (rho k) (sigma k) -
        thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b (x k) (rho k) (sigma k)| ≤
        LG k * (s - x k))
    (c : ℝ) (hc : 0 < c)
    (hTerminalScale : ∀ᶠ k : ℕ in atTop,
      c ≤ margin k * sigma k ^ 6 * (T - x k)) :
    ∀ C : ℝ, 0 < C →
      ∀ᶠ k : ℕ in atTop,
        C * margin k ^ 2 * sigma k ^ 6 < LM k ∨
        C * margin k * epsilon k * sigma k ^ 6 < LG k := by
  obtain ⟨delta, hWindows, hIntegrated, _hCompression⟩ :=
    thirdFullPhysical_cofinalSelectedOuterMargins_explicitTemporalRateCompression244
      hH3 hClass hDInt b hb x rho sigma margin epsilon LM LG
      hx hCofinal hRho hAspect hMargin hEps hLM hLG
      hExcess hPeak hMassRate hDeficitRate
  let V : ℕ → ℝ := fun k =>
    ∫ r in x k..T, velocityH3DissipationAt u r
  have hTail : Tendsto V atTop (𝓝 (0 : ℝ)) :=
    thirdFull_scalarTerminalTail_integral_tendsto_zero244
      (velocityH3DissipationAt u) a T hClass.terminal_start.2
      hDInt x hCofinal
      (Filter.Eventually.of_forall (fun k =>
        ⟨le_of_lt (lt_trans hb.1 (hx k).1), (hx k).2.le⟩))
  have hThree (k : ℕ) :
      119 * margin k ^ 2 * sigma k ^ 6 ≤ 320 * LM k * V k ∨
      119 * margin k * epsilon k * sigma k ^ 6 ≤ 160 * LG k * V k ∨
      119 * margin k * sigma k ^ 6 * (T - x k) ≤ 320 * V k := by
    have hWidth := (hWindows k).1
    have hCost := hIntegrated k
    rw [hWidth] at hCost
    exact thirdFullKinetic_explicitOuterRate_threeWayBarrier244
      (margin k) (epsilon k) (sigma k) (LM k) (LG k)
      (T - x k) (V k) (hLM k) (hLG k) hCost
  have hSmallTime : ∀ᶠ k : ℕ in atTop, V k < 119 * c / 320 :=
    hTail.eventually
      (isOpen_Iio.mem_nhds (by positivity : (0 : ℝ) < 119 * c / 320))
  have hTwo : ∀ᶠ k : ℕ in atTop,
      119 * margin k ^ 2 * sigma k ^ 6 ≤ 320 * LM k * V k ∨
      119 * margin k * epsilon k * sigma k ^ 6 ≤ 160 * LG k * V k := by
    filter_upwards [hTerminalScale, hSmallTime] with k hFloor hSmall
    exact thirdFullKinetic_outerRate_threeWay_noTimeArm244
      (margin k) (epsilon k) (sigma k) (LM k) (LG k)
      (T - x k) (V k) c hc hFloor hSmall (hThree k)
  intro C hC
  have hSmallM : ∀ᶠ k : ℕ in atTop, V k < 119 / (320 * C) :=
    hTail.eventually
      (isOpen_Iio.mem_nhds (by positivity : (0 : ℝ) < 119 / (320 * C)))
  have hSmallY : ∀ᶠ k : ℕ in atTop, V k < 119 / (160 * C) :=
    hTail.eventually
      (isOpen_Iio.mem_nhds (by positivity : (0 : ℝ) < 119 / (160 * C)))
  filter_upwards [hTwo, hSmallM, hSmallY] with k hk hV1 hV2
  have hSigma : 0 < sigma k := by
    linarith only [hRho k, hAspect k]
  exact thirdFullKinetic_outerRate_smallTail_amplification244
    (margin k) (epsilon k) (sigma k) (LM k) (LG k) (V k) C
    (hMargin k) (hEps k) hSigma (hLM k) (hLG k) hC
    hV1 hV2 hk

end
end PrimeTensor.FirstMonomialTriad
