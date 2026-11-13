import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierIntegratedCompression
import Mathlib.Tactic

/-!
# Selected outer carrier: explicit temporal-rate compression

The earlier physical theorem forces 119 * margin * sigma^6 <= 80 * D_H3(s)
whenever the *actual* sharp highpass excess and the actual annular Young-width
kinetic deficit have the required signs at time s. Its continuity argument
only supplies an unquantified time interval.

Here we keep the same physical observables but assume quantitative forward
variation bounds on the two scalar quantities, with arbitrary positive
rates LM and LG. These are EXTRA hypotheses, not claimed consequences of
finite H3 dissipation. We obtain the explicit admissible width

  d = min { margin/(2 LM), epsilon/LG, (T-x)/2 } > 0

and the true terminal-viscosity payment

  d * (119 * margin * sigma^6 / 160) <= integral_x^T D_H3.

For cofinal snapshots, these explicit rates must satisfy the same vanishing
sixth-power terminal-tail charge. Thus a prospective PDE time-modulus estimate
has a numerical target to beat, without pretending that continuity supplies
an inverse time scale.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Explicit survival of a selected physical outer margin and annular Young
width deficit under quantitative *forward* variation bounds. The weighted
highpass quantity already includes the exact rho/sigma kinetic multiplier.
The hypotheses concern actual physical H3-path observables. -/
theorem thirdFullPhysical_selectedOuterMargin_explicitTemporalRateWindow244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (rho sigma margin epsilon LM LG : ℝ)
    (hRho : 0 < rho) (hAspect : 2 * rho ≤ sigma)
    (hMargin : 0 < margin) (hEps : 0 < epsilon)
    (hLM : 0 < LM) (hLG : 0 < LG)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho)
    (hPeak : 2 * epsilon ≤
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma)
    (hMassRate : ∀ s : ℝ, s ∈ Set.Ico x T →
      |((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho -
        ((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho| ≤
        LM * (s - x))
    (hDeficitRate : ∀ s : ℝ, s ∈ Set.Ico x T →
      |thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma -
        thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma| ≤
        LG * (s - x)) :
    ∃ delta : ℝ,
      delta = min (margin / (2 * LM))
        (min (epsilon / LG) ((T - x) / 2)) ∧
      0 < delta ∧ x + delta < T ∧
      delta * (119 * margin * sigma ^ 6 / 160) ≤
        ∫ r in x..T, velocityH3DissipationAt u r := by
  let delta : ℝ := min (margin / (2 * LM))
    (min (epsilon / LG) ((T - x) / 2))
  have hd : 0 < delta := by
    dsimp only [delta]
    exact lt_min (div_pos hMargin (by positivity))
      (lt_min (div_pos hEps hLG) (by linarith only [hx.2]))
  have hdLM : delta ≤ margin / (2 * LM) := by
    dsimp only [delta]
    exact min_le_left _ _
  have hdLG : delta ≤ epsilon / LG := by
    dsimp only [delta]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hdT : delta ≤ (T - x) / 2 := by
    dsimp only [delta]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hEnd : x + delta < T := by
    linarith only [hdT, hx.2]
  have hLMbound : LM * delta ≤ margin / 2 := by
    calc
      LM * delta = delta * LM := by ring
      _ ≤ margin / (2 * LM) * LM :=
        mul_le_mul_of_nonneg_right hdLM hLM.le
      _ = margin / 2 := by
        field_simp [ne_of_gt hLM]
        <;> ring
  have hLGbound : LG * delta ≤ epsilon := by
    calc
      LG * delta = delta * LG := by ring
      _ ≤ epsilon / LG * LG :=
        mul_le_mul_of_nonneg_right hdLG hLG.le
      _ = epsilon := by
        field_simp [ne_of_gt hLG]
        <;> ring
  have hWindow (s : ℝ) (hs : s ∈ Set.Icc x (x + delta)) :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin / 2 ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho ∧
      0 ≤ thirdFullPhysicalActualAnnularKineticDeficit244
        hH3 b s rho sigma := by
    have hsRange : s ∈ Set.Ico x T :=
      ⟨hs.1, lt_of_le_of_lt hs.2 hEnd⟩
    have hsDelta : s - x ≤ delta := by
      linarith only [hs.2]
    have hMassAbs :
        |((rho ^ 2 + sigma ^ 2) / 2) *
            thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho -
          ((rho ^ 2 + sigma ^ 2) / 2) *
            thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho| ≤
        margin / 2 := by
      calc
        _ ≤ LM * (s - x) := hMassRate s hsRange
        _ ≤ LM * delta :=
          mul_le_mul_of_nonneg_left hsDelta hLM.le
        _ ≤ margin / 2 := hLMbound
    have hDefAbs :
        |thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma -
          thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma| ≤
        epsilon := by
      calc
        _ ≤ LG * (s - x) := hDeficitRate s hsRange
        _ ≤ LG * delta :=
          mul_le_mul_of_nonneg_left hsDelta hLG.le
        _ ≤ epsilon := hLGbound
    have hMassLower := (abs_le.mp hMassAbs).1
    have hDefLower := (abs_le.mp hDefAbs).1
    constructor
    · linarith only [hExcess, hMassLower]
    · linarith only [hPeak, hDefLower, hEps]
  have hCharge := thirdFullPhysical_selectedOuterMargin_integratedWindow244
    hH3 hClass hDInt b hb x hx rho sigma (margin / 2) delta
    hRho hAspect (div_pos hMargin (by norm_num : (0 : ℝ) < 2))
    hd hEnd hWindow
  refine ⟨delta, rfl, hd, hEnd, ?_⟩
  convert hCharge using 1 <;> ring

/-- Cofinal snapshots have vanishing *explicit* inverse-rate viscous cost.
Unlike the prior continuity-only result, the width is now an actual formula
in two putative temporal variation rates and the terminal time distance.
No uniform bound on those rates is assumed. -/
theorem thirdFullPhysical_cofinalSelectedOuterMargins_explicitTemporalRateCompression244
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
        LG k * (s - x k)) :
    ∃ delta : ℕ → ℝ,
      (∀ k : ℕ, delta k = min (margin k / (2 * LM k))
          (min (epsilon k / LG k) ((T - x k) / 2)) ∧
        0 < delta k ∧ x k + delta k < T) ∧
      (∀ k : ℕ, delta k * (119 * margin k * sigma k ^ 6 / 160) ≤
        ∫ r in x k..T, velocityH3DissipationAt u r) ∧
      Tendsto (fun k : ℕ =>
        delta k * (119 * margin k * sigma k ^ 6 / 160))
        atTop (𝓝 (0 : ℝ)) := by
  classical
  have hEach (k : ℕ) :
      ∃ d : ℝ,
        d = min (margin k / (2 * LM k))
          (min (epsilon k / LG k) ((T - x k) / 2)) ∧
        0 < d ∧ x k + d < T ∧
        d * (119 * margin k * sigma k ^ 6 / 160) ≤
          ∫ r in x k..T, velocityH3DissipationAt u r := by
    exact thirdFullPhysical_selectedOuterMargin_explicitTemporalRateWindow244
      hH3 hClass hDInt b hb (x k) (hx k)
      (rho k) (sigma k) (margin k) (epsilon k) (LM k) (LG k)
      (hRho k) (hAspect k) (hMargin k) (hEps k) (hLM k) (hLG k)
      (hExcess k) (hPeak k) (hMassRate k) (hDeficitRate k)
  choose d hdEq hdPos hdEnd hIntegrated using hEach
  have hTail : Tendsto (fun k : ℕ =>
      ∫ r in x k..T, velocityH3DissipationAt u r)
      atTop (𝓝 (0 : ℝ)) :=
    thirdFull_scalarTerminalTail_integral_tendsto_zero244
      (velocityH3DissipationAt u) a T hClass.terminal_start.2
      hDInt x hCofinal
      (Filter.Eventually.of_forall (fun k =>
        ⟨le_of_lt (lt_trans hb.1 (hx k).1), (hx k).2.le⟩))
  have hNonneg (k : ℕ) :
      0 ≤ d k * (119 * margin k * sigma k ^ 6 / 160) := by
    have hSigma : 0 ≤ sigma k := by
      linarith only [hRho k, hAspect k]
    have hD : 0 ≤ d k := (hdPos k).le
    have hM : 0 ≤ margin k := (hMargin k).le
    positivity
  have hLimit : Tendsto (fun k : ℕ =>
      d k * (119 * margin k * sigma k ^ 6 / 160))
      atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero' (Filter.Eventually.of_forall hNonneg)
      (Filter.Eventually.of_forall hIntegrated) hTail
  exact ⟨d, (fun k => ⟨hdEq k, hdPos k, hdEnd k⟩),
    hIntegrated, hLimit⟩

end
end PrimeTensor.FirstMonomialTriad
