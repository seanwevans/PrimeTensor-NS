import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.UniformNineteenQuarterTailMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.NineteenQuarterMildMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.UniformFourthMomentEnvelope
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.UniformFifteenQuarterMomentEnvelope

/-!
# Sixth Fréchet endpoint: interval-uniform selected nineteen-quarter state envelope

`UniformNineteenQuarterTailMass` supplies one terminal-tail `19/4` budget valid
for every `r ∈ [a,t]`.

This file closes the complete `19/4` state uniformization:

* the free `19/4` heat coefficient is antitone in positive time;
* the midpoint-head residual `3/4` heat coefficient is antitone;
* the inherited full-fourth Duhamel state at `r/2` is bounded directly by the
  already-compiled interval-uniform fourth-moment Duhamel estimate on
  `[a/2,t]`;
* the terminal tail is bounded by the enlarged global `19/4` tail budget.

The resulting explicit constant bounds the canonical raw Fourier `19/4` mass
of every selected mild coordinate throughout `[a,t]`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSixthEndpointUniformNineteenQuarterMomentEnvelope
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The complete positive-time free-heat `19/4` coefficient is antitone. -/
theorem h3HeatNineteenQuarterRawL1Coefficient_antitone_pos
    {ν a b : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (hab : a ≤ b) :
    h3HeatNineteenQuarterRawL1Coefficient ν b
      ≤
    h3HeatNineteenQuarterRawL1Coefficient ν a := by
  have ha2 : 0 < a / 2 := by
    positivity

  have hab2 : a / 2 ≤ b / 2 := by
    linarith

  have hFourth :
      h3HeatFourthRawL1Coefficient ν (b / 2)
        ≤
      h3HeatFourthRawL1Coefficient ν (a / 2) :=
    h3HeatFourthRawL1Coefficient_antitone_pos
      hν ha2 hab2

  have hThreeQuarter :
      h3HeatThreeQuarterMomentCoefficient ν (b / 2)
        ≤
      h3HeatThreeQuarterMomentCoefficient ν (a / 2) :=
    h3HeatThreeQuarterMomentCoefficient_antitone_pos
      hν ha2 hab2

  have hb :
      0 < b :=
    lt_of_lt_of_le ha hab

  have hThreeQuarterB0 :
      0 ≤ h3HeatThreeQuarterMomentCoefficient ν (b / 2) :=
    h3HeatThreeQuarterMomentCoefficient_nonneg
      hν.le (by positivity)

  have hFourthA0 :
      0 ≤ h3HeatFourthRawL1Coefficient ν (a / 2) :=
    h3HeatFourthRawL1Coefficient_nonneg
      hν.le (by positivity)

  unfold h3HeatNineteenQuarterRawL1Coefficient

  exact
    mul_le_mul
      hFourth
      hThreeQuarter
      hThreeQuarterB0
      hFourthA0

/-- Uniform midpoint-head `19/4` envelope on `[a,t]`.

The `max 0` wrapper makes the inherited uniform fourth Duhamel factor
manifestly nonnegative without reopening its internal budget algebra. -/
noncomputable def h3SelectedDuhamelHeadNineteenQuarterMomentUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  h3HeatThreeQuarterMomentCoefficient ν (a / 2) *
    max 0
      (h3SelectedDuhamelFourthMomentUniformEnvelope
        ν A (a / 2) t)

/-- Every selected midpoint head at `r ∈ [a,t]` is bounded by the single
uniform `19/4` head envelope. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_nineteenQuarterMomentMass_le_uniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ (lt_of_lt_of_le ha har) i :
              H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3SelectedDuhamelHeadNineteenQuarterMomentUniformEnvelope
      ν A a t := by
  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := r / 2) hν U₀ hA hU₀ i

  have hr : 0 < r :=
    lt_of_lt_of_le ha har

  have hrR :
      r ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hrt htR

  have ha2 : 0 < a / 2 := by
    positivity

  have hr2 : 0 < r / 2 := by
    positivity

  have har2 : a / 2 ≤ r / 2 := by
    linarith

  have hr2t : r / 2 ≤ t := by
    have hr0 : 0 ≤ r := hr.le
    linarith

  have hr2R :
      r / 2 ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans (by linarith) hrR

  have hD4 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_fourthMoment_integrable
        hν U₀ hA hU₀ hr2 hr2R i

  have hHeat :=
    h3HeatFourierSymbol_nineteenQuarter_norm_integral_le_of_fourth
      hν hr2 D hD4

  have hD4Uniform :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 4 * ‖D ξ‖)
        ≤
      h3SelectedDuhamelFourthMomentUniformEnvelope
        ν A (a / 2) t := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_fourthMoment_integral_le_uniform_on
        hν U₀ hA hU₀
        ha2 har2 hr2t htR i

  have hD4Max :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 4 * ‖D ξ‖)
        ≤
      max 0
        (h3SelectedDuhamelFourthMomentUniformEnvelope
          ν A (a / 2) t) :=
    le_trans hD4Uniform
      (le_max_right
        0
        (h3SelectedDuhamelFourthMomentUniformEnvelope
          ν A (a / 2) t))

  have hCoeff :
      h3HeatThreeQuarterMomentCoefficient ν (r / 2)
        ≤
      h3HeatThreeQuarterMomentCoefficient ν (a / 2) :=
    h3HeatThreeQuarterMomentCoefficient_antitone_pos
      hν ha2 har2

  have hCoeffR0 :
      0 ≤ h3HeatThreeQuarterMomentCoefficient ν (r / 2) :=
    h3HeatThreeQuarterMomentCoefficient_nonneg
      hν.le hr2.le

  have hMax0 :
      0 ≤
        max 0
          (h3SelectedDuhamelFourthMomentUniformEnvelope
            ν A (a / 2) t) :=
    le_max_left _ _

  have hRep :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heat_mul_halfDuhamelRawFourierL2
      hν U₀ hA hU₀ hr i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
                hν U₀ hA hU₀ (lt_of_lt_of_le ha har) i :
                H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν (r / 2) ξ * D ξ‖ := by
    apply integral_congr_ae
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  unfold h3SelectedDuhamelHeadNineteenQuarterMomentUniformEnvelope

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ (lt_of_lt_of_le ha har) i :
              H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν (r / 2) ξ * D ξ‖ :=
      hIntegralEq
    _ ≤
      h3HeatThreeQuarterMomentCoefficient ν (r / 2) *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 4 * ‖D ξ‖) :=
      hHeat
    _ ≤
      h3HeatThreeQuarterMomentCoefficient ν (r / 2) *
        max 0
          (h3SelectedDuhamelFourthMomentUniformEnvelope
            ν A (a / 2) t) :=
      mul_le_mul_of_nonneg_left hD4Max hCoeffR0
    _ ≤
      h3HeatThreeQuarterMomentCoefficient ν (a / 2) *
        max 0
          (h3SelectedDuhamelFourthMomentUniformEnvelope
            ν A (a / 2) t) :=
      mul_le_mul_of_nonneg_right hCoeff hMax0

/-- Uniform complete selected Duhamel `19/4` envelope on `[a,t]`. -/
noncomputable def h3SelectedDuhamelNineteenQuarterMomentUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  h3SelectedDuhamelHeadNineteenQuarterMomentUniformEnvelope ν A a t +
    h3SelectedDuhamelNineteenQuarterTailIntervalUniformBudget ν A a t

/-- The named selected Duhamel contribution at every `r ∈ [a,t]` has `19/4`
mass bounded by one interval-uniform constant. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_nineteenQuarterMoment_integral_le_uniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
              (t := r) hν U₀ hA hU₀ i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3SelectedDuhamelNineteenQuarterMomentUniformEnvelope
      ν A a t := by
  let H : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
      hν U₀ hA hU₀ (lt_of_lt_of_le ha har) i

  let T : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
      (t := r) hν U₀ hA hU₀ i

  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := r) hν U₀ hA hU₀ i

  have hr : 0 < r :=
    lt_of_lt_of_le ha har

  have hrR :
      r ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hrt htR

  have hHeadInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_nineteenQuarterMoment_integrable
        hν U₀ hA hU₀ hr hrR i

  have hTailInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ * ‖T ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [T]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_nineteenQuarterMoment_integrable
        hν U₀ hA hU₀ hr hrR i

  have hFullInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_nineteenQuarterMoment_integrable
        hν U₀ hA hU₀ hr hrR i

  have hRep :
      ((D : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 => H ξ + T ξ) := by
    dsimp only [D, H, T]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_ae_eq_head_add_tail
        hν U₀ hA hU₀ hr i

  have hWeightedRep :
      (fun ξ : H3FourierPoint3 =>
        h3FourierNineteenQuarterWeight ξ * ‖D ξ‖)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        h3FourierNineteenQuarterWeight ξ * ‖H ξ + T ξ‖) := by
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  have hSumInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ * ‖H ξ + T ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hFullInt.congr hWeightedRep

  have hMajorInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ * ‖H ξ‖ +
            h3FourierNineteenQuarterWeight ξ * ‖T ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHeadInt.add hTailInt

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ * ‖H ξ + T ξ‖
          ≤
        h3FourierNineteenQuarterWeight ξ * ‖H ξ‖ +
          h3FourierNineteenQuarterWeight ξ * ‖T ξ‖ := by
    intro ξ

    have hw :
        0 ≤ h3FourierNineteenQuarterWeight ξ := by
      unfold h3FourierNineteenQuarterWeight
      exact Real.rpow_nonneg (norm_nonneg ξ) _

    calc
      h3FourierNineteenQuarterWeight ξ * ‖H ξ + T ξ‖
          ≤
        h3FourierNineteenQuarterWeight ξ * (‖H ξ‖ + ‖T ξ‖) :=
        mul_le_mul_of_nonneg_left
          (norm_add_le (H ξ) (T ξ))
          hw
      _ =
        h3FourierNineteenQuarterWeight ξ * ‖H ξ‖ +
          h3FourierNineteenQuarterWeight ξ * ‖T ξ‖ := by
        ring

  have hMono :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ * ‖H ξ + T ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (h3FourierNineteenQuarterWeight ξ * ‖H ξ‖ +
          h3FourierNineteenQuarterWeight ξ * ‖T ξ‖) :=
    integral_mono hSumInt hMajorInt hPoint

  have hHeadBound :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ * ‖H ξ‖)
        ≤
      h3SelectedDuhamelHeadNineteenQuarterMomentUniformEnvelope
        ν A a t := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_nineteenQuarterMomentMass_le_uniform_on
        hν U₀ hA hU₀ ha har hrt htR i

  have hTailBound :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ * ‖T ξ‖)
        ≤
      h3SelectedDuhamelNineteenQuarterTailIntervalUniformBudget
        ν A a t := by
    dsimp only [T]
    exact
      integral_nineteenQuarterMoment_h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_le_intervalUniform
        hν U₀ hA hU₀ ha har hrt htR i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ * ‖D ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ * ‖H ξ + T ξ‖ :=
    integral_congr_ae hWeightedRep

  unfold h3SelectedDuhamelNineteenQuarterMomentUniformEnvelope

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ * ‖D ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ * ‖H ξ + T ξ‖ :=
      hIntegralEq
    _ ≤
      ∫ ξ : H3FourierPoint3,
        (h3FourierNineteenQuarterWeight ξ * ‖H ξ‖ +
          h3FourierNineteenQuarterWeight ξ * ‖T ξ‖) :=
      hMono
    _ =
      (∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ * ‖H ξ‖) +
        ∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ * ‖T ξ‖ := by
      rw [integral_add hHeadInt hTailInt]
    _ ≤
      h3SelectedDuhamelHeadNineteenQuarterMomentUniformEnvelope ν A a t +
        h3SelectedDuhamelNineteenQuarterTailIntervalUniformBudget ν A a t :=
      add_le_add hHeadBound hTailBound

/-- Uniform selected mild-state `19/4` envelope on `[a,t]`. -/
noncomputable def h3SelectedMildNineteenQuarterMomentUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  h3HeatNineteenQuarterRawL1Coefficient ν a *
      h3RawFourierL1DeweightingCoefficient * A
    +
  h3SelectedDuhamelNineteenQuarterMomentUniformEnvelope ν A a t

/-- Every named selected mild coordinate at `r ∈ [a,t]` has `19/4` mass
bounded by the uniform state envelope. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_nineteenQuarterMoment_integral_le_uniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              hν U₀ hA hU₀ r i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3SelectedMildNineteenQuarterMomentUniformEnvelope
      ν A a t := by
  let H : H3FourierComplexL2 :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
      hν U₀ (lt_of_lt_of_le ha har) i

  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := r) hν U₀ hA hU₀ i

  let W : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
      hν U₀ hA hU₀ r i

  have hr : 0 < r :=
    lt_of_lt_of_le ha har

  have hrR :
      r ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hrt htR

  have hHeatInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_nineteenQuarterMoment_integrable
        hν U₀ hr i

  have hDuhamelInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_nineteenQuarterMoment_integrable
        hν U₀ hA hU₀ hr hrR i

  have hFullInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ * ‖W ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_nineteenQuarterMoment_integrable
        hν U₀ hA hU₀ hr hrR i

  have hRep :
      ((W : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 => H ξ - D ξ) := by
    dsimp only [W, H, D]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_heat_add_duhamel
        hν U₀ hA hU₀ hr hrR i

  have hWeightedRep :
      (fun ξ : H3FourierPoint3 =>
        h3FourierNineteenQuarterWeight ξ * ‖W ξ‖)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        h3FourierNineteenQuarterWeight ξ * ‖H ξ - D ξ‖) := by
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  have hSumInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ * ‖H ξ - D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hFullInt.congr hWeightedRep

  have hMajorInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ * ‖H ξ‖ +
            h3FourierNineteenQuarterWeight ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHeatInt.add hDuhamelInt

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ * ‖H ξ - D ξ‖
          ≤
        h3FourierNineteenQuarterWeight ξ * ‖H ξ‖ +
          h3FourierNineteenQuarterWeight ξ * ‖D ξ‖ := by
    intro ξ

    have hw :
        0 ≤ h3FourierNineteenQuarterWeight ξ := by
      unfold h3FourierNineteenQuarterWeight
      exact Real.rpow_nonneg (norm_nonneg ξ) _

    calc
      h3FourierNineteenQuarterWeight ξ * ‖H ξ - D ξ‖
          ≤
        h3FourierNineteenQuarterWeight ξ * (‖H ξ‖ + ‖D ξ‖) :=
        mul_le_mul_of_nonneg_left
          (norm_sub_le (H ξ) (D ξ))
          hw
      _ =
        h3FourierNineteenQuarterWeight ξ * ‖H ξ‖ +
          h3FourierNineteenQuarterWeight ξ * ‖D ξ‖ := by
        ring

  have hMono :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ * ‖H ξ - D ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (h3FourierNineteenQuarterWeight ξ * ‖H ξ‖ +
          h3FourierNineteenQuarterWeight ξ * ‖D ξ‖) :=
    integral_mono hSumInt hMajorInt hPoint

  have hHeatPoint :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ * ‖H ξ‖)
        ≤
      h3HeatNineteenQuarterRawL1Coefficient ν r *
        h3RawFourierL1DeweightingCoefficient * A := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_nineteenQuarterMoment_integral_le
        hν U₀ hA hU₀ hr i

  have hHeatCoeff :
      h3HeatNineteenQuarterRawL1Coefficient ν r
        ≤
      h3HeatNineteenQuarterRawL1Coefficient ν a :=
    h3HeatNineteenQuarterRawL1Coefficient_antitone_pos
      hν ha har

  have hHeatFactor0 :
      0 ≤ h3RawFourierL1DeweightingCoefficient * A :=
    mul_nonneg
      h3RawFourierL1DeweightingCoefficient_nonneg
      hA.le

  have hHeatBound :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ * ‖H ξ‖)
        ≤
      h3HeatNineteenQuarterRawL1Coefficient ν a *
        h3RawFourierL1DeweightingCoefficient * A := by
    calc
      (∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ * ‖H ξ‖)
          ≤
        h3HeatNineteenQuarterRawL1Coefficient ν r *
          h3RawFourierL1DeweightingCoefficient * A :=
        hHeatPoint
      _ =
        h3HeatNineteenQuarterRawL1Coefficient ν r *
          (h3RawFourierL1DeweightingCoefficient * A) := by
        ring
      _ ≤
        h3HeatNineteenQuarterRawL1Coefficient ν a *
          (h3RawFourierL1DeweightingCoefficient * A) :=
        mul_le_mul_of_nonneg_right
          hHeatCoeff hHeatFactor0
      _ =
        h3HeatNineteenQuarterRawL1Coefficient ν a *
          h3RawFourierL1DeweightingCoefficient * A := by
        ring

  have hDuhamelBound :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ * ‖D ξ‖)
        ≤
      h3SelectedDuhamelNineteenQuarterMomentUniformEnvelope
        ν A a t := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_nineteenQuarterMoment_integral_le_uniform_on
        hν U₀ hA hU₀ ha har hrt htR i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ * ‖W ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ * ‖H ξ - D ξ‖ :=
    integral_congr_ae hWeightedRep

  unfold h3SelectedMildNineteenQuarterMomentUniformEnvelope

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ * ‖W ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ * ‖H ξ - D ξ‖ :=
      hIntegralEq
    _ ≤
      ∫ ξ : H3FourierPoint3,
        (h3FourierNineteenQuarterWeight ξ * ‖H ξ‖ +
          h3FourierNineteenQuarterWeight ξ * ‖D ξ‖) :=
      hMono
    _ =
      (∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ * ‖H ξ‖) +
        ∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ * ‖D ξ‖ := by
      rw [integral_add hHeatInt hDuhamelInt]
    _ ≤
      h3HeatNineteenQuarterRawL1Coefficient ν a *
          h3RawFourierL1DeweightingCoefficient * A
        +
      h3SelectedDuhamelNineteenQuarterMomentUniformEnvelope ν A a t :=
      add_le_add hHeatBound hDuhamelBound

/-- Every canonical selected mild coordinate has one `19/4` raw Fourier mass
bound valid throughout `[a,t]`. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineteenQuarterMass_le_uniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    h3SpectralScalarRawFourierNineteenQuarterMass
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ r i)
      ≤
    h3SelectedMildNineteenQuarterMomentUniformEnvelope
      ν A a t := by
  have hNamed :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_nineteenQuarterMoment_integral_le_uniform_on
      hν U₀ hA hU₀ ha har hrt htR i

  have hEq :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_nineteenQuarterMoment_ae_eq_rawFourierL2
      (t := r)
      hν U₀ hA hU₀ i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ r i) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              hν U₀ hA hU₀ r i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖ :=
    integral_congr_ae hEq

  unfold h3SpectralScalarRawFourierNineteenQuarterMass
  rw [hIntegralEq]
  exact hNamed

/-- The interval-uniform selected mild `19/4` envelope is nonnegative on every
nonempty positive interval. -/
theorem h3SelectedMildNineteenQuarterMomentUniformEnvelope_nonneg
    {ν A a t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    0 ≤ h3SelectedMildNineteenQuarterMomentUniformEnvelope
      ν A a t := by
  let k0 : Fin 3 := 0

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hMass0 :
      0 ≤
        h3SpectralScalarRawFourierNineteenQuarterMass
          (W a k0) :=
    h3SpectralScalarRawFourierNineteenQuarterMass_nonneg
      (W a k0)

  have hBound0 :
      h3SpectralScalarRawFourierNineteenQuarterMass
          (W a k0)
        ≤
      h3SelectedMildNineteenQuarterMomentUniformEnvelope
        ν A a t := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineteenQuarterMass_le_uniform_on
        hν U₀ hA hU₀
        ha (le_refl a) hat.le htR k0

  exact le_trans hMass0 hBound0

end
end Euclidean
end Bridge
end PrimeTensor
