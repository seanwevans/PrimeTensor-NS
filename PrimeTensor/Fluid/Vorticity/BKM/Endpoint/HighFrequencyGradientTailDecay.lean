import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.HighFrequencyGradientL2
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# BKM endpoint: qualitative decay of the high-frequency H³ multiplier tail

`HighFrequencyGradientL2` isolates the upper-frequency gradient contribution as

    m_hi,i(ξ) G(ξ),

where

    m_hi,i(ξ)
      = χ_hi(ξ) d_i(ξ) W₃(ξ)⁻¹

belongs to Fourier `L²`.

The dyadic upper cutoff radius tends to infinity.  Hence for each fixed
frequency point the high cutoff is eventually exactly zero.  The multiplier is
uniformly dominated by

    (2π) ‖ξ‖ W₃(ξ)⁻¹,

which already belongs to `L²`.

Dominated convergence therefore gives

    m_hi,i → 0 in L²

for every derivative coordinate `i`.  Consequently the scalar multiplier norm
appearing in the high-frequency pointwise BKM estimate tends to zero.

This checkpoint is intentionally qualitative.  The next quantitative layer can
replace convergence by an explicit dyadic decay rate without touching the
Fourier/Hölder packaging again.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeBKMEndpointHighFrequencyGradientTailDecay
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Pointwise disappearance of the high cutoff -/

theorem h3BKMDyadicRadius_tendsto_atTop :
    Tendsto
      h3BKMDyadicRadius
      atTop
      atTop := by

  unfold h3BKMDyadicRadius

  exact
    tendsto_pow_atTop_atTop_of_one_lt
      (show (1 : ℝ) < 2 by norm_num)

/--
For every fixed Fourier point, sufficiently large dyadic upper cutoffs contain
that point in their inner ball.
-/
theorem h3BKMDyadicHighFrequencyFactor_eventually_eq_zero
    (ξ : H3FourierPoint3) :
    ∀ᶠ hi : ℕ in atTop,
      h3BKMDyadicHighFrequencyFactor hi ξ = 0 := by

  have hEventually :
      ∀ᶠ hi : ℕ in atTop,
        ‖ξ‖ ≤ h3BKMDyadicRadius hi :=
    h3BKMDyadicRadius_tendsto_atTop
      (eventually_ge_atTop ‖ξ‖)

  filter_upwards [hEventually] with hi hhi

  have hSucc :
      ‖ξ‖ ≤ h3BKMDyadicRadius (hi + 1) := by
    calc
      ‖ξ‖
          ≤
        h3BKMDyadicRadius hi := hhi
      _ ≤
        h3BKMDyadicRadius (hi + 1) := by
          rw [h3BKMDyadicRadius_succ]
          have hR :
              0 ≤ h3BKMDyadicRadius hi :=
            (h3BKMDyadicRadius_pos hi).le
          nlinarith

  exact
    h3BKMDyadicHighFrequencyFactor_eq_zero_of_norm_le
      hi hSucc

/--
For every fixed Fourier point and coordinate, the high-gradient deweighting
multiplier is eventually exactly zero.
-/
theorem h3BKMHighGradientDeweightingMultiplier_eventually_eq_zero
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    ∀ᶠ hi : ℕ in atTop,
      h3BKMHighGradientDeweightingMultiplier hi i ξ = 0 := by

  filter_upwards [
    h3BKMDyadicHighFrequencyFactor_eventually_eq_zero ξ
  ] with hi hhi

  unfold h3BKMHighGradientDeweightingMultiplier

  rw [hhi]

  simp

theorem h3BKMHighGradientDeweightingMultiplier_tendsto_pointwise_zero
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    Tendsto
      (fun hi : ℕ =>
        h3BKMHighGradientDeweightingMultiplier hi i ξ)
      atTop
      (𝓝 0) := by

  refine
    (tendsto_congr'
      (h3BKMHighGradientDeweightingMultiplier_eventually_eq_zero i ξ)).2
      tendsto_const_nhds

/-! ## Continuous representatives and L² dominated convergence -/

theorem h3BKMHighGradientDeweightingMultiplier_continuous
    (hi : ℕ)
    (i : Fin 3) :
    Continuous
      (h3BKMHighGradientDeweightingMultiplier hi i) := by

  have hHigh :
      Continuous
        (fun ξ : H3FourierPoint3 =>
          (h3BKMDyadicHighFrequencyFactor hi ξ : ℂ)) :=
    Complex.continuous_ofReal.comp
      (h3BKMDyadicHighFrequencyFactor_continuous hi)

  have hInv :
      Continuous
        (fun ξ : H3FourierPoint3 =>
          h3SobolevFrequencyWeightInvComplex ξ) := by
    unfold h3SobolevFrequencyWeightInvComplex
    exact
      Complex.continuous_ofReal.comp
        continuous_h3SobolevFrequencyWeightInv

  unfold h3BKMHighGradientDeweightingMultiplier

  exact
    (hHigh.mul
      (h3FourierDerivativeSymbol_continuous i)).mul hInv

/--
The raw `L²` seminorm of the high-gradient deweighting multiplier tends to
zero.
-/
theorem h3BKMHighGradientDeweightingMultiplier_tendsto_eLpNorm_two
    (i : Fin 3) :
    Tendsto
      (fun hi : ℕ =>
        eLpNorm
          (h3BKMHighGradientDeweightingMultiplier hi i)
          2
          (volume : Measure H3FourierPoint3))
      atTop
      (𝓝 0) := by

  have hpZero :
      (2 : ℝ≥0∞) ≠ 0 := by
    norm_num

  have hpTop :
      (2 : ℝ≥0∞) ≠ ∞ := by
    norm_num

  have hpPos :
      0 < (2 : ℝ≥0∞).toReal :=
    ENNReal.toReal_pos hpZero hpTop

  suffices hIntegral :
      Tendsto
        (fun hi : ℕ =>
          ∫⁻ ξ : H3FourierPoint3,
            ‖h3BKMHighGradientDeweightingMultiplier hi i ξ‖ₑ
                ^ (2 : ℝ≥0∞).toReal
            ∂volume)
        atTop
        (𝓝 0) by

    simp only [
      eLpNorm_eq_lintegral_rpow_enorm_toReal
        hpZero
        hpTop
    ]

    have hPow :
        Tendsto
          (fun z : ℝ≥0∞ =>
            z ^ (1 / (2 : ℝ≥0∞).toReal))
          (𝓝 0)
          (𝓝
            ((0 : ℝ≥0∞) ^
              (1 / (2 : ℝ≥0∞).toReal))) :=
      ENNReal.continuous_rpow_const.tendsto 0

    have hComposed :=
      hPow.comp hIntegral

    have hExponentPos :
        0 < 1 / (2 : ℝ≥0∞).toReal := by
      simpa [one_div] using
        (_root_.inv_pos.mpr hpPos)

    have hZeroPow :
        (0 : ℝ≥0∞) ^
            (1 / (2 : ℝ≥0∞).toReal)
          =
        0 := by
      exact
        ENNReal.zero_rpow_of_pos hExponentPos

    rw [hZeroPow] at hComposed

    simpa only [Function.comp_def] using hComposed

  let majorant : H3FourierPoint3 → ℝ :=
    fun ξ =>
      (2 * Real.pi)
        *
      h3SobolevFrequencyFirstMomentInv ξ

  have hMajorantMem :
      MemLp
        majorant
        2
        (volume : Measure H3FourierPoint3) := by
    dsimp [majorant]
    exact
      h3SobolevFrequencyFirstMomentInv_memLp2.const_mul
        (2 * Real.pi)

  have hFMeas :
      ∀ hi : ℕ,
        Measurable
          (fun ξ : H3FourierPoint3 =>
            ‖h3BKMHighGradientDeweightingMultiplier hi i ξ‖ₑ
              ^ (2 : ℝ≥0∞).toReal) := by
    intro hi

    exact
      ((h3BKMHighGradientDeweightingMultiplier_continuous hi i).measurable.enorm.pow_const
        (2 : ℝ≥0∞).toReal)

  have hBound :
      ∀ hi : ℕ,
        (fun ξ : H3FourierPoint3 =>
          ‖h3BKMHighGradientDeweightingMultiplier hi i ξ‖ₑ
            ^ (2 : ℝ≥0∞).toReal)
          ≤ᵐ[volume]
        (fun ξ : H3FourierPoint3 =>
          ‖majorant ξ‖ₑ
            ^ (2 : ℝ≥0∞).toReal) := by
    intro hi

    exact
      Filter.Eventually.of_forall
        (fun ξ =>
          ENNReal.rpow_le_rpow
            (by
              rw [enorm_le_iff_norm_le]

              have hFirstNonneg :
                  0 ≤ h3SobolevFrequencyFirstMomentInv ξ := by
                unfold
                  h3SobolevFrequencyFirstMomentInv
                  h3SobolevFrequencyWeightInv
                exact
                  mul_nonneg
                    (norm_nonneg ξ)
                    (inv_nonneg.mpr
                      (h3SobolevFrequencyWeight_pos ξ).le)

              have hMajorantNonneg :
                  0 ≤ majorant ξ := by
                dsimp [majorant]
                exact
                  mul_nonneg
                    (by positivity)
                    hFirstNonneg

              rw [
                show ‖majorant ξ‖ = majorant ξ by
                  rw [
                    Real.norm_eq_abs,
                    abs_of_nonneg hMajorantNonneg
                  ]
              ]
              dsimp [majorant]
              exact
                norm_h3BKMHighGradientDeweightingMultiplier_le
                  hi i ξ)
            ENNReal.toReal_nonneg)

  have hFinite :
      (∫⁻ ξ : H3FourierPoint3,
        ‖majorant ξ‖ₑ ^ (2 : ℝ≥0∞).toReal
        ∂volume)
        ≠
      ∞ := by
    exact
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        hpZero
        hpTop
        hMajorantMem.2).ne

  have hLimit :
      ∀ᵐ ξ : H3FourierPoint3 ∂volume,
        Tendsto
          (fun hi : ℕ =>
            ‖h3BKMHighGradientDeweightingMultiplier hi i ξ‖ₑ
              ^ (2 : ℝ≥0∞).toReal)
          atTop
          (𝓝 0) := by

    filter_upwards with ξ

    refine
      (tendsto_congr' ?_).2
        tendsto_const_nhds

    filter_upwards [
      h3BKMHighGradientDeweightingMultiplier_eventually_eq_zero
        i ξ
    ] with hi hhi

    rw [hhi]

    simp

  simpa using
    (tendsto_lintegral_of_dominated_convergence
      (fun ξ : H3FourierPoint3 =>
        ‖majorant ξ‖ₑ ^ (2 : ℝ≥0∞).toReal)
      hFMeas
      hBound
      hFinite
      hLimit)

/-! ## Bundled L² and scalar norm decay -/

/--
The bundled high-gradient deweighting multiplier converges strongly to zero in
Fourier `L²`.
-/
theorem h3BKMHighGradientDeweightingMultiplierL2_tendsto_zero
    (i : Fin 3) :
    Tendsto
      (fun hi : ℕ =>
        h3BKMHighGradientDeweightingMultiplierL2 hi i)
      atTop
      (𝓝 0) := by

  have hRaw :=
    h3BKMHighGradientDeweightingMultiplier_tendsto_eLpNorm_two
      i

  have hMem :
      ∀ hi : ℕ,
        MemLp
          (h3BKMHighGradientDeweightingMultiplier hi i)
          2
          (volume : Measure H3FourierPoint3) :=
    fun hi =>
      h3BKMHighGradientDeweightingMultiplier_memLp2
        hi i

  have hZeroMem :
      MemLp
        (0 : H3FourierPoint3 → ℂ)
        2
        (volume : Measure H3FourierPoint3) :=
    MemLp.zero

  have hRawZero :
      Tendsto
        (fun hi : ℕ =>
          eLpNorm
            ((h3BKMHighGradientDeweightingMultiplier hi i)
              -
            (0 : H3FourierPoint3 → ℂ))
            2
            (volume : Measure H3FourierPoint3))
        atTop
        (𝓝 0) := by
    simpa only [
      Pi.sub_apply,
      sub_zero
    ] using hRaw

  have hBundled :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun hi : ℕ =>
        h3BKMHighGradientDeweightingMultiplier hi i)
      hMem
      (0 : H3FourierPoint3 → ℂ)
      hZeroMem).2
      hRawZero

  unfold h3BKMHighGradientDeweightingMultiplierL2

  simpa only [
    MemLp.toLp_zero
  ] using hBundled

/--
The scalar coefficient in the high-frequency BKM pointwise bound tends to
zero with the upper dyadic cutoff.
-/
theorem norm_h3BKMHighGradientDeweightingMultiplierL2_tendsto_zero
    (i : Fin 3) :
    Tendsto
      (fun hi : ℕ =>
        ‖h3BKMHighGradientDeweightingMultiplierL2 hi i‖)
      atTop
      (𝓝 0) := by

  have h :=
    continuous_norm.continuousAt.tendsto.comp
      (h3BKMHighGradientDeweightingMultiplierL2_tendsto_zero i)

  simpa [Function.comp_def] using h

end

end Euclidean
end Bridge
end PrimeTensor
