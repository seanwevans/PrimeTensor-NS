import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Schwartz.Cutoff
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Classicalization: zeroth-order L² convergence of the cutoff family

`Schwartz.Cutoff` constructed compact smooth approximants

    χₙ φ

which are literally transports of physical weak tests.

This file proves the zeroth-order part of the `W¹,²` convergence:

    χₙ φ → φ  in L².

For every fixed point `x`, the expanding cutoff is eventually exactly one.
Moreover `0 ≤ χₙ ≤ 1`, hence

    ‖χₙ(x) φ(x) - φ(x)‖ ≤ ‖φ(x)‖.

Since a Schwartz function belongs to `L²`, dominated convergence applies to the
square of the pointwise error.  We first obtain convergence of the raw
`eLpNorm`, then upgrade it to convergence in the bundled real `L²` space.

The remaining checkpoint is only the first-derivative coordinates of the
`W¹,²` graph.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityDualCurlSchwartzCutoffL2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Pointwise stabilization -/

/-- At every fixed Euclidean point, the expanding cutoff is eventually
identically one. -/
theorem h3W12CutoffBump_eventually_eq_one
    (x : H3FourierPoint3) :
    ∀ᶠ n : ℕ in atTop,
      h3W12CutoffBump n x = 1 := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_ge ‖x‖

  filter_upwards [eventually_ge_atTop N] with n hn

  apply h3W12CutoffBump_eq_one_of_norm_le

  calc
    ‖x‖ ≤ (N : ℝ) := hN
    _ ≤ (n : ℝ) := by
      exact_mod_cast hn
    _ ≤ (n : ℝ) + 1 := by
      linarith

/-- Consequently every cutoff Schwartz approximant is eventually exactly the
original Schwartz function at each fixed point. -/
theorem h3W12CutoffSchwartz_eventually_eq
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (x : H3FourierPoint3) :
    ∀ᶠ n : ℕ in atTop,
      h3W12CutoffSchwartz n φ x = φ x := by
  filter_upwards [h3W12CutoffBump_eventually_eq_one x] with n hn

  rw [
    h3W12CutoffSchwartz_apply,
    hn,
    one_mul
  ]

/-- Pointwise convergence of the compact cutoff sequence. -/
theorem h3W12CutoffSchwartz_tendsto_pointwise
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (x : H3FourierPoint3) :
    Tendsto
      (fun n : ℕ =>
        h3W12CutoffSchwartz n φ x)
      atTop
      (𝓝 (φ x)) := by
  refine (tendsto_congr' ?_).2 tendsto_const_nhds

  exact
    h3W12CutoffSchwartz_eventually_eq φ x

/-! ## Uniform domination of the pointwise error -/

/-- Because every cutoff takes values in `[0,1]`, multiplying by the cutoff
moves a real scalar toward zero and changes it by at most its original norm. -/
theorem norm_h3W12CutoffSchwartz_sub_le
    (n : ℕ)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (x : H3FourierPoint3) :
    ‖h3W12CutoffSchwartz n φ x - φ x‖
      ≤
    ‖φ x‖ := by
  have hχ0 :
      0 ≤ h3W12CutoffBump n x :=
    h3W12CutoffBump_nonneg n x

  have hχ1 :
      h3W12CutoffBump n x ≤ 1 :=
    h3W12CutoffBump_le_one n x

  rw [h3W12CutoffSchwartz_apply]

  have hRewrite :
      h3W12CutoffBump n x * φ x - φ x
        =
      (h3W12CutoffBump n x - 1) * φ x := by
    ring

  rw [hRewrite, norm_mul]

  have hAbs :
      |h3W12CutoffBump n x - 1|
        =
      1 - h3W12CutoffBump n x := by
    rw [abs_of_nonpos]
    · ring
    · linarith

  rw [Real.norm_eq_abs, hAbs]

  calc
    (1 - h3W12CutoffBump n x) * |φ x|
        ≤
      1 * |φ x| := by
        gcongr
        linarith
    _ = |φ x| := by
      ring

/-- The same domination in `ENNReal` norm form. -/
theorem enorm_h3W12CutoffSchwartz_sub_le
    (n : ℕ)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (x : H3FourierPoint3) :
    ‖h3W12CutoffSchwartz n φ x - φ x‖ₑ
      ≤
    ‖φ x‖ₑ := by
  rw [enorm_le_iff_norm_le]
  exact
    norm_h3W12CutoffSchwartz_sub_le n φ x

/-! ## Raw eLpNorm convergence -/

/-- The cutoff error converges to zero in raw `L²` seminorm. -/
theorem h3W12CutoffSchwartz_tendsto_eLpNorm_two
    (φ : 𝓢(H3FourierPoint3, ℝ)) :
    Tendsto
      (fun n : ℕ =>
        eLpNorm
          (fun x : H3FourierPoint3 =>
            h3W12CutoffSchwartz n φ x - φ x)
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
        (fun n : ℕ =>
          ∫⁻ x : H3FourierPoint3,
            ‖h3W12CutoffSchwartz n φ x - φ x‖ₑ
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

    simpa only [
      Function.comp_def
    ] using hComposed

  have hFMeas :
      ∀ n : ℕ,
        Measurable
          (fun x : H3FourierPoint3 =>
            ‖h3W12CutoffSchwartz n φ x - φ x‖ₑ
              ^ (2 : ℝ≥0∞).toReal) := by
    intro n

    exact
      (((h3W12CutoffSchwartz n φ).continuous.measurable.sub
          φ.continuous.measurable).enorm.pow_const
        (2 : ℝ≥0∞).toReal)

  have hBound :
      ∀ n : ℕ,
        (fun x : H3FourierPoint3 =>
          ‖h3W12CutoffSchwartz n φ x - φ x‖ₑ
            ^ (2 : ℝ≥0∞).toReal)
          ≤ᵐ[volume]
        (fun x : H3FourierPoint3 =>
          ‖φ x‖ₑ ^ (2 : ℝ≥0∞).toReal) := by
    intro n

    exact
      Filter.Eventually.of_forall
        (fun x =>
          ENNReal.rpow_le_rpow
            (enorm_h3W12CutoffSchwartz_sub_le n φ x)
            ENNReal.toReal_nonneg)

  have hφMemLp :
      MemLp
        (φ : H3FourierPoint3 → ℝ)
        2
        (volume : Measure H3FourierPoint3) :=
    φ.memLp 2 volume

  have hFinite :
      (∫⁻ x : H3FourierPoint3,
        ‖φ x‖ₑ ^ (2 : ℝ≥0∞).toReal
        ∂volume)
        ≠
      ∞ := by
    exact
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        hpZero
        hpTop
        hφMemLp.2).ne

  have hLimit :
      ∀ᵐ x : H3FourierPoint3 ∂volume,
        Tendsto
          (fun n : ℕ =>
            ‖h3W12CutoffSchwartz n φ x - φ x‖ₑ
              ^ (2 : ℝ≥0∞).toReal)
          atTop
          (𝓝 0) := by
    filter_upwards with x

    refine (tendsto_congr' ?_).2 tendsto_const_nhds

    filter_upwards [
      h3W12CutoffSchwartz_eventually_eq φ x
    ] with n hn

    rw [hn, sub_self]

    simp

  simpa using
    (tendsto_lintegral_of_dominated_convergence
      (fun x : H3FourierPoint3 =>
        ‖φ x‖ₑ ^ (2 : ℝ≥0∞).toReal)
      hFMeas
      hBound
      hFinite
      hLimit)

/-! ## Bundled L² convergence -/

/-- Zeroth-order cutoff convergence in the actual real Euclidean `L²` space. -/
theorem h3W12CutoffSchwartz_toLp_tendsto
    (φ : 𝓢(H3FourierPoint3, ℝ)) :
    Tendsto
      (fun n : ℕ =>
        (h3W12CutoffSchwartz n φ).toLp
          2
          (volume : Measure H3FourierPoint3))
      atTop
      (𝓝
        (φ.toLp
          2
          (volume : Measure H3FourierPoint3))) := by
  have hRaw :
      Tendsto
        (fun n : ℕ =>
          eLpNorm
            (fun x : H3FourierPoint3 =>
              h3W12CutoffSchwartz n φ x - φ x)
            2
            (volume : Measure H3FourierPoint3))
        atTop
        (𝓝 0) :=
    h3W12CutoffSchwartz_tendsto_eLpNorm_two φ

  have hCutMem :
      ∀ n : ℕ,
        MemLp
          (h3W12CutoffSchwartz n φ :
            H3FourierPoint3 → ℝ)
          2
          (volume : Measure H3FourierPoint3) :=
    fun n =>
      (h3W12CutoffSchwartz n φ).memLp 2 volume

  have hφMem :
      MemLp
        (φ : H3FourierPoint3 → ℝ)
        2
        (volume : Measure H3FourierPoint3) :=
    φ.memLp 2 volume

  unfold SchwartzMap.toLp

  exact
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n : ℕ =>
        (h3W12CutoffSchwartz n φ :
          H3FourierPoint3 → ℝ))
      hCutMem
      (φ : H3FourierPoint3 → ℝ)
      hφMem).2
      hRaw

end

end Euclidean
end Bridge
end PrimeTensor
