import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Schwartz.Cutoff.Derivative.Bound
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Classicalization: L² decay of the derivative cutoff remainder

The two previous checkpoints supplied exactly the hypotheses for dominated
convergence:

* `Derivative.Pointwise`: for every fixed `x`,
  `h3W12CutoffDerivativeRemainder n φ a x` is eventually exactly zero;
* `Derivative.Bound`: there is a constant `C ≥ 0`, independent of `n`, such
  that

      ‖h3W12CutoffDerivativeRemainder n φ a x‖ ≤ C ‖φ x‖.

Since `C • φ` is again Schwartz, it lies in `L²`.  We therefore apply the same
`eLpNorm` dominated-convergence pattern already used for the zeroth-order
cutoff sequence.

This closes the last analytic estimate isolated by
`H3W12CutoffDerivativeRemainderTendsToZero`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityDualCurlSchwartzCutoffDerivativeL2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Raw eLpNorm convergence -/

/-- The derivative cutoff remainder tends to zero in the raw `L²` seminorm. -/
theorem h3W12CutoffDerivativeRemainder_tendsto_eLpNorm_two
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (a : PrimeTensor.Axis Depth.three) :
    Tendsto
      (fun n : ℕ =>
        eLpNorm
          (fun x : H3FourierPoint3 =>
            h3W12CutoffDerivativeRemainder n φ a x)
          2
          (volume : Measure H3FourierPoint3))
      atTop
      (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_h3W12CutoffDerivativeRemainder_uniform_bound
      φ a

  let ψ : 𝓢(H3FourierPoint3, ℝ) :=
    C • φ

  have hψApply :
      ∀ x : H3FourierPoint3,
        ψ x = C * φ x := by
    intro x
    simp [ψ, smul_eq_mul]

  have hNormBound :
      ∀ (n : ℕ) (x : H3FourierPoint3),
        ‖h3W12CutoffDerivativeRemainder n φ a x‖
          ≤
        ‖ψ x‖ := by
    intro n x

    calc
      ‖h3W12CutoffDerivativeRemainder n φ a x‖
          ≤
        C * ‖φ x‖ :=
          hC n x
      _ =
        ‖ψ x‖ := by
          have hNormC :
              ‖C‖ = C := by
            simpa [Real.norm_eq_abs] using
              (abs_of_nonneg hC0)

          rw [
            hψApply,
            norm_mul,
            hNormC
          ]

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
            ‖h3W12CutoffDerivativeRemainder n φ a x‖ₑ
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
            ‖h3W12CutoffDerivativeRemainder n φ a x‖ₑ
              ^ (2 : ℝ≥0∞).toReal) := by
    intro n

    exact
      ((h3W12CutoffDerivativeRemainder n φ a).continuous.measurable.enorm.pow_const
        (2 : ℝ≥0∞).toReal)

  have hBound :
      ∀ n : ℕ,
        (fun x : H3FourierPoint3 =>
          ‖h3W12CutoffDerivativeRemainder n φ a x‖ₑ
            ^ (2 : ℝ≥0∞).toReal)
          ≤ᵐ[volume]
        (fun x : H3FourierPoint3 =>
          ‖ψ x‖ₑ ^ (2 : ℝ≥0∞).toReal) := by
    intro n

    exact
      Filter.Eventually.of_forall
        (fun x =>
          ENNReal.rpow_le_rpow
            (by
              rw [enorm_le_iff_norm_le]
              exact hNormBound n x)
            ENNReal.toReal_nonneg)

  have hψMemLp :
      MemLp
        (ψ : H3FourierPoint3 → ℝ)
        2
        (volume : Measure H3FourierPoint3) :=
    ψ.memLp 2 volume

  have hFinite :
      (∫⁻ x : H3FourierPoint3,
        ‖ψ x‖ₑ ^ (2 : ℝ≥0∞).toReal
        ∂volume)
        ≠
      ∞ := by
    exact
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        hpZero
        hpTop
        hψMemLp.2).ne

  have hLimit :
      ∀ᵐ x : H3FourierPoint3 ∂volume,
        Tendsto
          (fun n : ℕ =>
            ‖h3W12CutoffDerivativeRemainder n φ a x‖ₑ
              ^ (2 : ℝ≥0∞).toReal)
          atTop
          (𝓝 0) := by
    filter_upwards with x

    exact
      h3W12CutoffDerivativeRemainder_enorm_sq_tendsto_pointwise_zero
        φ a x

  simpa using
    (tendsto_lintegral_of_dominated_convergence
      (fun x : H3FourierPoint3 =>
        ‖ψ x‖ₑ ^ (2 : ℝ≥0∞).toReal)
      hFMeas
      hBound
      hFinite
      hLimit)

/-! ## Bundled L² convergence -/

/-- The derivative cutoff remainder tends to zero in the actual bundled
Euclidean real `L²` space. -/
theorem h3W12CutoffDerivativeRemainder_toLp_tendsto_zero
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (a : PrimeTensor.Axis Depth.three) :
    Tendsto
      (fun n : ℕ =>
        (h3W12CutoffDerivativeRemainder n φ a).toLp
          2
          (volume : Measure H3FourierPoint3))
      atTop
      (𝓝 0) := by
  have hRaw :=
    h3W12CutoffDerivativeRemainder_tendsto_eLpNorm_two
      φ a

  have hRemMem :
      ∀ n : ℕ,
        MemLp
          (h3W12CutoffDerivativeRemainder n φ a :
            H3FourierPoint3 → ℝ)
          2
          (volume : Measure H3FourierPoint3) :=
    fun n =>
      (h3W12CutoffDerivativeRemainder n φ a).memLp
        2 volume

  have hZeroMem :
      MemLp
        (0 : H3FourierPoint3 → ℝ)
        2
        (volume : Measure H3FourierPoint3) :=
    MemLp.zero

  have hRawZero :
      Tendsto
        (fun n : ℕ =>
          eLpNorm
            ((h3W12CutoffDerivativeRemainder n φ a :
                H3FourierPoint3 → ℝ)
              -
            (0 : H3FourierPoint3 → ℝ))
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
      (fun n : ℕ =>
        (h3W12CutoffDerivativeRemainder n φ a :
          H3FourierPoint3 → ℝ))
      hRemMem
      (0 : H3FourierPoint3 → ℝ)
      hZeroMem).2
      hRawZero

  unfold SchwartzMap.toLp

  simpa only [
    MemLp.toLp_zero
  ] using hBundled

/-! ## Close the derivative-remainder frontier -/

/-- The remaining first-derivative cutoff estimate isolated in
`Schwartz.Cutoff.Derivative` is now proved. -/
theorem H3W12CutoffDerivativeRemainderTendsToZero_proved :
    H3W12CutoffDerivativeRemainderTendsToZero := by
  intro φ a

  exact
    h3W12CutoffDerivativeRemainder_toLp_tendsto_zero
      φ a

end

end Euclidean
end Bridge
end PrimeTensor
