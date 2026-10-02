import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Raw.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Normalized.Vorticity.Radial.Split
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Bounded truncations of the intrinsic `q²` multiplier

The selected raw Fourier velocity now has a genuine strong `L²` time
derivative.  The remaining top-tail operation is multiplication by

    q(ξ)^2,

which is unbounded on global `L²`.

For a positive radial cutoff `R`, the infrared set

    {|D(ξ)| < R}

makes this multiplier bounded because

    q(ξ) = |D(ξ)|^2,

hence on that set

    q(ξ)^2 = |D(ξ)|^4 ≤ R^4.

This file packages

    T_R f = 1_{|D|<R} q² f

as a bounded real continuous-linear map on `H3FourierComplexL2`, proves the
literal almost-everywhere representative, and proves the operator estimate

    ‖T_R f‖ ≤ R^4 ‖f‖.

The next checkpoint can therefore transport the raw `HasDerivAt` theorem
through `T_R` for every fixed `R`, with no unbounded-operator issue.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailWeightedTruncation
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1200000

/-! ## Pointwise truncated multiplier -/

/--
Intrinsic `q²` multiplier truncated to the strict radial ball `|D| < R`.
-/
noncomputable def h3TopTailTruncatedQSqMultiplier
    (R : ℝ)
    (ξ : H3FourierPoint3) : ℂ :=
  (h3TerminalRadialFrequencyBelow R).indicator
    (fun η : H3FourierPoint3 =>
      ((h3FourierGradientSquare η ^ 2 : ℝ) : ℂ))
    ξ

/--
The truncated multiplier is strongly measurable.
-/
theorem h3TopTailTruncatedQSqMultiplier_aestronglyMeasurable
    (R : ℝ) :
    AEStronglyMeasurable
      (h3TopTailTruncatedQSqMultiplier R)
      (volume : Measure H3FourierPoint3) := by

  unfold h3TopTailTruncatedQSqMultiplier

  apply AEStronglyMeasurable.indicator
    ?_
    (measurableSet_h3TerminalRadialFrequencyBelow R)

  have hQSq :
      Continuous
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ ^ 2) := by
    unfold h3FourierGradientSquare
    fun_prop

  exact
    (
      Complex.continuous_ofReal.comp hQSq
    ).aestronglyMeasurable

/--
On a nonnegative cutoff, the truncated `q²` multiplier has norm at most `R⁴`.
-/
theorem norm_h3TopTailTruncatedQSqMultiplier_le
    {R : ℝ}
    (hR : 0 ≤ R)
    (ξ : H3FourierPoint3) :
    ‖h3TopTailTruncatedQSqMultiplier R ξ‖
      ≤
    R ^ 4 := by

  by_cases hξ :
      ξ ∈ h3TerminalRadialFrequencyBelow R

  · unfold h3TopTailTruncatedQSqMultiplier
    rw [Set.indicator_of_mem hξ]

    have hGradLt :
        h3FourierGradientMagnitude ξ < R := by
      simpa only [
        h3TerminalRadialFrequencyBelow,
        Set.mem_ofPred_eq
      ] using hξ

    have hGradLe :
        h3FourierGradientMagnitude ξ ≤ R :=
      hGradLt.le

    have hPow :
        (h3FourierGradientMagnitude ξ) ^ 4
          ≤
        R ^ 4 :=
      pow_le_pow_left₀
        (h3FourierGradientMagnitude_nonneg ξ)
        hGradLe
        4

    rw [
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg
        (sq_nonneg (h3FourierGradientSquare ξ)),
      ← h3FourierGradientMagnitude_sq
    ]

    calc
      (h3FourierGradientMagnitude ξ ^ 2) ^ 2
          =
        h3FourierGradientMagnitude ξ ^ 4 := by
        ring
      _ ≤ R ^ 4 :=
        hPow

  · unfold h3TopTailTruncatedQSqMultiplier
    rw [Set.indicator_of_notMem hξ, norm_zero]
    positivity

/-! ## `L²` package -/

/--
Pointwise action of the bounded truncated `q²` multiplier on an `L²` state.
-/
noncomputable def h3TopTailTruncatedQSqFunction
    (R : ℝ)
    (f : H3FourierComplexL2)
    (ξ : H3FourierPoint3) : ℂ :=
  h3TopTailTruncatedQSqMultiplier R ξ * f ξ

/--
The pointwise truncated product belongs to Fourier `L²`.
-/
theorem h3TopTailTruncatedQSqFunction_memLp
    {R : ℝ}
    (hR : 0 ≤ R)
    (f : H3FourierComplexL2) :
    MemLp
      (h3TopTailTruncatedQSqFunction R f)
      2
      (volume : Measure H3FourierPoint3) := by

  apply
    (MeasureTheory.Lp.memLp f).of_le_mul
      (c := R ^ 4)
      (
        (
          h3TopTailTruncatedQSqMultiplier_aestronglyMeasurable R
        ).mul
          (MeasureTheory.Lp.aestronglyMeasurable f)
      )

  filter_upwards with ξ

  change
    ‖h3TopTailTruncatedQSqMultiplier R ξ * f ξ‖
      ≤
    R ^ 4 * ‖f ξ‖

  rw [norm_mul]

  exact
    mul_le_mul_of_nonneg_right
      (norm_h3TopTailTruncatedQSqMultiplier_le hR ξ)
      (norm_nonneg (f ξ))

/--
The bounded truncated `q²` multiplier as an actual Fourier `L²` state.
-/
noncomputable def h3TopTailTruncatedQSqL2
    (R : ℝ)
    (hR : 0 ≤ R)
    (f : H3FourierComplexL2) :
    H3FourierComplexL2 :=
  (
    h3TopTailTruncatedQSqFunction_memLp
      hR f
  ).toLp
    (h3TopTailTruncatedQSqFunction R f)

/--
The `L²` package has the literal truncated pointwise representative.
-/
theorem h3TopTailTruncatedQSqL2_ae
    (R : ℝ)
    (hR : 0 ≤ R)
    (f : H3FourierComplexL2) :
    (
      (
        h3TopTailTruncatedQSqL2 R hR f :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3TopTailTruncatedQSqFunction R f := by

  unfold h3TopTailTruncatedQSqL2

  exact
    MemLp.coeFn_toLp
      (
        h3TopTailTruncatedQSqFunction_memLp
          hR f
      )

/-! ## Linearity -/

/--
The truncated `q²` operator is additive on Fourier `L²`.
-/
theorem h3TopTailTruncatedQSqL2_add
    (R : ℝ)
    (hR : 0 ≤ R)
    (f g : H3FourierComplexL2) :
    h3TopTailTruncatedQSqL2 R hR (f + g)
      =
    h3TopTailTruncatedQSqL2 R hR f
      +
    h3TopTailTruncatedQSqL2 R hR g := by

  rw [Lp.ext_iff]

  filter_upwards [
    h3TopTailTruncatedQSqL2_ae R hR (f + g),
    h3TopTailTruncatedQSqL2_ae R hR f,
    h3TopTailTruncatedQSqL2_ae R hR g,
    Lp.coeFn_add f g,
    Lp.coeFn_add
      (h3TopTailTruncatedQSqL2 R hR f)
      (h3TopTailTruncatedQSqL2 R hR g)
  ] with ξ hfg hf hg hAdd hOutAdd

  rw [hfg, hOutAdd]
  simp only [Pi.add_apply]
  rw [hf, hg]

  unfold h3TopTailTruncatedQSqFunction

  rw [hAdd]
  simp only [Pi.add_apply]

  ring

/--
The truncated `q²` operator commutes with real scalar multiplication.
-/
theorem h3TopTailTruncatedQSqL2_smul_real
    (R : ℝ)
    (hR : 0 ≤ R)
    (c : ℝ)
    (f : H3FourierComplexL2) :
    h3TopTailTruncatedQSqL2 R hR (c • f)
      =
    c • h3TopTailTruncatedQSqL2 R hR f := by

  rw [Lp.ext_iff]

  filter_upwards [
    h3TopTailTruncatedQSqL2_ae R hR (c • f),
    h3TopTailTruncatedQSqL2_ae R hR f,
    Lp.coeFn_smul c f,
    Lp.coeFn_smul c
      (h3TopTailTruncatedQSqL2 R hR f)
  ] with ξ hcf hf hInSmul hOutSmul

  rw [hcf, hOutSmul]
  simp only [Pi.smul_apply]
  rw [hf]

  unfold h3TopTailTruncatedQSqFunction

  rw [hInSmul]

  simp only [Pi.smul_apply, Complex.real_smul]

  ring

/--
The truncated `q²` multiplier as a real linear map.
-/
noncomputable def h3TopTailTruncatedQSqRealLinearMap
    (R : ℝ)
    (hR : 0 ≤ R) :
    H3FourierComplexL2 →ₗ[ℝ] H3FourierComplexL2 where
  toFun :=
    h3TopTailTruncatedQSqL2 R hR
  map_add' :=
    h3TopTailTruncatedQSqL2_add R hR
  map_smul' := by
    intro c f
    exact
      h3TopTailTruncatedQSqL2_smul_real
        R hR c f

@[simp]
theorem h3TopTailTruncatedQSqRealLinearMap_apply
    (R : ℝ)
    (hR : 0 ≤ R)
    (f : H3FourierComplexL2) :
    h3TopTailTruncatedQSqRealLinearMap R hR f
      =
    h3TopTailTruncatedQSqL2 R hR f := by
  rfl

/-! ## Operator norm bound -/

/--
The truncated multiplier satisfies the sharp elementary bound

    `‖T_R f‖ ≤ R⁴ ‖f‖`.
-/
theorem norm_h3TopTailTruncatedQSqL2_le
    (R : ℝ)
    (hR : 0 ≤ R)
    (f : H3FourierComplexL2) :
    ‖h3TopTailTruncatedQSqL2 R hR f‖
      ≤
    R ^ 4 * ‖f‖ := by

  apply
    Lp.norm_le_mul_norm_of_ae_le_mul

  filter_upwards [
    h3TopTailTruncatedQSqL2_ae R hR f
  ] with ξ hξ

  rw [hξ]

  unfold h3TopTailTruncatedQSqFunction

  rw [norm_mul]

  exact
    mul_le_mul_of_nonneg_right
      (norm_h3TopTailTruncatedQSqMultiplier_le hR ξ)
      (norm_nonneg (f ξ))

/--
Bounded real continuous-linear version of the truncated intrinsic `q²`
multiplier.
-/
noncomputable def h3TopTailTruncatedQSqRealCLM
    (R : ℝ)
    (hR : 0 ≤ R) :
    H3FourierComplexL2 →L[ℝ] H3FourierComplexL2 :=
  (
    h3TopTailTruncatedQSqRealLinearMap R hR
  ).mkContinuous
    (R ^ 4)
    (fun f => by
      change
        ‖h3TopTailTruncatedQSqL2 R hR f‖
          ≤
        R ^ 4 * ‖f‖
      exact
        norm_h3TopTailTruncatedQSqL2_le
          R hR f)

@[simp]
theorem h3TopTailTruncatedQSqRealCLM_apply
    (R : ℝ)
    (hR : 0 ≤ R)
    (f : H3FourierComplexL2) :
    h3TopTailTruncatedQSqRealCLM R hR f
      =
    h3TopTailTruncatedQSqL2 R hR f := by
  rfl

end

end Euclidean
end Bridge
end PrimeTensor
