import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Raw.Derivative
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Generic bounded natural-radial truncation on Fourier L²

The selected raw Fourier velocity has a genuine strong time derivative.  The
remaining operation needed to promote that derivative to arbitrary radial
order is multiplication by

    |ξ|^m,

which is unbounded on global `L²`.

For a cutoff radius `R ≥ 0`, define

    T[m,R] f(ξ)
      =
    1_{|ξ| < R} |ξ|^m f(ξ).

On the cutoff ball,

    |ξ|^m ≤ R^m,

so `T[m,R]` is a bounded real continuous-linear operator on
`H3FourierComplexL2`, with

    ‖T[m,R] f‖ ≤ R^m ‖f‖.

This is the order-generic analogue of the already successful `q²` and `q³`
truncation layers.  The following checkpoints will remove this cutoff against
the existing arbitrary radial selected velocity and projected-RHS packages,
then pass the raw selected derivative through the limit.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityNatRadialTruncation
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1400000

/-! ## Cutoff set and pointwise multiplier -/

/--
Strict Euclidean Fourier ball used by the generic radial cutoff.
-/
def h3SelectedNatRadialFrequencyBelow
    (R : ℝ) :
    Set H3FourierPoint3 :=
  Metric.ball 0 R

/--
The generic radial cutoff set is measurable.
-/
theorem measurableSet_h3SelectedNatRadialFrequencyBelow
    (R : ℝ) :
    MeasurableSet
      (h3SelectedNatRadialFrequencyBelow R) := by

  unfold h3SelectedNatRadialFrequencyBelow

  exact
    Metric.isOpen_ball.measurableSet

/--
Natural radial multiplier `|ξ|^m` truncated to the strict Euclidean ball
`|ξ| < R`.
-/
noncomputable def h3SelectedTruncatedNatRadialMultiplier
    (m : ℕ)
    (R : ℝ)
    (ξ : H3FourierPoint3) : ℂ :=
  (h3SelectedNatRadialFrequencyBelow R).indicator
    (fun η : H3FourierPoint3 =>
      ((‖η‖ ^ m : ℝ) : ℂ))
    ξ

/--
The generic truncated radial multiplier is strongly measurable.
-/
theorem h3SelectedTruncatedNatRadialMultiplier_aestronglyMeasurable
    (m : ℕ)
    (R : ℝ) :
    AEStronglyMeasurable
      (h3SelectedTruncatedNatRadialMultiplier m R)
      (volume : Measure H3FourierPoint3) := by

  unfold h3SelectedTruncatedNatRadialMultiplier

  apply
    AEStronglyMeasurable.indicator
      ?_
      (measurableSet_h3SelectedNatRadialFrequencyBelow R)

  exact
    (
      Complex.continuous_ofReal.comp
        (continuous_norm.pow m)
    ).aestronglyMeasurable

/--
On a nonnegative cutoff radius, the truncated natural radial multiplier has
norm at most `R^m`.
-/
theorem norm_h3SelectedTruncatedNatRadialMultiplier_le
    (m : ℕ)
    {R : ℝ}
    (hR : 0 ≤ R)
    (ξ : H3FourierPoint3) :
    ‖h3SelectedTruncatedNatRadialMultiplier m R ξ‖
      ≤
    R ^ m := by

  by_cases hξ :
      ξ ∈ h3SelectedNatRadialFrequencyBelow R

  · have hNormLt :
        ‖ξ‖ < R := by
      unfold h3SelectedNatRadialFrequencyBelow at hξ
      simpa only [
        Metric.mem_ball,
        dist_zero_right
      ] using hξ

    have hNormLe :
        ‖ξ‖ ≤ R :=
      hNormLt.le

    have hPow :
        ‖ξ‖ ^ m ≤ R ^ m :=
      pow_le_pow_left₀
        (norm_nonneg ξ)
        hNormLe
        m

    unfold h3SelectedTruncatedNatRadialMultiplier

    rw [
      Set.indicator_of_mem hξ,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg
        (pow_nonneg (norm_nonneg ξ) m)
    ]

    exact hPow

  · unfold h3SelectedTruncatedNatRadialMultiplier

    rw [
      Set.indicator_of_notMem hξ,
      norm_zero
    ]

    exact
      pow_nonneg hR m

/-! ## Fourier L² package -/

/--
Pointwise action of the bounded natural radial truncation.
-/
noncomputable def h3SelectedTruncatedNatRadialFunction
    (m : ℕ)
    (R : ℝ)
    (f : H3FourierComplexL2)
    (ξ : H3FourierPoint3) : ℂ :=
  h3SelectedTruncatedNatRadialMultiplier m R ξ *
    f ξ

/--
The pointwise generic radial truncation preserves Fourier `L²`.
-/
theorem h3SelectedTruncatedNatRadialFunction_memLp2
    (m : ℕ)
    {R : ℝ}
    (hR : 0 ≤ R)
    (f : H3FourierComplexL2) :
    MemLp
      (h3SelectedTruncatedNatRadialFunction m R f)
      2
      (volume : Measure H3FourierPoint3) := by

  apply
    (MeasureTheory.Lp.memLp f).of_le_mul
      (c := R ^ m)
      (
        (
          h3SelectedTruncatedNatRadialMultiplier_aestronglyMeasurable
            m R
        ).mul
          (MeasureTheory.Lp.aestronglyMeasurable f)
      )

  filter_upwards with ξ

  change
    ‖h3SelectedTruncatedNatRadialMultiplier m R ξ *
        f ξ‖
      ≤
    R ^ m * ‖f ξ‖

  rw [norm_mul]

  exact
    mul_le_mul_of_nonneg_right
      (norm_h3SelectedTruncatedNatRadialMultiplier_le
        m hR ξ)
      (norm_nonneg (f ξ))

/--
The bounded natural radial truncation as a genuine Fourier `L²` state.
-/
noncomputable def h3SelectedTruncatedNatRadialL2
    (m : ℕ)
    (R : ℝ)
    (hR : 0 ≤ R)
    (f : H3FourierComplexL2) :
    H3FourierComplexL2 :=
  (
    h3SelectedTruncatedNatRadialFunction_memLp2
      m hR f
  ).toLp
    (h3SelectedTruncatedNatRadialFunction
      m R f)

/--
Literal pointwise representative of the packaged radial truncation.
-/
theorem h3SelectedTruncatedNatRadialL2_ae
    (m : ℕ)
    (R : ℝ)
    (hR : 0 ≤ R)
    (f : H3FourierComplexL2) :
    (
      (
        h3SelectedTruncatedNatRadialL2
          m R hR f :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3SelectedTruncatedNatRadialFunction
      m R f := by

  unfold h3SelectedTruncatedNatRadialL2

  exact
    MemLp.coeFn_toLp
      (
        h3SelectedTruncatedNatRadialFunction_memLp2
          m hR f
      )

/-! ## Linearity -/

/--
The generic truncated radial operator is additive.
-/
theorem h3SelectedTruncatedNatRadialL2_add
    (m : ℕ)
    (R : ℝ)
    (hR : 0 ≤ R)
    (f g : H3FourierComplexL2) :
    h3SelectedTruncatedNatRadialL2
        m R hR (f + g)
      =
    h3SelectedTruncatedNatRadialL2
        m R hR f
      +
    h3SelectedTruncatedNatRadialL2
        m R hR g := by

  rw [Lp.ext_iff]

  filter_upwards [
    h3SelectedTruncatedNatRadialL2_ae
      m R hR (f + g),
    h3SelectedTruncatedNatRadialL2_ae
      m R hR f,
    h3SelectedTruncatedNatRadialL2_ae
      m R hR g,
    Lp.coeFn_add f g,
    Lp.coeFn_add
      (h3SelectedTruncatedNatRadialL2
        m R hR f)
      (h3SelectedTruncatedNatRadialL2
        m R hR g)
  ] with ξ hfg hf hg hAdd hOutAdd

  rw [hfg, hOutAdd]
  simp only [Pi.add_apply]
  rw [hf, hg]

  unfold h3SelectedTruncatedNatRadialFunction

  rw [hAdd]
  simp only [Pi.add_apply]

  ring

/--
The generic truncated radial operator commutes with real scalar
multiplication.
-/
theorem h3SelectedTruncatedNatRadialL2_smul_real
    (m : ℕ)
    (R : ℝ)
    (hR : 0 ≤ R)
    (c : ℝ)
    (f : H3FourierComplexL2) :
    h3SelectedTruncatedNatRadialL2
        m R hR (c • f)
      =
    c •
      h3SelectedTruncatedNatRadialL2
        m R hR f := by

  rw [Lp.ext_iff]

  filter_upwards [
    h3SelectedTruncatedNatRadialL2_ae
      m R hR (c • f),
    h3SelectedTruncatedNatRadialL2_ae
      m R hR f,
    Lp.coeFn_smul c f,
    Lp.coeFn_smul c
      (h3SelectedTruncatedNatRadialL2
        m R hR f)
  ] with ξ hcf hf hInSmul hOutSmul

  rw [hcf, hOutSmul]
  simp only [Pi.smul_apply]
  rw [hf]

  unfold h3SelectedTruncatedNatRadialFunction

  rw [hInSmul]

  simp only [
    Pi.smul_apply,
    Complex.real_smul
  ]

  ring

/--
Generic truncated natural radial multiplier as a real linear map.
-/
noncomputable def h3SelectedTruncatedNatRadialRealLinearMap
    (m : ℕ)
    (R : ℝ)
    (hR : 0 ≤ R) :
    H3FourierComplexL2 →ₗ[ℝ]
      H3FourierComplexL2 where
  toFun :=
    h3SelectedTruncatedNatRadialL2
      m R hR
  map_add' :=
    h3SelectedTruncatedNatRadialL2_add
      m R hR
  map_smul' := by
    intro c f
    exact
      h3SelectedTruncatedNatRadialL2_smul_real
        m R hR c f

@[simp]
theorem h3SelectedTruncatedNatRadialRealLinearMap_apply
    (m : ℕ)
    (R : ℝ)
    (hR : 0 ≤ R)
    (f : H3FourierComplexL2) :
    h3SelectedTruncatedNatRadialRealLinearMap
        m R hR f
      =
    h3SelectedTruncatedNatRadialL2
      m R hR f := by
  rfl

/-! ## Operator norm bound -/

/--
Sharp elementary operator estimate

    `‖T[m,R] f‖ ≤ R^m ‖f‖`.
-/
theorem norm_h3SelectedTruncatedNatRadialL2_le
    (m : ℕ)
    (R : ℝ)
    (hR : 0 ≤ R)
    (f : H3FourierComplexL2) :
    ‖h3SelectedTruncatedNatRadialL2
        m R hR f‖
      ≤
    R ^ m * ‖f‖ := by

  apply
    Lp.norm_le_mul_norm_of_ae_le_mul

  filter_upwards [
    h3SelectedTruncatedNatRadialL2_ae
      m R hR f
  ] with ξ hξ

  rw [hξ]

  unfold h3SelectedTruncatedNatRadialFunction

  rw [norm_mul]

  exact
    mul_le_mul_of_nonneg_right
      (
        norm_h3SelectedTruncatedNatRadialMultiplier_le
          m hR ξ
      )
      (norm_nonneg (f ξ))

/--
Bounded real continuous-linear version of the generic natural radial
truncation.
-/
noncomputable def h3SelectedTruncatedNatRadialRealCLM
    (m : ℕ)
    (R : ℝ)
    (hR : 0 ≤ R) :
    H3FourierComplexL2 →L[ℝ]
      H3FourierComplexL2 :=
  (
    h3SelectedTruncatedNatRadialRealLinearMap
      m R hR
  ).mkContinuous
    (R ^ m)
    (fun f => by
      change
        ‖h3SelectedTruncatedNatRadialL2
            m R hR f‖
          ≤
        R ^ m * ‖f‖
      exact
        norm_h3SelectedTruncatedNatRadialL2_le
          m R hR f)

@[simp]
theorem h3SelectedTruncatedNatRadialRealCLM_apply
    (m : ℕ)
    (R : ℝ)
    (hR : 0 ≤ R)
    (f : H3FourierComplexL2) :
    h3SelectedTruncatedNatRadialRealCLM
        m R hR f
      =
    h3SelectedTruncatedNatRadialL2
      m R hR f := by
  rfl

end

end Euclidean
end Bridge
end PrimeTensor
