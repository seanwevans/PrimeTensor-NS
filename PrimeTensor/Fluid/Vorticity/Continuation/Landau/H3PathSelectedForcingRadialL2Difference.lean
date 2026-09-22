import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedForcingRadialL2State
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spectral.Difference.Energy

/-!
# Radial Fourier L² difference interpolation for selected forcing

The selected forcing now has quotient-safe weighted `L²` states at every
natural radial order.  This file supplies the topology bridge between adjacent
orders.

For `R > 0` and every `x ≥ 0`,

    x^m ≤ R^m + R⁻¹ x^(m+1).

Applying this to the difference of two forcing snapshots and using

    |N_s - N_t| ≤ |N_s| + |N_t|

gives the `L²` interpolation estimate

    ‖F_m(s) - F_m(t)‖²
      ≤ 2 R^(2m) ‖F_0(s) - F_0(t)‖²
        + 4 R⁻² (‖F_{m+1}(s)‖² + ‖F_{m+1}(t)‖²).

Thus ordinary forcing `L²` continuity plus a uniform next-order radial bound
implies order-`m` radial continuity.  The next file will apply this with
`m = 4,5`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedForcingRadialL2Difference
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Elementary adjacent-order radial interpolation inequality. -/
theorem norm_pow_nat_le_radius_pow_add_inv_mul_succ
    (m : ℕ)
    {R : ℝ}
    (hR : 0 < R)
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ m
      ≤
    R ^ m + R⁻¹ * ‖ξ‖ ^ (m + 1) := by

  have hx0 : 0 ≤ ‖ξ‖ := norm_nonneg ξ
  have hR0 : 0 ≤ R := hR.le

  by_cases hxR : ‖ξ‖ ≤ R

  · have hpow :
        ‖ξ‖ ^ m ≤ R ^ m :=
      pow_le_pow_left₀ hx0 hxR m

    have htail0 :
        0 ≤ R⁻¹ * ‖ξ‖ ^ (m + 1) :=
      mul_nonneg
        (inv_nonneg.mpr hR0)
        (pow_nonneg hx0 (m + 1))

    exact le_add_of_le_of_nonneg hpow htail0

  · have hRx : R ≤ ‖ξ‖ :=
      le_of_lt (lt_of_not_ge hxR)

    have hxm0 : 0 ≤ ‖ξ‖ ^ m :=
      pow_nonneg hx0 m

    have hmul :
        R * ‖ξ‖ ^ m
          ≤
        ‖ξ‖ * ‖ξ‖ ^ m :=
      mul_le_mul_of_nonneg_right hRx hxm0

    have hhigh :
        ‖ξ‖ ^ m
          ≤
        R⁻¹ * ‖ξ‖ ^ (m + 1) := by
      rw [inv_mul_eq_div]
      apply (le_div_iff₀ hR).2
      calc
        ‖ξ‖ ^ m * R = R * ‖ξ‖ ^ m := by ring
        _ ≤ ‖ξ‖ * ‖ξ‖ ^ m := hmul
        _ = ‖ξ‖ ^ (m + 1) := by
          rw [pow_succ]
          ring

    exact
      le_add_of_nonneg_of_le
        (pow_nonneg hR0 m)
        hhigh

/--
Pointwise square interpolation for a pair of complex forcing amplitudes.
-/
private theorem radialDifference_sq_le
    (m : ℕ)
    {R : ℝ}
    (hR : 0 < R)
    (ξ : H3FourierPoint3)
    (z w : ℂ) :
    ‖((‖ξ‖ ^ m : ℝ) : ℂ) * (z - w)‖ ^ 2
      ≤
    2 * (R ^ m) ^ 2 * ‖z - w‖ ^ 2
      +
    4 * (R⁻¹) ^ 2 *
      (‖((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * z‖ ^ 2
        +
       ‖((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * w‖ ^ 2) := by

  have hR0 : 0 ≤ R := hR.le
  have hInv0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hR0
  have hx0 : 0 ≤ ‖ξ‖ := norm_nonneg ξ
  have hxm0 : 0 ≤ ‖ξ‖ ^ m := pow_nonneg hx0 m
  have hxsucc0 : 0 ≤ ‖ξ‖ ^ (m + 1) := pow_nonneg hx0 (m + 1)

  have hWeight :=
    norm_pow_nat_le_radius_pow_add_inv_mul_succ
      m hR ξ

  have hDiff0 : 0 ≤ ‖z - w‖ := norm_nonneg _
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg _

  have hSub :
      ‖z - w‖ ≤ ‖z‖ + ‖w‖ :=
    norm_sub_le z w

  let A : ℝ := R ^ m * ‖z - w‖
  let B : ℝ := R⁻¹ * (‖ξ‖ ^ (m + 1) * ‖z‖)
  let C : ℝ := R⁻¹ * (‖ξ‖ ^ (m + 1) * ‖w‖)

  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (pow_nonneg hR0 m) hDiff0

  have hB0 : 0 ≤ B := by
    dsimp only [B]
    positivity

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity

  have hNorm :
      ‖((‖ξ‖ ^ m : ℝ) : ℂ) * (z - w)‖
        ≤ A + B + C := by

    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg hxm0
    ]

    calc
      ‖ξ‖ ^ m * ‖z - w‖
          ≤
        (R ^ m + R⁻¹ * ‖ξ‖ ^ (m + 1)) *
          ‖z - w‖ :=
        mul_le_mul_of_nonneg_right hWeight hDiff0
      _ =
        A +
          R⁻¹ *
            (‖ξ‖ ^ (m + 1) * ‖z - w‖) := by
        dsimp only [A]
        ring
      _ ≤
        A +
          R⁻¹ *
            (‖ξ‖ ^ (m + 1) * (‖z‖ + ‖w‖)) := by
        have hInner :
            R⁻¹ * (‖ξ‖ ^ (m + 1) * ‖z - w‖)
              ≤
            R⁻¹ * (‖ξ‖ ^ (m + 1) * (‖z‖ + ‖w‖)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              hSub
              hxsucc0)
            hInv0
        exact add_le_add_right hInner A
      _ = A + B + C := by
        dsimp only [B, C]
        ring

  have hSq :
      ‖((‖ξ‖ ^ m : ℝ) : ℂ) * (z - w)‖ ^ 2
        ≤
      (A + B + C) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hNorm 2

  have hABC :
      (A + B + C) ^ 2
        ≤
      2 * A ^ 2 + 4 * B ^ 2 + 4 * C ^ 2 := by
    nlinarith [
      sq_nonneg (A - (B + C)),
      sq_nonneg (B - C)
    ]

  calc
    ‖((‖ξ‖ ^ m : ℝ) : ℂ) * (z - w)‖ ^ 2
        ≤
      2 * A ^ 2 + 4 * B ^ 2 + 4 * C ^ 2 :=
      hSq.trans hABC
    _ =
      2 * (R ^ m) ^ 2 * ‖z - w‖ ^ 2
        +
      4 * (R⁻¹) ^ 2 *
        (‖((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * z‖ ^ 2
          +
         ‖((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * w‖ ^ 2) := by
      dsimp only [A, B, C]
      simp only [
        norm_mul,
        Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg hxsucc0
      ]
      ring

/--
Adjacent-order interpolation for the quotient-safe selected forcing states on
the terminal slab.
-/
theorem norm_sq_h3SelectedRestartForcingRadialFourierL2OnSlab_sub_le
    {ν A q : ℝ}
    (m : ℕ)
    {R : ℝ}
    (hR : 0 < R)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (s t : Set.Icc (q / 2) q) :
    ‖h3SelectedRestartForcingRadialFourierL2OnSlab
          m hν U₀ hA hU₀ hq hqR i s
        -
      h3SelectedRestartForcingRadialFourierL2OnSlab
          m hν U₀ hA hU₀ hq hqR i t‖ ^ 2
      ≤
    2 * (R ^ m) ^ 2 *
      ‖h3RawFinLerayOuterProductDivergenceFourierL2
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ (s : ℝ))
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ (s : ℝ))
          i
        -
        h3RawFinLerayOuterProductDivergenceFourierL2
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ (t : ℝ))
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ (t : ℝ))
          i‖ ^ 2
      +
    4 * (R⁻¹) ^ 2 *
      (‖h3SelectedRestartForcingRadialFourierL2OnSlab
            (m + 1) hν U₀ hA hU₀ hq hqR i s‖ ^ 2
        +
       ‖h3SelectedRestartForcingRadialFourierL2OnSlab
            (m + 1) hν U₀ hA hU₀ hq hqR i t‖ ^ 2) := by

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let Ns : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W (s : ℝ)) (W (s : ℝ)) i

  let Nt : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W (t : ℝ)) (W (t : ℝ)) i

  let F0s : H3FourierComplexL2 :=
    h3RawFinLerayOuterProductDivergenceFourierL2
      (W (s : ℝ)) (W (s : ℝ)) i

  let F0t : H3FourierComplexL2 :=
    h3RawFinLerayOuterProductDivergenceFourierL2
      (W (t : ℝ)) (W (t : ℝ)) i

  let Fms : H3FourierComplexL2 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      m hν U₀ hA hU₀ hq hqR i s

  let Fmt : H3FourierComplexL2 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      m hν U₀ hA hU₀ hq hqR i t

  let Fnexts : H3FourierComplexL2 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      (m + 1) hν U₀ hA hU₀ hq hqR i s

  let Fnextt : H3FourierComplexL2 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      (m + 1) hν U₀ hA hU₀ hq hqR i t

  have hF0s :
      ((F0s : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      Ns := by
    dsimp only [F0s, Ns]
    unfold h3RawFinLerayOuterProductDivergenceFourierL2
    exact
      MemLp.coeFn_toLp
        (h3RawFinLerayOuterProductDivergence_memLp2
          (W (s : ℝ)) (W (s : ℝ)) i)

  have hF0t :
      ((F0t : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      Nt := by
    dsimp only [F0t, Nt]
    unfold h3RawFinLerayOuterProductDivergenceFourierL2
    exact
      MemLp.coeFn_toLp
        (h3RawFinLerayOuterProductDivergence_memLp2
          (W (t : ℝ)) (W (t : ℝ)) i)

  have hFms :
      ((Fms : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) * Ns ξ) := by
    dsimp only [Fms, Ns, W]
    exact
      h3SelectedRestartForcingRadialFourierL2OnSlab_ae
        m hν U₀ hA hU₀ hq hqR i s

  have hFmt :
      ((Fmt : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) * Nt ξ) := by
    dsimp only [Fmt, Nt, W]
    exact
      h3SelectedRestartForcingRadialFourierL2OnSlab_ae
        m hν U₀ hA hU₀ hq hqR i t

  have hFnexts :
      ((Fnexts : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ =>
        ((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * Ns ξ) := by
    dsimp only [Fnexts, Ns, W]
    exact
      h3SelectedRestartForcingRadialFourierL2OnSlab_ae
        (m + 1) hν U₀ hA hU₀ hq hqR i s

  have hFnextt :
      ((Fnextt : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ =>
        ((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * Nt ξ) := by
    dsimp only [Fnextt, Nt, W]
    exact
      h3SelectedRestartForcingRadialFourierL2OnSlab_ae
        (m + 1) hν U₀ hA hU₀ hq hqR i t

  have hLeftInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖((‖ξ‖ ^ m : ℝ) : ℂ) *
              (Ns ξ - Nt ξ)‖ ^ 2)
        volume := by
    have hRaw :=
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        Fms Fmt
    refine hRaw.congr ?_
    filter_upwards [
      hFms,
      hFmt
    ] with ξ hsξ htξ
    rw [hsξ, htξ]
    ring_nf

  have hLowInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖Ns ξ - Nt ξ‖ ^ 2)
        volume := by
    have hRaw :=
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        F0s F0t
    refine hRaw.congr ?_
    filter_upwards [
      hF0s,
      hF0t
    ] with ξ hsξ htξ
    rw [hsξ, htξ]

  have hNextSInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * Ns ξ‖ ^ 2)
        volume := by
    have hRaw :=
      (MeasureTheory.Lp.memLp Fnexts).norm.integrable_sq
    refine hRaw.congr ?_
    filter_upwards [hFnexts] with ξ hξ
    rw [hξ]

  have hNextTInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * Nt ξ‖ ^ 2)
        volume := by
    have hRaw :=
      (MeasureTheory.Lp.memLp Fnextt).norm.integrable_sq
    refine hRaw.congr ?_
    filter_upwards [hFnextt] with ξ hξ
    rw [hξ]

  let major : H3FourierPoint3 → ℝ :=
    fun ξ =>
      2 * (R ^ m) ^ 2 * ‖Ns ξ - Nt ξ‖ ^ 2
        +
      4 * (R⁻¹) ^ 2 *
        (‖((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * Ns ξ‖ ^ 2
          +
         ‖((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * Nt ξ‖ ^ 2)

  have hMajorInt :
      Integrable major volume := by
    dsimp only [major]
    exact
      (hLowInt.const_mul (2 * (R ^ m) ^ 2)).add
        ((hNextSInt.add hNextTInt).const_mul
          (4 * (R⁻¹) ^ 2))

  have hInt :
      (∫ ξ : H3FourierPoint3,
          ‖((‖ξ‖ ^ m : ℝ) : ℂ) *
              (Ns ξ - Nt ξ)‖ ^ 2)
        ≤
      ∫ ξ : H3FourierPoint3, major ξ := by
    apply integral_mono hLeftInt hMajorInt
    intro ξ
    exact radialDifference_sq_le m hR ξ (Ns ξ) (Nt ξ)

  have hLeftEq :
      ‖Fms - Fmt‖ ^ 2
        =
      ∫ ξ : H3FourierPoint3,
        ‖((‖ξ‖ ^ m : ℝ) : ℂ) *
            (Ns ξ - Nt ξ)‖ ^ 2 := by
    rw [
      h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq
    ]
    apply integral_congr_ae
    filter_upwards [hFms, hFmt] with ξ hsξ htξ
    rw [hsξ, htξ]
    ring_nf

  have hLowEq :
      ‖F0s - F0t‖ ^ 2
        =
      ∫ ξ : H3FourierPoint3,
        ‖Ns ξ - Nt ξ‖ ^ 2 := by
    rw [
      h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq
    ]
    apply integral_congr_ae
    filter_upwards [hF0s, hF0t] with ξ hsξ htξ
    rw [hsξ, htξ]

  have hNextSEq :
      ‖Fnexts‖ ^ 2
        =
      ∫ ξ : H3FourierPoint3,
        ‖((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * Ns ξ‖ ^ 2 := by
    rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [hFnexts] with ξ hξ
    rw [hξ]

  have hNextTEq :
      ‖Fnextt‖ ^ 2
        =
      ∫ ξ : H3FourierPoint3,
        ‖((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * Nt ξ‖ ^ 2 := by
    rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [hFnextt] with ξ hξ
    rw [hξ]

  have hMajorEq :
      (∫ ξ : H3FourierPoint3, major ξ)
        =
      2 * (R ^ m) ^ 2 *
          (∫ ξ : H3FourierPoint3,
            ‖Ns ξ - Nt ξ‖ ^ 2)
        +
      4 * (R⁻¹) ^ 2 *
          ((∫ ξ : H3FourierPoint3,
              ‖((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * Ns ξ‖ ^ 2)
            +
           (∫ ξ : H3FourierPoint3,
              ‖((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * Nt ξ‖ ^ 2)) := by
    calc
      (∫ ξ : H3FourierPoint3, major ξ)
          =
        (∫ ξ : H3FourierPoint3,
          2 * (R ^ m) ^ 2 * ‖Ns ξ - Nt ξ‖ ^ 2)
          +
        ∫ ξ : H3FourierPoint3,
          4 * (R⁻¹) ^ 2 *
            (‖((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * Ns ξ‖ ^ 2
              +
             ‖((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * Nt ξ‖ ^ 2) := by
        dsimp only [major]
        exact
          integral_add
            (hLowInt.const_mul (2 * (R ^ m) ^ 2))
            ((hNextSInt.add hNextTInt).const_mul
              (4 * (R⁻¹) ^ 2))
      _ =
        2 * (R ^ m) ^ 2 *
            (∫ ξ : H3FourierPoint3,
              ‖Ns ξ - Nt ξ‖ ^ 2)
          +
        4 * (R⁻¹) ^ 2 *
            (∫ ξ : H3FourierPoint3,
              ‖((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * Ns ξ‖ ^ 2
                +
              ‖((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * Nt ξ‖ ^ 2) := by
        rw [integral_const_mul, integral_const_mul]
      _ =
        2 * (R ^ m) ^ 2 *
            (∫ ξ : H3FourierPoint3,
              ‖Ns ξ - Nt ξ‖ ^ 2)
          +
        4 * (R⁻¹) ^ 2 *
            ((∫ ξ : H3FourierPoint3,
                ‖((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * Ns ξ‖ ^ 2)
              +
             (∫ ξ : H3FourierPoint3,
                ‖((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * Nt ξ‖ ^ 2)) := by
        rw [integral_add hNextSInt hNextTInt]

  dsimp only [Fms, Fmt, F0s, F0t, Fnexts, Fnextt] at hLeftEq hLowEq hNextSEq hNextTEq ⊢

  rw [hLeftEq]
  calc
    (∫ ξ : H3FourierPoint3,
        ‖((‖ξ‖ ^ m : ℝ) : ℂ) *
            (Ns ξ - Nt ξ)‖ ^ 2)
        ≤
      ∫ ξ : H3FourierPoint3, major ξ :=
      hInt
    _ =
      2 * (R ^ m) ^ 2 *
          ‖h3RawFinLerayOuterProductDivergenceFourierL2
              (W (s : ℝ)) (W (s : ℝ)) i
            -
            h3RawFinLerayOuterProductDivergenceFourierL2
              (W (t : ℝ)) (W (t : ℝ)) i‖ ^ 2
        +
      4 * (R⁻¹) ^ 2 *
        (‖h3SelectedRestartForcingRadialFourierL2OnSlab
              (m + 1) hν U₀ hA hU₀ hq hqR i s‖ ^ 2
          +
         ‖h3SelectedRestartForcingRadialFourierL2OnSlab
              (m + 1) hν U₀ hA hU₀ hq hqR i t‖ ^ 2) := by
      rw [
        hMajorEq,
        ← hLowEq,
        ← hNextSEq,
        ← hNextTEq
      ]

end

end Euclidean
end Bridge
end PrimeTensor
