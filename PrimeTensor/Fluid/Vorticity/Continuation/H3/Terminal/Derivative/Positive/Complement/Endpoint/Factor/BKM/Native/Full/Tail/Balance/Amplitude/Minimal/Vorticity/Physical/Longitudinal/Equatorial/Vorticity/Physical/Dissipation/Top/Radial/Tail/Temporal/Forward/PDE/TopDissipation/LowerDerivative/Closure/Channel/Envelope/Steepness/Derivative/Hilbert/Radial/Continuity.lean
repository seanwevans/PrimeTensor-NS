import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Sixth.Continuity

/-!
# Order-generic compact selected velocity radial continuity

The previous checkpoint made the compact selected-velocity radial norm-square
bound generic in the natural order.  The old sixth-radial continuity theorem
uses only one order-independent frequency-splitting mechanism:

    |ξ|^m ≤ R^m + R⁻¹ |ξ|^(m+1).

Consequently, for `R > 0`,

    ‖F_m(s) - F_m(t)‖²
      ≤
    2 (R^m)² ‖F_0(s) - F_0(t)‖²
      +
    4 R⁻² (‖F_(m+1)(s)‖² + ‖F_(m+1)(t)‖²).

The raw selected Fourier state is already strongly continuous.  The generic
compact `(m+1)`-radial norm-square ceiling makes the high-frequency term
uniformly small.  Therefore every finite radial selected velocity state
`F_m`, `m ≥ 2`, is strongly continuous on every positive compact restart
slab.

The final specialization at `m = 8` supplies the exact velocity continuity
needed to differentiate the sixth-diffusion Hilbert state `q³ û_j`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalGenericVelocityRadialContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 3500000

/-! ## Generic pointwise frequency split -/

/--
Pointwise frequency split at arbitrary natural radial order.
-/
private theorem natRadialDifference_sq_le
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
  have hxm : 0 ≤ ‖ξ‖ ^ m := pow_nonneg hx0 m
  have hxm1 : 0 ≤ ‖ξ‖ ^ (m + 1) := pow_nonneg hx0 (m + 1)

  have hWeight :=
    norm_pow_nat_le_radius_pow_add_inv_mul_succ
      m hR ξ

  have hDiff0 : 0 ≤ ‖z - w‖ := norm_nonneg _

  have hSub :
      ‖z - w‖ ≤ ‖z‖ + ‖w‖ :=
    norm_sub_le z w

  let A : ℝ :=
    R ^ m * ‖z - w‖

  let B : ℝ :=
    R⁻¹ * (‖ξ‖ ^ (m + 1) * ‖z‖)

  let C : ℝ :=
    R⁻¹ * (‖ξ‖ ^ (m + 1) * ‖w‖)

  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact
      mul_nonneg
        (pow_nonneg hR0 m)
        hDiff0

  have hB0 : 0 ≤ B := by
    dsimp only [B]
    positivity

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity

  have hNorm :
      ‖((‖ξ‖ ^ m : ℝ) : ℂ) * (z - w)‖
        ≤
      A + B + C := by

    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg hxm
    ]

    calc
      ‖ξ‖ ^ m * ‖z - w‖
          ≤
        (R ^ m + R⁻¹ * ‖ξ‖ ^ (m + 1)) *
          ‖z - w‖ :=
        mul_le_mul_of_nonneg_right
          hWeight hDiff0
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
            R⁻¹ *
                (‖ξ‖ ^ (m + 1) * ‖z - w‖)
              ≤
            R⁻¹ *
                (‖ξ‖ ^ (m + 1) * (‖z‖ + ‖w‖)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              hSub hxm1)
            hInv0
        exact
          add_le_add_right hInner A
      _ =
        A + B + C := by
        dsimp only [B, C]
        ring

  have hSq :
      ‖((‖ξ‖ ^ m : ℝ) : ℂ) * (z - w)‖ ^ 2
        ≤
      (A + B + C) ^ 2 :=
    pow_le_pow_left₀
      (norm_nonneg _)
      hNorm
      2

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
        abs_of_nonneg hxm1
      ]
      ring

/-! ## Generic compact difference estimate -/

/--
Frequency-splitting estimate for arbitrary selected velocity radial order
`m ≥ 2`, with the high-frequency term controlled by the generic `(m+1)` state.
-/
theorem norm_sq_h3PreterminalSelectedVelocityNatRadialFourierL2_sub_leOnCompact
    (m : ℕ)
    (hm : 2 ≤ m)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ a b : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (ha : 0 < a)
    (hbR : b < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    {R : ℝ}
    (hR : 0 < R)
    (j : Fin 3)
    (s t : Set.Icc a b) :
    let U₀ : H3SpectralVelocityState :=
      h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail
    let hA : 0 < E :=
      lt_of_lt_of_le zero_lt_one hE
    let hU₀ : ‖U₀‖ ≤ E :=
      norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail
    ‖h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
          m hm
          (one_pos : (0 : ℝ) < 1)
          U₀ hA hU₀ ha hbR s j
        -
      h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
          m hm
          (one_pos : (0 : ℝ) < 1)
          U₀ hA hU₀ ha hbR t j‖ ^ 2
      ≤
    2 * (R ^ m) ^ 2 *
      ‖h3SpectralScalarRawFourierL2
          ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              (one_pos : (0 : ℝ) < 1)
              U₀ hA hU₀
              (s : ℝ))
            j)
        -
        h3SpectralScalarRawFourierL2
          ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              (one_pos : (0 : ℝ) < 1)
              U₀ hA hU₀
              (t : ℝ))
            j)‖ ^ 2
      +
    4 * (R⁻¹) ^ 2 *
      (‖h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
            (m + 1) (by omega)
            (one_pos : (0 : ℝ) < 1)
            U₀ hA hU₀ ha hbR s j‖ ^ 2
        +
       ‖h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
            (m + 1) (by omega)
            (one_pos : (0 : ℝ) < 1)
            U₀ hA hU₀ ha hbR t j‖ ^ 2) := by

  dsimp only

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀

  let Ns : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourier
      (W (s : ℝ) j)

  let Nt : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourier
      (W (t : ℝ) j)

  let F0s : H3FourierComplexL2 :=
    h3SpectralScalarRawFourierL2
      (W (s : ℝ) j)

  let F0t : H3FourierComplexL2 :=
    h3SpectralScalarRawFourierL2
      (W (t : ℝ) j)

  let Fms : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
      m hm
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ ha hbR s j

  let Fmt : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
      m hm
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ ha hbR t j

  let Fnexts : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
      (m + 1) (by omega)
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ ha hbR s j

  let Fnextt : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
      (m + 1) (by omega)
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ ha hbR t j

  have hF0s :
      ((F0s : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      Ns := by
    dsimp only [F0s, Ns]
    exact
      h3SpectralScalarRawFourierL2_ae
        (W (s : ℝ) j)

  have hF0t :
      ((F0t : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      Nt := by
    dsimp only [F0t, Nt]
    exact
      h3SpectralScalarRawFourierL2_ae
        (W (t : ℝ) j)

  have hFms0 :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact_ae
      m hm
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ ha hbR s j

  have hFmt0 :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact_ae
      m hm
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ ha hbR t j

  have hFnexts0 :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact_ae
      (m + 1) (by omega)
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ ha hbR s j

  have hFnextt0 :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact_ae
      (m + 1) (by omega)
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ ha hbR t j

  have hWs :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_rawFourier
      (t := (s : ℝ))
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ j

  have hWt :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_rawFourier
      (t := (t : ℝ))
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ j

  have hFms :
      ((Fms : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) * Ns ξ) := by
    dsimp only [Fms]
    filter_upwards [hFms0, hWs] with ξ hmξ hWξ
    rw [hmξ, hWξ]

  have hFmt :
      ((Fmt : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) * Nt ξ) := by
    dsimp only [Fmt]
    filter_upwards [hFmt0, hWt] with ξ hmξ hWξ
    rw [hmξ, hWξ]

  have hFnexts :
      ((Fnexts : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ =>
        ((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * Ns ξ) := by
    dsimp only [Fnexts]
    filter_upwards [hFnexts0, hWs] with ξ hnextξ hWξ
    rw [hnextξ, hWξ]

  have hFnextt :
      ((Fnextt : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ =>
        ((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * Nt ξ) := by
    dsimp only [Fnextt]
    filter_upwards [hFnextt0, hWt] with ξ hnextξ hWξ
    rw [hnextξ, hWξ]

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
    filter_upwards [hFms, hFmt] with ξ hsξ htξ
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
    filter_upwards [hF0s, hF0t] with ξ hsξ htξ
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
      (hLowInt.const_mul
        (2 * (R ^ m) ^ 2)).add
        ((hNextSInt.add hNextTInt).const_mul
          (4 * (R⁻¹) ^ 2))

  have hInt :
      (∫ ξ : H3FourierPoint3,
          ‖((‖ξ‖ ^ m : ℝ) : ℂ) *
              (Ns ξ - Nt ξ)‖ ^ 2)
        ≤
      ∫ ξ : H3FourierPoint3,
        major ξ := by
    apply integral_mono hLeftInt hMajorInt
    intro ξ
    exact
      natRadialDifference_sq_le
        m hR ξ (Ns ξ) (Nt ξ)

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
    rw [
      h3FourierComplexL2_norm_sq_eq_integral_norm_sq
    ]
    apply integral_congr_ae
    filter_upwards [hFnexts] with ξ hξ
    rw [hξ]

  have hNextTEq :
      ‖Fnextt‖ ^ 2
        =
      ∫ ξ : H3FourierPoint3,
        ‖((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * Nt ξ‖ ^ 2 := by
    rw [
      h3FourierComplexL2_norm_sq_eq_integral_norm_sq
    ]
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
          2 * (R ^ m) ^ 2 *
            ‖Ns ξ - Nt ξ‖ ^ 2)
          +
        ∫ ξ : H3FourierPoint3,
          4 * (R⁻¹) ^ 2 *
            (‖((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * Ns ξ‖ ^ 2
              +
             ‖((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) * Nt ξ‖ ^ 2) := by
        dsimp only [major]
        exact
          integral_add
            (hLowInt.const_mul
              (2 * (R ^ m) ^ 2))
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
        rw [
          integral_const_mul,
          integral_const_mul
        ]
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
        rw [
          integral_add
            hNextSInt hNextTInt
        ]

  dsimp only [
    Fms, Fmt, F0s, F0t,
    Fnexts, Fnextt,
    W, U₀, hA, hU₀
  ] at hLeftEq hLowEq hNextSEq hNextTEq ⊢

  rw [hLeftEq]

  calc
    (∫ ξ : H3FourierPoint3,
        ‖((‖ξ‖ ^ m : ℝ) : ℂ) *
            (Ns ξ - Nt ξ)‖ ^ 2)
        ≤
      ∫ ξ : H3FourierPoint3,
        major ξ :=
      hInt
    _ =
      2 * (R ^ m) ^ 2 *
        ‖h3SpectralScalarRawFourierL2
            ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                (one_pos : (0 : ℝ) < 1)
                (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
                (lt_of_lt_of_le zero_lt_one hE)
                (norm_h3PreterminalSelectedDecoderAnchorState_le
                  hNS ht₀ hE hTail)
                (s : ℝ))
              j)
          -
          h3SpectralScalarRawFourierL2
            ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                (one_pos : (0 : ℝ) < 1)
                (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
                (lt_of_lt_of_le zero_lt_one hE)
                (norm_h3PreterminalSelectedDecoderAnchorState_le
                  hNS ht₀ hE hTail)
                (t : ℝ))
              j)‖ ^ 2
        +
      4 * (R⁻¹) ^ 2 *
        (‖h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
              (m + 1) (by omega)
              (one_pos : (0 : ℝ) < 1)
              (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
              (lt_of_lt_of_le zero_lt_one hE)
              (norm_h3PreterminalSelectedDecoderAnchorState_le
                hNS ht₀ hE hTail)
              ha hbR s j‖ ^ 2
          +
         ‖h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
              (m + 1) (by omega)
              (one_pos : (0 : ℝ) < 1)
              (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
              (lt_of_lt_of_le zero_lt_one hE)
              (norm_h3PreterminalSelectedDecoderAnchorState_le
                hNS ht₀ hE hTail)
              ha hbR t j‖ ^ 2) := by
      rw [
        hMajorEq,
        ← hLowEq,
        ← hNextSEq,
        ← hNextTEq
      ]

/-! ## Generic compact continuity -/

/--
Every natural selected velocity radial state `m ≥ 2` is strongly continuous
on each positive compact restart slab.
-/
theorem continuous_h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
    (m : ℕ)
    (hm : 2 ≤ m)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ a b : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (ha : 0 < a)
    (hab : a ≤ b)
    (hbR : b < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (j : Fin 3) :
    Continuous
      (fun s : Set.Icc a b =>
        h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
          m hm
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
          ha hbR s j) := by

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀

  let F0 :
      Set.Icc a b → H3FourierComplexL2 :=
    fun s =>
      h3SpectralScalarRawFourierL2
        (W (s : ℝ) j)

  let Fm :
      Set.Icc a b → H3FourierComplexL2 :=
    fun s =>
      h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
        m hm
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀ ha hbR s j

  let Fnext :
      Set.Icc a b → H3FourierComplexL2 :=
    fun s =>
      h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
        (m + 1) (by omega)
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀ ha hbR s j

  have hF0 :
      Continuous F0 := by
    dsimp only [F0, W]
    exact
      (continuous_h3PreterminalSelectedVelocityRawFourierL2
        hNS ht₀ hE hTail j).comp
        continuous_subtype_val

  obtain
    ⟨B, hB0, hB⟩ :=
    exists_norm_sq_bound_h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
      (m + 1) (by omega)
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      ha hab hbR

  rw [continuous_iff_continuousAt]

  intro s₀

  apply
    tendsto_iff_norm_sub_tendsto_zero.2

  have hLowNormTend :
      Tendsto
        (fun s : Set.Icc a b =>
          ‖F0 s - F0 s₀‖)
        (𝓝 s₀)
        (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1
      hF0.continuousAt

  have hPow :
      Tendsto
        (fun x : ℝ => x ^ 2)
        (𝓝 0)
        (𝓝 ((0 : ℝ) ^ 2)) := by
    exact
      continuousAt_id.pow 2

  have hLowSqTend :
      Tendsto
        (fun s : Set.Icc a b =>
          ‖F0 s - F0 s₀‖ ^ 2)
        (𝓝 s₀)
        (𝓝 0) := by

    have hComp :=
      hPow.comp hLowNormTend

    change
      Tendsto
        (fun s : Set.Icc a b =>
          ‖F0 s - F0 s₀‖ ^ 2)
        (𝓝 s₀)
        (𝓝 ((0 : ℝ) ^ 2))
      at hComp

    norm_num at hComp

    exact hComp

  have hSqTend :
      Tendsto
        (fun s : Set.Icc a b =>
          ‖Fm s - Fm s₀‖ ^ 2)
        (𝓝 s₀)
        (𝓝 0) := by

    refine
      tendsto_order.2
        ⟨?_, ?_⟩

    · intro c hc

      exact
        Filter.Eventually.of_forall
          (fun s =>
            lt_of_lt_of_le
              hc
              (sq_nonneg
                ‖Fm s - Fm s₀‖))

    · intro ε hε

      let R : ℝ :=
        1 + (16 * B) / ε

      have hFrac0 :
          0 ≤ (16 * B) / ε := by
        exact
          div_nonneg
            (mul_nonneg
              (by norm_num)
              hB0)
            hε.le

      have hR :
          0 < R := by
        dsimp only [R]
        linarith

      have hRone :
          1 ≤ R := by
        dsimp only [R]
        linarith

      have hRfrac :
          (16 * B) / ε < R := by
        dsimp only [R]
        linarith

      have hBR :
          16 * B < ε * R := by
        simpa only [mul_comm] using
          (div_lt_iff₀ hε).1 hRfrac

      have hInv0 :
          0 ≤ R⁻¹ :=
        inv_nonneg.mpr hR.le

      have hInvOne :
          R⁻¹ ≤ 1 :=
        (inv_le_one₀ hR).2 hRone

      have hInvSq :
          (R⁻¹) ^ 2 ≤ R⁻¹ := by
        nlinarith [
          sq_nonneg (R⁻¹)
        ]

      have hSixteen :
          16 * B * R⁻¹ < ε := by
        have hDiv :
            (16 * B) / R < ε :=
          (div_lt_iff₀ hR).2 hBR
        simpa only [
          div_eq_mul_inv,
          mul_assoc
        ] using hDiv

      have hTailBudget :
          8 * B * (R⁻¹) ^ 2 < ε / 2 := by

        have hStep :
            8 * B * (R⁻¹) ^ 2
              ≤
            8 * B * R⁻¹ :=
          mul_le_mul_of_nonneg_left
            hInvSq
            (mul_nonneg
              (by norm_num)
              hB0)

        have hHalf :
            8 * B * R⁻¹ < ε / 2 := by
          nlinarith

        exact
          hStep.trans_lt hHalf

      let C : ℝ :=
        2 * (R ^ m) ^ 2

      have hC0 :
          0 ≤ C := by
        dsimp only [C]
        positivity

      have hC1 :
          0 < C + 1 := by
        linarith

      let η : ℝ :=
        ε / (2 * (C + 1))

      have hη :
          0 < η := by
        dsimp only [η]
        positivity

      have hLowEventually :
          ∀ᶠ s in 𝓝 s₀,
            ‖F0 s - F0 s₀‖ ^ 2 < η :=
        (tendsto_order.1 hLowSqTend).2
          η hη

      filter_upwards [hLowEventually]
        with s hsLow

      have hInterp :=
        norm_sq_h3PreterminalSelectedVelocityNatRadialFourierL2_sub_leOnCompact
          m hm
          hNS ht₀ hE hTail
          ha hbR hR j s s₀

      have hηEq :
          (C + 1) * η = ε / 2 := by
        dsimp only [η]
        field_simp [ne_of_gt hC1]

      have hLow :
          C * ‖F0 s - F0 s₀‖ ^ 2
            <
          ε / 2 := by

        have hCLe :
            C ≤ C + 1 := by
          linarith

        have hSq0 :
            0 ≤
              ‖F0 s - F0 s₀‖ ^ 2 :=
          sq_nonneg _

        have hStep1 :
            C *
                ‖F0 s - F0 s₀‖ ^ 2
              ≤
            (C + 1) *
                ‖F0 s - F0 s₀‖ ^ 2 :=
          mul_le_mul_of_nonneg_right
            hCLe hSq0

        have hStep2 :
            (C + 1) *
                ‖F0 s - F0 s₀‖ ^ 2
              <
            (C + 1) * η :=
          mul_lt_mul_of_pos_left
            hsLow hC1

        exact
          lt_of_le_of_lt
            hStep1
            (hStep2.trans_eq hηEq)

      have hNext :
          ‖Fnext s‖ ^ 2 +
              ‖Fnext s₀‖ ^ 2
            ≤
          B + B := by
        exact
          add_le_add
            (by
              dsimp only [Fnext]
              exact hB s j)
            (by
              dsimp only [Fnext]
              exact hB s₀ j)

      have hTailSmall :
          4 * (R⁻¹) ^ 2 *
              (‖Fnext s‖ ^ 2 +
               ‖Fnext s₀‖ ^ 2)
            <
          ε / 2 := by
        calc
          4 * (R⁻¹) ^ 2 *
              (‖Fnext s‖ ^ 2 +
               ‖Fnext s₀‖ ^ 2)
              ≤
            4 * (R⁻¹) ^ 2 *
              (B + B) :=
            mul_le_mul_of_nonneg_left
              hNext
              (mul_nonneg
                (by norm_num)
                (sq_nonneg _))
          _ =
            8 * B * (R⁻¹) ^ 2 := by
            ring
          _ < ε / 2 :=
            hTailBudget

      have hSqLt :
          ‖Fm s - Fm s₀‖ ^ 2
            <
          ε := by

        have hInterp' :
            ‖Fm s - Fm s₀‖ ^ 2
              ≤
            2 * (R ^ m) ^ 2 *
                ‖F0 s - F0 s₀‖ ^ 2
              +
            4 * (R⁻¹) ^ 2 *
              (‖Fnext s‖ ^ 2 +
               ‖Fnext s₀‖ ^ 2) := by
          dsimp only [
            Fm, Fnext, F0,
            W, U₀, hA, hU₀
          ]
          exact hInterp

        calc
          ‖Fm s - Fm s₀‖ ^ 2
              ≤
            2 * (R ^ m) ^ 2 *
                ‖F0 s - F0 s₀‖ ^ 2
              +
            4 * (R⁻¹) ^ 2 *
              (‖Fnext s‖ ^ 2 +
               ‖Fnext s₀‖ ^ 2) :=
            hInterp'
          _ <
            ε / 2 + ε / 2 := by
            exact
              add_lt_add
                hLow hTailSmall
          _ =
            ε := by
            ring

      exact hSqLt

  have hSqrt :=
    (Real.continuous_sqrt.tendsto 0).comp
      hSqTend

  change
    Tendsto
      (fun s : Set.Icc a b =>
        Real.sqrt
          (‖Fm s - Fm s₀‖ ^ 2))
      (𝓝 s₀)
      (𝓝 (Real.sqrt 0))
    at hSqrt

  simpa only [
    Real.sqrt_sq_eq_abs,
    abs_of_nonneg,
    norm_nonneg,
    Real.sqrt_zero
  ] using hSqrt

/-! ## Eighth-radial specialization -/

/--
The selected eighth-radial velocity state is strongly continuous on every
positive compact restart slab.
-/
theorem continuous_h3PreterminalSelectedVelocityEighthRadialFourierL2OnCompact
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ a b : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (ha : 0 < a)
    (hab : a ≤ b)
    (hbR : b < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (j : Fin 3) :
    Continuous
      (fun s : Set.Icc a b =>
        h3PreterminalSelectedVelocityEighthRadialFourierL2OnCompact
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
          ha hbR s j) := by

  unfold
    h3PreterminalSelectedVelocityEighthRadialFourierL2OnCompact

  exact
    continuous_h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
      8 (by norm_num)
      hNS ht₀ hE hTail
      ha hab hbR j

end

end Euclidean
end Bridge
end PrimeTensor
