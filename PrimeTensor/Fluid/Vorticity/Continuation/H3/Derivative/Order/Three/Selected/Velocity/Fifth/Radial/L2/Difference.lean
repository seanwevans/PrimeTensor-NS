import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Three.Selected.Velocity.Sixth.Radial.L2.Compact.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Two.Selected.Velocity.Radial.L2.Difference

/-!
# Selected velocity fifth-radial L² difference interpolation

The order-three temporal coefficient needs strong physical `L²` continuity of
repeated fifth selected velocity jets.  The previous checkpoint supplied the
missing locally uniform sixth-radial Fourier `L²` ceiling.

This file performs the quantitative interpolation step on one positive compact
restart slab.  For `R > 0`,

    ‖F₅(s) - F₅(t)‖²
      ≤ 2 R¹⁰ ‖F₀(s) - F₀(t)‖²
        + 4 R⁻² (‖F₆(s)‖² + ‖F₆(t)‖²).

Here `F₅` is the already-existing canonical selected fifth-radial state while
`F₆` is only the compact-slab package introduced in the preceding file.  Thus
no global sixth-radial selected state is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderThreeSelectedVelocityFifthRadialL2Difference
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 3000000

/-- Specialized pointwise frequency split for radial order five. -/
private theorem fifthRadialDifference_sq_le
    {R : ℝ}
    (hR : 0 < R)
    (ξ : H3FourierPoint3)
    (z w : ℂ) :
    ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) * (z - w)‖ ^ 2
      ≤
    2 * (R ^ 5) ^ 2 * ‖z - w‖ ^ 2
      +
    4 * (R⁻¹) ^ 2 *
      (‖((‖ξ‖ ^ 6 : ℝ) : ℂ) * z‖ ^ 2
        +
       ‖((‖ξ‖ ^ 6 : ℝ) : ℂ) * w‖ ^ 2) := by
  have hR0 : 0 ≤ R := hR.le
  have hInv0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hR0
  have hx0 : 0 ≤ ‖ξ‖ := norm_nonneg ξ
  have hx5 : 0 ≤ ‖ξ‖ ^ 5 := pow_nonneg hx0 5
  have hx6 : 0 ≤ ‖ξ‖ ^ 6 := pow_nonneg hx0 6

  have hWeight :=
    norm_pow_nat_le_radius_pow_add_inv_mul_succ
      5 hR ξ

  have hDiff0 : 0 ≤ ‖z - w‖ := norm_nonneg _
  have hSub :
      ‖z - w‖ ≤ ‖z‖ + ‖w‖ :=
    norm_sub_le z w

  let A : ℝ := R ^ 5 * ‖z - w‖
  let B : ℝ := R⁻¹ * (‖ξ‖ ^ 6 * ‖z‖)
  let C : ℝ := R⁻¹ * (‖ξ‖ ^ 6 * ‖w‖)

  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (pow_nonneg hR0 5) hDiff0

  have hB0 : 0 ≤ B := by
    dsimp only [B]
    positivity

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity

  have hNorm :
      ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) * (z - w)‖
        ≤ A + B + C := by
    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg hx5
    ]

    calc
      ‖ξ‖ ^ 5 * ‖z - w‖
          ≤
        (R ^ 5 + R⁻¹ * ‖ξ‖ ^ 6) *
          ‖z - w‖ :=
        mul_le_mul_of_nonneg_right hWeight hDiff0
      _ =
        A + R⁻¹ * (‖ξ‖ ^ 6 * ‖z - w‖) := by
        dsimp only [A]
        ring
      _ ≤
        A + R⁻¹ * (‖ξ‖ ^ 6 * (‖z‖ + ‖w‖)) := by
        have hInner :
            R⁻¹ * (‖ξ‖ ^ 6 * ‖z - w‖)
              ≤
            R⁻¹ * (‖ξ‖ ^ 6 * (‖z‖ + ‖w‖)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hSub hx6)
            hInv0
        exact add_le_add_right hInner A
      _ = A + B + C := by
        dsimp only [B, C]
        ring

  have hSq :
      ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) * (z - w)‖ ^ 2
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
    ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) * (z - w)‖ ^ 2
        ≤
      2 * A ^ 2 + 4 * B ^ 2 + 4 * C ^ 2 :=
      hSq.trans hABC
    _ =
      2 * (R ^ 5) ^ 2 * ‖z - w‖ ^ 2
        +
      4 * (R⁻¹) ^ 2 *
        (‖((‖ξ‖ ^ 6 : ℝ) : ℂ) * z‖ ^ 2
          +
         ‖((‖ξ‖ ^ 6 : ℝ) : ℂ) * w‖ ^ 2) := by
      dsimp only [A, B, C]
      simp only [
        norm_mul,
        Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg hx6
      ]
      ring

/-- Compact-slab frequency-splitting estimate for fifth-radial selected
velocity differences.  The high-frequency term uses only the local sixth-radial
packages from the preceding checkpoint. -/
theorem norm_sq_h3PreterminalSelectedVelocityFifthRadialFourierL2_sub_leOnCompact
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
    let sOpen :
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
      ⟨(s : ℝ),
        lt_of_lt_of_le ha s.property.1,
        lt_of_le_of_lt s.property.2 hbR⟩
    let tOpen :
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
      ⟨(t : ℝ),
        lt_of_lt_of_le ha t.property.1,
        lt_of_le_of_lt t.property.2 hbR⟩
    ‖h3PreterminalSelectedVelocityFifthRadialFourierL2
          hNS ht₀ hE hTail sOpen j
        -
      h3PreterminalSelectedVelocityFifthRadialFourierL2
          hNS ht₀ hE hTail tOpen j‖ ^ 2
      ≤
    2 * (R ^ 5) ^ 2 *
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
      (‖h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact
            (one_pos : (0 : ℝ) < 1)
            U₀ hA hU₀ ha hbR s j‖ ^ 2
        +
       ‖h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact
            (one_pos : (0 : ℝ) < 1)
            U₀ hA hU₀ ha hbR t j‖ ^ 2) := by
  dsimp only

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀

  let sOpen :
      Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨(s : ℝ),
      lt_of_lt_of_le ha s.property.1,
      lt_of_le_of_lt s.property.2 hbR⟩

  let tOpen :
      Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨(t : ℝ),
      lt_of_lt_of_le ha t.property.1,
      lt_of_le_of_lt t.property.2 hbR⟩

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

  let F5s : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityFifthRadialFourierL2
      hNS ht₀ hE hTail sOpen j

  let F5t : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityFifthRadialFourierL2
      hNS ht₀ hE hTail tOpen j

  let F6s : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ ha hbR s j

  let F6t : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact
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

  have hF5s :
      ((F5s : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ =>
        ((‖ξ‖ ^ 5 : ℝ) : ℂ) * Ns ξ) := by
    dsimp only [F5s, Ns, W, sOpen, U₀, hA, hU₀]
    filter_upwards [
      h3PreterminalSelectedVelocityFifthRadialFourierL2_ae
        hNS ht₀ hE hTail
        ⟨(s : ℝ),
          lt_of_lt_of_le ha s.property.1,
          lt_of_le_of_lt s.property.2 hbR⟩
        j
    ] with ξ hξ
    simpa [h3SelectedRawFourierFifthRadialWeight] using hξ

  have hF5t :
      ((F5t : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ =>
        ((‖ξ‖ ^ 5 : ℝ) : ℂ) * Nt ξ) := by
    dsimp only [F5t, Nt, W, tOpen, U₀, hA, hU₀]
    filter_upwards [
      h3PreterminalSelectedVelocityFifthRadialFourierL2_ae
        hNS ht₀ hE hTail
        ⟨(t : ℝ),
          lt_of_lt_of_le ha t.property.1,
          lt_of_le_of_lt t.property.2 hbR⟩
        j
    ] with ξ hξ
    simpa [h3SelectedRawFourierFifthRadialWeight] using hξ

  have hF6s0 :=
    h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact_ae
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ ha hbR s j

  have hF6t0 :=
    h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact_ae
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

  have hF6s :
      ((F6s : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ =>
        ((‖ξ‖ ^ 6 : ℝ) : ℂ) * Ns ξ) := by
    dsimp only [F6s]
    filter_upwards [hF6s0, hWs] with ξ h6ξ hWξ
    rw [h6ξ, hWξ]

  have hF6t :
      ((F6t : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ =>
        ((‖ξ‖ ^ 6 : ℝ) : ℂ) * Nt ξ) := by
    dsimp only [F6t]
    filter_upwards [hF6t0, hWt] with ξ h6ξ hWξ
    rw [h6ξ, hWξ]

  have hLeftInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) *
              (Ns ξ - Nt ξ)‖ ^ 2)
        volume := by
    have hRaw :=
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        F5s F5t
    refine hRaw.congr ?_
    filter_upwards [hF5s, hF5t] with ξ hsξ htξ
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

  have hSixthSInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖((‖ξ‖ ^ 6 : ℝ) : ℂ) * Ns ξ‖ ^ 2)
        volume := by
    have hRaw :=
      (MeasureTheory.Lp.memLp F6s).norm.integrable_sq
    refine hRaw.congr ?_
    filter_upwards [hF6s] with ξ hξ
    rw [hξ]

  have hSixthTInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖((‖ξ‖ ^ 6 : ℝ) : ℂ) * Nt ξ‖ ^ 2)
        volume := by
    have hRaw :=
      (MeasureTheory.Lp.memLp F6t).norm.integrable_sq
    refine hRaw.congr ?_
    filter_upwards [hF6t] with ξ hξ
    rw [hξ]

  let major : H3FourierPoint3 → ℝ :=
    fun ξ =>
      2 * (R ^ 5) ^ 2 * ‖Ns ξ - Nt ξ‖ ^ 2
        +
      4 * (R⁻¹) ^ 2 *
        (‖((‖ξ‖ ^ 6 : ℝ) : ℂ) * Ns ξ‖ ^ 2
          +
         ‖((‖ξ‖ ^ 6 : ℝ) : ℂ) * Nt ξ‖ ^ 2)

  have hMajorInt :
      Integrable major volume := by
    dsimp only [major]
    exact
      (hLowInt.const_mul (2 * (R ^ 5) ^ 2)).add
        ((hSixthSInt.add hSixthTInt).const_mul
          (4 * (R⁻¹) ^ 2))

  have hInt :
      (∫ ξ : H3FourierPoint3,
          ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) *
              (Ns ξ - Nt ξ)‖ ^ 2)
        ≤
      ∫ ξ : H3FourierPoint3, major ξ := by
    apply integral_mono hLeftInt hMajorInt
    intro ξ
    exact fifthRadialDifference_sq_le hR ξ (Ns ξ) (Nt ξ)

  have hLeftEq :
      ‖F5s - F5t‖ ^ 2
        =
      ∫ ξ : H3FourierPoint3,
        ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) *
            (Ns ξ - Nt ξ)‖ ^ 2 := by
    rw [
      h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq
    ]
    apply integral_congr_ae
    filter_upwards [hF5s, hF5t] with ξ hsξ htξ
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

  have hSixthSEq :
      ‖F6s‖ ^ 2
        =
      ∫ ξ : H3FourierPoint3,
        ‖((‖ξ‖ ^ 6 : ℝ) : ℂ) * Ns ξ‖ ^ 2 := by
    rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [hF6s] with ξ hξ
    rw [hξ]

  have hSixthTEq :
      ‖F6t‖ ^ 2
        =
      ∫ ξ : H3FourierPoint3,
        ‖((‖ξ‖ ^ 6 : ℝ) : ℂ) * Nt ξ‖ ^ 2 := by
    rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [hF6t] with ξ hξ
    rw [hξ]

  have hMajorEq :
      (∫ ξ : H3FourierPoint3, major ξ)
        =
      2 * (R ^ 5) ^ 2 *
          (∫ ξ : H3FourierPoint3,
            ‖Ns ξ - Nt ξ‖ ^ 2)
        +
      4 * (R⁻¹) ^ 2 *
          ((∫ ξ : H3FourierPoint3,
              ‖((‖ξ‖ ^ 6 : ℝ) : ℂ) * Ns ξ‖ ^ 2)
            +
           (∫ ξ : H3FourierPoint3,
              ‖((‖ξ‖ ^ 6 : ℝ) : ℂ) * Nt ξ‖ ^ 2)) := by
    calc
      (∫ ξ : H3FourierPoint3, major ξ)
          =
        (∫ ξ : H3FourierPoint3,
          2 * (R ^ 5) ^ 2 * ‖Ns ξ - Nt ξ‖ ^ 2)
          +
        ∫ ξ : H3FourierPoint3,
          4 * (R⁻¹) ^ 2 *
            (‖((‖ξ‖ ^ 6 : ℝ) : ℂ) * Ns ξ‖ ^ 2
              +
             ‖((‖ξ‖ ^ 6 : ℝ) : ℂ) * Nt ξ‖ ^ 2) := by
        dsimp only [major]
        exact
          integral_add
            (hLowInt.const_mul (2 * (R ^ 5) ^ 2))
            ((hSixthSInt.add hSixthTInt).const_mul
              (4 * (R⁻¹) ^ 2))
      _ =
        2 * (R ^ 5) ^ 2 *
            (∫ ξ : H3FourierPoint3,
              ‖Ns ξ - Nt ξ‖ ^ 2)
          +
        4 * (R⁻¹) ^ 2 *
            (∫ ξ : H3FourierPoint3,
              ‖((‖ξ‖ ^ 6 : ℝ) : ℂ) * Ns ξ‖ ^ 2
                +
              ‖((‖ξ‖ ^ 6 : ℝ) : ℂ) * Nt ξ‖ ^ 2) := by
        rw [integral_const_mul, integral_const_mul]
      _ =
        2 * (R ^ 5) ^ 2 *
            (∫ ξ : H3FourierPoint3,
              ‖Ns ξ - Nt ξ‖ ^ 2)
          +
        4 * (R⁻¹) ^ 2 *
            ((∫ ξ : H3FourierPoint3,
                ‖((‖ξ‖ ^ 6 : ℝ) : ℂ) * Ns ξ‖ ^ 2)
              +
             (∫ ξ : H3FourierPoint3,
                ‖((‖ξ‖ ^ 6 : ℝ) : ℂ) * Nt ξ‖ ^ 2)) := by
        rw [integral_add hSixthSInt hSixthTInt]

  dsimp only [
    F5s, F5t, F0s, F0t, F6s, F6t,
    W, U₀, hA, hU₀, sOpen, tOpen
  ] at hLeftEq hLowEq hSixthSEq hSixthTEq ⊢

  rw [hLeftEq]
  calc
    (∫ ξ : H3FourierPoint3,
        ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) *
            (Ns ξ - Nt ξ)‖ ^ 2)
        ≤
      ∫ ξ : H3FourierPoint3, major ξ :=
      hInt
    _ =
      2 * (R ^ 5) ^ 2 *
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
        (‖h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact
              (one_pos : (0 : ℝ) < 1)
              (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
              (lt_of_lt_of_le zero_lt_one hE)
              (norm_h3PreterminalSelectedDecoderAnchorState_le
                hNS ht₀ hE hTail)
              ha hbR s j‖ ^ 2
          +
         ‖h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact
              (one_pos : (0 : ℝ) < 1)
              (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
              (lt_of_lt_of_le zero_lt_one hE)
              (norm_h3PreterminalSelectedDecoderAnchorState_le
                hNS ht₀ hE hTail)
              ha hbR t j‖ ^ 2) := by
      rw [
        hMajorEq,
        ← hLowEq,
        ← hSixthSEq,
        ← hSixthTEq
      ]

end

end Euclidean
end Bridge
end PrimeTensor
