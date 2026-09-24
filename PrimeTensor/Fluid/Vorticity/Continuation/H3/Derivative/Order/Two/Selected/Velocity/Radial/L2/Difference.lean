import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Velocity.Jet.High.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Forcing.Radial.L2.Difference

/-!
# Selected velocity fourth-radial L² difference interpolation

The order-two temporal coefficient now has a completely closed forcing-Hessian
continuity branch.  Its remaining term is the repeated-index fourth spatial
velocity jet.

Fourth velocity derivatives are not native to the H³ state, so unlike the
order-one cubic branch they are not obtained from the base spectral norm by a
globally bounded multiplier.  Positive-time smoothing already gives both
fourth- and fifth-radial raw Fourier `L²` mass at every strict restart time.

This file packages those radial states quotient-safely and proves the same
frequency-splitting inequality already used successfully for selected forcing.

For `R > 0`,

    ‖F₄(s) - F₄(t)‖²
      ≤ 2 R⁸ ‖F₀(s) - F₀(t)‖²
        + 4 R⁻² (‖F₅(s)‖² + ‖F₅(t)‖²).

Thus fourth-radial continuity reduces to:

* ordinary raw selected-state `L²` continuity;
* a local uniform fifth-radial `L²` bound.

No moving-terminal Duhamel continuity is needed at this stage.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderTwoSelectedVelocityRadialL2Difference
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Public packaging of the already-closed selected fourth/fifth radial raw
Fourier `L²` theorem. -/
theorem h3CanonicalSelectedFourthFifthRadialRawFourierMemLp2OnRestartRadius_closed :
    H3CanonicalSelectedFourthFifthRadialRawFourierMemLp2OnRestartRadius := by
  have hTail :
      H3CanonicalSelectedDuhamelTailFourthFifthRadialRawFourierMemLp2OnRestartRadius :=
    h3CanonicalSelectedDuhamelTailFourthFifthRadialRawFourierMemLp2OnRestartRadius

  have hDuhamel :
      H3CanonicalSelectedDuhamelFourthFifthRadialRawFourierMemLp2OnRestartRadius :=
    h3CanonicalSelectedDuhamelFourthFifthRadialRawFourierMemLp2OnRestartRadius_of_tail
      hTail

  exact
    h3CanonicalSelectedFourthFifthRadialRawFourierMemLp2OnRestartRadius_of_duhamel
      hDuhamel

/-- Quotient-safe fourth-radial raw Fourier state for one selected velocity
coordinate on the open restart interval. -/
noncomputable def h3PreterminalSelectedVelocityFourthRadialFourierL2
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (q :
      Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (j : Fin 3) :
    H3FourierComplexL2 :=
  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail
  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE
  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1) U₀ hA hU₀
  let hRadial :=
    h3CanonicalSelectedFourthFifthRadialRawFourierMemLp2OnRestartRadius_closed
      E u T t₀ hNS ht₀ hE hTail (q : ℝ) q.property
  (hRadial.1 j).toLp
    (h3SelectedRawFourierFourthRadialWeight
      (W (q : ℝ) j))

/-- A.e. representative of the selected fourth-radial state. -/
theorem h3PreterminalSelectedVelocityFourthRadialFourierL2_ae
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (q :
      Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (j : Fin 3) :
    let U₀ : H3SpectralVelocityState :=
      h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail
    let hA : 0 < E :=
      lt_of_lt_of_le zero_lt_one hE
    let hU₀ : ‖U₀‖ ≤ E :=
      norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        (one_pos : (0 : ℝ) < 1) U₀ hA hU₀
    ((h3PreterminalSelectedVelocityFourthRadialFourierL2
        hNS ht₀ hE hTail q j : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3SelectedRawFourierFourthRadialWeight
      (W (q : ℝ) j) := by
  dsimp only

  have hRadial :=
    h3CanonicalSelectedFourthFifthRadialRawFourierMemLp2OnRestartRadius_closed
      E u T t₀ hNS ht₀ hE hTail (q : ℝ) q.property

  unfold h3PreterminalSelectedVelocityFourthRadialFourierL2
  exact
    MeasureTheory.MemLp.coeFn_toLp
      (hRadial.1 j)

/-- Quotient-safe fifth-radial raw Fourier state for one selected velocity
coordinate on the open restart interval. -/
noncomputable def h3PreterminalSelectedVelocityFifthRadialFourierL2
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (q :
      Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (j : Fin 3) :
    H3FourierComplexL2 :=
  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail
  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE
  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1) U₀ hA hU₀
  let hRadial :=
    h3CanonicalSelectedFourthFifthRadialRawFourierMemLp2OnRestartRadius_closed
      E u T t₀ hNS ht₀ hE hTail (q : ℝ) q.property
  (hRadial.2 j).toLp
    (h3SelectedRawFourierFifthRadialWeight
      (W (q : ℝ) j))

/-- A.e. representative of the selected fifth-radial state. -/
theorem h3PreterminalSelectedVelocityFifthRadialFourierL2_ae
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (q :
      Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (j : Fin 3) :
    let U₀ : H3SpectralVelocityState :=
      h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail
    let hA : 0 < E :=
      lt_of_lt_of_le zero_lt_one hE
    let hU₀ : ‖U₀‖ ≤ E :=
      norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        (one_pos : (0 : ℝ) < 1) U₀ hA hU₀
    ((h3PreterminalSelectedVelocityFifthRadialFourierL2
        hNS ht₀ hE hTail q j : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3SelectedRawFourierFifthRadialWeight
      (W (q : ℝ) j) := by
  dsimp only

  have hRadial :=
    h3CanonicalSelectedFourthFifthRadialRawFourierMemLp2OnRestartRadius_closed
      E u T t₀ hNS ht₀ hE hTail (q : ℝ) q.property

  unfold h3PreterminalSelectedVelocityFifthRadialFourierL2
  exact
    MeasureTheory.MemLp.coeFn_toLp
      (hRadial.2 j)

/-- Specialized pointwise frequency split for radial order four. -/
private theorem fourthRadialDifference_sq_le
    {R : ℝ}
    (hR : 0 < R)
    (ξ : H3FourierPoint3)
    (z w : ℂ) :
    ‖((‖ξ‖ ^ 4 : ℝ) : ℂ) * (z - w)‖ ^ 2
      ≤
    2 * (R ^ 4) ^ 2 * ‖z - w‖ ^ 2
      +
    4 * (R⁻¹) ^ 2 *
      (‖((‖ξ‖ ^ 5 : ℝ) : ℂ) * z‖ ^ 2
        +
       ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) * w‖ ^ 2) := by
  have hR0 : 0 ≤ R := hR.le
  have hInv0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hR0
  have hx0 : 0 ≤ ‖ξ‖ := norm_nonneg ξ
  have hx4 : 0 ≤ ‖ξ‖ ^ 4 := pow_nonneg hx0 4
  have hx5 : 0 ≤ ‖ξ‖ ^ 5 := pow_nonneg hx0 5

  have hWeight :=
    norm_pow_nat_le_radius_pow_add_inv_mul_succ
      4 hR ξ

  have hDiff0 : 0 ≤ ‖z - w‖ := norm_nonneg _
  have hSub :
      ‖z - w‖ ≤ ‖z‖ + ‖w‖ :=
    norm_sub_le z w

  let A : ℝ := R ^ 4 * ‖z - w‖
  let B : ℝ := R⁻¹ * (‖ξ‖ ^ 5 * ‖z‖)
  let C : ℝ := R⁻¹ * (‖ξ‖ ^ 5 * ‖w‖)

  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (pow_nonneg hR0 4) hDiff0

  have hB0 : 0 ≤ B := by
    dsimp only [B]
    positivity

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity

  have hNorm :
      ‖((‖ξ‖ ^ 4 : ℝ) : ℂ) * (z - w)‖
        ≤ A + B + C := by
    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg hx4
    ]

    calc
      ‖ξ‖ ^ 4 * ‖z - w‖
          ≤
        (R ^ 4 + R⁻¹ * ‖ξ‖ ^ 5) *
          ‖z - w‖ :=
        mul_le_mul_of_nonneg_right hWeight hDiff0
      _ =
        A + R⁻¹ * (‖ξ‖ ^ 5 * ‖z - w‖) := by
        dsimp only [A]
        ring
      _ ≤
        A + R⁻¹ * (‖ξ‖ ^ 5 * (‖z‖ + ‖w‖)) := by
        have hInner :
            R⁻¹ * (‖ξ‖ ^ 5 * ‖z - w‖)
              ≤
            R⁻¹ * (‖ξ‖ ^ 5 * (‖z‖ + ‖w‖)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hSub hx5)
            hInv0
        exact add_le_add_right hInner A
      _ = A + B + C := by
        dsimp only [B, C]
        ring

  have hSq :
      ‖((‖ξ‖ ^ 4 : ℝ) : ℂ) * (z - w)‖ ^ 2
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
    ‖((‖ξ‖ ^ 4 : ℝ) : ℂ) * (z - w)‖ ^ 2
        ≤
      2 * A ^ 2 + 4 * B ^ 2 + 4 * C ^ 2 :=
      hSq.trans hABC
    _ =
      2 * (R ^ 4) ^ 2 * ‖z - w‖ ^ 2
        +
      4 * (R⁻¹) ^ 2 *
        (‖((‖ξ‖ ^ 5 : ℝ) : ℂ) * z‖ ^ 2
          +
         ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) * w‖ ^ 2) := by
      dsimp only [A, B, C]
      simp only [
        norm_mul,
        Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg hx5
      ]
      ring

/-- Frequency-splitting estimate for fourth-radial selected velocity
differences.  This is the exact quantitative bridge needed for continuity. -/
theorem norm_sq_h3PreterminalSelectedVelocityFourthRadialFourierL2_sub_le
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    {R : ℝ}
    (hR : 0 < R)
    (j : Fin 3)
    (s t :
      Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E)) :
    ‖h3PreterminalSelectedVelocityFourthRadialFourierL2
          hNS ht₀ hE hTail s j
        -
      h3PreterminalSelectedVelocityFourthRadialFourierL2
          hNS ht₀ hE hTail t j‖ ^ 2
      ≤
    2 * (R ^ 4) ^ 2 *
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
      (‖h3PreterminalSelectedVelocityFifthRadialFourierL2
            hNS ht₀ hE hTail s j‖ ^ 2
        +
       ‖h3PreterminalSelectedVelocityFifthRadialFourierL2
            hNS ht₀ hE hTail t j‖ ^ 2) := by
  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail)

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

  let F4s : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityFourthRadialFourierL2
      hNS ht₀ hE hTail s j

  let F4t : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityFourthRadialFourierL2
      hNS ht₀ hE hTail t j

  let F5s : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityFifthRadialFourierL2
      hNS ht₀ hE hTail s j

  let F5t : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityFifthRadialFourierL2
      hNS ht₀ hE hTail t j

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

  have hF4s :
      ((F4s : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ =>
        ((‖ξ‖ ^ 4 : ℝ) : ℂ) * Ns ξ) := by
    dsimp only [F4s, Ns, W, U₀]
    filter_upwards [
      h3PreterminalSelectedVelocityFourthRadialFourierL2_ae
        hNS ht₀ hE hTail s j
    ] with ξ hξ
    simpa [h3SelectedRawFourierFourthRadialWeight] using hξ

  have hF4t :
      ((F4t : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ =>
        ((‖ξ‖ ^ 4 : ℝ) : ℂ) * Nt ξ) := by
    dsimp only [F4t, Nt, W, U₀]
    filter_upwards [
      h3PreterminalSelectedVelocityFourthRadialFourierL2_ae
        hNS ht₀ hE hTail t j
    ] with ξ hξ
    simpa [h3SelectedRawFourierFourthRadialWeight] using hξ

  have hF5s :
      ((F5s : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ =>
        ((‖ξ‖ ^ 5 : ℝ) : ℂ) * Ns ξ) := by
    dsimp only [F5s, Ns, W, U₀]
    filter_upwards [
      h3PreterminalSelectedVelocityFifthRadialFourierL2_ae
        hNS ht₀ hE hTail s j
    ] with ξ hξ
    simpa [h3SelectedRawFourierFifthRadialWeight] using hξ

  have hF5t :
      ((F5t : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ =>
        ((‖ξ‖ ^ 5 : ℝ) : ℂ) * Nt ξ) := by
    dsimp only [F5t, Nt, W, U₀]
    filter_upwards [
      h3PreterminalSelectedVelocityFifthRadialFourierL2_ae
        hNS ht₀ hE hTail t j
    ] with ξ hξ
    simpa [h3SelectedRawFourierFifthRadialWeight] using hξ

  have hLeftInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖((‖ξ‖ ^ 4 : ℝ) : ℂ) *
              (Ns ξ - Nt ξ)‖ ^ 2)
        volume := by
    have hRaw :=
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        F4s F4t
    refine hRaw.congr ?_
    filter_upwards [hF4s, hF4t] with ξ hsξ htξ
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

  have hFifthSInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) * Ns ξ‖ ^ 2)
        volume := by
    have hRaw :=
      (MeasureTheory.Lp.memLp F5s).norm.integrable_sq
    refine hRaw.congr ?_
    filter_upwards [hF5s] with ξ hξ
    rw [hξ]

  have hFifthTInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) * Nt ξ‖ ^ 2)
        volume := by
    have hRaw :=
      (MeasureTheory.Lp.memLp F5t).norm.integrable_sq
    refine hRaw.congr ?_
    filter_upwards [hF5t] with ξ hξ
    rw [hξ]

  let major : H3FourierPoint3 → ℝ :=
    fun ξ =>
      2 * (R ^ 4) ^ 2 * ‖Ns ξ - Nt ξ‖ ^ 2
        +
      4 * (R⁻¹) ^ 2 *
        (‖((‖ξ‖ ^ 5 : ℝ) : ℂ) * Ns ξ‖ ^ 2
          +
         ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) * Nt ξ‖ ^ 2)

  have hMajorInt :
      Integrable major volume := by
    dsimp only [major]
    exact
      (hLowInt.const_mul (2 * (R ^ 4) ^ 2)).add
        ((hFifthSInt.add hFifthTInt).const_mul
          (4 * (R⁻¹) ^ 2))

  have hInt :
      (∫ ξ : H3FourierPoint3,
          ‖((‖ξ‖ ^ 4 : ℝ) : ℂ) *
              (Ns ξ - Nt ξ)‖ ^ 2)
        ≤
      ∫ ξ : H3FourierPoint3, major ξ := by
    apply integral_mono hLeftInt hMajorInt
    intro ξ
    exact fourthRadialDifference_sq_le hR ξ (Ns ξ) (Nt ξ)

  have hLeftEq :
      ‖F4s - F4t‖ ^ 2
        =
      ∫ ξ : H3FourierPoint3,
        ‖((‖ξ‖ ^ 4 : ℝ) : ℂ) *
            (Ns ξ - Nt ξ)‖ ^ 2 := by
    rw [
      h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq
    ]
    apply integral_congr_ae
    filter_upwards [hF4s, hF4t] with ξ hsξ htξ
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

  have hFifthSEq :
      ‖F5s‖ ^ 2
        =
      ∫ ξ : H3FourierPoint3,
        ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) * Ns ξ‖ ^ 2 := by
    rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [hF5s] with ξ hξ
    rw [hξ]

  have hFifthTEq :
      ‖F5t‖ ^ 2
        =
      ∫ ξ : H3FourierPoint3,
        ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) * Nt ξ‖ ^ 2 := by
    rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [hF5t] with ξ hξ
    rw [hξ]

  have hMajorEq :
      (∫ ξ : H3FourierPoint3, major ξ)
        =
      2 * (R ^ 4) ^ 2 *
          (∫ ξ : H3FourierPoint3,
            ‖Ns ξ - Nt ξ‖ ^ 2)
        +
      4 * (R⁻¹) ^ 2 *
          ((∫ ξ : H3FourierPoint3,
              ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) * Ns ξ‖ ^ 2)
            +
           (∫ ξ : H3FourierPoint3,
              ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) * Nt ξ‖ ^ 2)) := by
    calc
      (∫ ξ : H3FourierPoint3, major ξ)
          =
        (∫ ξ : H3FourierPoint3,
          2 * (R ^ 4) ^ 2 * ‖Ns ξ - Nt ξ‖ ^ 2)
          +
        ∫ ξ : H3FourierPoint3,
          4 * (R⁻¹) ^ 2 *
            (‖((‖ξ‖ ^ 5 : ℝ) : ℂ) * Ns ξ‖ ^ 2
              +
             ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) * Nt ξ‖ ^ 2) := by
        dsimp only [major]
        exact
          integral_add
            (hLowInt.const_mul (2 * (R ^ 4) ^ 2))
            ((hFifthSInt.add hFifthTInt).const_mul
              (4 * (R⁻¹) ^ 2))
      _ =
        2 * (R ^ 4) ^ 2 *
            (∫ ξ : H3FourierPoint3,
              ‖Ns ξ - Nt ξ‖ ^ 2)
          +
        4 * (R⁻¹) ^ 2 *
            (∫ ξ : H3FourierPoint3,
              ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) * Ns ξ‖ ^ 2
                +
              ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) * Nt ξ‖ ^ 2) := by
        rw [integral_const_mul, integral_const_mul]
      _ =
        2 * (R ^ 4) ^ 2 *
            (∫ ξ : H3FourierPoint3,
              ‖Ns ξ - Nt ξ‖ ^ 2)
          +
        4 * (R⁻¹) ^ 2 *
            ((∫ ξ : H3FourierPoint3,
                ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) * Ns ξ‖ ^ 2)
              +
             (∫ ξ : H3FourierPoint3,
                ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) * Nt ξ‖ ^ 2)) := by
        rw [integral_add hFifthSInt hFifthTInt]

  dsimp only [
    F4s, F4t, F0s, F0t, F5s, F5t,
    W, U₀
  ] at hLeftEq hLowEq hFifthSEq hFifthTEq ⊢

  rw [hLeftEq]
  calc
    (∫ ξ : H3FourierPoint3,
        ‖((‖ξ‖ ^ 4 : ℝ) : ℂ) *
            (Ns ξ - Nt ξ)‖ ^ 2)
        ≤
      ∫ ξ : H3FourierPoint3, major ξ :=
      hInt
    _ =
      2 * (R ^ 4) ^ 2 *
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
        (‖h3PreterminalSelectedVelocityFifthRadialFourierL2
              hNS ht₀ hE hTail s j‖ ^ 2
          +
         ‖h3PreterminalSelectedVelocityFifthRadialFourierL2
              hNS ht₀ hE hTail t j‖ ^ 2) := by
      rw [
        hMajorEq,
        ← hLowEq,
        ← hFifthSEq,
        ← hFifthTEq
      ]

end

end Euclidean
end Bridge
end PrimeTensor
