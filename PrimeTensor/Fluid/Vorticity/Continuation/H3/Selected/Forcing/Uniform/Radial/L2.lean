import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Forcing.Fourier.Linf
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.Third.Variation.Zero.Envelope
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.Moment.Third.Seed

/-!
# Uniform fourth/fifth radial Fourier L² bounds for selected forcing

The previous checkpoint supplied a frequency-independent pointwise ceiling for
the unheated selected nonlinear forcing.  The all-orders moment induction also
supplies, on every positive compact source-time slab, one uniform weighted
`L¹` forcing mass at every finite order.

These two estimates combine by the elementary square bound

    (|ξ|^m |N_s(ξ)|)^2
      <= ‖N_s‖_∞ |ξ|^(2m) |N_s(ξ)|.

For the two orders needed by the terminal Duhamel frontier:

* a state moment slab at order `9` supplies a forcing moment `8`, hence
  uniform radial-fourth Fourier `L²`;
* a state moment slab at order `11` supplies a forcing moment `10`, hence
  uniform radial-fifth Fourier `L²`.

The result is quantitative: for every positive selected terminal time `q`
there are finite constants `B4,B5`, independent of `s ∈ [q/2,q]` and of the
output coordinate, which bound the corresponding squared Fourier integrals.

The only step left above this file is temporal measurability / Bochner
integrability of the quotient-safe weighted source-state path.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedForcingUniformRadialL2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Normalize the Young L∞ factors to actual L² norms -/

/--
The explicit half-power square integral of the canonical raw Fourier `L²`
package is exactly its `L²` norm.
-/
private theorem h3SpectralScalarRawFourier_integral_norm_sq_rpow_half_eq_norm
    (G : H3SpectralScalarState) :
    (∫ ξ : H3FourierPoint3,
        ‖h3SpectralScalarRawFourier G ξ‖ ^ (2 : ℝ))
      ^ ((1 : ℝ) / 2)
      =
    ‖h3SpectralScalarRawFourierL2 G‖ := by

  have hRep :=
    h3SpectralScalarRawFourierL2_ae G

  calc
    (∫ ξ : H3FourierPoint3,
        ‖h3SpectralScalarRawFourier G ξ‖ ^ (2 : ℝ))
      ^ ((1 : ℝ) / 2)
        =
      (∫ ξ : H3FourierPoint3,
          ‖((h3SpectralScalarRawFourierL2 G :
              H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖ ^ (2 : ℝ))
        ^ ((1 : ℝ) / 2) := by
          congr 1
          apply integral_congr_ae
          filter_upwards [hRep] with ξ hξ
          rw [hξ]
    _ =
      ‖h3SpectralScalarRawFourierL2 G‖ :=
      h3SpectralScalarState_integral_norm_sq_rpow_half_eq_norm
        (h3SpectralScalarRawFourierL2 G)

/-- The first explicit Young `L∞` factor is exactly raw-`L²` times weighted-`L²`. -/
private theorem h3FirstYoungMajorantLinfBound_eq_norms
    (F G : H3SpectralScalarState) :
    h3FirstYoungMajorantLinfBound F G
      =
    ‖h3SpectralScalarRawFourierL2 G‖ * ‖F‖ := by
  unfold h3FirstYoungMajorantLinfBound
  rw [
    h3SpectralScalarRawFourier_integral_norm_sq_rpow_half_eq_norm,
    h3SpectralScalarState_integral_norm_sq_rpow_half_eq_norm
  ]

/-- The second explicit Young `L∞` factor is exactly raw-`L²` times weighted-`L²`. -/
private theorem h3SecondYoungMajorantLinfBound_eq_norms
    (F G : H3SpectralScalarState) :
    h3SecondYoungMajorantLinfBound F G
      =
    ‖h3SpectralScalarRawFourierL2 F‖ * ‖G‖ := by
  unfold h3SecondYoungMajorantLinfBound
  rw [
    h3SpectralScalarRawFourier_integral_norm_sq_rpow_half_eq_norm,
    h3SpectralScalarState_integral_norm_sq_rpow_half_eq_norm
  ]

/--
The weighted raw product-convolution `L∞` ceiling is bounded purely by the two
native H³ norms.
-/
theorem h3WeightedRawProductConvolutionLinfBound_le_norms
    (F G : H3SpectralScalarState) :
    h3WeightedRawProductConvolutionLinfBound F G
      ≤
    16 * ‖F‖ * ‖G‖ := by

  rw [
    h3WeightedRawProductConvolutionLinfBound,
    h3FirstYoungMajorantLinfBound_eq_norms,
    h3SecondYoungMajorantLinfBound_eq_norms
  ]

  have hRawF :=
    norm_h3SpectralScalarRawFourierL2_le F

  have hRawG :=
    norm_h3SpectralScalarRawFourierL2_le G

  have hFirst :
      ‖h3SpectralScalarRawFourierL2 G‖ * ‖F‖
        ≤
      ‖G‖ * ‖F‖ :=
    mul_le_mul_of_nonneg_right hRawG (norm_nonneg F)

  have hSecond :
      ‖h3SpectralScalarRawFourierL2 F‖ * ‖G‖
        ≤
      ‖F‖ * ‖G‖ :=
    mul_le_mul_of_nonneg_right hRawF (norm_nonneg G)

  calc
    8 *
        (‖h3SpectralScalarRawFourierL2 G‖ * ‖F‖
          +
         ‖h3SpectralScalarRawFourierL2 F‖ * ‖G‖)
        ≤
      8 * (‖G‖ * ‖F‖ + ‖F‖ * ‖G‖) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hFirst hSecond)
        (by norm_num)
    _ =
      16 * ‖F‖ * ‖G‖ := by
      ring

/-! ## One slab-wide Fourier L∞ forcing ceiling -/

/--
A coarse but explicit selected forcing Fourier `L∞` envelope.  It keeps the
finite coordinate sums visible so no cardinality normalization is required.
-/
noncomputable def h3SelectedForcingFourierLinfEnvelope
    (A : ℝ) : ℝ :=
  ∑ _k : Fin 3,
    2 *
      ∑ _j : Fin 3,
        (2 * Real.pi) *
          (16 * (2 * A) * (2 * A))

theorem h3SelectedForcingFourierLinfEnvelope_nonneg
    {A : ℝ}
    (hA : 0 ≤ A) :
    0 ≤ h3SelectedForcingFourierLinfEnvelope A := by
  unfold h3SelectedForcingFourierLinfEnvelope
  exact
    Finset.sum_nonneg fun _k _ =>
      mul_nonneg
        (by norm_num)
        (Finset.sum_nonneg fun _j _ =>
          mul_nonneg
            (by positivity)
            (mul_nonneg
              (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hA))
              (mul_nonneg (by norm_num) hA)))

/--
The state-dependent forcing `L∞` bound is dominated by one numerical envelope
along the globally `2A`-bounded selected restart extension.
-/
theorem h3RawFinLerayOuterProductDivergenceLinfBound_selectedRestart_le
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3RawFinLerayOuterProductDivergenceLinfBound
        (W s) (W s)
      ≤
    h3SelectedForcingFourierLinfEnvelope A := by

  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hW :
      ‖W s‖ ≤ 2 * A := by
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        hν U₀ hA hU₀ s

  have hTwoA :
      0 ≤ 2 * A := by
    positivity

  have hCoord :
      ∀ j : Fin 3, ‖W s j‖ ≤ 2 * A := by
    intro j
    exact
      (h3SpectralVelocity_coordinate_norm_le (W s) j).trans hW

  unfold
    h3RawFinLerayOuterProductDivergenceLinfBound
    h3RawFinOuterProductDivergenceLinfBound
    h3FourierDerivativeRawProductConvolutionLinfBound
    h3SelectedForcingFourierLinfEnvelope

  apply Finset.sum_le_sum
  intro k hk

  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro j hj

    apply mul_le_mul_of_nonneg_left
    · have hProduct :
          ‖W s k‖ * ‖W s j‖
            ≤
          (2 * A) * (2 * A) :=
        mul_le_mul
          (hCoord k)
          (hCoord j)
          (norm_nonneg _)
          hTwoA

      have hScaled :
          16 * ‖W s k‖ * ‖W s j‖
            ≤
          16 * (2 * A) * (2 * A) := by
        simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_left
            hProduct
            (by norm_num : (0 : ℝ) ≤ 16))

      exact
        (h3WeightedRawProductConvolutionLinfBound_le_norms
          (W s k) (W s j)).trans
          hScaled
    · positivity
  · norm_num

/--
Every selected nonlinear forcing coordinate is bounded uniformly in both
source time and Fourier frequency by the same slab-independent numerical
constant.
-/
theorem norm_h3RawFinLerayOuterProductDivergence_selectedRestart_le_uniformLinf
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖h3RawFinLerayOuterProductDivergence
        (W s) (W s) i ξ‖
      ≤
    h3SelectedForcingFourierLinfEnvelope A := by

  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  exact
    (norm_h3RawFinLerayOuterProductDivergence_le_linfBound
      (W s) (W s) i ξ).trans
      (h3RawFinLerayOuterProductDivergenceLinfBound_selectedRestart_le
        hν U₀ hA hU₀)

/-! ## Generic L∞ × weighted-L¹ -> weighted-L² square estimate -/

/--
A frequency-independent pointwise ceiling plus a doubled weighted `L¹` moment
gives an order-`m` weighted Fourier `L²` field.
-/
private theorem radialWeight_memLp2_of_linf_of_doubleMoment
    (m : ℕ)
    (N : H3FourierPoint3 → ℂ)
    (hN2 :
      MemLp N 2 (volume : Measure H3FourierPoint3))
    (L : ℝ)
    (hL0 : 0 ≤ L)
    (hLinf : ∀ ξ, ‖N ξ‖ ≤ L)
    (hMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ (2 * m) * ‖N ξ‖)
        (volume : Measure H3FourierPoint3)) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) * N ξ)
      2
      (volume : Measure H3FourierPoint3) := by

  have hMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ m : ℝ) : ℂ) * N ξ)
        (volume : Measure H3FourierPoint3) := by
    exact
      (Complex.continuous_ofReal.comp
        (continuous_norm.pow m)).aestronglyMeasurable.mul
        hN2.1

  rw [memLp_two_iff_integrable_sq_norm hMeas]

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          L * (‖ξ‖ ^ (2 * m) * ‖N ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMoment.const_mul L

  refine
    hMajor.mono'
      ((hMeas.norm.aemeasurable.pow_const 2).aestronglyMeasurable)
      ?_

  filter_upwards with ξ

  have hr0 :
      0 ≤ ‖ξ‖ := norm_nonneg ξ

  have hrm0 :
      0 ≤ ‖ξ‖ ^ m :=
    pow_nonneg hr0 m

  have hN0 :
      0 ≤ ‖N ξ‖ :=
    norm_nonneg _

  have hPow :
      (‖ξ‖ ^ m) ^ 2 = ‖ξ‖ ^ (2 * m) := by
    rw [pow_two, ← pow_add]
    congr 1
    omega

  rw [
    Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _),
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hrm0,
    mul_pow,
    hPow
  ]

  calc
    ‖ξ‖ ^ (2 * m) * ‖N ξ‖ ^ 2
        =
      ‖ξ‖ ^ (2 * m) * (‖N ξ‖ * ‖N ξ‖) := by
      rw [pow_two]
    _ ≤
      ‖ξ‖ ^ (2 * m) * (L * ‖N ξ‖) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (hLinf ξ)
            hN0)
          (pow_nonneg hr0 (2 * m))
    _ =
      L * (‖ξ‖ ^ (2 * m) * ‖N ξ‖) := by
      ring

/--
The same hypotheses give an explicit bound on the squared weighted `L²`
integral.
-/
private theorem integral_sq_radialWeight_le_linf_mul_momentMass
    (m : ℕ)
    (N : H3FourierPoint3 → ℂ)
    (hN2 :
      MemLp N 2 (volume : Measure H3FourierPoint3))
    (L M : ℝ)
    (hL0 : 0 ≤ L)
    (hM0 : 0 ≤ M)
    (hLinf : ∀ ξ, ‖N ξ‖ ≤ L)
    (hMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ (2 * m) * ‖N ξ‖)
        (volume : Measure H3FourierPoint3))
    (hMass :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ (2 * m) * ‖N ξ‖)
        ≤ M) :
    (∫ ξ : H3FourierPoint3,
        ‖((‖ξ‖ ^ m : ℝ) : ℂ) * N ξ‖ ^ 2)
      ≤
    L * M := by

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          L * (‖ξ‖ ^ (2 * m) * ‖N ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMoment.const_mul L

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖((‖ξ‖ ^ m : ℝ) : ℂ) * N ξ‖ ^ 2
          ≤
        L * (‖ξ‖ ^ (2 * m) * ‖N ξ‖) := by
    intro ξ

    have hr0 :
        0 ≤ ‖ξ‖ := norm_nonneg ξ

    have hrm0 :
        0 ≤ ‖ξ‖ ^ m :=
      pow_nonneg hr0 m

    have hN0 :
        0 ≤ ‖N ξ‖ :=
      norm_nonneg _

    have hPow :
        (‖ξ‖ ^ m) ^ 2 = ‖ξ‖ ^ (2 * m) := by
      rw [pow_two, ← pow_add]
      congr 1
      omega

    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg hrm0,
      mul_pow,
      hPow
    ]

    calc
      ‖ξ‖ ^ (2 * m) * ‖N ξ‖ ^ 2
          =
        ‖ξ‖ ^ (2 * m) * (‖N ξ‖ * ‖N ξ‖) := by
        rw [pow_two]
      _ ≤
        ‖ξ‖ ^ (2 * m) * (L * ‖N ξ‖) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              (hLinf ξ)
              hN0)
            (pow_nonneg hr0 (2 * m))
      _ =
        L * (‖ξ‖ ^ (2 * m) * ‖N ξ‖) := by
        ring

  have hLeftMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖((‖ξ‖ ^ m : ℝ) : ℂ) * N ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) := by
    exact
      (((Complex.continuous_ofReal.comp
          (continuous_norm.pow m)).aestronglyMeasurable.mul
          hN2.1).norm.aemeasurable.pow_const 2).aestronglyMeasurable

  have hPointNorm :
      ∀ ξ : H3FourierPoint3,
        ‖‖((‖ξ‖ ^ m : ℝ) : ℂ) * N ξ‖ ^ 2‖
          ≤
        L * (‖ξ‖ ^ (2 * m) * ‖N ξ‖) := by
    intro ξ
    rw [
      Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)
    ]
    exact hPoint ξ

  have hLeftInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖((‖ξ‖ ^ m : ℝ) : ℂ) * N ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) :=
    hMajor.mono' hLeftMeas
      (Filter.Eventually.of_forall hPointNorm)

  calc
    (∫ ξ : H3FourierPoint3,
        ‖((‖ξ‖ ^ m : ℝ) : ℂ) * N ξ‖ ^ 2)
        ≤
      ∫ ξ : H3FourierPoint3,
        L * (‖ξ‖ ^ (2 * m) * ‖N ξ‖) :=
      integral_mono
        hLeftInt
        hMajor
        hPoint
    _ =
      L *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ (2 * m) * ‖N ξ‖) := by
      rw [integral_const_mul]
    _ ≤
      L * M :=
      mul_le_mul_of_nonneg_left hMass hL0

/-! ## Uniform selected fourth/fifth forcing bounds on a terminal half -/

/--
On every positive selected terminal half `[q/2,q]`, the unheated nonlinear
forcing has fourth radial Fourier `L²` uniformly in source time and output
coordinate.
-/
theorem exists_selectedRestart_forcing_fourth_radialL2_uniform
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A) :
    ∃ B4 : ℝ,
      0 ≤ B4 ∧
      ∀ s ∈ Set.Icc (q / 2) q, ∀ i : Fin 3,
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        MemLp
          (fun ξ : H3FourierPoint3 =>
            ((‖ξ‖ ^ 4 : ℝ) : ℂ) *
              h3RawFinLerayOuterProductDivergence
                (W s) (W s) i ξ)
          2
          (volume : Measure H3FourierPoint3)
        ∧
        (∫ ξ : H3FourierPoint3,
            ‖((‖ξ‖ ^ 4 : ℝ) : ℂ) *
              h3RawFinLerayOuterProductDivergence
                (W s) (W s) i ξ‖ ^ 2)
          ≤ B4 := by

  have hHalf :
      0 < q / 2 := by
    positivity

  have hHalfQ :
      q / 2 ≤ q := by
    linarith

  obtain ⟨BState, BDuhamel, B0, hSlab⟩ :=
    h3SelectedMomentSlab_nat_ge_three
      (a := q / 2)
      (t := q)
      9
      (by norm_num)
      hν U₀ hA hU₀
      hHalf hHalfQ hqR

  unfold H3SelectedMomentSlab at hSlab
  rcases hSlab with ⟨hBS0, _hBD0, hB00, _hData⟩

  let L : ℝ :=
    h3SelectedForcingFourierLinfEnvelope A

  let M : ℝ :=
    h3SelectedMomentSlabForcingEnvelope
      (9 : ℝ) BState B0

  let B4 : ℝ := L * M

  have hL0 : 0 ≤ L := by
    dsimp only [L]
    exact
      h3SelectedForcingFourierLinfEnvelope_nonneg
        hA.le

  have hM0 : 0 ≤ M := by
    dsimp only [M]
    exact
      h3SelectedMomentSlabForcingEnvelope_nonneg
        hBS0 hB00

  refine ⟨B4, mul_nonneg hL0 hM0, ?_⟩

  intro s hs i
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W s) (W s) i

  have hN2 :
      MemLp N 2 (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact
      h3RawFinLerayOuterProductDivergence_memLp2
        (W s) (W s) i

  have hLinf :
      ∀ ξ : H3FourierPoint3, ‖N ξ‖ ≤ L := by
    intro ξ
    dsimp only [N, L, W]
    exact
      norm_h3RawFinLerayOuterProductDivergence_selectedRestart_le_uniformLinf
        hν U₀ hA hU₀ i ξ

  have hMomentGeneric :=
    h3RawFinLerayOuterProductDivergence_selectedMomentSlab_subOneMoment_integrable
      (p := (9 : ℝ))
      (by norm_num)
      hν U₀ hA hU₀
      (by
        unfold H3SelectedMomentSlab
        exact ⟨hBS0, _hBD0, hB00, _hData⟩)
      s hs i

  have hWeight8 :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (8 : ℝ) ξ = ‖ξ‖ ^ 8 := by
    intro ξ
    have h := h3FourierMomentWeight_natCast 8 ξ
    norm_num at h ⊢
    exact h

  have hMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 8 * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    simpa only [
      show (9 : ℝ) - 1 = 8 by norm_num,
      hWeight8
    ] using hMomentGeneric

  have hMassGeneric :=
    h3RawFinLerayOuterProductDivergence_selectedMomentSlab_subOneMass_le
      (p := (9 : ℝ))
      (by norm_num)
      hν U₀ hA hU₀
      (by
        unfold H3SelectedMomentSlab
        exact ⟨hBS0, _hBD0, hB00, _hData⟩)
      s hs i

  have hMass :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 8 * ‖N ξ‖)
        ≤ M := by
    dsimp only [N, W, M]
    simpa only [
      show (9 : ℝ) - 1 = 8 by norm_num,
      hWeight8,
      h3RawFinLerayOuterProductDivergenceMomentMass
    ] using hMassGeneric

  constructor

  · exact
      radialWeight_memLp2_of_linf_of_doubleMoment
        4 N hN2 L hL0 hLinf
        (by
          simpa only [show 2 * 4 = 8 by norm_num] using hMoment)

  · dsimp only [B4]
    exact
      integral_sq_radialWeight_le_linf_mul_momentMass
        4 N hN2 L M hL0 hM0 hLinf
        (by
          simpa only [show 2 * 4 = 8 by norm_num] using hMoment)
        (by
          simpa only [show 2 * 4 = 8 by norm_num] using hMass)

/--
The analogous slab-wide fifth radial Fourier `L²` bound is generated by the
order-eleven state moment slab, whose forcing moment is order ten.
-/
theorem exists_selectedRestart_forcing_fifth_radialL2_uniform
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A) :
    ∃ B5 : ℝ,
      0 ≤ B5 ∧
      ∀ s ∈ Set.Icc (q / 2) q, ∀ i : Fin 3,
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        MemLp
          (fun ξ : H3FourierPoint3 =>
            ((‖ξ‖ ^ 5 : ℝ) : ℂ) *
              h3RawFinLerayOuterProductDivergence
                (W s) (W s) i ξ)
          2
          (volume : Measure H3FourierPoint3)
        ∧
        (∫ ξ : H3FourierPoint3,
            ‖((‖ξ‖ ^ 5 : ℝ) : ℂ) *
              h3RawFinLerayOuterProductDivergence
                (W s) (W s) i ξ‖ ^ 2)
          ≤ B5 := by

  have hHalf :
      0 < q / 2 := by
    positivity

  have hHalfQ :
      q / 2 ≤ q := by
    linarith

  obtain ⟨BState, BDuhamel, B0, hSlab⟩ :=
    h3SelectedMomentSlab_nat_ge_three
      (a := q / 2)
      (t := q)
      11
      (by norm_num)
      hν U₀ hA hU₀
      hHalf hHalfQ hqR

  unfold H3SelectedMomentSlab at hSlab
  rcases hSlab with ⟨hBS0, _hBD0, hB00, _hData⟩

  let L : ℝ :=
    h3SelectedForcingFourierLinfEnvelope A

  let M : ℝ :=
    h3SelectedMomentSlabForcingEnvelope
      (11 : ℝ) BState B0

  let B5 : ℝ := L * M

  have hL0 : 0 ≤ L := by
    dsimp only [L]
    exact
      h3SelectedForcingFourierLinfEnvelope_nonneg
        hA.le

  have hM0 : 0 ≤ M := by
    dsimp only [M]
    exact
      h3SelectedMomentSlabForcingEnvelope_nonneg
        hBS0 hB00

  refine ⟨B5, mul_nonneg hL0 hM0, ?_⟩

  intro s hs i
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W s) (W s) i

  have hN2 :
      MemLp N 2 (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact
      h3RawFinLerayOuterProductDivergence_memLp2
        (W s) (W s) i

  have hLinf :
      ∀ ξ : H3FourierPoint3, ‖N ξ‖ ≤ L := by
    intro ξ
    dsimp only [N, L, W]
    exact
      norm_h3RawFinLerayOuterProductDivergence_selectedRestart_le_uniformLinf
        hν U₀ hA hU₀ i ξ

  have hMomentGeneric :=
    h3RawFinLerayOuterProductDivergence_selectedMomentSlab_subOneMoment_integrable
      (p := (11 : ℝ))
      (by norm_num)
      hν U₀ hA hU₀
      (by
        unfold H3SelectedMomentSlab
        exact ⟨hBS0, _hBD0, hB00, _hData⟩)
      s hs i

  have hWeight10 :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (10 : ℝ) ξ = ‖ξ‖ ^ 10 := by
    intro ξ
    have h := h3FourierMomentWeight_natCast 10 ξ
    norm_num at h ⊢
    exact h

  have hMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 10 * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    simpa only [
      show (11 : ℝ) - 1 = 10 by norm_num,
      hWeight10
    ] using hMomentGeneric

  have hMassGeneric :=
    h3RawFinLerayOuterProductDivergence_selectedMomentSlab_subOneMass_le
      (p := (11 : ℝ))
      (by norm_num)
      hν U₀ hA hU₀
      (by
        unfold H3SelectedMomentSlab
        exact ⟨hBS0, _hBD0, hB00, _hData⟩)
      s hs i

  have hMass :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 10 * ‖N ξ‖)
        ≤ M := by
    dsimp only [N, W, M]
    simpa only [
      show (11 : ℝ) - 1 = 10 by norm_num,
      hWeight10,
      h3RawFinLerayOuterProductDivergenceMomentMass
    ] using hMassGeneric

  constructor

  · exact
      radialWeight_memLp2_of_linf_of_doubleMoment
        5 N hN2 L hL0 hLinf
        (by
          simpa only [show 2 * 5 = 10 by norm_num] using hMoment)

  · dsimp only [B5]
    exact
      integral_sq_radialWeight_le_linf_mul_momentMass
        5 N hN2 L M hL0 hM0 hLinf
        (by
          simpa only [show 2 * 5 = 10 by norm_num] using hMoment)
        (by
          simpa only [show 2 * 5 = 10 by norm_num] using hMass)

end

end Euclidean
end Bridge
end PrimeTensor
