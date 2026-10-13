import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadSchwartz
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Product.Convolution

/-!
# The physical Schwartz triple integral and the seven-derivative phase

Use the project's Euclidean Fourier carrier and its existing Schwartz
product-to-convolution theorem. The physical triple product is exactly the
frequency integral on p+q+r=0. For the first D³u (D²u D²u) monomial the
multiplier is (2πi)^7, with no additional Fourier normalization constant.

This file handles a single Schwartz monomial. Transport to the physical
Point3 carrier and identification with the full path aggregate are separate.
-/

namespace PrimeTensor.Bridge.Euclidean

open MeasureTheory
open scoped FourierTransform SchwartzMap LineDeriv

noncomputable section

noncomputable local instance axisFintypeH3TriadFourier (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Absolute convergence of a scalar Schwartz triad on the Euclidean carrier. -/
theorem h3Schwartz_triad_integrable
    (F G H : SchwartzMap H3FourierPoint3 ℂ) :
    Integrable (fun z : H3FourierPoint3 × H3FourierPoint3 =>
      (F z.1 * H z.2) * G (-(z.1 + z.2))) (volume.prod volume) := by
  have hF : Integrable F := F.integrable
  have hH : Integrable H := H.integrable
  have hbound := (hF.norm.mul_prod hH.norm).mul_const (SchwartzMap.seminorm ℝ 0 0 G)
  apply hbound.mono' ?_ (Filter.Eventually.of_forall ?_)
  · exact (((F.continuous.comp continuous_fst).mul
      (H.continuous.comp continuous_snd)).mul
      (G.continuous.comp (continuous_fst.add continuous_snd).neg)).aestronglyMeasurable
  · intro z
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ G _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The bilinear Fourier pairing places the middle frequency at -(p+r).
There is no complex conjugation and no extra normalization factor. -/
theorem h3Schwartz_triple_integral_eq_triad
    (f g h : SchwartzMap H3FourierPoint3 ℂ) :
    (∫ x, (f x * g x) * h x) =
      ∫ z : H3FourierPoint3 × H3FourierPoint3,
        (𝓕 f z.1 * 𝓕 h z.2) * 𝓕 g (-(z.1 + z.2)) ∂volume.prod volume := by
  let hg : SchwartzMap H3FourierPoint3 ℂ :=
    SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) h g
  have hpair := SchwartzMap.integral_fourierInv_mul_eq (𝓕 f) hg
  rw [FourierTransform.fourierInv_fourier_eq] at hpair
  calc
    (∫ x, (f x * g x) * h x) = ∫ x, f x * hg x := by
      apply integral_congr_ae
      filter_upwards with x
      change (f x * g x) * h x = f x * (h x * g x)
      ring
    _ = ∫ p, 𝓕 f p * 𝓕⁻ hg p := hpair
    _ = ∫ p, ∫ r, (𝓕 f p * 𝓕 h r) * 𝓕 g (-(p + r)) := by
      apply integral_congr_ae
      filter_upwards with p
      have hinv : 𝓕⁻ hg p = 𝓕 hg (-p) := rfl
      rw [hinv]
      dsimp only [hg]
      rw [h3Schwartz_fourier_product_apply_eq_convolution,
        SchwartzMap.convolution_apply]
      change 𝓕 f p * (∫ r, 𝓕 h r * 𝓕 g (-p - r)) = _
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with r
      rw [neg_add]
      simp only [sub_eq_add_neg]
      ring
    _ = ∫ z : H3FourierPoint3 × H3FourierPoint3,
        (𝓕 f z.1 * 𝓕 h z.2) * 𝓕 g (-(z.1 + z.2)) ∂volume.prod volume :=
      (integral_prod _ (h3Schwartz_triad_integrable (𝓕 f) (𝓕 g) (𝓕 h))).symm

/-- Pointwise derivative multiplier in the project's Fourier convention. -/
theorem h3Schwartz_fourier_lineDeriv_apply
    (f : SchwartzMap H3FourierPoint3 ℂ) (a p : H3FourierPoint3) :
    𝓕 (∂_{a} f) p =
      (2 * (Real.pi : ℂ) * Complex.I) * (inner ℝ p a : ℂ) * 𝓕 f p := by
  have hg : (fun p : H3FourierPoint3 => inner ℝ p a).HasTemperateGrowth :=
    ((innerSL ℝ).flip a).hasTemperateGrowth
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  simp [SchwartzMap.smulLeftCLM_apply_apply hg, Complex.real_smul,
    smul_eq_mul, mul_assoc]

/-- The frequency polynomial for one first-monomial coordinate slot, before
summing the four derivative indices and the velocity component. -/
def h3FirstMonomialSchwartzKernel
    (f g h : SchwartzMap H3FourierPoint3 ℂ)
    (a b c d : H3FourierPoint3) (z : H3FourierPoint3 × H3FourierPoint3) : ℂ :=
  (((inner ℝ z.1 a : ℂ) * (inner ℝ z.1 b : ℂ) * (inner ℝ z.1 c : ℂ) * 𝓕 f z.1) *
    ((inner ℝ z.2 a : ℂ) * (inner ℝ z.2 d : ℂ) * 𝓕 h z.2)) *
    ((inner ℝ (-(z.1 + z.2)) b : ℂ) * (inner ℝ (-(z.1 + z.2)) c : ℂ) *
      𝓕 g (-(z.1 + z.2)))

/-- Multiplication by the linear frequency functional associated with a direction. -/
def h3Schwartz_frequencyWeight (a : H3FourierPoint3)
    (F : SchwartzMap H3FourierPoint3 ℂ) : SchwartzMap H3FourierPoint3 ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun p : H3FourierPoint3 => inner ℝ p a) F

@[simp] theorem h3Schwartz_frequencyWeight_apply (a p : H3FourierPoint3)
    (F : SchwartzMap H3FourierPoint3 ℂ) :
    h3Schwartz_frequencyWeight a F p = (inner ℝ p a : ℂ) * F p := by
  have hg : (fun p : H3FourierPoint3 => inner ℝ p a).HasTemperateGrowth :=
    ((innerSL ℝ).flip a).hasTemperateGrowth
  simp [h3Schwartz_frequencyWeight, SchwartzMap.smulLeftCLM_apply_apply hg,
    Complex.real_smul]

/-- The polynomial kernel in the physical identity is absolutely integrable. -/
theorem h3FirstMonomialSchwartzKernel_integrable
    (f g h : SchwartzMap H3FourierPoint3 ℂ)
    (a b c d : H3FourierPoint3) :
    Integrable (h3FirstMonomialSchwartzKernel f g h a b c d) (volume.prod volume) := by
  have hi := h3Schwartz_triad_integrable
    (h3Schwartz_frequencyWeight a (h3Schwartz_frequencyWeight b
      (h3Schwartz_frequencyWeight c (𝓕 f))))
    (h3Schwartz_frequencyWeight b (h3Schwartz_frequencyWeight c (𝓕 g)))
    (h3Schwartz_frequencyWeight a (h3Schwartz_frequencyWeight d (𝓕 h)))
  apply hi.congr
  filter_upwards with z
  simp only [h3Schwartz_frequencyWeight_apply, h3FirstMonomialSchwartzKernel]
  ring

/-- Exact physical-to-frequency identity for D³f (D²g D²h).
The seven derivatives contribute exactly (2πi)^7. -/
theorem h3Schwartz_firstMonomial_integral_eq_triad
    (f g h : SchwartzMap H3FourierPoint3 ℂ)
    (a b c d : H3FourierPoint3) :
    (∫ x, (((∂_{a} (∂_{b} (∂_{c} f))) x) * ((∂_{b} (∂_{c} g)) x)) *
      ((∂_{a} (∂_{d} h)) x)) =
    (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
      ∫ z, h3FirstMonomialSchwartzKernel f g h a b c d z ∂volume.prod volume := by
  rw [h3Schwartz_triple_integral_eq_triad]
  calc
    _ = ∫ z : H3FourierPoint3 × H3FourierPoint3,
        (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
          h3FirstMonomialSchwartzKernel f g h a b c d z ∂volume.prod volume := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [h3Schwartz_fourier_lineDeriv_apply]
      unfold h3FirstMonomialSchwartzKernel
      ring
    _ = _ := integral_const_mul _ _

/-- The odd derivative phase is purely imaginary, with negative sign. -/
theorem h3FirstMonomial_fourier_phase :
    (2 * (Real.pi : ℂ) * Complex.I) ^ 7 =
      -(Complex.I * ((2 * Real.pi) ^ 7 : ℝ)) := by
  have hI : Complex.I ^ 7 = -Complex.I := by
    calc
      Complex.I ^ 7 = (Complex.I ^ 2) ^ 3 * Complex.I := by ring
      _ = -Complex.I := by rw [Complex.I_sq]; norm_num
  rw [mul_pow, hI]
  push_cast
  ring

/-- Real-part form with the physical energy pairing's factor two retained.
This is a Schwartz scalar identity on the Euclidean carrier. -/
theorem h3Schwartz_firstMonomial_twice_re_eq_triad_im
    (f g h : SchwartzMap H3FourierPoint3 ℂ)
    (a b c d : H3FourierPoint3) :
    2 * (∫ x, (((∂_{a} (∂_{b} (∂_{c} f))) x) * ((∂_{b} (∂_{c} g)) x)) *
      ((∂_{a} (∂_{d} h)) x)).re =
    2 * (2 * Real.pi) ^ 7 *
      (∫ z, h3FirstMonomialSchwartzKernel f g h a b c d z ∂volume.prod volume).im := by
  rw [h3Schwartz_firstMonomial_integral_eq_triad, h3FirstMonomial_fourier_phase]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

end
end PrimeTensor.Bridge.Euclidean
