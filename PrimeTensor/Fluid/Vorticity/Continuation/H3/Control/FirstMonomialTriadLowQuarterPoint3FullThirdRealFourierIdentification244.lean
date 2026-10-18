import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdGradientFourierBridge244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadPhysicalShell
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SignReversal
import Mathlib.Tactic

/-!
# Full static third-order Schwartz transport is the real part of a Fourier integral

For every three-component REAL Schwartz field, this identifies the complete
3+3+1 physical gradient channel with the real part of the Fourier expression
proved in the preceding gradient bridge.  The original five ordered axis sums,
four gradient terms, energy pairing coefficient 2, and the Fourier phase
(2*pi*i)^7 are retained.  Combining it with the existing 3+2+2 interpolation
identity produces an exact integral representation of G_3 + 3 M.

This does not infer integrated noncancellation from the previously formalized
finite six-permutation coefficient, and does not assert a Navier--Stokes path.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv FourierTransform

noncomputable section
set_option maxHeartbeats 800000

private abbrev V3 := H3FourierPoint3
private abbrev A3 := PrimeTensor.Axis Depth.three

noncomputable local instance axisFintypeFullThirdRealFourier244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Embedding a Schwartz 3+3+1 physical triple product into complex scalars
commutes with its integral, by absolute integrability of Schwartz products. -/
private theorem fullThird_real_triple_complexify244
    (F G H : SchwartzMap V3 ℝ) :
    (∫ x : V3, ((h3SchwartzComplexify F) x *
      (h3SchwartzComplexify G) x) * (h3SchwartzComplexify H) x) =
      ((∫ x : V3, F x * (G x * H x) : ℝ) : ℂ) := by
  have hi : Integrable (fun x : V3 => F x * (G x * H x)) :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) F
      (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) G H)).integrable
  calc
    _ = ∫ x : V3, ((F x * (G x * H x) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [h3SchwartzComplexify_apply]
      push_cast
      ring
    _ = _ := Complex.ofRealCLM.integral_comp_comm hi

/-- The genuine seven-derivative REAL gradient integral is twice the real part
of the corresponding complex Schwartz integral, for arbitrary 3+3+1 slots. -/
theorem thirdGradient_realSlot_eq_complexRe244
    (f g h : SchwartzMap V3 ℝ)
    (a b c d e k v : V3) :
    2 * (∫ x : V3,
        ((∂_{a} (∂_{b} (∂_{c} f))) x) *
          (((∂_{d} (∂_{e} (∂_{k} g))) x) * ((∂_{v} h) x))) =
      2 * (∫ x : V3,
        (((∂_{a} (∂_{b} (∂_{c} (h3SchwartzComplexify f)))) x) *
          ((∂_{d} (∂_{e} (∂_{k} (h3SchwartzComplexify g)))) x)) *
          ((∂_{v} (h3SchwartzComplexify h)) x)).re := by
  have h := fullThird_real_triple_complexify244
    (∂_{a} (∂_{b} (∂_{c} f)))
    (∂_{d} (∂_{e} (∂_{k} g))) (∂_{v} h)
  simp only [h3TriadComplexify_lineDeriv] at h ⊢
  rw [h]
  rfl

/-- The actual four-term real 3+3+1 physical gradient block equals the real
part of the complex block. No frequency approximation or divergence condition. -/
theorem fullSchwartzGradientAxis_eq_complexRe244
    (f : A3 → SchwartzMap V3 ℝ) (j i k l r : A3) :
    fullSchwartzGradientAxis244 f j i k l r =
      (thirdGradientSchwartzAxisComplex244
        (fun a => h3SchwartzComplexify (f a)) j i k l r).re := by
  unfold fullSchwartzGradientAxis244 fullGradientTriple244
  unfold thirdGradientSchwartzAxisComplex244
  -- Numerals `2 : ℂ` are not syntactically `Complex.ofReal` terms.
  -- Evaluate their real/imaginary projections explicitly before ring.
  have hTwoRe : (2 : ℂ).re = 2 := rfl
  have hTwoIm : (2 : ℂ).im = 0 := rfl
  simp only [Complex.add_re, Complex.mul_re, hTwoRe, hTwoIm,
    zero_mul, sub_zero]
  rw [thirdGradient_realSlot_eq_complexRe244 (f j) (f r) (f j)
      (h3FourierAxisDirection i) (h3FourierAxisDirection k)
      (h3FourierAxisDirection l) (h3FourierAxisDirection i)
      (h3FourierAxisDirection k) (h3FourierAxisDirection l)
      (h3FourierAxisDirection r),
    thirdGradient_realSlot_eq_complexRe244 (f j) (f j) (f r)
      (h3FourierAxisDirection i) (h3FourierAxisDirection k)
      (h3FourierAxisDirection l) (h3FourierAxisDirection i)
      (h3FourierAxisDirection k) (h3FourierAxisDirection r)
      (h3FourierAxisDirection l),
    thirdGradient_realSlot_eq_complexRe244 (f j) (f j) (f r)
      (h3FourierAxisDirection i) (h3FourierAxisDirection k)
      (h3FourierAxisDirection l) (h3FourierAxisDirection i)
      (h3FourierAxisDirection r) (h3FourierAxisDirection l)
      (h3FourierAxisDirection k),
    thirdGradient_realSlot_eq_complexRe244 (f j) (f j) (f r)
      (h3FourierAxisDirection i) (h3FourierAxisDirection k)
      (h3FourierAxisDirection l) (h3FourierAxisDirection r)
      (h3FourierAxisDirection k) (h3FourierAxisDirection l)
      (h3FourierAxisDirection i)]
  -- The four slot identities close the goal directly.

/-- Summing the full five original physical indices commutes with taking the
real part of the actual complex 3+3+1 gradient aggregate. -/
theorem fullSchwartzGradientTransport_eq_complexRe244
    (f : A3 → SchwartzMap V3 ℝ) :
    fullSchwartzGradientTransport244 f =
      (thirdGradientSchwartzTotalComplex244
        (fun j => h3SchwartzComplexify (f j))).re := by
  unfold fullSchwartzGradientTransport244 thirdGradientSchwartzTotalComplex244
  change (∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3,
      fullSchwartzGradientAxis244 f j i k l r) =
    Complex.reCLM (∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3,
      thirdGradientSchwartzAxisComplex244
        (fun a => h3SchwartzComplexify (f a)) j i k l r)
  simp only [map_sum, Complex.reCLM_apply]
  simp_rw [fullSchwartzGradientAxis_eq_complexRe244]

/-- The Fourier transform identity for the COMPLETE REAL physical gradient,
including the exact physical factor 2 and all four transport pieces. -/
theorem fullSchwartzGradientTransport_eq_fourierRe244
    (f : A3 → SchwartzMap V3 ℝ) :
    fullSchwartzGradientTransport244 f =
      (thirdGradientFourierTotalComplex244
        (fun j => h3SchwartzComplexify (f j))).re := by
  rw [fullSchwartzGradientTransport_eq_complexRe244,
    thirdGradientSchwartzTotalComplex_eq_fourier244]

/-- The exact complex-frequency coefficient for the entire STATIC H³ third
commutator. The interpolation coefficient 6 = 3 times the physical factor 2. -/
noncomputable def fullThirdSchwartzFourierCoefficient244
    (f : A3 → SchwartzMap V3 ℝ) : ℂ :=
  let u : A3 → SchwartzMap V3 ℂ := fun j => h3SchwartzComplexify (f j)
  thirdGradientFourierTotalComplex244 u +
    6 * (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
      ∫ z : V3 × V3, h3SchwartzTriadKernel u z ∂volume.prod volume

/-- **Exact full physical static transport identity** for EVERY real Schwartz
three-component velocity. No PDE, solenoidality or packet width assumption.
The final nonzero-physical-packet assertion is deliberately NOT assumed. -/
theorem fullSchwartzThirdCommutator_eq_fullFourierRe244
    (f : A3 → SchwartzMap V3 ℝ) :
    fullSchwartzThirdCommutator244 f =
      (fullThirdSchwartzFourierCoefficient244 f).re := by
  unfold fullSchwartzThirdCommutator244 fullThirdSchwartzFourierCoefficient244
  rw [fullSchwartzGradientTransport_eq_fourierRe244,
    lowNormalRealSchwartzPoint3Monomial_eq_complex]
  rw [h3SchwartzFirstMonomialAggregate_eq_triad]
  -- Work directly with `Complex.re` as an additive/real-linear map.
  -- Expanding the full seventh-power Fourier phase here needlessly
  -- destroys its common subexpression on the two sides.
  have hReSix (x y : ℂ) :
      x.re + 3 * (2 * y.re) = (x + 6 * y).re := by
    have hSixRe : (6 : ℂ).re = 6 := rfl
    have hSixIm : (6 : ℂ).im = 0 := rfl
    simp only [Complex.add_re, Complex.mul_re, hSixRe, hSixIm,
      zero_mul, sub_zero]
    ring
  simpa only [mul_assoc] using
    (hReSix
      (thirdGradientFourierTotalComplex244
        (fun j => h3SchwartzComplexify (f j)))
      ((2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
        ∫ z : V3 × V3,
          h3SchwartzTriadKernel
            (fun j => h3SchwartzComplexify (f j)) z
          ∂volume.prod volume))

end
end PrimeTensor.FirstMonomialTriad
