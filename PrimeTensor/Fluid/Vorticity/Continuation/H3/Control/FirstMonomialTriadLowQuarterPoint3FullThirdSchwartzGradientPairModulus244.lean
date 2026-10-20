import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzPhysicalFirstJet244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzGradientL2L2Linf244
import Mathlib.Tactic

/-!
# Two-profile H³-compatible modulus for the genuine signed 3–3–1 gradient

The preceding first-jet theorem compares a Schwartz approximation to an
actual preterminal physical velocity. To use it without falsely assuming the
physical H³ velocity is Schwartz, the nonlinear 3–3–1 gradient requires a
TWO-PROFILE, rather than fixed-Schwartz-target, continuity estimate.

For real Schwartz factors, the modulus below comes from the exact integrated
three-product telescoping identity and Cauchy–Schwarz:

  |I(a,b,c) - I(a',b',c')|
   ≤ K ‖a-a'‖₂ ‖b‖₂ + K ‖a'‖₂ ‖b-b'‖₂
     + δ ‖a'‖₂ ‖b'‖₂,

where |c| ≤ K and |c-c'| ≤ δ pointwise. The real three-product integral is
the one used by the actual 243-slot physical gradient channel.

For C¹ spectrally matched Schwartz velocities, K and δ are supplied by the
previously proved weighted H³ first-derivative evaluation bounds. No L⁴
control of a THIRD derivative is invoked; no nonlinear physical equality is
assumed. The remaining work is to pass from this modulus to the complete
finite gradient channel and identify its non-Schwartz physical L² product.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypePairModulus244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Genuine TWO-profile 2–2–infinity estimate for the actual real Schwartz
integral, including zero factors and zero error gauges. This uses neither
L⁴ third derivatives nor a fixed Schwartz target. -/
theorem schwartzTripleIntegral_pair_abs_le_L2L2Linf244
    (a b c a' b' c' : SchwartzMap V3 ℝ)
    (K δ : ℝ)
    (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hc : ∀ x : V3, |c x| ≤ K)
    (hcdiff : ∀ x : V3, |(c - c') x| ≤ δ) :
    |schwartzTripleIntegral244 a b c -
      schwartzTripleIntegral244 a' b' c'| ≤
      K * (schwartzIntegralL2Root244 (a - a') *
        schwartzIntegralL2Root244 b) +
      K * (schwartzIntegralL2Root244 a' *
        schwartzIntegralL2Root244 (b - b')) +
      δ * (schwartzIntegralL2Root244 a' *
        schwartzIntegralL2Root244 b') := by
  have hFirst := schwartzTripleIntegral_abs_le_L2L2Linf244
    (a - a') b c K hK hc
  have hSecond := schwartzTripleIntegral_abs_le_L2L2Linf244
    a' (b - b') c K hK hc
  have hThird := schwartzTripleIntegral_abs_le_L2L2Linf244
    a' b' (c - c') δ hδ hcdiff
  rw [schwartzTripleIntegral_telescoping244]
  calc
    |schwartzTripleIntegral244 (a - a') b c +
      schwartzTripleIntegral244 a' (b - b') c +
      schwartzTripleIntegral244 a' b' (c - c')| ≤
        (|schwartzTripleIntegral244 (a - a') b c| +
          |schwartzTripleIntegral244 a' (b - b') c|) +
          |schwartzTripleIntegral244 a' b' (c - c')| := by
            exact (abs_add_le _ _).trans
              (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ _ := by linarith only [hFirst, hSecond, hThird]

/-- Quantitative TWO-profile modulus for one gradient commutator triple.
The factor TWO is preserved from the physical H³ energy-pairing convention. -/
theorem fullGradientTriple_pair_abs_le_L2L2Linf244
    (a b c a' b' c' : SchwartzMap V3 ℝ)
    (K δ : ℝ)
    (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hc : ∀ x : V3, |c x| ≤ K)
    (hcdiff : ∀ x : V3, |(c - c') x| ≤ δ) :
    |fullGradientTriple244 a b c - fullGradientTriple244 a' b' c'| ≤
      2 * (K * (schwartzIntegralL2Root244 (a - a') *
                schwartzIntegralL2Root244 b) +
           K * (schwartzIntegralL2Root244 a' *
                schwartzIntegralL2Root244 (b - b')) +
           δ * (schwartzIntegralL2Root244 a' *
                schwartzIntegralL2Root244 b')) := by
  have h := schwartzTripleIntegral_pair_abs_le_L2L2Linf244
    a b c a' b' c' K δ hK hδ hc hcdiff
  change |2 * schwartzTripleIntegral244 a b c -
      2 * schwartzTripleIntegral244 a' b' c'| ≤ _
  rw [← mul_sub, abs_mul]
  simpa only [abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)] using
    mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 2 by norm_num)

/-- If a real Schwartz component is the EXACT pointwise C¹ reconstruction
of a weighted H³ state, its literal first Schwartz derivative is uniformly
controlled by that state's H³ norm. -/
theorem thirdFullSchwartz_matchedFirstJet_abs_le_H3_244
    (f : SchwartzMap V3 ℝ)
    (F : H3SpectralScalarState)
    (hF : h3SchwartzPoint3Scalar f =
      h3SpectralScalarRealC1RepresentativeOnPoint3 F)
    (i : A3) (x : V3) :
    |(∂_{h3FourierAxisDirection i} f) x| ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient * ‖F‖ := by
  rw [thirdFullSchwartz_firstJet_eq_of_zerothRealization244 f F hF i x]
  have hEval :=
    norm_h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_apply_le
      F (h3ClassicalizationFinOfAxis i)
      ((WithLp.ofLp : V3 → Point3) x)
  simpa only [h3AxisOfFin3_h3ClassicalizationFinOfAxis,
    Real.norm_eq_abs] using hEval

/-- Two different pointwise C¹ decoder-matched real Schwartz components
control the first-jet difference by precisely the spectral H³ distance.
This is a bound on their actual derivatives, not on an auxiliary model. -/
theorem thirdFullSchwartz_matchedFirstJet_pair_abs_le_H3_244
    (f g : SchwartzMap V3 ℝ)
    (F G : H3SpectralScalarState)
    (hf : h3SchwartzPoint3Scalar f =
      h3SpectralScalarRealC1RepresentativeOnPoint3 F)
    (hg : h3SchwartzPoint3Scalar g =
      h3SpectralScalarRealC1RepresentativeOnPoint3 G)
    (i : A3) (x : V3) :
    |(∂_{h3FourierAxisDirection i} f -
      ∂_{h3FourierAxisDirection i} g) x| ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        ‖F - G‖ :=
  thirdFullSchwartz_matchedFirstJetDifference_le_spectralDistance244
    f g F G hf hg i x

/-- The genuine 3–3–1 gradient triple is locally Lipschitz in the two
third-jet L² roots and first-jet weighted H³ norms, between ANY TWO
independently decoder-matched Schwartz profiles. Crucially, it does NOT
require that either profile be the final physical velocity. -/
theorem fullGradientTriple_spectralMatchedPair_modulus244
    (a b a' b' f g : SchwartzMap V3 ℝ)
    (F G : H3SpectralScalarState)
    (hf : h3SchwartzPoint3Scalar f =
      h3SpectralScalarRealC1RepresentativeOnPoint3 F)
    (hg : h3SchwartzPoint3Scalar g =
      h3SpectralScalarRealC1RepresentativeOnPoint3 G)
    (i : A3) :
    |fullGradientTriple244 a b (∂_{h3FourierAxisDirection i} f) -
      fullGradientTriple244 a' b' (∂_{h3FourierAxisDirection i} g)| ≤
      2 * (
        (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient * ‖F‖) *
          (schwartzIntegralL2Root244 (a - a') *
            schwartzIntegralL2Root244 b) +
        (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient * ‖F‖) *
          (schwartzIntegralL2Root244 a' *
            schwartzIntegralL2Root244 (b - b')) +
        (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            ‖F - G‖) *
          (schwartzIntegralL2Root244 a' *
            schwartzIntegralL2Root244 b')) := by
  let C : ℝ := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
  have hC : 0 ≤ C :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
  have hNorm : 0 ≤ C * ‖F‖ := mul_nonneg hC (norm_nonneg _)
  have hDiff : 0 ≤ C * ‖F - G‖ := mul_nonneg hC (norm_nonneg _)
  exact fullGradientTriple_pair_abs_le_L2L2Linf244
    a b (∂_{h3FourierAxisDirection i} f)
    a' b' (∂_{h3FourierAxisDirection i} g)
    (C * ‖F‖) (C * ‖F - G‖)
    hNorm hDiff
    (thirdFullSchwartz_matchedFirstJet_abs_le_H3_244 f F hf i)
    (thirdFullSchwartz_matchedFirstJet_pair_abs_le_H3_244 f g F G hf hg i)


/-- An explicit two-approximation error gauge relative to the SAME actual
physical velocity: no assertion that the physical field is Schwartz is
needed. This is the triangle inequality at the physical first-jet target,
and its two bounds are the genuine canonical H³ spectral estimates. -/
theorem thirdFullSchwartz_physicalPairFirstJet_abs_le_sumErrors244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (V W : H3SpectralVelocityState)
    (ψ φ : Fin 3 → SchwartzMap V3 ℝ)
    (hV : ∀ j : Fin 3,
      h3SchwartzPoint3Scalar (ψ j) =
        h3SpectralScalarRealC1RepresentativeOnPoint3 (V j))
    (hW : ∀ j : Fin 3,
      h3SchwartzPoint3Scalar (φ j) =
        h3SpectralScalarRealC1RepresentativeOnPoint3 (W j))
    (j : Fin 3) (i : A3) (x : V3) :
    |(∂_{h3FourierAxisDirection i} (ψ j) -
       ∂_{h3FourierAxisDirection i} (φ j)) x| ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        ‖V j - velocityH3SpectralScalarAt u t hInt hMeas hFourier j‖ +
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        ‖W j - velocityH3SpectralScalarAt u t hInt hMeas hFourier j‖ := by
  let z : ℝ := spatial3.d i
    (loggedVelocityComponent u t (h3AxisOfFin3 j))
      ((WithLp.ofLp : V3 → Point3) x)
  have hLeft := thirdFullSchwartz_physicalFirstJetError_le_spectral244
    hNS ht hFourier V ψ hV j i x
  have hRight := thirdFullSchwartz_physicalFirstJetError_le_spectral244
    hNS ht hFourier W φ hW j i x
  change |(∂_{h3FourierAxisDirection i} (ψ j)) x - z| ≤ _ at hLeft
  change |(∂_{h3FourierAxisDirection i} (φ j)) x - z| ≤ _ at hRight
  have hEq :
      (∂_{h3FourierAxisDirection i} (ψ j) -
        ∂_{h3FourierAxisDirection i} (φ j)) x =
      ((∂_{h3FourierAxisDirection i} (ψ j)) x - z) +
        (z - (∂_{h3FourierAxisDirection i} (φ j)) x) := by
    simp only [sub_apply]
    ring
  rw [hEq]
  have hFlip :
      |z - (∂_{h3FourierAxisDirection i} (φ j)) x| =
        |(∂_{h3FourierAxisDirection i} (φ j)) x - z| :=
    abs_sub_comm _ _
  calc
    |((∂_{h3FourierAxisDirection i} (ψ j)) x - z) +
      (z - (∂_{h3FourierAxisDirection i} (φ j)) x)| ≤
      |(∂_{h3FourierAxisDirection i} (ψ j)) x - z| +
        |z - (∂_{h3FourierAxisDirection i} (φ j)) x| := abs_add_le _ _
    _ = |(∂_{h3FourierAxisDirection i} (ψ j)) x - z| +
        |(∂_{h3FourierAxisDirection i} (φ j)) x - z| := by rw [hFlip]
    _ ≤ _ := add_le_add hLeft hRight

end
end PrimeTensor.FirstMonomialTriad
