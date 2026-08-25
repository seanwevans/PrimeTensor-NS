import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralDuhamelHeadRealC3Bridge

/-!
# Real C¹ reconstruction of arbitrary spectral H³ states

The positive-time heat layer is now spatially `C³`, and the regularized
Duhamel head inherits that regularity.  The singular Duhamel tail cannot be
upgraded to `C³` from a bare uniform H³ bound alone: near the upper endpoint
there is no fixed positive heat lag.

The correct bootstrap seed is already contained in H³ itself.  If

    G(ξ) = W₃(ξ) f̂(ξ),

then not only `f̂ ∈ L¹`, but also

    ‖ξ‖ f̂(ξ) ∈ L¹.

Indeed the exact H³ weight satisfies

    ‖ξ‖ / W₃(ξ) ≤ (1 + ‖ξ‖²)⁻¹,

and the right hand side belongs to `L²(R³)`.  Hölder against the weighted
`L²` state therefore gives the first raw Fourier moment in `L¹`.

Mathlib's Fourier differentiability theorem then gives a classical `C¹`
inverse-Fourier representative for every spectral H³ state.  The generic
`L¹ ∩ L²` compatibility theorem identifies it almost everywhere with the
existing decoder.  Taking real parts and transporting through the canonical
`WithLp.toLp` map gives the same statement on the project's `Point3` carrier,
coordinatewise for velocity states.

This is the bootstrap input for the genuinely singular near-endpoint Duhamel
tail: every positive-time mild slice already has a concrete real spatial `C¹`
representative before any additional parabolic smoothing is invoked.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralH3RealC1Bridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SchwartzSpectralH3RealC1Bridge :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## The first H³ deweighting moment -/

/-- The first-moment reciprocal H³ weight. -/
def h3SobolevFrequencyFirstMomentInv
    (ξ : H3FourierPoint3) : ℝ :=
  ‖ξ‖ * h3SobolevFrequencyWeightInv ξ

/-- The first-moment reciprocal weight is continuous. -/
theorem continuous_h3SobolevFrequencyFirstMomentInv :
    Continuous h3SobolevFrequencyFirstMomentInv := by
  unfold h3SobolevFrequencyFirstMomentInv
  exact continuous_norm.mul continuous_h3SobolevFrequencyWeightInv

/-- The exact H³ weight dominates `‖ξ‖ (1 + ‖ξ‖²)`. -/
theorem norm_mul_one_add_norm_sq_le_h3SobolevFrequencyWeight
    (ξ : H3FourierPoint3) :
    ‖ξ‖ * (1 + ‖ξ‖ ^ 2)
      ≤
    h3SobolevFrequencyWeight ξ := by
  let r : ℝ := ‖ξ‖ ^ 2
  let q : ℝ := h3FourierGradientSquare ξ

  have hr : 0 ≤ r := by
    dsimp [r]
    positivity
  have hq : 0 ≤ q := by
    dsimp [q]
    exact h3FourierGradientSquare_nonneg ξ
  have h2r : 2 * r ≤ q := by
    dsimp [r, q]
    exact two_mul_norm_sq_le_h3FourierGradientSquare ξ

  have h2rNonneg : 0 ≤ 2 * r := by positivity
  have hq2raw : (2 * r) ^ 2 ≤ q ^ 2 :=
    pow_le_pow_left₀ h2rNonneg h2r 2
  have hq3raw : (2 * r) ^ 3 ≤ q ^ 3 :=
    pow_le_pow_left₀ h2rNonneg h2r 3
  have hq2 : 4 * r ^ 2 ≤ q ^ 2 := by
    nlinarith
  have hq3 : 8 * r ^ 3 ≤ q ^ 3 := by
    nlinarith

  have hSq :
      (‖ξ‖ * (1 + ‖ξ‖ ^ 2)) ^ 2
        ≤
      (h3SobolevFrequencyWeight ξ) ^ 2 := by
    rw [h3SobolevFrequencyWeight_sq]
    change
      (‖ξ‖ * (1 + r)) ^ 2
        ≤
      1 + q + q ^ 2 + q ^ 3
    have hnormsq : ‖ξ‖ ^ 2 = r := by rfl
    nlinarith [sq_nonneg (r - 1)]

  have hAbs := (sq_le_sq).mp hSq
  have hLeft : 0 ≤ ‖ξ‖ * (1 + ‖ξ‖ ^ 2) := by positivity
  have hRight : 0 ≤ h3SobolevFrequencyWeight ξ :=
    (h3SobolevFrequencyWeight_pos ξ).le

  simpa [abs_of_nonneg hLeft, abs_of_nonneg hRight] using hAbs

/-- The first-moment reciprocal exact H³ weight is dominated by the same
standard inverse Bessel weight already known to lie in `L²`. -/
theorem h3SobolevFrequencyFirstMomentInv_le_standard
    (ξ : H3FourierPoint3) :
    h3SobolevFrequencyFirstMomentInv ξ
      ≤
    h3StandardInverseBesselWeight ξ := by
  let r : ℝ := ‖ξ‖
  let B : ℝ := 1 + ‖ξ‖ ^ 2
  let W : ℝ := h3SobolevFrequencyWeight ξ

  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hW : 0 < W := by
    dsimp [W]
    exact h3SobolevFrequencyWeight_pos ξ
  have hProd : r * B ≤ W := by
    dsimp [r, B, W]
    exact norm_mul_one_add_norm_sq_le_h3SobolevFrequencyWeight ξ
  have hWinv : 0 ≤ W⁻¹ := inv_nonneg.mpr hW.le

  unfold h3SobolevFrequencyFirstMomentInv h3SobolevFrequencyWeightInv
  unfold h3StandardInverseBesselWeight
  change r * W⁻¹ ≤ B⁻¹
  rw [show B⁻¹ = 1 / B by simp]
  apply (le_div_iff₀ hB).2
  calc
    r * W⁻¹ * B = (r * B) * W⁻¹ := by ring
    _ ≤ W * W⁻¹ :=
      mul_le_mul_of_nonneg_right hProd hWinv
    _ = 1 := mul_inv_cancel₀ (ne_of_gt hW)

/-- The first-moment reciprocal exact H³ weight belongs to real `L²`. -/
theorem h3SobolevFrequencyFirstMomentInv_memLp2 :
    MemLp
      h3SobolevFrequencyFirstMomentInv
      2
      (volume : Measure H3FourierPoint3) := by
  apply
    h3StandardInverseBesselWeight_memLp2.of_le
      continuous_h3SobolevFrequencyFirstMomentInv.aestronglyMeasurable

  filter_upwards with ξ

  have hFirstNonneg :
      0 ≤ h3SobolevFrequencyFirstMomentInv ξ := by
    unfold h3SobolevFrequencyFirstMomentInv h3SobolevFrequencyWeightInv
    exact
      mul_nonneg
        (norm_nonneg ξ)
        (inv_nonneg.mpr (h3SobolevFrequencyWeight_pos ξ).le)
  have hStdNonneg :
      0 ≤ h3StandardInverseBesselWeight ξ := by
    unfold h3StandardInverseBesselWeight
    positivity

  simpa [
    Real.norm_eq_abs,
    abs_of_nonneg hFirstNonneg,
    abs_of_nonneg hStdNonneg
  ] using h3SobolevFrequencyFirstMomentInv_le_standard ξ

/-- The first raw Fourier moment of every weighted H³ scalar state is
integrable. -/
theorem h3SpectralScalarRawFourier_firstMoment_integrable
    (G : H3SpectralScalarState) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ * ‖h3SpectralScalarRawFourier G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hProductMemLp1 :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          h3SobolevFrequencyFirstMomentInv ξ * ‖G ξ‖)
        1
        (volume : Measure H3FourierPoint3) := by
    exact
      (MeasureTheory.Lp.memLp G).norm.mul'
        h3SobolevFrequencyFirstMomentInv_memLp2

  have hProductInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3SobolevFrequencyFirstMomentInv ξ * ‖G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp hProductMemLp1

  refine hProductInt.congr ?_
  filter_upwards with ξ

  have hInvNonneg :
      0 ≤ h3SobolevFrequencyWeightInv ξ := by
    unfold h3SobolevFrequencyWeightInv
    exact inv_nonneg.mpr (h3SobolevFrequencyWeight_pos ξ).le

  unfold h3SobolevFrequencyFirstMomentInv
  unfold h3SpectralScalarRawFourier h3SobolevFrequencyWeightInvComplex
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hInvNonneg]
  ring

/-- Raw Fourier moments through order one are integrable for every H³ state. -/
theorem h3SpectralScalarRawFourier_moment_integrable_one
    (G : H3SpectralScalarState)
    (n : ℕ)
    (hn : n ≤ 1) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ n * ‖h3SpectralScalarRawFourier G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hnCases : n = 0 ∨ n = 1 := by omega
  rcases hnCases with rfl | rfl
  · have hRaw :
        Integrable
          (h3SpectralScalarRawFourier G)
          (volume : Measure H3FourierPoint3) :=
      MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1 G)
    simpa using hRaw.norm
  · simpa using h3SpectralScalarRawFourier_firstMoment_integrable G

/-! ## Classical C¹ reconstruction and exact decoder compatibility -/

/-- Ordinary inverse-Fourier reconstruction of an arbitrary weighted H³
spectral scalar state. -/
noncomputable def h3SpectralScalarC1Representative
    (G : H3SpectralScalarState) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3SpectralScalarRawFourier G)

/-- Every weighted H³ scalar state has a classical spatial `C¹` inverse-Fourier
representative. -/
theorem h3SpectralScalarC1Representative_contDiff_one
    (G : H3SpectralScalarState) :
    ContDiff ℝ 1 (h3SpectralScalarC1Representative G) := by
  have hFourier :
      ContDiff ℝ 1
        (FourierTransform.fourier
          (h3SpectralScalarRawFourier G)) := by
    apply Real.contDiff_fourier
    intro n hn
    have hn' : n ≤ 1 := by simpa using hn
    exact h3SpectralScalarRawFourier_moment_integrable_one G n hn'

  have hEq :
      h3SpectralScalarC1Representative G
        =
      fun x : H3FourierPoint3 =>
        FourierTransform.fourier
          (h3SpectralScalarRawFourier G) (-x) := by
    funext x
    unfold h3SpectralScalarC1Representative
    exact
      Real.fourierInv_eq_fourier_neg
        (h3SpectralScalarRawFourier G) x

  rw [hEq]
  exact hFourier.comp (by fun_prop)

/-- The classical `C¹` representative agrees almost everywhere with the
existing complex `L²` decoder of the same arbitrary H³ state. -/
theorem h3SpectralScalarC1Representative_ae_eq_decodeComplexL2
    (G : H3SpectralScalarState) :
    h3SpectralScalarC1Representative G
      =ᵐ[(volume : Measure H3FourierPoint3)]
    ((h3SpectralScalarDecodeComplexL2 G : H3ComplexPhysicalScalarL2) :
      H3FourierPoint3 → ℂ) := by
  have hRawInt :
      Integrable
        (h3SpectralScalarRawFourier G)
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)

  have hCompat :=
    h3FourierInv_integrable_memLp2_ae_eq_L2
      hRawInt
      (h3SpectralScalarRawFourier_memLp2 G)

  unfold h3SpectralScalarC1Representative
  unfold h3SpectralScalarDecodeComplexL2
  simpa [h3SpectralScalarRawFourierL2] using hCompat

/-! ## Real representative on the Fourier carrier -/

/-- Real part of the arbitrary-H³ classical `C¹` representative. -/
noncomputable def h3SpectralScalarRealC1Representative
    (G : H3SpectralScalarState) :
    H3FourierPoint3 → ℝ :=
  fun x => (h3SpectralScalarC1Representative G x).re

/-- The real arbitrary-H³ representative is spatially `C¹`. -/
theorem h3SpectralScalarRealC1Representative_contDiff_one
    (G : H3SpectralScalarState) :
    ContDiff ℝ 1 (h3SpectralScalarRealC1Representative G) := by
  unfold h3SpectralScalarRealC1Representative
  simpa [Function.comp_def] using
    (h3SpectralScalarC1Representative_contDiff_one G).continuousLinearMap_comp
      Complex.reCLM

/-- The real `C¹` representative agrees almost everywhere with the existing
real `L²` decoder. -/
theorem h3SpectralScalarRealC1Representative_ae_eq_decodeRealL2
    (G : H3SpectralScalarState) :
    h3SpectralScalarRealC1Representative G
      =ᵐ[(volume : Measure H3FourierPoint3)]
    ((h3SpectralScalarDecodeRealL2 G : H3RealPhysicalScalarL2) :
      H3FourierPoint3 → ℝ) := by
  have hComplex :
      h3SpectralScalarC1Representative G
        =ᵐ[(volume : Measure H3FourierPoint3)]
      ((h3SpectralScalarDecodeComplexL2 G : H3ComplexPhysicalScalarL2) :
        H3FourierPoint3 → ℂ) :=
    h3SpectralScalarC1Representative_ae_eq_decodeComplexL2 G

  have hRealPart :
      ((h3SpectralScalarDecodeRealL2 G : H3RealPhysicalScalarL2) :
          H3FourierPoint3 → ℝ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun x : H3FourierPoint3 =>
        ((h3SpectralScalarDecodeComplexL2 G : H3ComplexPhysicalScalarL2) x).re) := by
    unfold h3SpectralScalarDecodeRealL2 h3RealPartFourierL2
    exact
      Complex.reCLM.coeFn_compLp
        (h3SpectralScalarDecodeComplexL2 G)

  unfold h3SpectralScalarRealC1Representative
  filter_upwards [hComplex, hRealPart] with x hx hRe
  rw [hRe]
  simpa using congrArg Complex.re hx

/-! ## Transport to `Point3` -/

/-- Real arbitrary-H³ `C¹` representative on the project's spatial carrier. -/
noncomputable def h3SpectralScalarRealC1RepresentativeOnPoint3
    (G : H3SpectralScalarState) :
    Point3 → ℝ :=
  fun x =>
    h3SpectralScalarRealC1Representative G
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

/-- Transport to `Point3` preserves spatial `C¹` regularity. -/
theorem h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_one
    (G : H3SpectralScalarState) :
    ContDiff ℝ 1 (h3SpectralScalarRealC1RepresentativeOnPoint3 G) := by
  have hToLp :
      ContDiff ℝ 1
        (WithLp.toLp 2 : Point3 → H3FourierPoint3) := by
    exact PiLp.contDiff_toLp
  unfold h3SpectralScalarRealC1RepresentativeOnPoint3
  exact
    (h3SpectralScalarRealC1Representative_contDiff_one G).comp hToLp

/-- On `Point3`, the real `C¹` representative is exactly the a.e.
representative of the existing transported real decoder. -/
theorem h3SpectralScalarRealC1RepresentativeOnPoint3_ae_eq_decodeRealL2
    (G : H3SpectralScalarState) :
    h3SpectralScalarRealC1RepresentativeOnPoint3 G
      =ᵐ[(volume : Measure Point3)]
    ((h3FromFourierRealL2
        (h3SpectralScalarDecodeRealL2 G) : H3ScalarL2) :
      Point3 → ℝ) := by
  let R : H3FourierRealL2 := h3SpectralScalarDecodeRealL2 G

  have hFourier :
      h3SpectralScalarRealC1Representative G
        =ᵐ[(volume : Measure H3FourierPoint3)]
      ((R : H3FourierRealL2) : H3FourierPoint3 → ℝ) := by
    dsimp [R]
    exact h3SpectralScalarRealC1Representative_ae_eq_decodeRealL2 G

  have hComp :
      (fun x : Point3 =>
        h3SpectralScalarRealC1Representative G
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (R : H3FourierPoint3 → ℝ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)) := by
    exact
      (PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)).quasiMeasurePreserving.ae_eq_comp
          hFourier

  have hFrom :
      ((h3FromFourierRealL2 R : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (R : H3FourierPoint3 → ℝ)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)) := by
    unfold h3FromFourierRealL2
    exact
      MeasureTheory.Lp.coeFn_compMeasurePreserving
        R
        (PiLp.volume_preserving_toLp
          (PrimeTensor.Axis Depth.three))

  have hFinal := hComp.trans hFrom.symm
  change
    (fun x : Point3 =>
      h3SpectralScalarRealC1Representative G
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    ((h3FromFourierRealL2 R : H3ScalarL2) : Point3 → ℝ)
  exact hFinal

/-! ## Three-component velocity lift -/

/-- Coordinatewise real `C¹` reconstruction of an arbitrary spectral velocity
state on `Point3`. -/
noncomputable def h3SpectralVelocityRealC1RepresentativeOnPoint3
    (U : H3SpectralVelocityState) :
    Fin 3 → Point3 → ℝ :=
  fun j => h3SpectralScalarRealC1RepresentativeOnPoint3 (U j)

/-- Every coordinate of an arbitrary spectral H³ velocity state has a real
spatial `C¹` representative. -/
theorem h3SpectralVelocityRealC1RepresentativeOnPoint3_contDiff_one
    (U : H3SpectralVelocityState)
    (j : Fin 3) :
    ContDiff ℝ 1
      (h3SpectralVelocityRealC1RepresentativeOnPoint3 U j) := by
  exact h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_one (U j)

/-- Every coordinate agrees a.e. with the exact real decoder of the arbitrary
spectral H³ velocity state. -/
theorem h3SpectralVelocityRealC1RepresentativeOnPoint3_ae_eq_decodeRealL2
    (U : H3SpectralVelocityState)
    (j : Fin 3) :
    h3SpectralVelocityRealC1RepresentativeOnPoint3 U j
      =ᵐ[(volume : Measure Point3)]
    ((h3FromFourierRealL2
        (h3SpectralVelocityDecodeRealL2 U j) : H3ScalarL2) :
      Point3 → ℝ) := by
  change
    h3SpectralScalarRealC1RepresentativeOnPoint3 (U j)
      =ᵐ[(volume : Measure Point3)]
    ((h3FromFourierRealL2
        (h3SpectralScalarDecodeRealL2 (U j)) : H3ScalarL2) :
      Point3 → ℝ)
  exact h3SpectralScalarRealC1RepresentativeOnPoint3_ae_eq_decodeRealL2 (U j)

end

end Euclidean
end Bridge
end PrimeTensor
