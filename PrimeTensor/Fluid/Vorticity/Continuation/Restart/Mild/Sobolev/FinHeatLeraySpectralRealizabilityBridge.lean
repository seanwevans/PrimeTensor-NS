import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLeraySpectralEncodedReality
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLeraySpectralRealizabilityClosure

/-!
# Raw-Hermitian Fourier states are exactly physically real after decoding

The finite heat--Leray Picard construction now preserves the exact deweighted
Hermitian Fourier invariant, and genuine encoded real H³ restart data satisfy
that invariant automatically.  This file closes the final physical-space
bridge.

For a complex physical `L²` field `f`, split `f` into its real and imaginary
parts.  The Fourier transforms of the complexifications of both real `L²`
parts are Hermitian.  If the Fourier transform of `f` is itself Hermitian,
then subtracting the real contribution shows that `I` times the Fourier
transform of the imaginary part is Hermitian as well.  A Fourier field `B`
for which both `B` and `I • B` are Hermitian must vanish.  Fourier injectivity
therefore forces the imaginary physical `L²` part to vanish.

Consequently every raw-Hermitian weighted spectral state is realizable in the
previous decoder sense: its exact inverse Fourier decoder is the
complexification of its canonical real decoder.  Applying this to the
Banach-selected path started from a genuine encoded H³ snapshot certifies that
the selected complex spectral solution itself decodes to a genuinely real
physical velocity field.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped ENNReal NNReal Topology ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3SpectralRealizabilityBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Real/imaginary decomposition of complex `L²` -/

/-- Imaginary-part projection on the complex Fourier/physical `L²` carrier. -/
noncomputable def h3ImagPartFourierL2
    (f : H3FourierComplexL2) : H3FourierRealL2 :=
  Complex.imCLM.compLp f

/-- Every complex `L²` field is the complexification of its real part plus
`I` times the complexification of its imaginary part. -/
theorem h3ComplexFourierL2_re_im_decompose
    (f : H3FourierComplexL2) :
    f
      =
    h3ComplexifyFourierL2 (h3RealPartFourierL2 f)
      + Complex.I • h3ComplexifyFourierL2 (h3ImagPartFourierL2 f) := by
  unfold h3ComplexifyFourierL2 h3RealPartFourierL2 h3ImagPartFourierL2
  apply MeasureTheory.Lp.ext
  filter_upwards [
    Complex.reCLM.coeFn_compLp f,
    Complex.imCLM.coeFn_compLp f,
    Complex.ofRealCLM.coeFn_compLp (Complex.reCLM.compLp f),
    Complex.ofRealCLM.coeFn_compLp (Complex.imCLM.compLp f),
    MeasureTheory.Lp.coeFn_smul
      Complex.I (Complex.ofRealCLM.compLp (Complex.imCLM.compLp f)),
    MeasureTheory.Lp.coeFn_add
      (Complex.ofRealCLM.compLp (Complex.reCLM.compLp f))
      (Complex.I • Complex.ofRealCLM.compLp (Complex.imCLM.compLp f))
  ] with ξ hre him hOfRe hOfIm hSmul hAdd
  rw [hAdd]
  simp only [Pi.add_apply]
  rw [hOfRe, hSmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hOfIm, hre, him]
  change (f ξ) = (f ξ).re + Complex.I * (f ξ).im
  calc
    (f ξ) = (f ξ).re + (f ξ).im * Complex.I :=
      (Complex.re_add_im (f ξ)).symm
    _ = (f ξ).re + Complex.I * (f ξ).im := by
      rw [mul_comm]

/-! ## A Hermitian field cannot remain Hermitian after multiplication by `I` -/

/-- If both `B` and `I • B` satisfy the Hermitian Fourier symmetry, then `B`
vanishes in `L²`. -/
theorem h3FourierL2Hermitian_eq_zero_of_I_smul_hermitian
    {B : H3FourierComplexL2}
    (hB : H3FourierL2Hermitian B)
    (hIB : H3FourierL2Hermitian (Complex.I • B)) :
    B = 0 := by
  apply MeasureTheory.Lp.ext
  unfold H3FourierL2Hermitian at hB hIB
  have hSmul := MeasureTheory.Lp.coeFn_smul Complex.I B
  have hSmulNeg := h3Fourier_ae_neg hSmul
  filter_upwards [hB, hIB, hSmul, hSmulNeg] with ξ hHerm hIHerm hAt hNeg
  simp only [Pi.smul_apply, smul_eq_mul] at hAt hNeg
  rw [hNeg, hAt, hHerm] at hIHerm
  have hSelf :
      Complex.I * conj (B ξ)
        =
      -(Complex.I * conj (B ξ)) := by
    simpa only [map_mul, Complex.conj_I, neg_mul] using hIHerm
  have hTwo :
      (2 : ℂ) * (Complex.I * conj (B ξ)) = 0 := by
    calc
      (2 : ℂ) * (Complex.I * conj (B ξ))
          = (Complex.I * conj (B ξ)) + (Complex.I * conj (B ξ)) :=
        two_mul _
      _ = -(Complex.I * conj (B ξ)) + (Complex.I * conj (B ξ)) :=
        congrArg (fun z : ℂ => z + (Complex.I * conj (B ξ))) hSelf
      _ = 0 := neg_add_cancel _
  have hIZero : Complex.I * conj (B ξ) = 0 :=
    (mul_eq_zero.mp hTwo).resolve_left (by norm_num)
  have hConjZero : conj (B ξ) = 0 :=
    (mul_eq_zero.mp hIZero).resolve_left Complex.I_ne_zero
  have hZero : B ξ = 0 := by
    have h := congrArg (fun z : ℂ => conj z) hConjZero
    simpa using h
  simpa using hZero

/-! ## Hermitian Fourier `L²` implies a real inverse Fourier transform -/

/-- The inverse Fourier transform of a Hermitian complex `L²` field is exactly
the complexification of its own real part. -/
theorem h3FourierL2Hermitian_fourierInv_eq_complexify_real
    (F : H3FourierComplexL2)
    (hF : H3FourierL2Hermitian F) :
    (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm F
      =
    h3ComplexifyFourierL2
      (h3RealPartFourierL2
        ((MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm F)) := by
  let FT := MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ
  let f : H3FourierComplexL2 := FT.symm F
  let r : H3FourierRealL2 := h3RealPartFourierL2 f
  let q : H3FourierRealL2 := h3ImagPartFourierL2 f
  let A : H3FourierComplexL2 := FT (h3ComplexifyFourierL2 r)
  let B : H3FourierComplexL2 := FT (h3ComplexifyFourierL2 q)

  have hA : H3FourierL2Hermitian A := by
    exact h3FourierL2_complexify_real_hermitian r
  have hB : H3FourierL2Hermitian B := by
    exact h3FourierL2_complexify_real_hermitian q

  have hFTf : FT f = F := by
    dsimp [f]
    exact FT.apply_symm_apply F

  have hDecomp : F = A + Complex.I • B := by
    calc
      F = FT f := hFTf.symm
      _ = FT
          (h3ComplexifyFourierL2 r
            + Complex.I • h3ComplexifyFourierL2 q) := by
          rw [← h3ComplexFourierL2_re_im_decompose f]
      _ = A + Complex.I • B := by
          simp only [map_add, map_smul]
          rfl

  have hIB : H3FourierL2Hermitian (Complex.I • B) := by
    have hSub := hF.sub hA
    have hEq : F - A = Complex.I • B := by
      rw [hDecomp]
      abel
    rw [hEq] at hSub
    exact hSub

  have hBzero : B = 0 :=
    h3FourierL2Hermitian_eq_zero_of_I_smul_hermitian hB hIB

  have hComplexImZero : h3ComplexifyFourierL2 q = 0 := by
    apply FT.injective
    simpa only [B, map_zero] using hBzero

  have hqzero : q = 0 := by
    apply norm_eq_zero.mp
    calc
      ‖q‖ = ‖h3ComplexifyFourierL2 q‖ :=
        (norm_h3ComplexifyFourierL2_eq q).symm
      _ = 0 := by rw [hComplexImZero, norm_zero]

  have hfReal : f = h3ComplexifyFourierL2 r := by
    calc
      f = h3ComplexifyFourierL2 r
          + Complex.I • h3ComplexifyFourierL2 q :=
        h3ComplexFourierL2_re_im_decompose f
      _ = h3ComplexifyFourierL2 r := by
        rw [hqzero, h3ComplexifyFourierL2_zero, smul_zero, add_zero]

  simpa only [FT, f, r] using hfReal

/-! ## Raw-Hermitian weighted spectral states are realizable -/

/-- The raw-Hermitian invariant implies the earlier exact decoder
realizability predicate. -/
theorem h3SpectralScalarRawHermitian_realizable
    {G : H3SpectralScalarState}
    (hG : H3SpectralScalarRawHermitian G) :
    H3SpectralScalarRealizable G := by
  unfold H3SpectralScalarRawHermitian at hG
  unfold H3SpectralScalarRealizable h3SpectralScalarDecodeRealL2
  unfold h3SpectralScalarDecodeComplexL2
  exact
    h3FourierL2Hermitian_fourierInv_eq_complexify_real
      (h3SpectralScalarRawFourierL2 G) hG

/-- Coordinatewise velocity version. -/
theorem h3SpectralVelocityRawHermitian_realizable
    {U : H3SpectralVelocityState}
    (hU : H3SpectralVelocityRawHermitian U) :
    H3SpectralVelocityRealizable U := by
  intro j
  exact h3SpectralScalarRawHermitian_realizable (hU j)

/-- Pathwise version for normalized-time spectral velocities. -/
theorem h3SpectralVelocityPathRawHermitian_realizable
    {U : H3SpectralVelocityPath}
    (hU : H3SpectralVelocityPathRawHermitian U) :
    H3SpectralVelocityPathRealizable U := by
  intro s
  exact h3SpectralVelocityRawHermitian_realizable (hU s)

/-! ## Encoded-data mild solution is genuinely realizable -/

/-- The Banach-selected mild path started from a genuine encoded H³ snapshot is
realizable at every normalized time. -/
theorem h3SpectralFinHeatLerayMildSolution_encoded_realizable
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hA : 0 < A)
    (hU₀bound :
      ‖velocityH3SpectralStateAt u t hInt hMeas hFourier‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1) :
    H3SpectralVelocityPathRealizable
      (h3SpectralFinHeatLerayMildSolution
        hν hτ
        (velocityH3SpectralStateAt u t hInt hMeas hFourier)
        hA hU₀bound hsmall) := by
  exact
    h3SpectralVelocityPathRawHermitian_realizable
      (h3SpectralFinHeatLerayMildSolution_encoded_preserves_rawHermitian
        hν hτ hFourier hA hU₀bound hsmall)

/-- Every physical-time slice of the same encoded-data mild solution is
realizable. -/
theorem h3SpectralFinHeatLerayPhysicalMildSolution_encoded_realizable
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hA : 0 < A)
    (hU₀bound :
      ‖velocityH3SpectralStateAt u t hInt hMeas hFourier‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (q : Set.Icc (0 : ℝ) τ) :
    H3SpectralVelocityRealizable
      (h3SpectralFinHeatLerayPhysicalMildSolution
        hν hτ
        (velocityH3SpectralStateAt u t hInt hMeas hFourier)
        hA hU₀bound hsmall q) := by
  have hPath :=
    h3SpectralFinHeatLerayMildSolution_encoded_preserves_rawHermitian
      hν hτ hFourier hA hU₀bound hsmall
  apply h3SpectralVelocityRawHermitian_realizable
  change
    H3SpectralVelocityRawHermitian
      (h3PathPhysicalRealExtension τ
        (h3SpectralFinHeatLerayMildSolution
          hν hτ
          (velocityH3SpectralStateAt u t hInt hMeas hFourier)
          hA hU₀bound hsmall)
        (q : ℝ))
  exact h3PathPhysicalRealExtension_preserves_rawHermitian hPath (q : ℝ)

/-- Final physical certification: for a mild solution started from genuine
encoded real H³ data, the exact complex inverse-Fourier decoder at every
physical time and component is literally the complexification of the canonical
real decoded velocity.  No post hoc projection is being substituted for the
selected complex fixed point. -/
theorem h3SpectralFinHeatLerayPhysicalDecoded_encoded_eq_complexify_real
    {ν τ A : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hA : 0 < A)
    (hU₀bound :
      ‖velocityH3SpectralStateAt u t hInt hMeas hFourier‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (q : Set.Icc (0 : ℝ) τ)
    (j : Fin 3) :
    h3SpectralFinHeatLerayPhysicalDecodedComplexL2
        hν hτ
        (velocityH3SpectralStateAt u t hInt hMeas hFourier)
        hA hU₀bound hsmall q j
      =
    h3ComplexifyFourierL2
      (h3SpectralFinHeatLerayPhysicalDecodedRealL2
        hν hτ
        (velocityH3SpectralStateAt u t hInt hMeas hFourier)
        hA hU₀bound hsmall q j) := by
  change
    h3SpectralVelocityDecodeComplexL2
        (h3SpectralFinHeatLerayPhysicalMildSolution
          hν hτ
          (velocityH3SpectralStateAt u t hInt hMeas hFourier)
          hA hU₀bound hsmall q) j
      =
    h3ComplexifyFourierL2
      (h3SpectralVelocityDecodeRealL2
        (h3SpectralFinHeatLerayPhysicalMildSolution
          hν hτ
          (velocityH3SpectralStateAt u t hInt hMeas hFourier)
          hA hU₀bound hsmall q) j)
  exact
    h3SpectralVelocityDecodeComplexL2_eq_complexify_real
      (h3SpectralFinHeatLerayPhysicalMildSolution_encoded_realizable
        hν hτ hFourier hA hU₀bound hsmall q)
      j

end

end Euclidean
end Bridge
end PrimeTensor
