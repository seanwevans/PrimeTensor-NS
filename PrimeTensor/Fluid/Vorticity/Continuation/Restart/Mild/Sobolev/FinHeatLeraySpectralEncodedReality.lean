import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLeraySpectralPicardReality
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLeraySpectralRoundTrip

/-!
# Reality of genuinely encoded H³ restart data

The Picard reality theorem is formulated in terms of the exact deweighted
Hermitian invariant.  A genuine restart state, however, is produced by the H³
encoder from a real physical velocity field.  This file closes that input-side
bridge.

The analytic core is the standard real-Fourier symmetry theorem.  We first
prove it for an integrable complex-valued function that is real almost
everywhere.  We then specialize to complexifications of real Schwartz
functions and extend to arbitrary real `L²` by density.  Closedness of the
Hermitian `L²` subset was established earlier, so the density step is purely
functional analytic.

Finally the exact encoder/deweighting round trip identifies every encoded raw
Fourier component with the Fourier transform of a real `L²` component.  Hence
genuine encoded restart data satisfy the hypothesis of the already-proved
Picard reality theorem automatically.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped ENNReal NNReal Topology ComplexConjugate SchwartzMap Real RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SpectralEncodedReality
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Classical Fourier symmetry of real integrable functions -/

/-- The classical Fourier integral of a complex function that is real almost
 everywhere has Hermitian symmetry. -/
theorem h3FourierIntegral_real_hermitian
    {f : H3FourierPoint3 → ℂ}
    (hf : Integrable f volume)
    (hreal : ∀ᵐ x : H3FourierPoint3 ∂volume, conj (f x) = f x)
    (ξ : H3FourierPoint3) :
    𝓕 f (-ξ) = conj (𝓕 f ξ) := by
  rw [← Real.fourierInv_eq_fourier_neg]
  rw [Real.fourierInv_eq, Real.fourier_eq]
  have hKernel :
      Integrable
        (fun x : H3FourierPoint3 => 𝐞 (-(inner ℝ x ξ)) • f x)
        volume := by
    rw [Real.fourierIntegral_convergent_iff ξ]
    exact hf
  have hConjIntegral :
      (∫ x : H3FourierPoint3,
          conj (𝐞 (-(inner ℝ x ξ)) • f x))
        =
      conj
        (∫ x : H3FourierPoint3,
          𝐞 (-(inner ℝ x ξ)) • f x) := by
    exact
      Complex.conjCLE.toContinuousLinearMap.integral_comp_comm
        hKernel
  rw [← hConjIntegral]
  apply integral_congr_ae
  filter_upwards [hreal] with x hx
  simp only [Circle.smul_def, smul_eq_mul, map_mul, hx,
    ← Circle.coe_inv_eq_conj, AddChar.map_neg_eq_inv, inv_inv]

/-! ## Real Schwartz functions -/

/-- Complexify a real Schwartz function pointwise. -/
noncomputable def h3SchwartzComplexify
    (f : SchwartzMap H3FourierPoint3 ℝ) :
    SchwartzMap H3FourierPoint3 ℂ :=
  (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM) f

@[simp]
theorem h3SchwartzComplexify_apply
    (f : SchwartzMap H3FourierPoint3 ℝ)
    (x : H3FourierPoint3) :
    h3SchwartzComplexify f x = (f x : ℂ) := by
  simp [h3SchwartzComplexify]

/-- The Fourier transform of a complexified real Schwartz function is
pointwise Hermitian. -/
theorem h3SchwartzComplexify_fourier_hermitian
    (f : SchwartzMap H3FourierPoint3 ℝ) :
    H3FourierPointwiseHermitian
      ((𝓕 (h3SchwartzComplexify f) :
          SchwartzMap H3FourierPoint3 ℂ) :
        H3FourierPoint3 → ℂ) := by
  intro ξ
  have h :=
    h3FourierIntegral_real_hermitian
      (f := fun x : H3FourierPoint3 => h3SchwartzComplexify f x)
      (h3SchwartzComplexify f).integrable
      (Filter.Eventually.of_forall (fun x => by
        simp [h3SchwartzComplexify]))
      ξ
  simpa only [SchwartzMap.fourier_coe] using h

/-! ## Compatibility of Schwartz and `L²` complexification -/

/-- Complexification of a real Schwartz function commutes with passage to
`L²`. -/
theorem h3ComplexifyFourierL2_schwartz_toLp
    (f : SchwartzMap H3FourierPoint3 ℝ) :
    h3ComplexifyFourierL2 (f.toLp 2 volume)
      =
    (h3SchwartzComplexify f).toLp 2 volume := by
  unfold h3ComplexifyFourierL2
  apply MeasureTheory.Lp.ext
  filter_upwards [
    Complex.ofRealCLM.coeFn_compLp (f.toLp 2 volume),
    SchwartzMap.coeFn_toLp f 2 volume,
    SchwartzMap.coeFn_toLp (h3SchwartzComplexify f) 2 volume
  ] with x hComp hReal hComplex
  rw [hComp, hReal, hComplex]
  simp [h3SchwartzComplexify]

/-- The `L²` Fourier transform of a complexified real Schwartz function is
Hermitian. -/
theorem h3FourierL2_complexify_schwartz_hermitian
    (f : SchwartzMap H3FourierPoint3 ℝ) :
    H3FourierL2Hermitian
      ((MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
        (h3ComplexifyFourierL2 (f.toLp 2 volume))) := by
  rw [h3ComplexifyFourierL2_schwartz_toLp]
  change
    H3FourierL2Hermitian
      (𝓕 ((h3SchwartzComplexify f).toLp 2 volume))
  rw [SchwartzMap.toLp_fourier_eq]
  unfold H3FourierL2Hermitian
  have hAt :=
    SchwartzMap.coeFn_toLp
      (𝓕 (h3SchwartzComplexify f) :
        SchwartzMap H3FourierPoint3 ℂ)
      2 volume
  have hNeg := h3Fourier_ae_neg hAt
  filter_upwards [hAt, hNeg] with ξ hξ hneg
  rw [hneg, hξ]
  exact h3SchwartzComplexify_fourier_hermitian f ξ

/-! ## Density lift to arbitrary real `L²` -/

/-- Complexification as a continuous real-linear map on Fourier-carrier
`L²`. -/
noncomputable def h3ComplexifyFourierL2L :
    H3FourierRealL2 →L[ℝ] H3FourierComplexL2 :=
  ContinuousLinearMap.compLpL 2 volume Complex.ofRealCLM

@[simp]
theorem h3ComplexifyFourierL2L_apply
    (f : H3FourierRealL2) :
    h3ComplexifyFourierL2L f = h3ComplexifyFourierL2 f :=
  rfl

/-- Plancherel Fourier transform of an arbitrary real `L²` field has the
Hermitian frequency symmetry. -/
theorem h3FourierL2_complexify_real_hermitian
    (f : H3FourierRealL2) :
    H3FourierL2Hermitian
      ((MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
        (h3ComplexifyFourierL2 f)) := by
  let T : H3FourierRealL2 → H3FourierComplexL2 :=
    fun g =>
      (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
        (h3ComplexifyFourierL2 g)
  have hT : Continuous T := by
    unfold T
    exact
      (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).continuous.comp
        h3ComplexifyFourierL2L.continuous
  let p : H3FourierRealL2 → Prop :=
    fun g => H3FourierL2Hermitian (T g)
  have hpClosed : IsClosed {g : H3FourierRealL2 | p g} := by
    change IsClosed (T ⁻¹' {G : H3FourierComplexL2 | H3FourierL2Hermitian G})
    exact isClosed_h3FourierL2Hermitian.preimage hT
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM
      (F := ℝ) (p := (2 : ENNReal)) ENNReal.ofNat_ne_top)
    f
  · exact hpClosed
  intro g
  simpa only [p, T, SchwartzMap.toLpCLM_apply] using
    h3FourierL2_complexify_schwartz_hermitian g

/-! ## Genuine encoded restart states -/

/-- One genuine encoded H³ scalar component is raw-Hermitian after exact
H³ deweighting. -/
theorem velocityH3SpectralScalarAt_rawHermitian
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    H3SpectralScalarRawHermitian
      (velocityH3SpectralScalarAt u t hInt hMeas hFourier j) := by
  unfold H3SpectralScalarRawHermitian
  rw [h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
    hFourier j]
  change
    H3FourierL2Hermitian
      (h3ScalarFourierL2
        (velocityH3L2JetAt u t hInt hMeas (h3JetSlot0 j)))
  unfold h3ScalarFourierL2
  exact
    h3FourierL2_complexify_real_hermitian
      (h3ToFourierRealL2
        (velocityH3L2JetAt u t hInt hMeas (h3JetSlot0 j)))

/-- Every genuine encoded real H³ velocity snapshot is raw-Hermitian. -/
theorem velocityH3SpectralStateAt_rawHermitian
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    H3SpectralVelocityRawHermitian
      (velocityH3SpectralStateAt u t hInt hMeas hFourier) := by
  intro j
  change
    H3SpectralScalarRawHermitian
      (velocityH3SpectralScalarAt u t hInt hMeas hFourier j)
  exact velocityH3SpectralScalarAt_rawHermitian hFourier j

/-- Consequently the Banach-selected finite heat--Leray mild solution started
from a genuine encoded real H³ snapshot is raw-Hermitian at every normalized
time. -/
theorem h3SpectralFinHeatLerayMildSolution_encoded_preserves_rawHermitian
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
    H3SpectralVelocityPathRawHermitian
      (h3SpectralFinHeatLerayMildSolution
        hν hτ
        (velocityH3SpectralStateAt u t hInt hMeas hFourier)
        hA hU₀bound hsmall) := by
  exact
    h3SpectralFinHeatLerayMildSolution_preserves_rawHermitian
      hν hτ
      (velocityH3SpectralStateAt u t hInt hMeas hFourier)
      hA hU₀bound hsmall
      (velocityH3SpectralStateAt_rawHermitian hFourier)

end

end Euclidean
end Bridge
end PrimeTensor
