import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.DyadicFourierFactors

/-!
# BKM endpoint: exact L² localization of the physical-vorticity Fourier states

The dyadic kernel and the physical vorticity factors now have exact bundled
Fourier identities.  This file packages the remaining multiplication step.

For a fixed dyadic localized coordinate multiplier `Mᵢₖ,R`, pointwise
multiplication

    F ↦ Mᵢₖ,R F

preserves Fourier `L²` because `|Mᵢₖ,R| ≤ 1`.  We package that operation at the
`Lp` level and prove its canonical representative formula.

The canonical curl states introduced in `DyadicFourierFactors` then localize
exactly to the already-existing localized curl packages from
`LocalizedCurlReconstruction`.  Combining this with the physical-vorticity
Fourier sign identities yields

    M 𝓕ωₓ = -(M C12),
    M 𝓕ωᵧ =   M C02,
    M 𝓕ω_z = -(M C01)

as literal equalities of Fourier `L²` states.

Thus the Fourier-side target of the endpoint Young convolution theorem is now
completely explicit and sign-normalized.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicFourierLocalization
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
Apply one localized BKM coordinate multiplier to an arbitrary Fourier `L²`
state.
-/
noncomputable def h3BKMLocalizedCoordinateMultiplierApplyL2
    (R : ℝ)
    (hR : 0 < R)
    (i k : Fin 3)
    (F : H3FourierComplexL2) :
    H3FourierComplexL2 :=
  (
    h3BKMLocalizedCoordinateMultiplier_mul_memLp2
      hR i k
      (MeasureTheory.Lp.memLp F)
  ).toLp
    (fun ξ : H3FourierPoint3 =>
      h3BKMLocalizedCoordinateMultiplier
          R hR i k ξ
        *
      F ξ)

/-- The localized `L²` package has the expected pointwise representative. -/
theorem h3BKMLocalizedCoordinateMultiplierApplyL2_ae
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (F : H3FourierComplexL2) :
    (h3BKMLocalizedCoordinateMultiplierApplyL2
        R hR i k F :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    fun ξ : H3FourierPoint3 =>
      h3BKMLocalizedCoordinateMultiplier
          R hR i k ξ
        *
      F ξ := by

  unfold h3BKMLocalizedCoordinateMultiplierApplyL2

  exact
    MeasureTheory.MemLp.coeFn_toLp
      (
        h3BKMLocalizedCoordinateMultiplier_mul_memLp2
          hR i k
          (MeasureTheory.Lp.memLp F)
      )

/-! ## Representatives of the existing localized curl L² packages -/

theorem h3BKMLocalizedCanonicalCurl01L2_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    (h3BKMLocalizedCanonicalCurl01L2
        hFourier R hR i k :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    fun ξ : H3FourierPoint3 =>
      h3BKMLocalizedCoordinateMultiplier
          R hR i k ξ
        *
      h3BKMCanonicalCurl01Amplitude
        hInt hMeas ξ := by

  unfold h3BKMLocalizedCanonicalCurl01L2

  exact
    MeasureTheory.MemLp.coeFn_toLp
      (
        h3BKMLocalizedCoordinateMultiplier_mul_canonicalCurl01_memLp2
          hFourier hR i k
      )

theorem h3BKMLocalizedCanonicalCurl02L2_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    (h3BKMLocalizedCanonicalCurl02L2
        hFourier R hR i k :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    fun ξ : H3FourierPoint3 =>
      h3BKMLocalizedCoordinateMultiplier
          R hR i k ξ
        *
      h3BKMCanonicalCurl02Amplitude
        hInt hMeas ξ := by

  unfold h3BKMLocalizedCanonicalCurl02L2

  exact
    MeasureTheory.MemLp.coeFn_toLp
      (
        h3BKMLocalizedCoordinateMultiplier_mul_canonicalCurl02_memLp2
          hFourier hR i k
      )

theorem h3BKMLocalizedCanonicalCurl12L2_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    (h3BKMLocalizedCanonicalCurl12L2
        hFourier R hR i k :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    fun ξ : H3FourierPoint3 =>
      h3BKMLocalizedCoordinateMultiplier
          R hR i k ξ
        *
      h3BKMCanonicalCurl12Amplitude
        hInt hMeas ξ := by

  unfold h3BKMLocalizedCanonicalCurl12L2

  exact
    MeasureTheory.MemLp.coeFn_toLp
      (
        h3BKMLocalizedCoordinateMultiplier_mul_canonicalCurl12_memLp2
          hFourier hR i k
      )

/-! ## Localization commutes with the canonical curl L² packaging -/

theorem h3BKMLocalizedCoordinateMultiplierApplyL2_curl01
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    h3BKMLocalizedCoordinateMultiplierApplyL2
        R hR i k
        (h3BKMCanonicalCurl01L2 hFourier)
      =
    h3BKMLocalizedCanonicalCurl01L2
      hFourier R hR i k := by

  apply MeasureTheory.Lp.ext

  filter_upwards [
    h3BKMLocalizedCoordinateMultiplierApplyL2_ae
      hR i k (h3BKMCanonicalCurl01L2 hFourier),
    h3BKMCanonicalCurl01L2_ae hFourier,
    h3BKMLocalizedCanonicalCurl01L2_ae
      hFourier hR i k
  ] with ξ hApply hCurl hLocalized

  rw [hApply, hCurl, hLocalized]

theorem h3BKMLocalizedCoordinateMultiplierApplyL2_curl02
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    h3BKMLocalizedCoordinateMultiplierApplyL2
        R hR i k
        (h3BKMCanonicalCurl02L2 hFourier)
      =
    h3BKMLocalizedCanonicalCurl02L2
      hFourier R hR i k := by

  apply MeasureTheory.Lp.ext

  filter_upwards [
    h3BKMLocalizedCoordinateMultiplierApplyL2_ae
      hR i k (h3BKMCanonicalCurl02L2 hFourier),
    h3BKMCanonicalCurl02L2_ae hFourier,
    h3BKMLocalizedCanonicalCurl02L2_ae
      hFourier hR i k
  ] with ξ hApply hCurl hLocalized

  rw [hApply, hCurl, hLocalized]

theorem h3BKMLocalizedCoordinateMultiplierApplyL2_curl12
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    h3BKMLocalizedCoordinateMultiplierApplyL2
        R hR i k
        (h3BKMCanonicalCurl12L2 hFourier)
      =
    h3BKMLocalizedCanonicalCurl12L2
      hFourier R hR i k := by

  apply MeasureTheory.Lp.ext

  filter_upwards [
    h3BKMLocalizedCoordinateMultiplierApplyL2_ae
      hR i k (h3BKMCanonicalCurl12L2 hFourier),
    h3BKMCanonicalCurl12L2_ae hFourier,
    h3BKMLocalizedCanonicalCurl12L2_ae
      hFourier hR i k
  ] with ξ hApply hCurl hLocalized

  rw [hApply, hCurl, hLocalized]

/-! ## Exact localized Fourier states of physical vorticity -/

/--
Localized Fourier transform of physical x-vorticity is minus the localized
`C12` state.
-/
theorem h3BKMLocalizedCoordinateMultiplierApplyL2_physicalVorticityX_fourier
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    h3BKMLocalizedCoordinateMultiplierApplyL2
        R hR i k
        (h3ScalarFourierL2
          (h3BKMPhysicalVorticityXL2
            u t hInt hMeas))
      =
    - h3BKMLocalizedCanonicalCurl12L2
        hFourier R hR i k := by

  apply MeasureTheory.Lp.ext

  filter_upwards [
    h3BKMLocalizedCoordinateMultiplierApplyL2_ae
      hR i k
      (h3ScalarFourierL2
        (h3BKMPhysicalVorticityXL2 u t hInt hMeas)),
    h3BKMPhysicalVorticityXL2_fourier_ae_eq_neg_curl12 hFourier,
    h3BKMLocalizedCanonicalCurl12L2_ae
      hFourier hR i k,
    MeasureTheory.Lp.coeFn_neg
      (h3BKMLocalizedCanonicalCurl12L2
        hFourier R hR i k)
  ] with ξ hApply hPhysical hLocalized hNeg

  rw [hApply, hPhysical, hNeg]
  simp only [Pi.neg_apply]
  rw [hLocalized]
  ring

/--
Localized Fourier transform of physical y-vorticity is the localized `C02`
state.
-/
theorem h3BKMLocalizedCoordinateMultiplierApplyL2_physicalVorticityY_fourier
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    h3BKMLocalizedCoordinateMultiplierApplyL2
        R hR i k
        (h3ScalarFourierL2
          (h3BKMPhysicalVorticityYL2
            u t hInt hMeas))
      =
    h3BKMLocalizedCanonicalCurl02L2
      hFourier R hR i k := by

  apply MeasureTheory.Lp.ext

  filter_upwards [
    h3BKMLocalizedCoordinateMultiplierApplyL2_ae
      hR i k
      (h3ScalarFourierL2
        (h3BKMPhysicalVorticityYL2 u t hInt hMeas)),
    h3BKMPhysicalVorticityYL2_fourier_ae_eq_curl02 hFourier,
    h3BKMLocalizedCanonicalCurl02L2_ae
      hFourier hR i k
  ] with ξ hApply hPhysical hLocalized

  rw [hApply, hPhysical, hLocalized]

/--
Localized Fourier transform of physical z-vorticity is minus the localized
`C01` state.
-/
theorem h3BKMLocalizedCoordinateMultiplierApplyL2_physicalVorticityZ_fourier
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    h3BKMLocalizedCoordinateMultiplierApplyL2
        R hR i k
        (h3ScalarFourierL2
          (h3BKMPhysicalVorticityZL2
            u t hInt hMeas))
      =
    - h3BKMLocalizedCanonicalCurl01L2
        hFourier R hR i k := by

  apply MeasureTheory.Lp.ext

  filter_upwards [
    h3BKMLocalizedCoordinateMultiplierApplyL2_ae
      hR i k
      (h3ScalarFourierL2
        (h3BKMPhysicalVorticityZL2 u t hInt hMeas)),
    h3BKMPhysicalVorticityZL2_fourier_ae_eq_neg_curl01 hFourier,
    h3BKMLocalizedCanonicalCurl01L2_ae
      hFourier hR i k,
    MeasureTheory.Lp.coeFn_neg
      (h3BKMLocalizedCanonicalCurl01L2
        hFourier R hR i k)
  ] with ξ hApply hPhysical hLocalized hNeg

  rw [hApply, hPhysical, hNeg]
  simp only [Pi.neg_apply]
  rw [hLocalized]
  ring

end

end Euclidean
end Bridge
end PrimeTensor
