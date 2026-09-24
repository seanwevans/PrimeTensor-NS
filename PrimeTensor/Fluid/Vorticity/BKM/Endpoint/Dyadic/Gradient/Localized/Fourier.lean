import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Dyadic.Gradient.Localized.Physical
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Gradient.Localized.Multiplier

/-!
# BKM endpoint: Fourier identification of one-shell localized gradient states

`DyadicLocalizedGradientPhysical` constructed the three physical `L²` states

    G₀,R = C01⁻¹(i,1) + C02⁻¹(i,2),
    G₁,R = C12⁻¹(i,2) - C01⁻¹(i,0),
    G₂,R = -(C02⁻¹(i,0) + C12⁻¹(i,1)),

and proved their uniform physical bounds.

This file identifies those states spectrally.  Since every localized curl
inverse state is literally the inverse unitary Fourier transform of its
localized curl package, the forward transform of each `Gⱼ,R` is exactly the
corresponding localized Biot--Savart combination.

The existing one-shell multiplier identities then show, almost everywhere on
a canonical H³ slice,

    𝓕 Gⱼ,R(ξ)
      = ψ_R(ξ) * (dᵢ(ξ) * ûⱼ(ξ)).

Thus the physically bounded states constructed in the previous checkpoints
are exactly the one-shell localized velocity-gradient states, not merely
proxy combinations of vorticity convolutions.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicLocalizedGradientFourier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Exact bundled Fourier identities -/

/--
Forward Fourier transform of the target-component `0` one-shell inverse state.
-/
theorem h3BKMDyadicLocalizedGradientComponent0InverseL2_fourier_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i : Fin 3) :
    (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
      (h3BKMDyadicLocalizedGradientComponent0InverseL2
        hFourier R hR i)
      =
    h3BKMLocalizedCanonicalCurl01L2
        hFourier R hR i 1
      +
    h3BKMLocalizedCanonicalCurl02L2
        hFourier R hR i 2 := by

  let T :=
    MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ

  change
    T
      (h3BKMDyadicLocalizedGradientComponent0InverseL2
        hFourier R hR i)
      =
    h3BKMLocalizedCanonicalCurl01L2
        hFourier R hR i 1
      +
    h3BKMLocalizedCanonicalCurl02L2
        hFourier R hR i 2

  unfold h3BKMDyadicLocalizedGradientComponent0InverseL2

  calc
    T
      (h3BKMLocalizedCanonicalCurl01InverseL2
          hFourier R hR i 1
        +
       h3BKMLocalizedCanonicalCurl02InverseL2
          hFourier R hR i 2)
        =
      T
        (h3BKMLocalizedCanonicalCurl01InverseL2
          hFourier R hR i 1)
        +
      T
        (h3BKMLocalizedCanonicalCurl02InverseL2
          hFourier R hR i 2) := by
            exact T.map_add _ _

    _ =
      h3BKMLocalizedCanonicalCurl01L2
          hFourier R hR i 1
        +
      h3BKMLocalizedCanonicalCurl02L2
          hFourier R hR i 2 := by
            unfold
              h3BKMLocalizedCanonicalCurl01InverseL2
              h3BKMLocalizedCanonicalCurl02InverseL2
            rw [
              T.apply_symm_apply,
              T.apply_symm_apply
            ]

/--
Forward Fourier transform of the target-component `1` one-shell inverse state.
-/
theorem h3BKMDyadicLocalizedGradientComponent1InverseL2_fourier_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i : Fin 3) :
    (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
      (h3BKMDyadicLocalizedGradientComponent1InverseL2
        hFourier R hR i)
      =
    h3BKMLocalizedCanonicalCurl12L2
        hFourier R hR i 2
      -
    h3BKMLocalizedCanonicalCurl01L2
        hFourier R hR i 0 := by

  let T :=
    MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ

  change
    T
      (h3BKMDyadicLocalizedGradientComponent1InverseL2
        hFourier R hR i)
      =
    h3BKMLocalizedCanonicalCurl12L2
        hFourier R hR i 2
      -
    h3BKMLocalizedCanonicalCurl01L2
        hFourier R hR i 0

  unfold h3BKMDyadicLocalizedGradientComponent1InverseL2

  calc
    T
      (h3BKMLocalizedCanonicalCurl12InverseL2
          hFourier R hR i 2
        -
       h3BKMLocalizedCanonicalCurl01InverseL2
          hFourier R hR i 0)
        =
      T
        (h3BKMLocalizedCanonicalCurl12InverseL2
          hFourier R hR i 2)
        -
      T
        (h3BKMLocalizedCanonicalCurl01InverseL2
          hFourier R hR i 0) := by
            exact T.map_sub _ _

    _ =
      h3BKMLocalizedCanonicalCurl12L2
          hFourier R hR i 2
        -
      h3BKMLocalizedCanonicalCurl01L2
          hFourier R hR i 0 := by
            unfold
              h3BKMLocalizedCanonicalCurl12InverseL2
              h3BKMLocalizedCanonicalCurl01InverseL2
            rw [
              T.apply_symm_apply,
              T.apply_symm_apply
            ]

/--
Forward Fourier transform of the target-component `2` one-shell inverse state.
-/
theorem h3BKMDyadicLocalizedGradientComponent2InverseL2_fourier_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i : Fin 3) :
    (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
      (h3BKMDyadicLocalizedGradientComponent2InverseL2
        hFourier R hR i)
      =
    -
      (
        h3BKMLocalizedCanonicalCurl02L2
            hFourier R hR i 0
          +
        h3BKMLocalizedCanonicalCurl12L2
            hFourier R hR i 1
      ) := by

  let T :=
    MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ

  change
    T
      (h3BKMDyadicLocalizedGradientComponent2InverseL2
        hFourier R hR i)
      =
    -
      (
        h3BKMLocalizedCanonicalCurl02L2
            hFourier R hR i 0
          +
        h3BKMLocalizedCanonicalCurl12L2
            hFourier R hR i 1
      )

  unfold h3BKMDyadicLocalizedGradientComponent2InverseL2

  calc
    T
      (-
        (
          h3BKMLocalizedCanonicalCurl02InverseL2
              hFourier R hR i 0
            +
          h3BKMLocalizedCanonicalCurl12InverseL2
              hFourier R hR i 1
        ))
        =
      -
        T
          (
            h3BKMLocalizedCanonicalCurl02InverseL2
                hFourier R hR i 0
              +
            h3BKMLocalizedCanonicalCurl12InverseL2
                hFourier R hR i 1
          ) := by
            exact
              T.map_neg
                (
                  h3BKMLocalizedCanonicalCurl02InverseL2
                      hFourier R hR i 0
                    +
                  h3BKMLocalizedCanonicalCurl12InverseL2
                      hFourier R hR i 1
                )

    _ =
      -
        (
          T
            (h3BKMLocalizedCanonicalCurl02InverseL2
              hFourier R hR i 0)
            +
          T
            (h3BKMLocalizedCanonicalCurl12InverseL2
              hFourier R hR i 1)
        ) := by
          rw [T.map_add]

    _ =
      -
        (
          h3BKMLocalizedCanonicalCurl02L2
              hFourier R hR i 0
            +
          h3BKMLocalizedCanonicalCurl12L2
              hFourier R hR i 1
        ) := by
          unfold
            h3BKMLocalizedCanonicalCurl02InverseL2
            h3BKMLocalizedCanonicalCurl12InverseL2
          rw [
            T.apply_symm_apply,
            T.apply_symm_apply
          ]

/-! ## Canonical one-shell gradient representatives -/

/--
The Fourier transform of the target-component `0` one-shell state is exactly
the shell-localized canonical first derivative almost everywhere.
-/
theorem h3BKMDyadicLocalizedGradientComponent0InverseL2_fourier_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t R : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hR : 0 < R)
    (i : Fin 3) :
    ((MeasureTheory.Lp.fourierTransformₗᵢ
        H3FourierPoint3 ℂ)
      (h3BKMDyadicLocalizedGradientComponent0InverseL2
        hFourier R hR i) :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    fun ξ : H3FourierPoint3 =>
      (h3BKMFrequencyShell R hR ξ : ℂ)
        *
      (
        h3FourierDerivativeSymbol i ξ
          *
        velocityH3BaseFourierAt
          u t hInt hMeas 0 ξ
      ) := by

  rw [
    h3BKMDyadicLocalizedGradientComponent0InverseL2_fourier_eq
      hFourier hR i
  ]

  filter_upwards [
    MeasureTheory.Lp.coeFn_add
      (h3BKMLocalizedCanonicalCurl01L2
        hFourier R hR i 1)
      (h3BKMLocalizedCanonicalCurl02L2
        hFourier R hR i 2),
    h3BKMLocalizedCanonicalCurl01L2_ae
      hFourier hR i 1,
    h3BKMLocalizedCanonicalCurl02L2_ae
      hFourier hR i 2,
    velocityH3BaseFourier_frequencyShell_gradient_component0_eq_localizedCurl_ae
      hNS ht hFourier hR
  ] with ξ hAdd h01 h02 hGradient

  rw [hAdd]
  simp only [Pi.add_apply]
  rw [h01, h02]

  exact (hGradient i).symm

/--
The Fourier transform of the target-component `1` one-shell state is exactly
the shell-localized canonical first derivative almost everywhere.
-/
theorem h3BKMDyadicLocalizedGradientComponent1InverseL2_fourier_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t R : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hR : 0 < R)
    (i : Fin 3) :
    ((MeasureTheory.Lp.fourierTransformₗᵢ
        H3FourierPoint3 ℂ)
      (h3BKMDyadicLocalizedGradientComponent1InverseL2
        hFourier R hR i) :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    fun ξ : H3FourierPoint3 =>
      (h3BKMFrequencyShell R hR ξ : ℂ)
        *
      (
        h3FourierDerivativeSymbol i ξ
          *
        velocityH3BaseFourierAt
          u t hInt hMeas 1 ξ
      ) := by

  rw [
    h3BKMDyadicLocalizedGradientComponent1InverseL2_fourier_eq
      hFourier hR i
  ]

  filter_upwards [
    MeasureTheory.Lp.coeFn_sub
      (h3BKMLocalizedCanonicalCurl12L2
        hFourier R hR i 2)
      (h3BKMLocalizedCanonicalCurl01L2
        hFourier R hR i 0),
    h3BKMLocalizedCanonicalCurl12L2_ae
      hFourier hR i 2,
    h3BKMLocalizedCanonicalCurl01L2_ae
      hFourier hR i 0,
    velocityH3BaseFourier_frequencyShell_gradient_component1_eq_localizedCurl_ae
      hNS ht hFourier hR
  ] with ξ hSub h12 h01 hGradient

  rw [hSub]
  simp only [Pi.sub_apply]
  rw [h12, h01, hGradient i]

  ring

/--
The Fourier transform of the target-component `2` one-shell state is exactly
the shell-localized canonical first derivative almost everywhere.
-/
theorem h3BKMDyadicLocalizedGradientComponent2InverseL2_fourier_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t R : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hR : 0 < R)
    (i : Fin 3) :
    ((MeasureTheory.Lp.fourierTransformₗᵢ
        H3FourierPoint3 ℂ)
      (h3BKMDyadicLocalizedGradientComponent2InverseL2
        hFourier R hR i) :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    fun ξ : H3FourierPoint3 =>
      (h3BKMFrequencyShell R hR ξ : ℂ)
        *
      (
        h3FourierDerivativeSymbol i ξ
          *
        velocityH3BaseFourierAt
          u t hInt hMeas 2 ξ
      ) := by

  rw [
    h3BKMDyadicLocalizedGradientComponent2InverseL2_fourier_eq
      hFourier hR i
  ]

  let A :=
    h3BKMLocalizedCanonicalCurl02L2
      hFourier R hR i 0

  let B :=
    h3BKMLocalizedCanonicalCurl12L2
      hFourier R hR i 1

  have hNeg :=
    MeasureTheory.Lp.coeFn_neg
      (A + B)

  have hAdd :=
    MeasureTheory.Lp.coeFn_add A B

  have h02 :=
    h3BKMLocalizedCanonicalCurl02L2_ae
      hFourier hR i 0

  have h12 :=
    h3BKMLocalizedCanonicalCurl12L2_ae
      hFourier hR i 1

  have hGradient :=
    velocityH3BaseFourier_frequencyShell_gradient_component2_eq_localizedCurl_ae
      hNS ht hFourier hR

  filter_upwards [
    hNeg,
    hAdd,
    h02,
    h12,
    hGradient
  ] with ξ hNegξ hAddξ h02ξ h12ξ hGradientξ

  dsimp only [A, B] at hNegξ hAddξ

  rw [hNegξ]
  simp only [Pi.neg_apply]
  rw [hAddξ]
  simp only [Pi.add_apply]
  rw [h02ξ, h12ξ, hGradientξ i]

  ring

end

end Euclidean
end Bridge
end PrimeTensor
