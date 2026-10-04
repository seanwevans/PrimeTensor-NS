import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.NineQuarter.Convolution.Majorant.Mass

/-!
# Vanishing raw L¹ mass of the selected spectral slope error

The inverse-Bessel bridge used for positive radial moments also applies at
order zero.

For the common raw selected slope error, the order-zero input is the already
packaged raw Fourier `L²` slope error and the neighboring order-two input is
the compiled second-radial slope error.  Hence

    ‖E_raw(h)‖_{L¹}
      ≤
    C_Bessel (‖E_0(h)‖_{L²} + ‖E_2(h)‖_{L²}).

Both terms on the right tend to zero.  After transferring through the exact
spectral/raw representative bridge, the canonical raw `L¹` mass of every
coordinate of the genuine spectral slope error also tends to zero.

This supplies the missing low-frequency factor for the subsequent
Young/convolution estimate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedSpectralSlopeL1Limit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1800000

/-! ## Order-zero inverse-Bessel bridge -/

/--
The common raw selected slope error is integrable without a radial weight.
The two `L²` inputs are exactly the unweighted raw slope-error package and the
order-two radial slope-error package.
-/
theorem h3PreterminalSelectedVelocityRawSlopeError_integrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q)
    (h : ℝ)
    (hxh : x + h ∈ Set.Icc (Q / 2) Q) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖h3PreterminalSelectedVelocityRawSlopeErrorFourierOnSlab
          hNS ht₀ hE hTail hQ hQR i hx h ξ‖)
      (volume : Measure H3FourierPoint3) := by

  let F : H3FourierPoint3 → ℂ :=
    h3PreterminalSelectedVelocityRawSlopeErrorFourierOnSlab
      hNS ht₀ hE hTail hQ hQR i hx h

  let G0 : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityRawSlopeErrorFourierL2OnSlab
      hNS ht₀ hE hTail hQ hQR i hx h

  let G2 : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
      2 (by norm_num)
      hNS ht₀ hE hTail hQ hQR i hx h

  have hG0Base :=
    h3PreterminalSelectedVelocityRawSlopeErrorFourierL2OnSlab_ae_raw
      hNS ht₀ hE hTail hQ hQR i hx h

  have hG2Base :=
    h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab_ae_raw
      2 (by norm_num)
      hNS ht₀ hE hTail hQ hQR i hx h hxh

  have hG0 :
      ((G0 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ 0 : ℝ) : ℂ) * F ξ) := by
    simpa only [
      F,
      G0,
      pow_zero,
      Complex.ofReal_one,
      one_mul
    ] using hG0Base

  have hG2 :
      ((G2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ (0 + 2) : ℝ) : ℂ) * F ξ) := by
    simpa only [
      F,
      G2,
      zero_add
    ] using hG2Base

  have hInt :=
    h3RawFourier_natMoment_integrable_of_two_radialL2
      0 F G0 G2 hG0 hG2

  simpa only [
    F,
    pow_zero,
    one_mul
  ] using hInt

/--
Quantitative unweighted raw `L¹` bound for the common slope error.
-/
theorem integral_h3PreterminalSelectedVelocityRawSlopeError_le_bessel_mul_norms
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q)
    (h : ℝ)
    (hxh : x + h ∈ Set.Icc (Q / 2) Q) :
    (∫ ξ : H3FourierPoint3,
        ‖h3PreterminalSelectedVelocityRawSlopeErrorFourierOnSlab
          hNS ht₀ hE hTail hQ hQR i hx h ξ‖
      ∂volume)
      ≤
    h3StandardInverseBesselWeightL2Factor *
      (
        ‖h3PreterminalSelectedVelocityRawSlopeErrorFourierL2OnSlab
            hNS ht₀ hE hTail hQ hQR i hx h‖
          +
        ‖h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
            2 (by norm_num)
            hNS ht₀ hE hTail hQ hQR i hx h‖
      ) := by

  let F : H3FourierPoint3 → ℂ :=
    h3PreterminalSelectedVelocityRawSlopeErrorFourierOnSlab
      hNS ht₀ hE hTail hQ hQR i hx h

  let G0 : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityRawSlopeErrorFourierL2OnSlab
      hNS ht₀ hE hTail hQ hQR i hx h

  let G2 : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
      2 (by norm_num)
      hNS ht₀ hE hTail hQ hQR i hx h

  have hG0Base :=
    h3PreterminalSelectedVelocityRawSlopeErrorFourierL2OnSlab_ae_raw
      hNS ht₀ hE hTail hQ hQR i hx h

  have hG2Base :=
    h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab_ae_raw
      2 (by norm_num)
      hNS ht₀ hE hTail hQ hQR i hx h hxh

  have hG0 :
      ((G0 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ 0 : ℝ) : ℂ) * F ξ) := by
    simpa only [
      F,
      G0,
      pow_zero,
      Complex.ofReal_one,
      one_mul
    ] using hG0Base

  have hG2 :
      ((G2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ (0 + 2) : ℝ) : ℂ) * F ξ) := by
    simpa only [
      F,
      G2,
      zero_add
    ] using hG2Base

  have hBound :=
    integral_h3RawFourier_natMoment_le_bessel_mul_norms
      0 F G0 G2 hG0 hG2

  simpa only [
    F,
    G0,
    G2,
    pow_zero,
    one_mul
  ] using hBound

/-! ## Transfer to the genuine spectral carrier -/

/--
The canonical raw `L¹` mass of one coordinate of the genuine spectral slope
error is bounded by the unweighted and order-two strong slope-error norms.
-/
theorem h3SpectralScalarRawFourierL1Mass_h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_le
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q)
    (h : ℝ)
    (hxh : x + h ∈ Set.Icc (Q / 2) Q) :
    h3SpectralScalarRawFourierL1Mass
        (
          h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
            hNS ht₀ hE hTail hQ hQR hx h i
        )
      ≤
    h3StandardInverseBesselWeightL2Factor *
      (
        ‖h3PreterminalSelectedVelocityRawSlopeErrorFourierL2OnSlab
            hNS ht₀ hE hTail hQ hQR i hx h‖
          +
        ‖h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
            2 (by norm_num)
            hNS ht₀ hE hTail hQ hQR i hx h‖
      ) := by

  have hAE :=
    h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_ae_raw
      hNS ht₀ hE hTail hQ hQR i hx h

  have hMassEq :
      h3SpectralScalarRawFourierL1Mass
          (
            h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
              hNS ht₀ hE hTail hQ hQR hx h i
          )
        =
      ∫ ξ : H3FourierPoint3,
        ‖h3PreterminalSelectedVelocityRawSlopeErrorFourierOnSlab
          hNS ht₀ hE hTail hQ hQR i hx h ξ‖
        ∂volume := by

    unfold h3SpectralScalarRawFourierL1Mass

    apply integral_congr_ae

    filter_upwards [hAE] with ξ hξ

    rw [hξ]

  rw [hMassEq]

  exact
    integral_h3PreterminalSelectedVelocityRawSlopeError_le_bessel_mul_norms
      hNS ht₀ hE hTail hQ hQR i hx h hxh

/--
The raw `L¹` mass of every coordinate of the genuine spectral slope error
vanishes with the increment.
-/
theorem tendsto_h3SpectralScalarRawFourierL1Mass_h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_zero
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q) :
    Tendsto
      (fun h : ℝ =>
        h3SpectralScalarRawFourierL1Mass
          (
            h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
              hNS ht₀ hE hTail hQ hQR hx h i
          ))
      (𝓝[≠] (0 : ℝ))
      (𝓝 0) := by

  let M : ℝ → ℝ :=
    fun h =>
      h3SpectralScalarRawFourierL1Mass
        (
          h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
            hNS ht₀ hE hTail hQ hQR hx h i
        )

  let C : ℝ :=
    h3StandardInverseBesselWeightL2Factor

  let U : ℝ → ℝ :=
    fun h =>
      C *
        (
          ‖h3PreterminalSelectedVelocityRawSlopeErrorFourierL2OnSlab
              hNS ht₀ hE hTail hQ hQR i hx h‖
            +
          ‖h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
              2 (by norm_num)
              hNS ht₀ hE hTail hQ hQR i hx h‖
        )

  have hRaw :=
    tendsto_norm_h3PreterminalSelectedVelocityRawSlopeErrorFourierL2OnSlab_zero
      hNS ht₀ hE hTail hQ hQR i hx

  have hRadial :=
    tendsto_norm_h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab_zero
      2 (by norm_num)
      hNS ht₀ hE hTail hQ hQR i hx

  have hSum :
      Tendsto
        (fun h : ℝ =>
          ‖h3PreterminalSelectedVelocityRawSlopeErrorFourierL2OnSlab
              hNS ht₀ hE hTail hQ hQR i hx h‖
            +
          ‖h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
              2 (by norm_num)
              hNS ht₀ hE hTail hQ hQR i hx h‖)
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by
    simpa only [zero_add] using hRaw.add hRadial

  have hUpperTend :
      Tendsto U (𝓝[≠] (0 : ℝ)) (𝓝 0) := by

    have hConst :
        Tendsto
          (fun _h : ℝ => C)
          (𝓝[≠] (0 : ℝ))
          (𝓝 C) :=
      tendsto_const_nhds

    have hMul :=
      hConst.mul hSum

    simpa only [U, mul_zero] using hMul

  have hhZero :
      Tendsto
        (fun h : ℝ => h)
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds

  have hArg :
      Tendsto
        (fun h : ℝ => x + h)
        (𝓝[≠] (0 : ℝ))
        (𝓝 x) := by
    simpa only [add_zero] using
      tendsto_const_nhds.add hhZero

  have hInterior :
      Set.Icc (Q / 2) Q ∈ 𝓝 x :=
    Icc_mem_nhds hx.1 hx.2

  have hArgInterior :
      ∀ᶠ h : ℝ in (𝓝[≠] (0 : ℝ)),
        x + h ∈ Set.Icc (Q / 2) Q :=
    hArg.eventually hInterior

  have hNonneg :
      ∀ᶠ h : ℝ in (𝓝[≠] (0 : ℝ)),
        0 ≤ M h := by
    exact
      Filter.Eventually.of_forall
        (fun h => by
          dsimp only [M]
          unfold h3SpectralScalarRawFourierL1Mass
          exact integral_nonneg (fun ξ => norm_nonneg _))

  have hUpper :
      ∀ᶠ h : ℝ in (𝓝[≠] (0 : ℝ)),
        M h ≤ U h := by

    filter_upwards [hArgInterior] with h hxh

    have hBound :=
      h3SpectralScalarRawFourierL1Mass_h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_le
        hNS ht₀ hE hTail hQ hQR i hx h hxh

    simpa only [M, U, C] using hBound

  exact
    squeeze_zero'
      hNonneg
      hUpper
      hUpperTend

end

end Euclidean
end Bridge
end PrimeTensor
