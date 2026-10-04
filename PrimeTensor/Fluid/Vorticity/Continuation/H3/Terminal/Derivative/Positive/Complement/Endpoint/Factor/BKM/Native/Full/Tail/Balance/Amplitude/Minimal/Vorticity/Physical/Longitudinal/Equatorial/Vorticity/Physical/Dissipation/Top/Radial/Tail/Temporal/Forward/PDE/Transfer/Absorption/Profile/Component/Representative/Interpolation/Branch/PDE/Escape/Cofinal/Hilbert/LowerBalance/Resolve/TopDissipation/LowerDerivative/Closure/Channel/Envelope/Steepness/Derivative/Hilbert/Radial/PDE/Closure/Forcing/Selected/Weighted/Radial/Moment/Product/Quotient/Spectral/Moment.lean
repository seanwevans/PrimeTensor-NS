import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Raw
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral


/-!
# Raw moments of the genuine spectral selected slope error

`Raw` proves quantitative moment control for the literal unweighted selected
difference quotient.  `Spectral` supplies the genuine weighted H³ carrier whose
exact deweighting is the raw Fourier slope error.

This file joins those two representations.

For each component of the genuine spectral slope error:

* its deweighted `L²` representative is almost everywhere the common raw slope
  error from `Raw`;
* every natural moment `p ≥ 2` is integrable;
* its canonical raw moment mass is bounded by the already-vanishing order-`p`
  and order-`p+2` radial slope-error norms.

This is the exact input form required by the quantitative convolution/Leray
forcing estimate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedSpectralSlopeMoment
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1800000

/-! ## Raw `L²` representative of the common pointwise error -/

/--
The coordinatewise raw-`L²` slope-error package from `Spectral` has the common
pointwise raw representative introduced in `Raw`.
-/
theorem h3PreterminalSelectedVelocityRawSlopeErrorFourierL2OnSlab_ae_raw
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
    (h : ℝ) :
    (
      (
        h3PreterminalSelectedVelocityRawSlopeErrorFourierL2OnSlab
          hNS ht₀ hE hTail hQ hQR i hx h :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3PreterminalSelectedVelocityRawSlopeErrorFourierOnSlab
      hNS ht₀ hE hTail hQ hQR i hx h := by

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let sx : Set.Icc (Q / 2) Q :=
    ⟨x, hx.1.le, hx.2.le⟩

  let Vh : H3FourierComplexL2 :=
    h3SelectedRestartVelocityRawFourierVector
      hNS ht₀ hE hTail
      (x + h) i

  let V0 : H3FourierComplexL2 :=
    h3SelectedRestartVelocityRawFourierVector
      hNS ht₀ hE hTail
      x i

  let R : H3FourierComplexL2 :=
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
      hNS ht₀ hE hTail
      (h3SelectedProjectedRHSSlabRadius hE hQ hQR sx)
      i

  let R0 : H3FourierComplexL2 :=
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
      0 hNS ht₀ hE hTail hQ hQR i sx

  have hSub :=
    MeasureTheory.Lp.coeFn_sub
      Vh V0

  have hScale :=
    MeasureTheory.Lp.coeFn_smul
      (h⁻¹ : ℝ)
      (Vh - V0)

  have hErr :=
    MeasureTheory.Lp.coeFn_sub
      ((h⁻¹ : ℝ) • (Vh - V0))
      R

  have hR0 :=
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab_ae_eq_radial_projectedRHS
      0 hNS ht₀ hE hTail hQ hQR i sx

  dsimp only at hR0

  change
    (
      (
        ((h⁻¹ : ℝ) • (Vh - V0) - R :
          H3FourierComplexL2)
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3PreterminalSelectedVelocityRawSlopeErrorFourierOnSlab
      hNS ht₀ hE hTail hQ hQR i hx h

  filter_upwards [
    hSub,
    hScale,
    hErr,
    hR0
  ] with ξ hSubξ hScaleξ hErrξ hR0ξ

  rw [hErrξ]
  simp only [Pi.sub_apply]
  rw [hScaleξ]
  simp only [Pi.smul_apply, Complex.real_smul]
  rw [hSubξ]
  simp only [Pi.sub_apply]

  have hR0ξ' :
      R0 ξ = R ξ := by
    simpa only [
      pow_zero,
      Complex.ofReal_one,
      one_mul
    ] using hR0ξ

  rw [← hR0ξ']

  unfold
    h3PreterminalSelectedVelocityRawSlopeErrorFourierOnSlab

  dsimp only [U₀, hA, hU₀, sx, R0, Vh, V0]

  unfold
    h3SelectedRestartVelocityRawFourierVector

  rfl

/-! ## Genuine spectral carrier representative -/

/--
The literal raw Fourier realization of one coordinate of the genuine spectral
slope-error carrier is almost everywhere the common pointwise raw slope error.
-/
theorem h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_ae_raw
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
    (h : ℝ) :
    (fun ξ : H3FourierPoint3 =>
      h3SpectralScalarRawFourier
        (
          h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
            hNS ht₀ hE hTail hQ hQR hx h i
        )
        ξ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3PreterminalSelectedVelocityRawSlopeErrorFourierOnSlab
      hNS ht₀ hE hTail hQ hQR i hx h := by

  let S : H3SpectralScalarState :=
    h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
      hNS ht₀ hE hTail hQ hQR hx h i

  have hRawL2 :=
    h3SpectralScalarRawFourierL2_ae S

  have hExact :=
    h3SpectralScalarRawFourierL2_h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_eq
      hNS ht₀ hE hTail hQ hQR i hx h

  have hCommon :=
    h3PreterminalSelectedVelocityRawSlopeErrorFourierL2OnSlab_ae_raw
      hNS ht₀ hE hTail hQ hQR i hx h

  dsimp only [S] at hRawL2

  rw [hExact] at hRawL2

  exact
    hRawL2.symm.trans hCommon

/-! ## Moment integrability -/

/--
Every natural raw moment `p ≥ 2` of one coordinate of the genuine spectral
slope error is integrable, provided the shifted time remains in the compact
slab.
-/
theorem h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_natMoment_integrable
    (p : ℕ)
    (hp : 2 ≤ p)
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
    H3RawFourierMomentIntegrable
      (p : ℝ)
      (
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
          hNS ht₀ hE hTail hQ hQR hx h i
      ) := by

  have hInt :=
    h3PreterminalSelectedVelocityRawSlopeError_natMoment_integrable
      p hp
      hNS ht₀ hE hTail hQ hQR i hx h hxh

  have hAE :=
    h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_ae_raw
      hNS ht₀ hE hTail hQ hQR i hx h

  unfold H3RawFourierMomentIntegrable

  exact
    hInt.congr
      (by
        filter_upwards [hAE] with ξ hξ
        rw [hξ]
        rw [h3FourierMomentWeight_natCast])

/-! ## Quantitative moment mass -/

/--
The canonical raw order-`p` moment mass of the genuine spectral slope-error
coordinate is bounded by the two neighboring strong radial slope-error norms.
-/
theorem h3SpectralScalarRawFourierMomentMass_h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_le
    (p : ℕ)
    (hp : 2 ≤ p)
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
    h3SpectralScalarRawFourierMomentMass
        (p : ℝ)
        (
          h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
            hNS ht₀ hE hTail hQ hQR hx h i
        )
      ≤
    h3StandardInverseBesselWeightL2Factor *
      (
        ‖h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
            p hp
            hNS ht₀ hE hTail hQ hQR i hx h‖
          +
        ‖h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
            (p + 2) (by omega)
            hNS ht₀ hE hTail hQ hQR i hx h‖
      ) := by

  have hAE :=
    h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_ae_raw
      hNS ht₀ hE hTail hQ hQR i hx h

  have hIntegralEq :
      h3SpectralScalarRawFourierMomentMass
          (p : ℝ)
          (
            h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
              hNS ht₀ hE hTail hQ hQR hx h i
          )
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ p *
          ‖h3PreterminalSelectedVelocityRawSlopeErrorFourierOnSlab
            hNS ht₀ hE hTail hQ hQR i hx h ξ‖
        ∂volume := by

    unfold h3SpectralScalarRawFourierMomentMass

    apply integral_congr_ae

    filter_upwards [hAE] with ξ hξ

    rw [hξ]
    rw [h3FourierMomentWeight_natCast]

  rw [hIntegralEq]

  exact
    integral_h3PreterminalSelectedVelocityRawSlopeError_natMoment_le
      p hp
      hNS ht₀ hE hTail hQ hQR i hx h hxh

end

end Euclidean
end Bridge
end PrimeTensor
