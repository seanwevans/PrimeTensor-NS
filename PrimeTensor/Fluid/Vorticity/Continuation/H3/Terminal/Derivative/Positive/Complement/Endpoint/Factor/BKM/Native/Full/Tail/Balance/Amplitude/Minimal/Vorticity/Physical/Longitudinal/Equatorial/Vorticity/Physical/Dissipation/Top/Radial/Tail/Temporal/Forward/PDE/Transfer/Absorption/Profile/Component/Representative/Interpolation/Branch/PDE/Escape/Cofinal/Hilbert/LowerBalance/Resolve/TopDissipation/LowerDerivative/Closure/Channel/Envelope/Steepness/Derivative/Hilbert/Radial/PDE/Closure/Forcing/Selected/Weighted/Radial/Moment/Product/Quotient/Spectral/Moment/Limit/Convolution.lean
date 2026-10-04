import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.L1
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.Moment.Convolution

/-!
# Vanishing convolution moments with one spectral slope-error input

The genuine selected spectral slope error now has both of the scalar limits
needed by the generic Young moment inequality:

* its raw order-`p` moment mass tends to zero for every natural `p ≥ 2`;
* its raw `L¹` mass tends to zero.

Against any fixed spectral scalar state carrying the same `p`-moment,
the raw product-convolution `p`-moment therefore tends to zero.  We record
both bilinear orientations because the Leray forcing quotient uses both.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedSpectralSlopeConvolutionLimit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1800000

/--
With the selected spectral slope error in the left slot and a fixed state in
the right slot, the raw order-`p` convolution moment tends to zero.
-/
theorem tendsto_h3RawProductConvolutionMomentMass_spectralSlopeError_left_zero
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
    (G : H3SpectralScalarState)
    (hG : H3RawFourierMomentIntegrable (p : ℝ) G) :
    Tendsto
      (fun h : ℝ =>
        h3RawProductConvolutionMomentMass
          (p : ℝ)
          (
            h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
              hNS ht₀ hE hTail hQ hQR hx h i
          )
          G)
      (𝓝[≠] (0 : ℝ))
      (𝓝 0) := by

  let S : ℝ → H3SpectralScalarState :=
    fun h =>
      h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
        hNS ht₀ hE hTail hQ hQR hx h i

  let M : ℝ → ℝ :=
    fun h =>
      h3RawProductConvolutionMomentMass
        (p : ℝ) (S h) G

  let C : ℝ :=
    h3FourierMomentSplitCoefficient (p : ℝ)

  let U : ℝ → ℝ :=
    fun h =>
      C *
        (
          h3SpectralScalarRawFourierMomentMass
              (p : ℝ) (S h) *
            h3SpectralScalarRawFourierL1Mass G
          +
          h3SpectralScalarRawFourierL1Mass (S h) *
            h3SpectralScalarRawFourierMomentMass
              (p : ℝ) G
        )

  have hMoment :=
    tendsto_h3SpectralScalarRawFourierMomentMass_h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_zero
      p hp
      hNS ht₀ hE hTail hQ hQR i hx

  have hL1 :=
    tendsto_h3SpectralScalarRawFourierL1Mass_h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_zero
      hNS ht₀ hE hTail hQ hQR i hx

  have hMomentMul :
      Tendsto
        (fun h : ℝ =>
          h3SpectralScalarRawFourierMomentMass
              (p : ℝ) (S h) *
            h3SpectralScalarRawFourierL1Mass G)
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by

    have hConst :
        Tendsto
          (fun _h : ℝ =>
            h3SpectralScalarRawFourierL1Mass G)
          (𝓝[≠] (0 : ℝ))
          (𝓝 (h3SpectralScalarRawFourierL1Mass G)) :=
      tendsto_const_nhds

    have hMul := hMoment.mul hConst

    simpa only [S, zero_mul] using hMul

  have hL1Mul :
      Tendsto
        (fun h : ℝ =>
          h3SpectralScalarRawFourierL1Mass (S h) *
            h3SpectralScalarRawFourierMomentMass
              (p : ℝ) G)
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by

    have hConst :
        Tendsto
          (fun _h : ℝ =>
            h3SpectralScalarRawFourierMomentMass
              (p : ℝ) G)
          (𝓝[≠] (0 : ℝ))
          (𝓝
            (h3SpectralScalarRawFourierMomentMass
              (p : ℝ) G)) :=
      tendsto_const_nhds

    have hMul := hL1.mul hConst

    simpa only [S, zero_mul] using hMul

  have hInside :
      Tendsto
        (fun h : ℝ =>
          h3SpectralScalarRawFourierMomentMass
              (p : ℝ) (S h) *
            h3SpectralScalarRawFourierL1Mass G
          +
          h3SpectralScalarRawFourierL1Mass (S h) *
            h3SpectralScalarRawFourierMomentMass
              (p : ℝ) G)
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by
    simpa only [zero_add] using hMomentMul.add hL1Mul

  have hUpperTend :
      Tendsto U (𝓝[≠] (0 : ℝ)) (𝓝 0) := by

    have hConst :
        Tendsto
          (fun _h : ℝ => C)
          (𝓝[≠] (0 : ℝ))
          (𝓝 C) :=
      tendsto_const_nhds

    have hMul := hConst.mul hInside

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
          unfold h3RawProductConvolutionMomentMass
          exact
            integral_nonneg
              (fun ξ =>
                mul_nonneg
                  (h3FourierMomentWeight_nonneg (p : ℝ) ξ)
                  (norm_nonneg _)))

  have hUpper :
      ∀ᶠ h : ℝ in (𝓝[≠] (0 : ℝ)),
        M h ≤ U h := by

    filter_upwards [hArgInterior] with h hxh

    have hS :
        H3RawFourierMomentIntegrable
          (p : ℝ) (S h) := by
      dsimp only [S]
      exact
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_natMoment_integrable
          p hp
          hNS ht₀ hE hTail hQ hQR i hx h hxh

    have hBound :=
      h3RawProductConvolutionMomentMass_le
        (q := (p : ℝ))
        (by positivity)
        (S h) G hS hG

    simpa only [M, U, C] using hBound

  exact
    squeeze_zero'
      hNonneg
      hUpper
      hUpperTend

/--
With a fixed state in the left slot and the selected spectral slope error in
the right slot, the raw order-`p` convolution moment tends to zero.
-/
theorem tendsto_h3RawProductConvolutionMomentMass_spectralSlopeError_right_zero
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
    (G : H3SpectralScalarState)
    (hG : H3RawFourierMomentIntegrable (p : ℝ) G) :
    Tendsto
      (fun h : ℝ =>
        h3RawProductConvolutionMomentMass
          (p : ℝ)
          G
          (
            h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
              hNS ht₀ hE hTail hQ hQR hx h i
          ))
      (𝓝[≠] (0 : ℝ))
      (𝓝 0) := by

  let S : ℝ → H3SpectralScalarState :=
    fun h =>
      h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
        hNS ht₀ hE hTail hQ hQR hx h i

  let M : ℝ → ℝ :=
    fun h =>
      h3RawProductConvolutionMomentMass
        (p : ℝ) G (S h)

  let C : ℝ :=
    h3FourierMomentSplitCoefficient (p : ℝ)

  let U : ℝ → ℝ :=
    fun h =>
      C *
        (
          h3SpectralScalarRawFourierMomentMass
              (p : ℝ) G *
            h3SpectralScalarRawFourierL1Mass (S h)
          +
          h3SpectralScalarRawFourierL1Mass G *
            h3SpectralScalarRawFourierMomentMass
              (p : ℝ) (S h)
        )

  have hMoment :=
    tendsto_h3SpectralScalarRawFourierMomentMass_h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_zero
      p hp
      hNS ht₀ hE hTail hQ hQR i hx

  have hL1 :=
    tendsto_h3SpectralScalarRawFourierL1Mass_h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_zero
      hNS ht₀ hE hTail hQ hQR i hx

  have hMomentMul :
      Tendsto
        (fun h : ℝ =>
          h3SpectralScalarRawFourierL1Mass G *
            h3SpectralScalarRawFourierMomentMass
              (p : ℝ) (S h))
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by

    have hConst :
        Tendsto
          (fun _h : ℝ =>
            h3SpectralScalarRawFourierL1Mass G)
          (𝓝[≠] (0 : ℝ))
          (𝓝 (h3SpectralScalarRawFourierL1Mass G)) :=
      tendsto_const_nhds

    have hMul := hConst.mul hMoment

    simpa only [S, mul_zero] using hMul

  have hL1Mul :
      Tendsto
        (fun h : ℝ =>
          h3SpectralScalarRawFourierMomentMass
              (p : ℝ) G *
            h3SpectralScalarRawFourierL1Mass (S h))
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by

    have hConst :
        Tendsto
          (fun _h : ℝ =>
            h3SpectralScalarRawFourierMomentMass
              (p : ℝ) G)
          (𝓝[≠] (0 : ℝ))
          (𝓝
            (h3SpectralScalarRawFourierMomentMass
              (p : ℝ) G)) :=
      tendsto_const_nhds

    have hMul := hConst.mul hL1

    simpa only [S, mul_zero] using hMul

  have hInside :
      Tendsto
        (fun h : ℝ =>
          h3SpectralScalarRawFourierMomentMass
              (p : ℝ) G *
            h3SpectralScalarRawFourierL1Mass (S h)
          +
          h3SpectralScalarRawFourierL1Mass G *
            h3SpectralScalarRawFourierMomentMass
              (p : ℝ) (S h))
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by
    simpa only [zero_add] using hL1Mul.add hMomentMul

  have hUpperTend :
      Tendsto U (𝓝[≠] (0 : ℝ)) (𝓝 0) := by

    have hConst :
        Tendsto
          (fun _h : ℝ => C)
          (𝓝[≠] (0 : ℝ))
          (𝓝 C) :=
      tendsto_const_nhds

    have hMul := hConst.mul hInside

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
          unfold h3RawProductConvolutionMomentMass
          exact
            integral_nonneg
              (fun ξ =>
                mul_nonneg
                  (h3FourierMomentWeight_nonneg (p : ℝ) ξ)
                  (norm_nonneg _)))

  have hUpper :
      ∀ᶠ h : ℝ in (𝓝[≠] (0 : ℝ)),
        M h ≤ U h := by

    filter_upwards [hArgInterior] with h hxh

    have hS :
        H3RawFourierMomentIntegrable
          (p : ℝ) (S h) := by
      dsimp only [S]
      exact
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_natMoment_integrable
          p hp
          hNS ht₀ hE hTail hQ hQR i hx h hxh

    have hBound :=
      h3RawProductConvolutionMomentMass_le
        (q := (p : ℝ))
        (by positivity)
        G (S h) hG hS

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
