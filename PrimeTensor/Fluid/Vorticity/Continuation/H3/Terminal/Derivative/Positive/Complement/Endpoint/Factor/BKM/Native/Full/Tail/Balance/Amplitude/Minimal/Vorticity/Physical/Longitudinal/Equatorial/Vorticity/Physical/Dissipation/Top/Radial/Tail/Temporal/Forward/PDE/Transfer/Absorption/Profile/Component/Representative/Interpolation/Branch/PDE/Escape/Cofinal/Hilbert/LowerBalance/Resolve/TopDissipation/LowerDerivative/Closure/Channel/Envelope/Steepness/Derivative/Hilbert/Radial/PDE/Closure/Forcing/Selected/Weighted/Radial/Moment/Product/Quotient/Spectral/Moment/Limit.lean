import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment

/-!
# Vanishing raw moments of the genuine spectral slope error

The preceding checkpoint transfers the arbitrary-radial strong slope errors
onto the genuine weighted spectral carrier and bounds its raw order-`p` moment
mass by the neighboring order-`p` and order-`p+2` slope-error norms.

This file closes the corresponding limiting statement: at every strict
interior slab time, every natural raw moment `p ≥ 2` of each spectral
slope-error coordinate tends to zero as the increment tends to zero through
the punctured neighborhood.

This is the scalar vanishing input used by the subsequent quadratic
convolution/Leray forcing quotient estimate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedSpectralSlopeMomentLimit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1800000

/--
For every natural `p ≥ 2`, the canonical raw order-`p` moment mass of each
coordinate of the genuine selected spectral slope error tends to zero.
-/
theorem tendsto_h3SpectralScalarRawFourierMomentMass_h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_zero
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
    (hx : x ∈ Set.Ioo (Q / 2) Q) :
    Tendsto
      (fun h : ℝ =>
        h3SpectralScalarRawFourierMomentMass
          (p : ℝ)
          (
            h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
              hNS ht₀ hE hTail hQ hQR hx h i
          ))
      (𝓝[≠] (0 : ℝ))
      (𝓝 0) := by

  have hp2 :
      2 ≤ p + 2 := by
    omega

  let M : ℝ → ℝ :=
    fun h =>
      h3SpectralScalarRawFourierMomentMass
        (p : ℝ)
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
          ‖h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
              p hp
              hNS ht₀ hE hTail hQ hQR i hx h‖
            +
          ‖h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
              (p + 2) hp2
              hNS ht₀ hE hTail hQ hQR i hx h‖
        )

  have hP :=
    tendsto_norm_h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab_zero
      p hp
      hNS ht₀ hE hTail hQ hQR i hx

  have hP2 :=
    tendsto_norm_h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab_zero
      (p + 2) hp2
      hNS ht₀ hE hTail hQ hQR i hx

  have hSum :
      Tendsto
        (fun h : ℝ =>
          ‖h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
              p hp
              hNS ht₀ hE hTail hQ hQR i hx h‖
            +
          ‖h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
              (p + 2) hp2
              hNS ht₀ hE hTail hQ hQR i hx h‖)
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by
    simpa only [zero_add] using hP.add hP2

  have hUpperTend :
      Tendsto
        U
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by

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
        0 ≤ M h :=
    Filter.Eventually.of_forall
      (fun h =>
        h3SpectralScalarRawFourierMomentMass_nonneg
          (p : ℝ)
          (
            h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
              hNS ht₀ hE hTail hQ hQR hx h i
          ))

  have hUpper :
      ∀ᶠ h : ℝ in (𝓝[≠] (0 : ℝ)),
        M h ≤ U h := by

    filter_upwards [hArgInterior] with h hxh

    have hBound :=
      h3SpectralScalarRawFourierMomentMass_h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_le
        p hp
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
