import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Bound

/-!
# Vanishing radial convolution L² norms with one slope-error input

The previous checkpoint proves that the doubled raw convolution moment vanishes
when one factor is the genuine selected spectral slope error.  The radial
Young estimate upgrades that scalar statement to strong radial Fourier `L²`
decay.

Moment integrability of the slope error is available only while the shifted
time remains in the compact slab.  We therefore totalize each local radial
convolution package by setting it to zero outside that slab.  Since
`x + h ∈ [Q/2,Q]` eventually as `h → 0`, the artificial branch does not affect
the punctured-neighborhood limit.

Both bilinear orientations are recorded for the finite Leray forcing quotient.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedSpectralSlopeConvolutionL2Limit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2200000

/-! ## Local totalized radial convolution packages -/

/--
Order-`m` radial convolution `L²` package with the spectral slope error in the
left slot, totalized by zero outside the compact slab.
-/
noncomputable def h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Left
    (m : ℕ)
    (hm : 1 ≤ m)
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
    (hG :
      H3RawFourierMomentIntegrable
        (((2 * m : ℕ) : ℝ)) G)
    (h : ℝ) :
    H3FourierComplexL2 :=
  if hxh : x + h ∈ Set.Icc (Q / 2) Q then
    h3RawProductConvolutionRadialFourierL2
      m
      (
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
          hNS ht₀ hE hTail hQ hQR hx h i
      )
      G
      (
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_natMoment_integrable
          (2 * m) (by omega)
          hNS ht₀ hE hTail hQ hQR i hx h hxh
      )
      hG
  else
    0

/--
Order-`m` radial convolution `L²` package with the spectral slope error in the
right slot, totalized by zero outside the compact slab.
-/
noncomputable def h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Right
    (m : ℕ)
    (hm : 1 ≤ m)
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
    (hG :
      H3RawFourierMomentIntegrable
        (((2 * m : ℕ) : ℝ)) G)
    (h : ℝ) :
    H3FourierComplexL2 :=
  if hxh : x + h ∈ Set.Icc (Q / 2) Q then
    h3RawProductConvolutionRadialFourierL2
      m
      G
      (
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
          hNS ht₀ hE hTail hQ hQR hx h i
      )
      hG
      (
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_natMoment_integrable
          (2 * m) (by omega)
          hNS ht₀ hE hTail hQ hQR i hx h hxh
      )
  else
    0

/-! ## Left-slot decay -/

/--
The order-`m` radial convolution `L²` norm tends to zero when the selected
spectral slope error occupies the left slot.
-/
theorem tendsto_norm_h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Left_zero
    (m : ℕ)
    (hm : 1 ≤ m)
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
    (hG :
      H3RawFourierMomentIntegrable
        (((2 * m : ℕ) : ℝ)) G) :
    Tendsto
      (fun h : ℝ =>
        ‖h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Left
          m hm hNS ht₀ hE hTail hQ hQR i hx G hG h‖)
      (𝓝[≠] (0 : ℝ))
      (𝓝 0) := by

  let S : ℝ → H3SpectralScalarState :=
    fun h =>
      h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
        hNS ht₀ hE hTail hQ hQR hx h i

  let L : ℝ → H3FourierComplexL2 :=
    fun h =>
      h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Left
        m hm hNS ht₀ hE hTail hQ hQR i hx G hG h

  let B : ℝ → ℝ :=
    fun h =>
      ‖h3SpectralScalarRawFourierConjL2 (S h)‖ *
        ‖h3SpectralScalarRawFourierL2 G‖

  let R : ℝ → ℝ :=
    fun h =>
      B h *
        h3RawProductConvolutionMomentMass
          (((2 * m : ℕ) : ℝ))
          (S h) G

  have hRawL2 :=
    tendsto_h3SpectralScalarRawFourierL2_h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_zero
      hNS ht₀ hE hTail hQ hQR i hx

  have hConjL2 :
      Tendsto
        (fun h : ℝ =>
          h3SpectralScalarRawFourierConjL2 (S h))
        (𝓝[≠] (0 : ℝ))
        (𝓝 (0 : H3FourierComplexL2)) := by

    let K :
        H3FourierComplexL2 →L[ℝ] H3FourierComplexL2 :=
      ContinuousLinearMap.compLpL
        (2 : ℝ≥0∞)
        (volume : Measure H3FourierPoint3)
        (Complex.conjCLE : ℂ →L[ℝ] ℂ)

    have hK :
        (fun F : H3FourierComplexL2 =>
          (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLp F)
          =
        (K : H3FourierComplexL2 → H3FourierComplexL2) := by

      funext F

      apply MeasureTheory.Lp.ext

      filter_upwards
        [ContinuousLinearMap.coeFn_compLpL
          (Complex.conjCLE : ℂ →L[ℝ] ℂ) F,
         (Complex.conjCLE : ℂ →L[ℝ] ℂ).coeFn_compLp F]
        with ξ hL hComp

      rw [hL]

      exact hComp

    have hComp :=
      (K.continuous.tendsto
        (0 : H3FourierComplexL2)).comp
        hRawL2

    unfold h3SpectralScalarRawFourierConjL2

    have hEq :
        (fun h : ℝ =>
          (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLp
            (h3SpectralScalarRawFourierL2 (S h)))
          =
        (fun h : ℝ =>
          K (h3SpectralScalarRawFourierL2 (S h))) := by
      funext h
      exact
        congrFun hK
          (h3SpectralScalarRawFourierL2 (S h))

    rw [hEq]

    simpa only [
      S,
      Function.comp_def,
      map_zero
    ] using hComp

  have hConjNorm :
      Tendsto
        (fun h : ℝ =>
          ‖h3SpectralScalarRawFourierConjL2 (S h)‖)
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by

    have hNorm :=
      (continuous_norm.tendsto
        (0 : H3FourierComplexL2)).comp hConjL2

    change
      Tendsto
        (fun h : ℝ =>
          ‖h3SpectralScalarRawFourierConjL2 (S h)‖)
        (𝓝[≠] (0 : ℝ))
        (𝓝 ‖(0 : H3FourierComplexL2)‖)
      at hNorm

    simpa only [norm_zero] using hNorm

  have hFixedNorm :
      Tendsto
        (fun _h : ℝ =>
          ‖h3SpectralScalarRawFourierL2 G‖)
        (𝓝[≠] (0 : ℝ))
        (𝓝 ‖h3SpectralScalarRawFourierL2 G‖) :=
    tendsto_const_nhds

  have hBTend :
      Tendsto B
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by

    have hMul :=
      hConjNorm.mul hFixedNorm

    simpa only [B, zero_mul] using hMul

  have hMoment :=
    tendsto_h3RawProductConvolutionMomentMass_spectralSlopeError_left_zero
      (2 * m) (by omega)
      hNS ht₀ hE hTail hQ hQR i hx G hG

  have hRTend :
      Tendsto R
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by

    have hMul :=
      hBTend.mul hMoment

    simpa only [R, zero_mul] using hMul

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
        0 ≤ ‖L h‖ ^ 2 :=
    Filter.Eventually.of_forall
      (fun h => sq_nonneg ‖L h‖)

  have hUpper :
      ∀ᶠ h : ℝ in (𝓝[≠] (0 : ℝ)),
        ‖L h‖ ^ 2 ≤ R h := by

    filter_upwards [hArgInterior] with h hxh

    have hS :
        H3RawFourierMomentIntegrable
          (((2 * m : ℕ) : ℝ)) (S h) := by
      dsimp only [S]
      exact
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_natMoment_integrable
          (2 * m) (by omega)
          hNS ht₀ hE hTail hQ hQR i hx h hxh

    have hBound :=
      norm_sq_h3RawProductConvolutionRadialFourierL2_le
        m (S h) G hS hG

    dsimp only [L]

    simp only [
      h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Left,
      dite_eq_left hxh
    ]

    simpa only [R, B, S] using hBound

  have hSqTend :
      Tendsto
        (fun h : ℝ => ‖L h‖ ^ 2)
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) :=
    squeeze_zero'
      hNonneg
      hUpper
      hRTend

  have hSqrt :=
    (Real.continuous_sqrt.tendsto 0).comp hSqTend

  change
    Tendsto
      (fun h : ℝ =>
        Real.sqrt (‖L h‖ ^ 2))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (Real.sqrt 0))
    at hSqrt

  simpa only [
    L,
    Real.sqrt_sq_eq_abs,
    abs_of_nonneg,
    norm_nonneg,
    Real.sqrt_zero
  ] using hSqrt

/-! ## Right-slot decay -/

/--
The order-`m` radial convolution `L²` norm tends to zero when the selected
spectral slope error occupies the right slot.
-/
theorem tendsto_norm_h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Right_zero
    (m : ℕ)
    (hm : 1 ≤ m)
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
    (hG :
      H3RawFourierMomentIntegrable
        (((2 * m : ℕ) : ℝ)) G) :
    Tendsto
      (fun h : ℝ =>
        ‖h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Right
          m hm hNS ht₀ hE hTail hQ hQR i hx G hG h‖)
      (𝓝[≠] (0 : ℝ))
      (𝓝 0) := by

  let S : ℝ → H3SpectralScalarState :=
    fun h =>
      h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
        hNS ht₀ hE hTail hQ hQR hx h i

  let L : ℝ → H3FourierComplexL2 :=
    fun h =>
      h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Right
        m hm hNS ht₀ hE hTail hQ hQR i hx G hG h

  let B : ℝ → ℝ :=
    fun h =>
      ‖h3SpectralScalarRawFourierConjL2 G‖ *
        ‖h3SpectralScalarRawFourierL2 (S h)‖

  let R : ℝ → ℝ :=
    fun h =>
      B h *
        h3RawProductConvolutionMomentMass
          (((2 * m : ℕ) : ℝ))
          G (S h)

  have hRawL2 :=
    tendsto_h3SpectralScalarRawFourierL2_h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_zero
      hNS ht₀ hE hTail hQ hQR i hx

  have hRawNorm :
      Tendsto
        (fun h : ℝ =>
          ‖h3SpectralScalarRawFourierL2 (S h)‖)
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by

    have hNorm :=
      (continuous_norm.tendsto
        (0 : H3FourierComplexL2)).comp hRawL2

    change
      Tendsto
        (fun h : ℝ =>
          ‖h3SpectralScalarRawFourierL2 (S h)‖)
        (𝓝[≠] (0 : ℝ))
        (𝓝 ‖(0 : H3FourierComplexL2)‖)
      at hNorm

    simpa only [norm_zero] using hNorm

  have hFixedNorm :
      Tendsto
        (fun _h : ℝ =>
          ‖h3SpectralScalarRawFourierConjL2 G‖)
        (𝓝[≠] (0 : ℝ))
        (𝓝 ‖h3SpectralScalarRawFourierConjL2 G‖) :=
    tendsto_const_nhds

  have hBTend :
      Tendsto B
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by

    have hMul :=
      hFixedNorm.mul hRawNorm

    simpa only [B, mul_zero] using hMul

  have hMoment :=
    tendsto_h3RawProductConvolutionMomentMass_spectralSlopeError_right_zero
      (2 * m) (by omega)
      hNS ht₀ hE hTail hQ hQR i hx G hG

  have hRTend :
      Tendsto R
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by

    have hMul :=
      hBTend.mul hMoment

    simpa only [R, zero_mul] using hMul

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
        0 ≤ ‖L h‖ ^ 2 :=
    Filter.Eventually.of_forall
      (fun h => sq_nonneg ‖L h‖)

  have hUpper :
      ∀ᶠ h : ℝ in (𝓝[≠] (0 : ℝ)),
        ‖L h‖ ^ 2 ≤ R h := by

    filter_upwards [hArgInterior] with h hxh

    have hS :
        H3RawFourierMomentIntegrable
          (((2 * m : ℕ) : ℝ)) (S h) := by
      dsimp only [S]
      exact
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_natMoment_integrable
          (2 * m) (by omega)
          hNS ht₀ hE hTail hQ hQR i hx h hxh

    have hBound :=
      norm_sq_h3RawProductConvolutionRadialFourierL2_le
        m G (S h) hG hS

    dsimp only [L]

    simp only [
      h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Right,
      dite_eq_left hxh
    ]

    simpa only [R, B, S] using hBound

  have hSqTend :
      Tendsto
        (fun h : ℝ => ‖L h‖ ^ 2)
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) :=
    squeeze_zero'
      hNonneg
      hUpper
      hRTend

  have hSqrt :=
    (Real.continuous_sqrt.tendsto 0).comp hSqTend

  change
    Tendsto
      (fun h : ℝ =>
        Real.sqrt (‖L h‖ ^ 2))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (Real.sqrt 0))
    at hSqrt

  simpa only [
    L,
    Real.sqrt_sq_eq_abs,
    abs_of_nonneg,
    norm_nonneg,
    Real.sqrt_zero
  ] using hSqrt

end

end Euclidean
end Bridge
end PrimeTensor
