import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient

/-!
# Vanishing self-interaction of the selected spectral slope error

For the exact quadratic quotient identity the only new nonlinear channel is

    N(E_h, E_h),

where `E_h` is the genuine selected spectral slope error.

Both factors now vanish simultaneously.  The fully explicit radial Young bound
therefore gives a particularly strong estimate: the raw `L²` prefactor and all
raw `L¹`/moment masses appearing on the right tend to zero.  This file first
packages the scalar radial convolution self-channel and proves strong `L²`
decay, then lifts it through the finite divergence and Leray matrix.

As in the preceding local quotient files, the packages are totalized by zero
outside the compact slab.  That branch is irrelevant eventually at `h → 0`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedSpectralSlopeSelf
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2600000

/-! ## Scalar self-convolution -/

/--
Order-`m` radial convolution of two coordinates of the selected spectral slope
error, totalized by zero outside the compact slab.
-/
noncomputable def h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Self
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
    (a b : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q)
    (h : ℝ) :
    H3FourierComplexL2 :=
  if hxh : x + h ∈ Set.Icc (Q / 2) Q then
    h3RawProductConvolutionRadialFourierL2
      m
      (
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
          hNS ht₀ hE hTail hQ hQR hx h a
      )
      (
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
          hNS ht₀ hE hTail hQ hQR hx h b
      )
      (
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_natMoment_integrable
          (2 * m) (by omega)
          hNS ht₀ hE hTail hQ hQR a hx h hxh
      )
      (
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_natMoment_integrable
          (2 * m) (by omega)
          hNS ht₀ hE hTail hQ hQR b hx h hxh
      )
  else
    0

/--
Every radial scalar convolution self-channel of the selected spectral slope
error tends strongly to zero.
-/
theorem tendsto_norm_h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Self_zero
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
    (a b : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q) :
    Tendsto
      (fun h : ℝ =>
        ‖h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Self
          m hm hNS ht₀ hE hTail hQ hQR a b hx h‖)
      (𝓝[≠] (0 : ℝ))
      (𝓝 0) := by

  let Sa : ℝ → H3SpectralScalarState :=
    fun h =>
      h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
        hNS ht₀ hE hTail hQ hQR hx h a

  let Sb : ℝ → H3SpectralScalarState :=
    fun h =>
      h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
        hNS ht₀ hE hTail hQ hQR hx h b

  let L : ℝ → H3FourierComplexL2 :=
    fun h =>
      h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Self
        m hm hNS ht₀ hE hTail hQ hQR a b hx h

  let Pref : ℝ → ℝ :=
    fun h =>
      ‖h3SpectralScalarRawFourierConjL2 (Sa h)‖ *
        ‖h3SpectralScalarRawFourierL2 (Sb h)‖

  let Mass : ℝ → ℝ :=
    fun h =>
      h3FourierMomentSplitCoefficient
          (((2 * m : ℕ) : ℝ))
        *
      (
        h3SpectralScalarRawFourierMomentMass
            (((2 * m : ℕ) : ℝ))
            (Sa h)
          *
        h3SpectralScalarRawFourierL1Mass (Sb h)
        +
        h3SpectralScalarRawFourierL1Mass (Sa h)
          *
        h3SpectralScalarRawFourierMomentMass
            (((2 * m : ℕ) : ℝ))
            (Sb h)
      )

  let Major : ℝ → ℝ :=
    fun h => Pref h * Mass h

  have hRawA :=
    tendsto_h3SpectralScalarRawFourierL2_h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_zero
      hNS ht₀ hE hTail hQ hQR a hx

  have hRawB :=
    tendsto_h3SpectralScalarRawFourierL2_h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_zero
      hNS ht₀ hE hTail hQ hQR b hx

  have hConjA :
      Tendsto
        (fun h : ℝ =>
          h3SpectralScalarRawFourierConjL2 (Sa h))
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
        hRawA

    unfold h3SpectralScalarRawFourierConjL2

    have hEq :
        (fun h : ℝ =>
          (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLp
            (h3SpectralScalarRawFourierL2 (Sa h)))
          =
        (fun h : ℝ =>
          K (h3SpectralScalarRawFourierL2 (Sa h))) := by
      funext h
      exact
        congrFun hK
          (h3SpectralScalarRawFourierL2 (Sa h))

    rw [hEq]

    simpa only [
      Sa,
      Function.comp_def,
      map_zero
    ] using hComp

  have hConjNormA :
      Tendsto
        (fun h : ℝ =>
          ‖h3SpectralScalarRawFourierConjL2 (Sa h)‖)
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by

    have hNorm :=
      (continuous_norm.tendsto
        (0 : H3FourierComplexL2)).comp hConjA

    change
      Tendsto
        (fun h : ℝ =>
          ‖h3SpectralScalarRawFourierConjL2 (Sa h)‖)
        (𝓝[≠] (0 : ℝ))
        (𝓝 ‖(0 : H3FourierComplexL2)‖)
      at hNorm

    simpa only [norm_zero] using hNorm

  have hRawNormB :
      Tendsto
        (fun h : ℝ =>
          ‖h3SpectralScalarRawFourierL2 (Sb h)‖)
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by

    have hNorm :=
      (continuous_norm.tendsto
        (0 : H3FourierComplexL2)).comp hRawB

    change
      Tendsto
        (fun h : ℝ =>
          ‖h3SpectralScalarRawFourierL2 (Sb h)‖)
        (𝓝[≠] (0 : ℝ))
        (𝓝 ‖(0 : H3FourierComplexL2)‖)
      at hNorm

    simpa only [Sb, norm_zero] using hNorm

  have hPrefTend :
      Tendsto Pref
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by

    have hMul :=
      hConjNormA.mul hRawNormB

    simpa only [Pref, zero_mul] using hMul

  have hMomentA :=
    tendsto_h3SpectralScalarRawFourierMomentMass_h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_zero
      (2 * m) (by omega)
      hNS ht₀ hE hTail hQ hQR a hx

  have hMomentB :=
    tendsto_h3SpectralScalarRawFourierMomentMass_h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_zero
      (2 * m) (by omega)
      hNS ht₀ hE hTail hQ hQR b hx

  have hL1A :=
    tendsto_h3SpectralScalarRawFourierL1Mass_h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_zero
      hNS ht₀ hE hTail hQ hQR a hx

  have hL1B :=
    tendsto_h3SpectralScalarRawFourierL1Mass_h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_zero
      hNS ht₀ hE hTail hQ hQR b hx

  have hFirst :
      Tendsto
        (fun h : ℝ =>
          h3SpectralScalarRawFourierMomentMass
              (((2 * m : ℕ) : ℝ))
              (Sa h)
            *
          h3SpectralScalarRawFourierL1Mass (Sb h))
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by

    have hMul :=
      hMomentA.mul hL1B

    simpa only [Sa, Sb, zero_mul] using hMul

  have hSecond :
      Tendsto
        (fun h : ℝ =>
          h3SpectralScalarRawFourierL1Mass (Sa h)
            *
          h3SpectralScalarRawFourierMomentMass
              (((2 * m : ℕ) : ℝ))
              (Sb h))
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by

    have hMul :=
      hL1A.mul hMomentB

    simpa only [Sa, Sb, zero_mul] using hMul

  have hInside :
      Tendsto
        (fun h : ℝ =>
          h3SpectralScalarRawFourierMomentMass
              (((2 * m : ℕ) : ℝ))
              (Sa h)
            *
          h3SpectralScalarRawFourierL1Mass (Sb h)
          +
          h3SpectralScalarRawFourierL1Mass (Sa h)
            *
          h3SpectralScalarRawFourierMomentMass
              (((2 * m : ℕ) : ℝ))
              (Sb h))
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by

    have hAdd :=
      hFirst.add hSecond

    simpa only [zero_add] using hAdd

  have hCoeff :
      Tendsto
        (fun _h : ℝ =>
          h3FourierMomentSplitCoefficient
            (((2 * m : ℕ) : ℝ)))
        (𝓝[≠] (0 : ℝ))
        (𝓝
          (h3FourierMomentSplitCoefficient
            (((2 * m : ℕ) : ℝ)))) :=
    tendsto_const_nhds

  have hMassTend :
      Tendsto Mass
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by

    have hMul :=
      hCoeff.mul hInside

    simpa only [Mass, mul_zero] using hMul

  have hMajorTend :
      Tendsto Major
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by

    have hMul :=
      hPrefTend.mul hMassTend

    simpa only [Major, zero_mul] using hMul

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
        ‖L h‖ ^ 2 ≤ Major h := by

    filter_upwards [hArgInterior] with h hxh

    have hSa :
        H3RawFourierMomentIntegrable
          (((2 * m : ℕ) : ℝ))
          (Sa h) := by
      dsimp only [Sa]
      exact
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_natMoment_integrable
          (2 * m) (by omega)
          hNS ht₀ hE hTail hQ hQR a hx h hxh

    have hSb :
        H3RawFourierMomentIntegrable
          (((2 * m : ℕ) : ℝ))
          (Sb h) := by
      dsimp only [Sb]
      exact
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_natMoment_integrable
          (2 * m) (by omega)
          hNS ht₀ hE hTail hQ hQR b hx h hxh

    have hBound :=
      norm_sq_h3RawProductConvolutionRadialFourierL2_le_stateMasses
        m (Sa h) (Sb h) hSa hSb

    dsimp only [L]

    simp only [
      h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Self,
      dite_eq_left hxh
    ]

    simpa only [
      Major,
      Pref,
      Mass,
      Sa,
      Sb
    ] using hBound

  have hSqTend :
      Tendsto
        (fun h : ℝ => ‖L h‖ ^ 2)
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) :=
    squeeze_zero'
      hNonneg
      hUpper
      hMajorTend

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

/-! ## Finite Leray self-interaction -/

/--
Order-`m` radial finite Leray self-interaction of the selected spectral slope
error, totalized by zero outside the compact slab.
-/
noncomputable def h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Self
    (m : ℕ)
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
    H3FourierComplexL2 :=
  if hxh : x + h ∈ Set.Icc (Q / 2) Q then
    h3RawFinLerayOuterProductDivergenceRadialFourierL2
      m
      (
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
          hNS ht₀ hE hTail hQ hQR hx h
      )
      (
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
          hNS ht₀ hE hTail hQ hQR hx h
      )
      i
      (fun r =>
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_natMoment_integrable
          (2 * (m + 1)) (by omega)
          hNS ht₀ hE hTail hQ hQR r hx h hxh)
      (fun r =>
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_natMoment_integrable
          (2 * (m + 1)) (by omega)
          hNS ht₀ hE hTail hQ hQR r hx h hxh)
  else
    0

/--
The complete radial finite Leray self-interaction of the selected spectral
slope error tends strongly to zero.
-/
theorem tendsto_norm_h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Self_zero
    (m : ℕ)
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
        ‖h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Self
          m hNS ht₀ hE hTail hQ hQR i hx h‖)
      (𝓝[≠] (0 : ℝ))
      (𝓝 0) := by

  let S : ℝ → H3SpectralFinVectorState :=
    fun h =>
      h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
        hNS ht₀ hE hTail hQ hQR hx h

  let L : ℝ → H3FourierComplexL2 :=
    fun h =>
      h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Self
        m hNS ht₀ hE hTail hQ hQR i hx h

  let Major : ℝ → ℝ :=
    fun h =>
      ∑ k : Fin 3,
        2 *
          (
            ∑ j : Fin 3,
              (2 * Real.pi) *
                ‖h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Self
                    (m + 1) (by omega)
                    hNS ht₀ hE hTail hQ hQR k j hx h‖
          )

  have hTerm :
      ∀ k j : Fin 3,
        Tendsto
          (fun h : ℝ =>
            (2 * Real.pi) *
              ‖h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Self
                  (m + 1) (by omega)
                  hNS ht₀ hE hTail hQ hQR k j hx h‖)
          (𝓝[≠] (0 : ℝ))
          (𝓝 0) := by
    intro k j

    have hBase :=
      tendsto_norm_h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Self_zero
        (m + 1) (by omega)
        hNS ht₀ hE hTail hQ hQR k j hx

    have hConst :
        Tendsto
          (fun _h : ℝ => 2 * Real.pi)
          (𝓝[≠] (0 : ℝ))
          (𝓝 (2 * Real.pi)) :=
      tendsto_const_nhds

    simpa only [mul_zero] using hConst.mul hBase

  have hInner :
      ∀ k : Fin 3,
        Tendsto
          (fun h : ℝ =>
            ∑ j : Fin 3,
              (2 * Real.pi) *
                ‖h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Self
                    (m + 1) (by omega)
                    hNS ht₀ hE hTail hQ hQR k j hx h‖)
          (𝓝[≠] (0 : ℝ))
          (𝓝 0) := by
    intro k

    have hSum :=
      tendsto_finsetSum
        (Finset.univ : Finset (Fin 3))
        (fun j _hj => hTerm k j)

    simpa only [Finset.sum_const_zero] using hSum

  have hOuterTerm :
      ∀ k : Fin 3,
        Tendsto
          (fun h : ℝ =>
            2 *
              (
                ∑ j : Fin 3,
                  (2 * Real.pi) *
                    ‖h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Self
                        (m + 1) (by omega)
                        hNS ht₀ hE hTail hQ hQR k j hx h‖
              ))
          (𝓝[≠] (0 : ℝ))
          (𝓝 0) := by
    intro k

    have hConst :
        Tendsto
          (fun _h : ℝ => (2 : ℝ))
          (𝓝[≠] (0 : ℝ))
          (𝓝 2) :=
      tendsto_const_nhds

    simpa only [mul_zero] using hConst.mul (hInner k)

  have hMajorTend :
      Tendsto Major
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by

    have hSum :=
      tendsto_finsetSum
        (Finset.univ : Finset (Fin 3))
        (fun k _hk => hOuterTerm k)

    simpa only [Major, Finset.sum_const_zero] using hSum

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
        0 ≤ ‖L h‖ :=
    Filter.Eventually.of_forall
      (fun h => norm_nonneg _)

  have hUpper :
      ∀ᶠ h : ℝ in (𝓝[≠] (0 : ℝ)),
        ‖L h‖ ≤ Major h := by

    filter_upwards [hArgInterior] with h hxh

    have hS :
        ∀ r : Fin 3,
          H3RawFourierMomentIntegrable
            (((2 * (m + 1) : ℕ) : ℝ))
            (S h r) := by
      intro r
      dsimp only [S]
      exact
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_natMoment_integrable
          (2 * (m + 1)) (by omega)
          hNS ht₀ hE hTail hQ hQR r hx h hxh

    have hBound :=
      norm_h3RawFinLerayOuterProductDivergenceRadialFourierL2_le
        m (S h) (S h) i hS hS

    dsimp only [L]

    simp only [
      h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Self,
      dite_eq_left hxh
    ]

    simpa only [
      Major,
      S,
      h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Self,
      dite_eq_left hxh
    ] using hBound

  exact
    squeeze_zero'
      hNonneg
      hUpper
      hMajorTend

end

end Euclidean
end Bridge
end PrimeTensor
