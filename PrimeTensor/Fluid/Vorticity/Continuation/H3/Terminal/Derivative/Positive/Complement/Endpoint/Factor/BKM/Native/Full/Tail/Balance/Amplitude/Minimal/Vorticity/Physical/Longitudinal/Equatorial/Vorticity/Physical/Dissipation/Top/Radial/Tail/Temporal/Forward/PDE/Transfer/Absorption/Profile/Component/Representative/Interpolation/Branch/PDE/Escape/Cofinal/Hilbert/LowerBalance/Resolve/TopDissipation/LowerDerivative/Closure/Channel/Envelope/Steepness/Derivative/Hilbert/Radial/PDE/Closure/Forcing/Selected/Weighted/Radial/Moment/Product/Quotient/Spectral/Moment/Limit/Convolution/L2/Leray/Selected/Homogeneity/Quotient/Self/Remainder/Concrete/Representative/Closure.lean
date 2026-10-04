import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete.Representative

/-!
# Close the selected forcing radial difference quotient

For one natural radial order `m`, extend the selected forcing `L²` path from
the positive compact slab to all real source times with `Set.IccExtend`.  At a
strict interior base point `x`, define its literal slope error

    h⁻¹ • (F_m(x+h) - F_m(x)) - DF_m(x).

The preceding checkpoints identify this state, for every sufficiently small
nonzero increment, with exactly three terms:

* the slope-error/base-state left Leray channel;
* the slope-error/base-state right Leray channel;
* the quadratic remainder.

All three tend strongly to zero.  Hence the actual selected forcing radial path
has the product-rule candidate as its genuine derivative at every strict
interior slab point.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedForcingQuotientClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 3000000

/-! ## Extended forcing path and slope error -/

/--
Order-`m` selected nonlinear forcing radial `L²` path, extended off the compact
slab by the canonical `IccExtend`.
-/
noncomputable def h3PreterminalSelectedForcingRadialFourierL2OnSlabExtension
    (m : ℕ)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s : ℝ) :
    H3FourierComplexL2 :=
  Set.IccExtend
    (by linarith : Q / 2 ≤ Q)
    (fun q : Set.Icc (Q / 2) Q =>
      h3SelectedRestartForcingRadialFourierL2OnSlab
        m
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState
          hNS ht₀ hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNS ht₀ hE hTail)
        hQ hQR.le i q)
    s

/--
Literal radial forcing slope error at a strict interior slab point.
-/
noncomputable def h3PreterminalSelectedForcingRadialSlopeErrorFourierL2OnSlab
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
  (h⁻¹ : ℝ) •
      (
        h3PreterminalSelectedForcingRadialFourierL2OnSlabExtension
            m hNS ht₀ hE hTail hQ hQR i (x + h)
          -
        h3PreterminalSelectedForcingRadialFourierL2OnSlabExtension
            m hNS ht₀ hE hTail hQ hQR i x
      )
    -
  h3PreterminalSelectedForcingTimeDerivativeRadialFourierL2OnSlab
    m hNS ht₀ hE hTail hQ hQR i
    ⟨x, hx.1.le, hx.2.le⟩

/-! ## Exact state decomposition -/

/--
For every nonzero increment which stays in the compact slab, the actual forcing
slope error is exactly the two linear slope-error channels plus the quadratic
remainder.
-/
theorem h3PreterminalSelectedForcingRadialSlopeErrorFourierL2OnSlab_eq_channels
    (m : ℕ)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x h : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q)
    (hh : h ≠ 0)
    (hxh : x + h ∈ Set.Icc (Q / 2) Q) :
    let sx : Set.Icc (Q / 2) Q :=
      ⟨x, hx.1.le, hx.2.le⟩
    let U : H3SpectralFinVectorState :=
      h3PreterminalSelectedUnitSpectralStateOnRadius
        hNS ht₀ hE hTail
        (h3SelectedProjectedRHSSlabRadius hE hQ hQR sx)
    let hU :
        ∀ r : Fin 3,
          H3RawFourierMomentIntegrable
            (((2 * (m + 1) : ℕ) : ℝ))
            (U r) :=
      h3PreterminalSelectedUnitSpectralStateOnSlab_natMoment_integrable
        (2 * (m + 1))
        hNS ht₀ hE hTail hQ hQR sx
    h3PreterminalSelectedForcingRadialSlopeErrorFourierL2OnSlab
        m hNS ht₀ hE hTail hQ hQR i hx h
      =
    h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Left
        m hNS ht₀ hE hTail hQ hQR i hx U hU h
      +
    h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Right
        m hNS ht₀ hE hTail hQ hQR i hx U hU h
      +
    h3PreterminalSelectedVelocitySpectralSlopeQuadraticRemainderRadialFourierL2
        m hNS ht₀ hE hTail hQ hQR i hx h := by

  dsimp only

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

  let sxh : Set.Icc (Q / 2) Q :=
    ⟨x + h, hxh⟩

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀

  let U : H3SpectralFinVectorState :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht₀ hE hTail
      (h3SelectedProjectedRHSSlabRadius hE hQ hQR sx)

  let hU :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (U r) :=
    h3PreterminalSelectedUnitSpectralStateOnSlab_natMoment_integrable
      (2 * (m + 1))
      hNS ht₀ hE hTail hQ hQR sx

  let R : H3SpectralFinVectorState :=
    h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
      hNS ht₀ hE hTail hQ hQR sx

  let Err : H3SpectralFinVectorState :=
    h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
      hNS ht₀ hE hTail hQ hQR hx h

  let Fh : H3FourierComplexL2 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      m
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hQ hQR.le i sxh

  let F0 : H3FourierComplexL2 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      m
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hQ hQR.le i sx

  let C : H3FourierComplexL2 :=
    h3PreterminalSelectedForcingTimeDerivativeRadialFourierL2OnSlab
      m hNS ht₀ hE hTail hQ hQR i sx

  let L : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Left
      m hNS ht₀ hE hTail hQ hQR i hx U hU h

  let D : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Right
      m hNS ht₀ hE hTail hQ hQR i hx U hU h

  let Qr : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocitySpectralSlopeQuadraticRemainderRadialFourierL2
      m hNS ht₀ hE hTail hQ hQR i hx h

  have hUeq :
      U = W x := by
    dsimp only [U, W, U₀, hA, hU₀, sx]
    unfold
      h3PreterminalSelectedUnitSpectralStateOnRadius
    rfl

  have hFh :=
    h3SelectedRestartForcingRadialFourierL2OnSlab_ae
      m
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hQ hQR.le i sxh

  have hF0 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab_ae
      m
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hQ hQR.le i sx

  have hC :=
    h3PreterminalSelectedForcingTimeDerivativeRadialFourierL2OnSlab_ae
      m hNS ht₀ hE hTail hQ hQR i sx

  have hL :=
    h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Left_selectedState_ae
      m hNS ht₀ hE hTail hQ hQR i hx hxh

  have hD :=
    h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Right_selectedState_ae
      m hNS ht₀ hE hTail hQ hQR i hx hxh

  have hQr :=
    h3PreterminalSelectedVelocitySpectralSlopeQuadraticRemainderRadialFourierL2_ae
      m hNS ht₀ hE hTail hQ hQR i hx hxh

  dsimp only at hC hL hD hQr

  have hSub :=
    MeasureTheory.Lp.coeFn_sub
      Fh F0

  have hScale :=
    MeasureTheory.Lp.coeFn_smul
      (h⁻¹ : ℝ)
      (Fh - F0)

  have hErr :=
    MeasureTheory.Lp.coeFn_sub
      ((h⁻¹ : ℝ) • (Fh - F0))
      C

  have hAddLD :=
    MeasureTheory.Lp.coeFn_add
      L D

  have hAddAll :=
    MeasureTheory.Lp.coeFn_add
      (L + D) Qr

  unfold
    h3PreterminalSelectedForcingRadialSlopeErrorFourierL2OnSlab
    h3PreterminalSelectedForcingRadialFourierL2OnSlabExtension

  rw [
    Set.IccExtend_of_mem
      (by linarith : Q / 2 ≤ Q)
      (fun q : Set.Icc (Q / 2) Q =>
        h3SelectedRestartForcingRadialFourierL2OnSlab
          m
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState
            hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
          hQ hQR.le i q)
      hxh
  ]

  rw [
    Set.IccExtend_of_mem
      (by linarith : Q / 2 ≤ Q)
      (fun q : Set.Icc (Q / 2) Q =>
        h3SelectedRestartForcingRadialFourierL2OnSlab
          m
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState
            hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
          hQ hQR.le i q)
      ⟨hx.1.le, hx.2.le⟩
  ]

  change
    ((h⁻¹ : ℝ) • (Fh - F0) - C : H3FourierComplexL2)
      =
    L + D + Qr

  apply MeasureTheory.Lp.ext

  filter_upwards [
    hFh,
    hF0,
    hC,
    hL,
    hD,
    hQr,
    hSub,
    hScale,
    hErr,
    hAddLD,
    hAddAll
  ] with ξ hFhξ hF0ξ hCξ hLξ hDξ hQrξ
      hSubξ hScaleξ hErrξ hAddLDξ hAddAllξ

  rw [hErrξ]
  simp only [Pi.sub_apply]
  rw [hScaleξ]
  simp only [Pi.smul_apply, Complex.real_smul]
  rw [hSubξ]
  simp only [Pi.sub_apply]

  rw [hAddAllξ]
  simp only [Pi.add_apply]
  rw [hAddLDξ]
  simp only [Pi.add_apply]

  rw [hFhξ, hF0ξ, hCξ, hLξ, hDξ, hQrξ]

  change
    ((h⁻¹ : ℝ) : ℂ) *
          (
            ((‖ξ‖ ^ m : ℝ) : ℂ) *
                h3RawFinLerayOuterProductDivergence
                  (W (x + h)) (W (x + h)) i ξ
              -
            ((‖ξ‖ ^ m : ℝ) : ℂ) *
                h3RawFinLerayOuterProductDivergence
                  (W x) (W x) i ξ
          )
        -
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        (
          h3RawFinLerayOuterProductDivergence R U i ξ
            +
          h3RawFinLerayOuterProductDivergence U R i ξ
        )
      =
    ((‖ξ‖ ^ m : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergence Err U i ξ
        +
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergence U Err i ξ
        +
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        (
          h •
            (
              h3RawFinLerayOuterProductDivergence R R i ξ
                +
              h3RawFinLerayOuterProductDivergence Err R i ξ
                +
              h3RawFinLerayOuterProductDivergence R Err i ξ
                +
              h3RawFinLerayOuterProductDivergence Err Err i ξ
            )
        )

  rw [hUeq]

  have hPoint :=
    h3PreterminalSelectedRawFinLeray_differenceQuotient_productRule_error
      hNS ht₀ hE hTail hQ hQR i hx hh ξ

  dsimp only at hPoint

  change
    (h⁻¹ : ℝ) •
          (
            h3RawFinLerayOuterProductDivergence
                (W (x + h)) (W (x + h)) i ξ
              -
            h3RawFinLerayOuterProductDivergence
                (W x) (W x) i ξ
          )
        -
      (
        h3RawFinLerayOuterProductDivergence R (W x) i ξ
          +
        h3RawFinLerayOuterProductDivergence (W x) R i ξ
      )
      =
    h3RawFinLerayOuterProductDivergence Err (W x) i ξ
      +
    h3RawFinLerayOuterProductDivergence (W x) Err i ξ
      +
    h •
      (
        h3RawFinLerayOuterProductDivergence R R i ξ
          +
        h3RawFinLerayOuterProductDivergence Err R i ξ
          +
        h3RawFinLerayOuterProductDivergence R Err i ξ
          +
        h3RawFinLerayOuterProductDivergence Err Err i ξ
      )
    at hPoint

  calc
    ((h⁻¹ : ℝ) : ℂ) *
          (
            ((‖ξ‖ ^ m : ℝ) : ℂ) *
                h3RawFinLerayOuterProductDivergence
                  (W (x + h)) (W (x + h)) i ξ
              -
            ((‖ξ‖ ^ m : ℝ) : ℂ) *
                h3RawFinLerayOuterProductDivergence
                  (W x) (W x) i ξ
          )
        -
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        (
          h3RawFinLerayOuterProductDivergence R (W x) i ξ
            +
          h3RawFinLerayOuterProductDivergence (W x) R i ξ
        )
        =
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        (
          (h⁻¹ : ℝ) •
              (
                h3RawFinLerayOuterProductDivergence
                    (W (x + h)) (W (x + h)) i ξ
                  -
                h3RawFinLerayOuterProductDivergence
                    (W x) (W x) i ξ
              )
            -
          (
            h3RawFinLerayOuterProductDivergence R (W x) i ξ
              +
            h3RawFinLerayOuterProductDivergence (W x) R i ξ
          )
        ) := by
          simp only [Complex.real_smul]
          ring
    _ =
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        (
          h3RawFinLerayOuterProductDivergence Err (W x) i ξ
            +
          h3RawFinLerayOuterProductDivergence (W x) Err i ξ
            +
          h •
            (
              h3RawFinLerayOuterProductDivergence R R i ξ
                +
              h3RawFinLerayOuterProductDivergence Err R i ξ
                +
              h3RawFinLerayOuterProductDivergence R Err i ξ
                +
              h3RawFinLerayOuterProductDivergence Err Err i ξ
            )
        ) := by
          rw [hPoint]
    _ =
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergence Err (W x) i ξ
        +
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergence (W x) Err i ξ
        +
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        (
          h •
            (
              h3RawFinLerayOuterProductDivergence R R i ξ
                +
              h3RawFinLerayOuterProductDivergence Err R i ξ
                +
              h3RawFinLerayOuterProductDivergence R Err i ξ
                +
              h3RawFinLerayOuterProductDivergence Err Err i ξ
            )
        ) := by
          ring

/-! ## Strong quotient closure -/

/--
The actual order-`m` selected forcing slope error tends strongly to zero in
Fourier `L²`.
-/
theorem tendsto_h3PreterminalSelectedForcingRadialSlopeErrorFourierL2OnSlab_zero
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
        h3PreterminalSelectedForcingRadialSlopeErrorFourierL2OnSlab
          m hNS ht₀ hE hTail hQ hQR i hx h)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (0 : H3FourierComplexL2)) := by

  let sx : Set.Icc (Q / 2) Q :=
    ⟨x, hx.1.le, hx.2.le⟩

  let U : H3SpectralFinVectorState :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht₀ hE hTail
      (h3SelectedProjectedRHSSlabRadius hE hQ hQR sx)

  let hU :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (U r) :=
    h3PreterminalSelectedUnitSpectralStateOnSlab_natMoment_integrable
      (2 * (m + 1))
      hNS ht₀ hE hTail hQ hQR sx

  let L : ℝ → H3FourierComplexL2 :=
    fun h =>
      h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Left
        m hNS ht₀ hE hTail hQ hQR i hx U hU h

  let D : ℝ → H3FourierComplexL2 :=
    fun h =>
      h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Right
        m hNS ht₀ hE hTail hQ hQR i hx U hU h

  let Qr : ℝ → H3FourierComplexL2 :=
    fun h =>
      h3PreterminalSelectedVelocitySpectralSlopeQuadraticRemainderRadialFourierL2
        m hNS ht₀ hE hTail hQ hQR i hx h

  have hLNorm :=
    tendsto_norm_h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Left_selectedState_zero
      m hNS ht₀ hE hTail hQ hQR i hx

  change
    Tendsto
      (fun h : ℝ => ‖L h‖)
      (𝓝[≠] (0 : ℝ))
      (𝓝 0)
    at hLNorm

  have hDNorm :=
    tendsto_norm_h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Right_selectedState_zero
      m hNS ht₀ hE hTail hQ hQR i hx

  change
    Tendsto
      (fun h : ℝ => ‖D h‖)
      (𝓝[≠] (0 : ℝ))
      (𝓝 0)
    at hDNorm

  have hQrNorm :=
    tendsto_norm_h3PreterminalSelectedVelocitySpectralSlopeQuadraticRemainderRadialFourierL2_zero
      m hNS ht₀ hE hTail hQ hQR i hx

  change
    Tendsto
      (fun h : ℝ => ‖Qr h‖)
      (𝓝[≠] (0 : ℝ))
      (𝓝 0)
    at hQrNorm

  have hL :
      Tendsto L
        (𝓝[≠] (0 : ℝ))
        (𝓝 (0 : H3FourierComplexL2)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simpa only [sub_zero] using hLNorm

  have hD :
      Tendsto D
        (𝓝[≠] (0 : ℝ))
        (𝓝 (0 : H3FourierComplexL2)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simpa only [sub_zero] using hDNorm

  have hQr :
      Tendsto Qr
        (𝓝[≠] (0 : ℝ))
        (𝓝 (0 : H3FourierComplexL2)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simpa only [sub_zero] using hQrNorm

  have hSum :
      Tendsto
        (fun h : ℝ => L h + D h + Qr h)
        (𝓝[≠] (0 : ℝ))
        (𝓝 (0 : H3FourierComplexL2)) := by
    have hAdd :=
      (hL.add hD).add hQr
    simpa only [zero_add] using hAdd

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

  have hEq :
      (fun h : ℝ =>
        h3PreterminalSelectedForcingRadialSlopeErrorFourierL2OnSlab
          m hNS ht₀ hE hTail hQ hQR i hx h)
        =ᶠ[(𝓝[≠] (0 : ℝ))]
      (fun h : ℝ =>
        L h + D h + Qr h) := by

    filter_upwards
      [self_mem_nhdsWithin, hArgInterior]
      with h hh hxh

    have hh0 :
        h ≠ 0 := by
      simpa only [
        Set.mem_compl_iff,
        Set.mem_singleton_iff
      ] using hh

    exact
      h3PreterminalSelectedForcingRadialSlopeErrorFourierL2OnSlab_eq_channels
        m hNS ht₀ hE hTail hQ hQR i hx hh0 hxh

  exact
    Tendsto.congr'
      hEq.symm
      hSum

/--
Norm form of the selected forcing quotient closure.
-/
theorem tendsto_norm_h3PreterminalSelectedForcingRadialSlopeErrorFourierL2OnSlab_zero
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
        ‖h3PreterminalSelectedForcingRadialSlopeErrorFourierL2OnSlab
          m hNS ht₀ hE hTail hQ hQR i hx h‖)
      (𝓝[≠] (0 : ℝ))
      (𝓝 0) := by

  have hBase :=
    tendsto_h3PreterminalSelectedForcingRadialSlopeErrorFourierL2OnSlab_zero
      m hNS ht₀ hE hTail hQ hQR i hx

  have hNorm :=
    (continuous_norm.tendsto
      (0 : H3FourierComplexL2)).comp hBase

  change
    Tendsto
      (fun h : ℝ =>
        ‖h3PreterminalSelectedForcingRadialSlopeErrorFourierL2OnSlab
          m hNS ht₀ hE hTail hQ hQR i hx h‖)
      (𝓝[≠] (0 : ℝ))
      (𝓝 ‖(0 : H3FourierComplexL2)‖)
    at hNorm

  simpa only [norm_zero] using hNorm

/-! ## Genuine forcing derivative -/

/--
At every strict interior positive slab point, the extended selected nonlinear
forcing radial `L²` path has derivative equal to the canonical product-rule
candidate.
-/
theorem h3PreterminalSelectedForcingRadialFourierL2OnSlabExtension_hasDerivAt
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
    HasDerivAt
      (h3PreterminalSelectedForcingRadialFourierL2OnSlabExtension
        m hNS ht₀ hE hTail hQ hQR i)
      (
        h3PreterminalSelectedForcingTimeDerivativeRadialFourierL2OnSlab
          m hNS ht₀ hE hTail hQ hQR i
          ⟨x, hx.1.le, hx.2.le⟩
      )
      x := by

  rw [hasDerivAt_iff_tendsto_slope_zero]

  let C : H3FourierComplexL2 :=
    h3PreterminalSelectedForcingTimeDerivativeRadialFourierL2OnSlab
      m hNS ht₀ hE hTail hQ hQR i
      ⟨x, hx.1.le, hx.2.le⟩

  have hErr :=
    tendsto_h3PreterminalSelectedForcingRadialSlopeErrorFourierL2OnSlab_zero
      m hNS ht₀ hE hTail hQ hQR i hx

  change
    Tendsto
      (fun t : ℝ =>
        t⁻¹ •
            (
              h3PreterminalSelectedForcingRadialFourierL2OnSlabExtension
                  m hNS ht₀ hE hTail hQ hQR i (x + t)
                -
              h3PreterminalSelectedForcingRadialFourierL2OnSlabExtension
                  m hNS ht₀ hE hTail hQ hQR i x
            )
          -
        C)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (0 : H3FourierComplexL2))
    at hErr

  have hConst :
      Tendsto
        (fun _t : ℝ => C)
        (𝓝[≠] (0 : ℝ))
        (𝓝 C) :=
    tendsto_const_nhds

  have hSlope :=
    hErr.add hConst

  simpa only [
    sub_add_cancel,
    zero_add,
    C
  ] using hSlope

end

end Euclidean
end Bridge
end PrimeTensor
