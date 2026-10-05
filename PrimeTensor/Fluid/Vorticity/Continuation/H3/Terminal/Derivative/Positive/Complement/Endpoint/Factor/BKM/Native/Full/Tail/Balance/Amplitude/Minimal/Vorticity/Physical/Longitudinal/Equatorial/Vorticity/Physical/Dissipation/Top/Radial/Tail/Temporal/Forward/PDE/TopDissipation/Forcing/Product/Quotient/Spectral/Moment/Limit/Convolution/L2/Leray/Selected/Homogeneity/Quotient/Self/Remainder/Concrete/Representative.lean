import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete

/-!
# Raw representatives of the selected Leray quotient channels

The analytic limits are already closed.  Before identifying the actual selected
forcing quotient, this file exposes the literal raw Fourier representatives of

* the slope-error/base-state left channel;
* the slope-error/base-state right channel;
* the complete quadratic remainder.

All statements are made on an increment for which `x+h` remains in the positive
compact slab.  This is the only branch relevant in the punctured limit.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedLerayQuotientRepresentatives
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2200000

/-! ## Base-state cross channels -/

/--
Literal radial raw representative of the left slope-error channel against the
selected state at the base point.
-/
theorem h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Left_selectedState_ae
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
    (
      (
        h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Left
          m hNS ht₀ hE hTail hQ hQR i hx U hU h :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        h3RawFinLerayOuterProductDivergence
          (
            h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
              hNS ht₀ hE hTail hQ hQR hx h
          )
          U i ξ) := by

  dsimp only

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

  let S : H3SpectralFinVectorState :=
    h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
      hNS ht₀ hE hTail hQ hQR hx h

  let hS :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (S r) :=
    fun r =>
      h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_natMoment_integrable
        (2 * (m + 1)) (by omega)
        hNS ht₀ hE hTail hQ hQR r hx h hxh

  have hBase :=
    h3RawFinLerayOuterProductDivergenceRadialFourierL2_ae
      m S U i hS hU

  unfold
    h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Left

  simp only [dite_eq_left hxh]

  simpa only [S, U, hU, sx] using hBase

/--
Literal radial raw representative of the right slope-error channel against the
selected state at the base point.
-/
theorem h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Right_selectedState_ae
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
    (
      (
        h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Right
          m hNS ht₀ hE hTail hQ hQR i hx U hU h :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        h3RawFinLerayOuterProductDivergence
          U
          (
            h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
              hNS ht₀ hE hTail hQ hQR hx h
          )
          i ξ) := by

  dsimp only

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

  let S : H3SpectralFinVectorState :=
    h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
      hNS ht₀ hE hTail hQ hQR hx h

  let hS :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (S r) :=
    fun r =>
      h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_natMoment_integrable
        (2 * (m + 1)) (by omega)
        hNS ht₀ hE hTail hQ hQR r hx h hxh

  have hBase :=
    h3RawFinLerayOuterProductDivergenceRadialFourierL2_ae
      m U S i hU hS

  unfold
    h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Right

  simp only [dite_eq_left hxh]

  simpa only [S, U, hU, sx] using hBase

/-! ## Quadratic remainder representative -/

/--
The quadratic remainder package has the literal weighted raw representative
appearing in the concrete selected quotient identity.
-/
theorem h3PreterminalSelectedVelocitySpectralSlopeQuadraticRemainderRadialFourierL2_ae
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
    (hxh : x + h ∈ Set.Icc (Q / 2) Q) :
    let sx : Set.Icc (Q / 2) Q :=
      ⟨x, hx.1.le, hx.2.le⟩
    let R : H3SpectralFinVectorState :=
      h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
        hNS ht₀ hE hTail hQ hQR sx
    let Err : H3SpectralFinVectorState :=
      h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
        hNS ht₀ hE hTail hQ hQR hx h
    (
      (
        h3PreterminalSelectedVelocitySpectralSlopeQuadraticRemainderRadialFourierL2
          m hNS ht₀ hE hTail hQ hQR i hx h :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
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
        )) := by

  dsimp only

  let sx : Set.Icc (Q / 2) Q :=
    ⟨x, hx.1.le, hx.2.le⟩

  let R : H3SpectralFinVectorState :=
    h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
      hNS ht₀ hE hTail hQ hQR sx

  let Err : H3SpectralFinVectorState :=
    h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
      hNS ht₀ hE hTail hQ hQR hx h

  let hR :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (R r) :=
    fun r =>
      h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab_natMoment_integrable
        (2 * (m + 1)) (by omega)
        hNS ht₀ hE hTail hQ hQR r sx

  let hErr :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (Err r) :=
    fun r =>
      h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_natMoment_integrable
        (2 * (m + 1)) (by omega)
        hNS ht₀ hE hTail hQ hQR r hx h hxh

  let RR : H3FourierComplexL2 :=
    h3RawFinLerayOuterProductDivergenceRadialFourierL2
      m R R i hR hR

  let ER : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Left
      m hNS ht₀ hE hTail hQ hQR i hx R hR h

  let RE : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Right
      m hNS ht₀ hE hTail hQ hQR i hx R hR h

  let EE : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Self
      m hNS ht₀ hE hTail hQ hQR i hx h

  have hRR :=
    h3RawFinLerayOuterProductDivergenceRadialFourierL2_ae
      m R R i hR hR

  have hERBase :=
    h3RawFinLerayOuterProductDivergenceRadialFourierL2_ae
      m Err R i hErr hR

  have hREBase :=
    h3RawFinLerayOuterProductDivergenceRadialFourierL2_ae
      m R Err i hR hErr

  have hEEBase :=
    h3RawFinLerayOuterProductDivergenceRadialFourierL2_ae
      m Err Err i hErr hErr

  have hER :
      ((ER : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergence Err R i ξ) := by
    dsimp only [ER]
    unfold
      h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Left
    simp only [dite_eq_left hxh]
    simpa only [Err, R, hR, hErr, sx] using hERBase

  have hRE :
      ((RE : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergence R Err i ξ) := by
    dsimp only [RE]
    unfold
      h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Right
    simp only [dite_eq_left hxh]
    simpa only [Err, R, hR, hErr, sx] using hREBase

  have hEE :
      ((EE : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergence Err Err i ξ) := by
    dsimp only [EE]
    unfold
      h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Self
    simp only [dite_eq_left hxh]
    simpa only [Err, hErr] using hEEBase

  have hAdd₁ :=
    MeasureTheory.Lp.coeFn_add RR ER

  have hAdd₂ :=
    MeasureTheory.Lp.coeFn_add (RR + ER) RE

  have hAdd₃ :=
    MeasureTheory.Lp.coeFn_add (RR + ER + RE) EE

  have hSmul :=
    MeasureTheory.Lp.coeFn_smul
      h
      (RR + ER + RE + EE)

  unfold
    h3PreterminalSelectedVelocitySpectralSlopeQuadraticRemainderRadialFourierL2

  dsimp only [
    sx,
    R,
    hR,
    RR,
    ER,
    RE,
    EE
  ]

  filter_upwards [
    hRR,
    hER,
    hRE,
    hEE,
    hAdd₁,
    hAdd₂,
    hAdd₃,
    hSmul
  ] with ξ hRRξ hERξ hREξ hEEξ hAdd₁ξ hAdd₂ξ hAdd₃ξ hSmulξ

  rw [hSmulξ]
  simp only [Pi.smul_apply, Complex.real_smul]

  rw [hAdd₃ξ]
  simp only [Pi.add_apply]
  rw [hAdd₂ξ]
  simp only [Pi.add_apply]
  rw [hAdd₁ξ]
  simp only [Pi.add_apply]

  rw [hRRξ, hERξ, hREξ, hEEξ]

  ring

end

end Euclidean
end Bridge
end PrimeTensor
