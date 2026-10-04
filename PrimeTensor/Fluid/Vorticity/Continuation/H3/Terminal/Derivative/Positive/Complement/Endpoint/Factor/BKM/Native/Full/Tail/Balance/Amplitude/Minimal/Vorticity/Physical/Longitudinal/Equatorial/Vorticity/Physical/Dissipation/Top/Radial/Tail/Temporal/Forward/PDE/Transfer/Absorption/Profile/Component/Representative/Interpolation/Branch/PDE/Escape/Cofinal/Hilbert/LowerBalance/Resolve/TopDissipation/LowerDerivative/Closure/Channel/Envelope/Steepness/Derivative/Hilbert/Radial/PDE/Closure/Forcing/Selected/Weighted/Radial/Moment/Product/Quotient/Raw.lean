import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient

/-!
# Raw representatives and moments of selected radial slope errors

`Quotient` packages the strong order-`m` Fourier `L²` slope error

    E_m(h)
      =
    h⁻¹ • (V_m(x+h) - V_m(x)) - G_m(x).

For increments which remain in the positive compact slab, all radial orders are
literal powers of one common unweighted raw quotient.  This file identifies
that quotient and immediately feeds the order-`p` and order-`p+2` error
packages into the inverse-Bessel Cauchy--Schwarz bridge.

No new radial `L²` object is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedRawSlopeError
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1800000

/-! ## Common raw slope error -/

/--
The literal unweighted selected velocity slope error at a strict interior slab
time.  The projected-RHS term is taken from the already-compiled order-zero
radial package, so every positive radial order can be compared against exactly
the same raw object.
-/
noncomputable def h3PreterminalSelectedVelocityRawSlopeErrorFourierOnSlab
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
    (ξ : H3FourierPoint3) :
    ℂ :=
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
  ((h⁻¹ : ℝ) : ℂ) *
      (
        (
          (
            h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              (one_pos : (0 : ℝ) < 1)
              U₀ hA hU₀
              (x + h) i :
            H3FourierComplexL2
          ) ξ
        )
          -
        (
          (
            h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              (one_pos : (0 : ℝ) < 1)
              U₀ hA hU₀
              x i :
            H3FourierComplexL2
          ) ξ
        )
      )
    -
  (
    (
      h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
        0 hNS ht₀ hE hTail hQ hQR i sx :
      H3FourierComplexL2
    ) ξ
  )

/-! ## Radial representative identity -/

/--
If the shifted time remains in the compact slab, the compiled order-`m`
selected slope error is almost everywhere exactly `|ξ|^m` times the common
raw slope error.
-/
theorem h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab_ae_raw
    (m : ℕ)
    (hm : 2 ≤ m)
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
    (
      (
        h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
          m hm
          hNS ht₀ hE hTail hQ hQR i hx h :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        h3PreterminalSelectedVelocityRawSlopeErrorFourierOnSlab
          hNS ht₀ hE hTail hQ hQR i hx h ξ) := by

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  have hHalfLe :
      Q / 2 ≤ Q := by
    linarith

  let sx : Set.Icc (Q / 2) Q :=
    ⟨x, hx.1.le, hx.2.le⟩

  let sxh : Set.Icc (Q / 2) Q :=
    ⟨x + h, hxh⟩

  let VmH : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
      m hm
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      (by positivity : 0 < Q / 2)
      hQR
      sxh i

  let Vm0 : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
      m hm
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      (by positivity : 0 < Q / 2)
      hQR
      sx i

  let Rm : H3FourierComplexL2 :=
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
      m hNS ht₀ hE hTail hQ hQR i sx

  let R0 : H3FourierComplexL2 :=
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
      0 hNS ht₀ hE hTail hQ hQR i sx

  have hVmH :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact_ae
      m hm
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      (by positivity : 0 < Q / 2)
      hQR
      sxh i

  have hVm0 :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact_ae
      m hm
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      (by positivity : 0 < Q / 2)
      hQR
      sx i

  have hRm :=
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab_ae_eq_radial_projectedRHS
      m hNS ht₀ hE hTail hQ hQR i sx

  have hR0 :=
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab_ae_eq_radial_projectedRHS
      0 hNS ht₀ hE hTail hQ hQR i sx

  dsimp only at hRm hR0

  have hSub :=
    MeasureTheory.Lp.coeFn_sub
      VmH Vm0

  have hScale :=
    MeasureTheory.Lp.coeFn_smul
      (h⁻¹ : ℝ)
      (VmH - Vm0)

  have hErr :=
    MeasureTheory.Lp.coeFn_sub
      ((h⁻¹ : ℝ) • (VmH - Vm0))
      Rm

  unfold
    h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab

  rw [
    Set.IccExtend_of_mem
      hHalfLe
      (fun s : Set.Icc (Q / 2) Q =>
        h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
          m hm
          (one_pos : (0 : ℝ) < 1)
          U₀ hA hU₀
          (by positivity : 0 < Q / 2)
          hQR s i)
      hxh
  ]

  rw [
    Set.IccExtend_of_mem
      hHalfLe
      (fun s : Set.Icc (Q / 2) Q =>
        h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
          m hm
          (one_pos : (0 : ℝ) < 1)
          U₀ hA hU₀
          (by positivity : 0 < Q / 2)
          hQR s i)
      ⟨hx.1.le, hx.2.le⟩
  ]

  change
    (
      (
        ((h⁻¹ : ℝ) • (VmH - Vm0) - Rm :
          H3FourierComplexL2)
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        h3PreterminalSelectedVelocityRawSlopeErrorFourierOnSlab
          hNS ht₀ hE hTail hQ hQR i hx h ξ)

  filter_upwards [
    hVmH,
    hVm0,
    hRm,
    hR0,
    hSub,
    hScale,
    hErr
  ] with ξ hVmHξ hVm0ξ hRmξ hR0ξ hSubξ hScaleξ hErrξ

  rw [hErrξ]
  simp only [Pi.sub_apply]
  rw [hScaleξ]
  simp only [Pi.smul_apply, Complex.real_smul]
  rw [hSubξ]
  simp only [Pi.sub_apply]

  rw [hVmHξ, hVm0ξ, hRmξ]

  have hR0ξ' :
      R0 ξ
        =
      (
        h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
          hNS ht₀ hE hTail
          (h3SelectedProjectedRHSSlabRadius hE hQ hQR sx)
          i :
        H3FourierComplexL2
      ) ξ := by
    simpa only [
      pow_zero,
      Complex.ofReal_one,
      one_mul
    ] using hR0ξ

  unfold
    h3PreterminalSelectedVelocityRawSlopeErrorFourierOnSlab

  dsimp only

  rw [hR0ξ']

  ring

/-! ## Raw moment bridge -/

/--
The common raw slope error has an integrable order-`p` moment whenever the
shifted time stays in the compact slab.  The proof uses exactly the order-`p`
and order-`p+2` strong slope-error packages.
-/
theorem h3PreterminalSelectedVelocityRawSlopeError_natMoment_integrable
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
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ p *
          ‖h3PreterminalSelectedVelocityRawSlopeErrorFourierOnSlab
            hNS ht₀ hE hTail hQ hQR i hx h ξ‖)
      (volume : Measure H3FourierPoint3) := by

  exact
    h3RawFourier_natMoment_integrable_of_two_radialL2
      p
      (h3PreterminalSelectedVelocityRawSlopeErrorFourierOnSlab
        hNS ht₀ hE hTail hQ hQR i hx h)
      (h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
        p hp
        hNS ht₀ hE hTail hQ hQR i hx h)
      (h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
        (p + 2) (by omega)
        hNS ht₀ hE hTail hQ hQR i hx h)
      (h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab_ae_raw
        p hp
        hNS ht₀ hE hTail hQ hQR i hx h hxh)
      (by
        simpa only [Nat.add_assoc] using
          h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab_ae_raw
            (p + 2) (by omega)
            hNS ht₀ hE hTail hQ hQR i hx h hxh)

/--
Quantitative inverse-Bessel bound for the raw order-`p` slope-error moment.
This is the form needed by the nonlinear forcing quotient estimate.
-/
theorem integral_h3PreterminalSelectedVelocityRawSlopeError_natMoment_le
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
    (
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ p *
          ‖h3PreterminalSelectedVelocityRawSlopeErrorFourierOnSlab
            hNS ht₀ hE hTail hQ hQR i hx h ξ‖
      ∂volume
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

  exact
    integral_h3RawFourier_natMoment_le_bessel_mul_norms
      p
      (h3PreterminalSelectedVelocityRawSlopeErrorFourierOnSlab
        hNS ht₀ hE hTail hQ hQR i hx h)
      (h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
        p hp
        hNS ht₀ hE hTail hQ hQR i hx h)
      (h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab
        (p + 2) (by omega)
        hNS ht₀ hE hTail hQ hQR i hx h)
      (h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab_ae_raw
        p hp
        hNS ht₀ hE hTail hQ hQR i hx h hxh)
      (by
        simpa only [Nat.add_assoc] using
          h3PreterminalSelectedVelocityNatRadialSlopeErrorFourierL2OnSlab_ae_raw
            (p + 2) (by omega)
            hNS ht₀ hE hTail hQ hQR i hx h hxh)

end

end Euclidean
end Bridge
end PrimeTensor
