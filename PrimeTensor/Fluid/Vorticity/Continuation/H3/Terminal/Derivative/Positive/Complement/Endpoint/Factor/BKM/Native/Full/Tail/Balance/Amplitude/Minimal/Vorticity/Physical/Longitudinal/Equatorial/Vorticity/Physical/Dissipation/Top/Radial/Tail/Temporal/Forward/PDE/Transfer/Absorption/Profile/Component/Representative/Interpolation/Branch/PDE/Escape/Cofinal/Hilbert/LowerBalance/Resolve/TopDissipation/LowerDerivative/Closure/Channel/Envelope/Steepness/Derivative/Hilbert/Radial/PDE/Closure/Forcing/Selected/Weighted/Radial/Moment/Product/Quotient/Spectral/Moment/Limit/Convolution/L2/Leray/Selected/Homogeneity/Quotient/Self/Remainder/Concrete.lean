import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder

/-!
# Concrete selected raw Leray quotient identity

The generic quotient algebra is now specialized to the actual selected mild
spectral path.  At a base point `x`, write

    U = W(x),
    V = W(x+h),
    R = projectedRHS(x),
    D = h⁻¹ • (V-U),
    E = D-R.

For nonzero `h`, the nonlinear forcing difference quotient minus its product
rule candidate is exactly

    N(E,U) + N(U,E)
      + h [N(R,R) + N(E,R) + N(R,E) + N(E,E)].

The final bracket is precisely the pointwise representative of the quadratic
remainder package from the preceding file.

No estimate or limiting argument is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedRawLerayConcreteQuotient
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1600000

/--
Concrete selected product-rule error identity for one raw finite Leray forcing
coordinate.
-/
theorem h3PreterminalSelectedRawFinLeray_differenceQuotient_productRule_error
    {E0 : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x h : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E0)
    (hTail : CanonicalH3TailDataFrom u t₀ T E0)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E0)
    (i : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q)
    (hh : h ≠ 0)
    (ξ : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState
          hNS ht₀ hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNS ht₀ hE hTail)
    let U : H3SpectralFinVectorState :=
      W x
    let V : H3SpectralFinVectorState :=
      W (x + h)
    let R : H3SpectralFinVectorState :=
      h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
        hNS ht₀ hE hTail hQ hQR
        ⟨x, hx.1.le, hx.2.le⟩
    let D : H3SpectralFinVectorState :=
      (h⁻¹ : ℝ) • (V - U)
    let Err : H3SpectralFinVectorState :=
      h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
        hNS ht₀ hE hTail hQ hQR hx h
    (h⁻¹ : ℝ) •
          (
            h3RawFinLerayOuterProductDivergence V V i ξ -
              h3RawFinLerayOuterProductDivergence U U i ξ
          )
        -
      (
        h3RawFinLerayOuterProductDivergence R U i ξ +
          h3RawFinLerayOuterProductDivergence U R i ξ
      )
      =
    h3RawFinLerayOuterProductDivergence Err U i ξ +
      h3RawFinLerayOuterProductDivergence U Err i ξ
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
      ) := by

  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState
        hNS ht₀ hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail)

  let U : H3SpectralFinVectorState :=
    W x

  let V : H3SpectralFinVectorState :=
    W (x + h)

  let R : H3SpectralFinVectorState :=
    h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
      hNS ht₀ hE hTail hQ hQR
      ⟨x, hx.1.le, hx.2.le⟩

  let D : H3SpectralFinVectorState :=
    (h⁻¹ : ℝ) • (V - U)

  let Err : H3SpectralFinVectorState :=
    h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
      hNS ht₀ hE hTail hQ hQR hx h

  have hQuot :
      (h⁻¹ : ℝ) • (V - U) = D := by
    rfl

  have hStep :
      V - U = h • D := by
    dsimp only [D]
    rw [smul_smul, mul_inv_cancel₀ hh, one_smul]

  have hError :
      Err = D - R := by
    dsimp only [
      Err,
      D,
      R,
      U,
      V,
      W,
      h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
    ]

  have hBase :=
    h3RawFinLerayOuterProductDivergence_differenceQuotient_productRule_error
      h U V D R Err i ξ hQuot hStep hError

  have hD :
      D = R + Err := by
    rw [hError]
    abel

  rw [hD] at hBase

  rw [
    h3RawFinLerayOuterProductDivergence_add_left,
    h3RawFinLerayOuterProductDivergence_add_right,
    h3RawFinLerayOuterProductDivergence_add_right
  ] at hBase

  exact
    hBase.trans
      (by
        dsimp only [
          U,
          R,
          Err,
          W
        ]
        simp only [smul_add]
        abel)

end

end Euclidean
end Bridge
end PrimeTensor
