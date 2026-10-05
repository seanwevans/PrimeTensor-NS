import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete.Representative.Closure.ForcingWeights.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square.Factor.Norm.PDE.Factor.Amplitude.Sixth.Factors.Factor.Overlap.Raw.Mass.Higher.Moment
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Bound.Forcing

/-!
# Terminal third-q forcing under the radial Leray hierarchy

The remaining sixth-diffusion factor is

    q(ξ)^3 F_j(U,U)(ξ).

Since `q(ξ)^3 = (2π)^6 |ξ|^6`, this is exactly a constant multiple of the
generic order-six radial finite Leray package.

The preceding terminal-moment checkpoint supplies raw moment order fourteen
for every terminal spectral coordinate.  That is exactly the doubled input
moment `2(6+1)` required by the generic order-six Leray estimate.

This file therefore places the canonical terminal third-q forcing factor under
the already-compiled quantitative radial Leray hierarchy, with no selected
restart chart in the final statements.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3TerminalThirdQForcingBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalThirdQForcingBound :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
The terminal state carries exactly the doubled moment required by an
order-six radial Leray package.
-/
theorem h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLeraySix
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    ∀ k : Fin 3,
      H3RawFourierMomentIntegrable
        (((2 * (6 + 1) : ℕ) : ℝ))
        (U k) := by

  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat] using
    h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_fourteen
      hH3 hClass ht

/--
Canonical order-six radial finite Leray package built directly from the
terminal spectral state.
-/
noncomputable def h3TerminalForcingSixthRadialLerayFourierL2At
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    H3FourierComplexL2 :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let h14 :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (6 + 1) : ℕ) : ℝ))
          (U k) :=
    h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLeraySix
      hH3 hClass ht
  h3RawFinLerayOuterProductDivergenceRadialFourierL2
    6 U U j h14 h14

/--
The terminal radial Leray package has the literal order-six raw forcing
representative.
-/
theorem h3TerminalForcingSixthRadialLerayFourierL2At_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    ((
      h3TerminalForcingSixthRadialLerayFourierL2At
        hH3 hClass ht j :
      H3FourierComplexL2
    ) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ 6 : ℝ) : ℂ) *
        h3RawFinLerayOuterProductDivergence U U j ξ) := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  let h14 :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (6 + 1) : ℕ) : ℝ))
          (U k) :=
    h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLeraySix
      hH3 hClass ht

  change
    ((
      h3RawFinLerayOuterProductDivergenceRadialFourierL2
        6 U U j h14 h14 :
      H3FourierComplexL2
    ) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ 6 : ℝ) : ℂ) *
        h3RawFinLerayOuterProductDivergence U U j ξ)

  exact
    h3RawFinLerayOuterProductDivergenceRadialFourierL2_ae
      6 U U j h14 h14

/--
The canonical terminal third-q forcing state is exactly `(2π)^6` times the
terminal order-six radial Leray package.
-/
theorem h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At_eq_smul_sixthRadialLeray
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At
        hH3 hClass ht j
      =
    ((2 * Real.pi) ^ 6 : ℝ) •
      h3TerminalForcingSixthRadialLerayFourierL2At
        hH3 hClass ht j := by

  have hTerminalAE :=
    h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At_ae
      hH3 hClass ht j

  have hRadialAE :=
    h3TerminalForcingSixthRadialLerayFourierL2At_ae
      hH3 hClass ht j

  have hSmulAE :=
    MeasureTheory.Lp.coeFn_smul
      (((2 * Real.pi) ^ 6 : ℝ))
      (h3TerminalForcingSixthRadialLerayFourierL2At
        hH3 hClass ht j)

  apply MeasureTheory.Lp.ext

  filter_upwards [hTerminalAE, hSmulAE, hRadialAE]
    with ξ hTerminalξ hSmulξ hRadialξ

  rw [hTerminalξ, hSmulξ]
  simp only [Pi.smul_apply, Complex.real_smul]
  rw [hRadialξ]

  unfold h3FourierGradientSquare

  push_cast
  ring

/--
Quantitative terminal norm bound inherited verbatim from the generic
finite-dimensional order-six radial Leray estimate.
-/
theorem norm_h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At_le_radialLeray
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    let h14 :
        ∀ k : Fin 3,
          H3RawFourierMomentIntegrable
            (((2 * (6 + 1) : ℕ) : ℝ))
            (U k) :=
      h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLeraySix
        hH3 hClass ht
    ‖h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At
        hH3 hClass ht j‖
      ≤
    ((2 * Real.pi) ^ 6 : ℝ)
      *
    (
      ∑ k : Fin 3,
        2 *
          (
            ∑ l : Fin 3,
              (2 * Real.pi) *
                ‖h3RawProductConvolutionRadialFourierL2
                    7
                    (U k) (U l)
                    (h14 k) (h14 l)‖
          )
    ) := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  let h14 :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (6 + 1) : ℕ) : ℝ))
          (U k) :=
    h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLeraySix
      hH3 hClass ht

  have hLeray :
      ‖h3RawFinLerayOuterProductDivergenceRadialFourierL2
          6 U U j h14 h14‖
        ≤
      ∑ k : Fin 3,
        2 *
          (
            ∑ l : Fin 3,
              (2 * Real.pi) *
                ‖h3RawProductConvolutionRadialFourierL2
                    7
                    (U k) (U l)
                    (h14 k) (h14 l)‖
          ) := by

    exact
      norm_h3RawFinLerayOuterProductDivergenceRadialFourierL2_le
        6 U U j h14 h14

  have hEq :=
    h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At_eq_smul_sixthRadialLeray
      hH3 hClass ht j

  rw [hEq]

  change
    ‖((2 * Real.pi) ^ 6 : ℝ) •
        h3RawFinLerayOuterProductDivergenceRadialFourierL2
          6 U U j h14 h14‖
      ≤
    ((2 * Real.pi) ^ 6 : ℝ)
      *
    (
      ∑ k : Fin 3,
        2 *
          (
            ∑ l : Fin 3,
              (2 * Real.pi) *
                ‖h3RawProductConvolutionRadialFourierL2
                    7
                    (U k) (U l)
                    (h14 k) (h14 l)‖
          )
    )

  rw [norm_smul]

  have hCoeff0 :
      0 ≤ ((2 * Real.pi) ^ 6 : ℝ) := by
    positivity

  rw [
    Real.norm_eq_abs,
    abs_of_nonneg hCoeff0
  ]

  exact
    mul_le_mul_of_nonneg_left
      hLeray
      hCoeff0

/--
Consequently the canonical third-q forcing raw mass is bounded by the square
of the existing radial Leray envelope.
-/
theorem h3TerminalPhysicalTopDissipationForcingThirdQRawMassAt_le_sq_radialLeray
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    let h14 :
        ∀ k : Fin 3,
          H3RawFourierMomentIntegrable
            (((2 * (6 + 1) : ℕ) : ℝ))
            (U k) :=
      h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLeraySix
        hH3 hClass ht
    h3TerminalPhysicalTopDissipationForcingThirdQRawMassAt
        hH3 hClass ht j
      ≤
    (
      ((2 * Real.pi) ^ 6 : ℝ)
        *
      (
        ∑ k : Fin 3,
          2 *
            (
              ∑ l : Fin 3,
                (2 * Real.pi) *
                  ‖h3RawProductConvolutionRadialFourierL2
                      7
                      (U k) (U l)
                      (h14 k) (h14 l)‖
            )
      )
    ) ^ 2 := by

  dsimp only

  have hNorm :=
    norm_h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At_le_radialLeray
      hH3 hClass ht j

  let E : ℝ :=
    ((2 * Real.pi) ^ 6 : ℝ)
      *
    (
      ∑ k : Fin 3,
        2 *
          (
            ∑ l : Fin 3,
              (2 * Real.pi) *
                ‖h3RawProductConvolutionRadialFourierL2
                    7
                    (h3TerminalVelocitySpectralStateAt
                      hH3 t
                      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩ k)
                    (h3TerminalVelocitySpectralStateAt
                      hH3 t
                      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩ l)
                    ((h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLeraySix
                      hH3 hClass ht) k)
                    ((h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLeraySix
                      hH3 hClass ht) l)‖
          )
    )

  have hE0 :
      0 ≤ E := by

    dsimp only [E]

    apply mul_nonneg
    · positivity

    apply Finset.sum_nonneg
    intro k hk

    apply mul_nonneg
    · norm_num

    apply Finset.sum_nonneg
    intro l hl

    exact
      mul_nonneg
        (by positivity)
        (norm_nonneg _)

  unfold
    h3TerminalPhysicalTopDissipationForcingThirdQRawMassAt

  change
    ‖h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At
        hH3 hClass ht j‖ ^ 2
      ≤
    E ^ 2

  exact
    (sq_le_sq₀
      (norm_nonneg _)
      hE0).2
      (by
        dsimp only [E]
        exact hNorm)

end

end Euclidean
end Bridge
end PrimeTensor
