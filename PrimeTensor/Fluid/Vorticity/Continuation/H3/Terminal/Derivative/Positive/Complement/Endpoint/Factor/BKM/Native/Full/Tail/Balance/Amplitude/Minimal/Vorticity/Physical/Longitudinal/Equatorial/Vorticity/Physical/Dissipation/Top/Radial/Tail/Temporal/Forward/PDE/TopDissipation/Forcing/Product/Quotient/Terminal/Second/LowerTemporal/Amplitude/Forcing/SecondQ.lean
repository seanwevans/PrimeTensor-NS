import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Bound.Forcing

/-!
# Second-q forcing state under the order-two radial Leray hierarchy

After resolving the fourth-temporal and sixth-diffusion scalar channels, the
remaining nontrivial scalar channel is lower temporal.  Its strict PDE balance

    d/dt(q û_j) = -q² û_j - q F_j

contains the canonical second-q forcing state `q F_j`.

Since

    q(ξ) = (2π)^2 |ξ|^2,

the second-q forcing state is exactly a fixed scalar multiple of the generic
order-two radial Leray package.  The generic finite-dimensional forcing
estimate therefore bounds it by a finite sum of order-three scalar
product-convolution norms.

Order two requires input raw moment

    2 * (2 + 1) = 6,

which is already available for every terminal velocity coordinate.

This file only packages that existing estimate at terminal physical time.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalSecondQForcingAmplitude
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalSecondQForcingAmplitude :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

set_option maxHeartbeats 1800000

theorem h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLerayTwo
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
        (((2 * (2 + 1) : ℕ) : ℝ))
        (U k) := by

  dsimp only

  intro k

  have h :=
    h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_nat
      hH3 hClass ht 6 (by norm_num) k

  convert h using 1 <;> norm_num

noncomputable def h3TerminalForcingSecondRadialLerayFourierL2At
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
  let h6 :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (2 + 1) : ℕ) : ℝ))
          (U k) :=
    h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLerayTwo
      hH3 hClass ht
  h3RawFinLerayOuterProductDivergenceRadialFourierL2
    2 U U j h6 h6

theorem h3TerminalForcingSecondRadialLerayFourierL2At_ae
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
      h3TerminalForcingSecondRadialLerayFourierL2At
        hH3 hClass ht j :
      H3FourierComplexL2
    ) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ 2 : ℝ) : ℂ) *
        h3RawFinLerayOuterProductDivergence U U j ξ) := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  let h6 :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (2 + 1) : ℕ) : ℝ))
          (U k) :=
    h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLerayTwo
      hH3 hClass ht

  change
    ((
      h3RawFinLerayOuterProductDivergenceRadialFourierL2
        2 U U j h6 h6 :
      H3FourierComplexL2
    ) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ 2 : ℝ) : ℂ) *
        h3RawFinLerayOuterProductDivergence U U j ξ)

  exact
    h3RawFinLerayOuterProductDivergenceRadialFourierL2_ae
      2 U U j h6 h6

/--
The canonical second-q forcing state is exactly `(2π)^2` times the terminal
order-two radial Leray package.
-/
theorem h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At_eq_smul_secondRadialLeray
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At
        hH3 hClass ht j
      =
    ((2 * Real.pi) ^ 2 : ℝ) •
      h3TerminalForcingSecondRadialLerayFourierL2At
        hH3 hClass ht j := by

  have hTerminalAE :=
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At_ae
      hH3 hClass ht j

  have hRadialAE :=
    h3TerminalForcingSecondRadialLerayFourierL2At_ae
      hH3 hClass ht j

  have hSmulAE :=
    MeasureTheory.Lp.coeFn_smul
      (((2 * Real.pi) ^ 2 : ℝ))
      (h3TerminalForcingSecondRadialLerayFourierL2At
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
Explicit finite-dimensional bound for the canonical second-q forcing state.
-/
theorem norm_h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At_le_radialLeray
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
    let h6 :
        ∀ k : Fin 3,
          H3RawFourierMomentIntegrable
            (((2 * (2 + 1) : ℕ) : ℝ))
            (U k) :=
      h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLerayTwo
        hH3 hClass ht
    ‖h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At
        hH3 hClass ht j‖
      ≤
    ((2 * Real.pi) ^ 2 : ℝ)
      *
    (
      ∑ k : Fin 3,
        2 *
          (
            ∑ l : Fin 3,
              (2 * Real.pi) *
                ‖h3RawProductConvolutionRadialFourierL2
                    3
                    (U k) (U l)
                    (h6 k) (h6 l)‖
          )
    ) := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  let h6 :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (2 + 1) : ℕ) : ℝ))
          (U k) :=
    h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLerayTwo
      hH3 hClass ht

  have hLeray :
      ‖h3RawFinLerayOuterProductDivergenceRadialFourierL2
          2 U U j h6 h6‖
        ≤
      ∑ k : Fin 3,
        2 *
          (
            ∑ l : Fin 3,
              (2 * Real.pi) *
                ‖h3RawProductConvolutionRadialFourierL2
                    3
                    (U k) (U l)
                    (h6 k) (h6 l)‖
          ) := by

    exact
      norm_h3RawFinLerayOuterProductDivergenceRadialFourierL2_le
        2 U U j h6 h6

  have hEq :=
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At_eq_smul_secondRadialLeray
      hH3 hClass ht j

  rw [hEq]

  change
    ‖((2 * Real.pi) ^ 2 : ℝ) •
        h3RawFinLerayOuterProductDivergenceRadialFourierL2
          2 U U j h6 h6‖
      ≤
    ((2 * Real.pi) ^ 2 : ℝ)
      *
    (
      ∑ k : Fin 3,
        2 *
          (
            ∑ l : Fin 3,
              (2 * Real.pi) *
                ‖h3RawProductConvolutionRadialFourierL2
                    3
                    (U k) (U l)
                    (h6 k) (h6 l)‖
          )
    )

  rw [norm_smul]

  have hCoeff0 :
      0 ≤ ((2 * Real.pi) ^ 2 : ℝ) := by
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
The physical second-q forcing mass is bounded by the square of the explicit
order-two radial Leray envelope.
-/
theorem h3TerminalPhysicalTopDissipationForcingSecondQMassAt_le_sq_radialLeray
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
    let h6 :
        ∀ k : Fin 3,
          H3RawFourierMomentIntegrable
            (((2 * (2 + 1) : ℕ) : ℝ))
            (U k) :=
      h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLerayTwo
        hH3 hClass ht
    h3TerminalPhysicalTopDissipationForcingSecondQMassAt
        hH3 hClass ht j
      ≤
    (
      ((2 * Real.pi) ^ 2 : ℝ)
        *
      (
        ∑ k : Fin 3,
          2 *
            (
              ∑ l : Fin 3,
                (2 * Real.pi) *
                  ‖h3RawProductConvolutionRadialFourierL2
                      3
                      (U k) (U l)
                      (h6 k) (h6 l)‖
            )
      )
    ) ^ 2 := by

  dsimp only

  have hNorm :=
    norm_h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At_le_radialLeray
      hH3 hClass ht j

  let E : ℝ :=
    ((2 * Real.pi) ^ 2 : ℝ)
      *
    (
      ∑ k : Fin 3,
        2 *
          (
            ∑ l : Fin 3,
              (2 * Real.pi) *
                ‖h3RawProductConvolutionRadialFourierL2
                    3
                    (h3TerminalVelocitySpectralStateAt
                      hH3 t
                      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩ k)
                    (h3TerminalVelocitySpectralStateAt
                      hH3 t
                      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩ l)
                    ((h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLerayTwo
                      hH3 hClass ht) k)
                    ((h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLerayTwo
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

  rw [
    ← norm_sq_h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At
      hH3 hClass ht j
  ]

  change
    ‖h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At
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
