import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Sixth
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Bound.Forcing

/-!
# Fourth-q forcing state under the order-four radial Leray hierarchy

The remaining fourth-temporal amplitude obstruction is the canonical forcing
state

    q(ξ)^2 F_j(U,U)(ξ).

Since

    q(ξ)^2 = (2π)^4 |ξ|^4,

this is exactly a fixed scalar multiple of the generic order-four radial Leray
package.  The generic finite-dimensional forcing estimate therefore bounds it
by a finite sum of order-five scalar product-convolution norms.

Order four requires input raw moment

    2 * (4 + 1) = 10,

which is already available for every terminal velocity coordinate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalFourthQForcingAmplitude
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalFourthQForcingAmplitude :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

set_option maxHeartbeats 1800000

theorem h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLerayFour
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
        (((2 * (4 + 1) : ℕ) : ℝ))
        (U k) := by

  dsimp only

  intro k

  have h :=
    h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_nat
      hH3 hClass ht 10 (by norm_num) k

  convert h using 1 <;> norm_num

noncomputable def h3TerminalForcingFourthRadialLerayFourierL2At
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
  let h10 :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (4 + 1) : ℕ) : ℝ))
          (U k) :=
    h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLerayFour
      hH3 hClass ht
  h3RawFinLerayOuterProductDivergenceRadialFourierL2
    4 U U j h10 h10

theorem h3TerminalForcingFourthRadialLerayFourierL2At_ae
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
      h3TerminalForcingFourthRadialLerayFourierL2At
        hH3 hClass ht j :
      H3FourierComplexL2
    ) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ 4 : ℝ) : ℂ) *
        h3RawFinLerayOuterProductDivergence U U j ξ) := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  let h10 :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (4 + 1) : ℕ) : ℝ))
          (U k) :=
    h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLerayFour
      hH3 hClass ht

  change
    ((
      h3RawFinLerayOuterProductDivergenceRadialFourierL2
        4 U U j h10 h10 :
      H3FourierComplexL2
    ) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ 4 : ℝ) : ℂ) *
        h3RawFinLerayOuterProductDivergence U U j ξ)

  exact
    h3RawFinLerayOuterProductDivergenceRadialFourierL2_ae
      4 U U j h10 h10

/--
The canonical fourth-q forcing state is exactly `(2π)^4` times the terminal
order-four radial Leray package.
-/
theorem h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At_eq_smul_fourthRadialLeray
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At
        hH3 hClass ht j
      =
    ((2 * Real.pi) ^ 4 : ℝ) •
      h3TerminalForcingFourthRadialLerayFourierL2At
        hH3 hClass ht j := by

  have hTerminalAE :=
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At_ae
      hH3 hClass ht j

  have hRadialAE :=
    h3TerminalForcingFourthRadialLerayFourierL2At_ae
      hH3 hClass ht j

  have hSmulAE :=
    MeasureTheory.Lp.coeFn_smul
      (((2 * Real.pi) ^ 4 : ℝ))
      (h3TerminalForcingFourthRadialLerayFourierL2At
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
Explicit finite-dimensional bound for the canonical fourth-q forcing state.
-/
theorem norm_h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At_le_radialLeray
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
    let h10 :
        ∀ k : Fin 3,
          H3RawFourierMomentIntegrable
            (((2 * (4 + 1) : ℕ) : ℝ))
            (U k) :=
      h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLerayFour
        hH3 hClass ht
    ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At
        hH3 hClass ht j‖
      ≤
    ((2 * Real.pi) ^ 4 : ℝ)
      *
    (
      ∑ k : Fin 3,
        2 *
          (
            ∑ l : Fin 3,
              (2 * Real.pi) *
                ‖h3RawProductConvolutionRadialFourierL2
                    5
                    (U k) (U l)
                    (h10 k) (h10 l)‖
          )
    ) := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  let h10 :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (4 + 1) : ℕ) : ℝ))
          (U k) :=
    h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLerayFour
      hH3 hClass ht

  have hLeray :
      ‖h3RawFinLerayOuterProductDivergenceRadialFourierL2
          4 U U j h10 h10‖
        ≤
      ∑ k : Fin 3,
        2 *
          (
            ∑ l : Fin 3,
              (2 * Real.pi) *
                ‖h3RawProductConvolutionRadialFourierL2
                    5
                    (U k) (U l)
                    (h10 k) (h10 l)‖
          ) := by

    exact
      norm_h3RawFinLerayOuterProductDivergenceRadialFourierL2_le
        4 U U j h10 h10

  have hEq :=
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At_eq_smul_fourthRadialLeray
      hH3 hClass ht j

  rw [hEq]

  change
    ‖((2 * Real.pi) ^ 4 : ℝ) •
        h3RawFinLerayOuterProductDivergenceRadialFourierL2
          4 U U j h10 h10‖
      ≤
    ((2 * Real.pi) ^ 4 : ℝ)
      *
    (
      ∑ k : Fin 3,
        2 *
          (
            ∑ l : Fin 3,
              (2 * Real.pi) *
                ‖h3RawProductConvolutionRadialFourierL2
                    5
                    (U k) (U l)
                    (h10 k) (h10 l)‖
          )
    )

  rw [norm_smul]

  have hCoeff0 :
      0 ≤ ((2 * Real.pi) ^ 4 : ℝ) := by
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
The physical fourth-q forcing mass is bounded by the square of the explicit
order-four radial Leray envelope.
-/
theorem h3TerminalPhysicalTopDissipationForcingFourthQMassAt_le_sq_radialLeray
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
    let h10 :
        ∀ k : Fin 3,
          H3RawFourierMomentIntegrable
            (((2 * (4 + 1) : ℕ) : ℝ))
            (U k) :=
      h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLerayFour
        hH3 hClass ht
    h3TerminalPhysicalTopDissipationForcingFourthQMassAt
        hH3 hClass ht j
      ≤
    (
      ((2 * Real.pi) ^ 4 : ℝ)
        *
      (
        ∑ k : Fin 3,
          2 *
            (
              ∑ l : Fin 3,
                (2 * Real.pi) *
                  ‖h3RawProductConvolutionRadialFourierL2
                      5
                      (U k) (U l)
                      (h10 k) (h10 l)‖
            )
      )
    ) ^ 2 := by

  dsimp only

  have hNorm :=
    norm_h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At_le_radialLeray
      hH3 hClass ht j

  let E : ℝ :=
    ((2 * Real.pi) ^ 4 : ℝ)
      *
    (
      ∑ k : Fin 3,
        2 *
          (
            ∑ l : Fin 3,
              (2 * Real.pi) *
                ‖h3RawProductConvolutionRadialFourierL2
                    5
                    (h3TerminalVelocitySpectralStateAt
                      hH3 t
                      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩ k)
                    (h3TerminalVelocitySpectralStateAt
                      hH3 t
                      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩ l)
                    ((h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLerayFour
                      hH3 hClass ht) k)
                    ((h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLerayFour
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
    ← h3TerminalPhysicalTopDissipationForcingFourthQMassPath_eq
      hH3 hClass ht j
  ]

  rw [
    h3TerminalPhysicalTopDissipationForcingFourthQMassPath_eq_norm_sq_fourthQFourierL2Path
      hH3 hClass ht j
  ]

  rw [
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path_eq
      hH3 hClass ht j
  ]

  change
    ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At
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
