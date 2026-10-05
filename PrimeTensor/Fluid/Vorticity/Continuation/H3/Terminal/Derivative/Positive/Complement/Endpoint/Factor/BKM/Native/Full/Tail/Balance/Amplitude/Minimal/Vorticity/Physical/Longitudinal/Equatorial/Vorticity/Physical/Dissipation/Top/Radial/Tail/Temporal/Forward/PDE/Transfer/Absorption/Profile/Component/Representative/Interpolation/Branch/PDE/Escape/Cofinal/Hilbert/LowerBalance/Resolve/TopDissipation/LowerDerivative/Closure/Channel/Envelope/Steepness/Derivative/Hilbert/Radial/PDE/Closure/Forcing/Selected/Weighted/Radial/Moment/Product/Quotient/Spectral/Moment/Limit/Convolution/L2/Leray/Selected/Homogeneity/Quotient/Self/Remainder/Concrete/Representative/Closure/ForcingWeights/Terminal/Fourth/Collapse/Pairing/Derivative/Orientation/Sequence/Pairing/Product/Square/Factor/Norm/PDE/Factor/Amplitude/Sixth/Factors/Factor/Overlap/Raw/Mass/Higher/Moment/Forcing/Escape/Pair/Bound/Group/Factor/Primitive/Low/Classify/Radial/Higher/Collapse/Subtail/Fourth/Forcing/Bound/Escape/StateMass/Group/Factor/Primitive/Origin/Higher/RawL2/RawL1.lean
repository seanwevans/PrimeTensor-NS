import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete.Representative.Closure.ForcingWeights.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square.Factor.Norm.PDE.Factor.Amplitude.Sixth.Factors.Factor.Overlap.Raw.Mass.Higher.Moment.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.Fourth.Forcing.Bound.Escape.StateMass.Group.Factor.Primitive.Origin.Higher.RawL2
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.L1.Bound
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Absorb projected-RHS raw L¹ escape

The remaining projected-RHS raw `L¹` mass is controlled directly from the
recorded raw PDE identity

    R_i = -q U_i - P div(U ⊗ U)_i.

The nonlinear forcing has the existing H³-bilinear Fourier-`L¹` bound.  For
the diffusion term, `q(ξ) = (2π)² |ξ|²`, and

    |ξ|² ≤ 1 + |ξ|¹⁴.

Thus the diffusion `L¹` mass is controlled by the terminal velocity raw `L¹`
mass plus its already-classified order-fourteen moment.  Raw velocity `L¹`
is absorbed by physical H³ energy, while the order-fourteen moment is already
absorbed by the extended higher-radial hierarchy.

Consequently fourth-temporal escape now leaves exactly one projected-RHS
primitive: the order-ten moment.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 3000000

noncomputable local instance axisFintypeH3TerminalFourthQProjectedRHSRawL1
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

noncomputable local instance point3MeasureSpaceH3TerminalFourthQProjectedRHSRawL1 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (axisFintypeH3TerminalFourthQProjectedRHSRawL1 Depth.three)
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Elementary radial domination -/

theorem norm_sq_le_one_add_pow_fourteen
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 2 ≤ 1 + ‖ξ‖ ^ 14 := by

  have hx0 : 0 ≤ ‖ξ‖ :=
    norm_nonneg ξ

  by_cases hx1 : ‖ξ‖ ≤ 1

  · have hpow :
        ‖ξ‖ ^ 2 ≤ (1 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hx0 hx1 2

    have hpowOne :
        ‖ξ‖ ^ 2 ≤ 1 := by
      simpa using hpow

    have h14 :
        0 ≤ ‖ξ‖ ^ 14 :=
      pow_nonneg hx0 14

    linarith

  · have hx1' :
        1 ≤ ‖ξ‖ :=
      le_of_lt (lt_of_not_ge hx1)

    have h12 :
        (1 : ℝ) ^ 12 ≤ ‖ξ‖ ^ 12 :=
      pow_le_pow_left₀
        (by norm_num : 0 ≤ (1 : ℝ))
        hx1'
        12

    have h12' :
        1 ≤ ‖ξ‖ ^ 12 := by
      simpa using h12

    have h2 :
        0 ≤ ‖ξ‖ ^ 2 :=
      pow_nonneg hx0 2

    have hmul :=
      mul_le_mul_of_nonneg_left
        h12'
        h2

    have h2le14 :
        ‖ξ‖ ^ 2 ≤ ‖ξ‖ ^ 14 := by
      calc
        ‖ξ‖ ^ 2
            =
          ‖ξ‖ ^ 2 * 1 := by ring
        _ ≤
          ‖ξ‖ ^ 2 * ‖ξ‖ ^ 12 := hmul
        _ =
          ‖ξ‖ ^ 14 := by ring

    exact
      le_add_of_nonneg_of_le
        zero_le_one
        h2le14

/-! ## Pointwise PDE mass bound -/

/--
The chosen projected-RHS raw `L¹` mass is bounded by the velocity raw `L¹`,
the velocity order-fourteen moment, and the exact nonlinear forcing `L¹` mass.
-/
theorem h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt_le_velocityL1_moment14_forcing
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j i : Fin 3) :
    h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
        hH3 hClass ht j i
      ≤
    (2 * Real.pi) ^ 2 *
      (
        h3TerminalForcingThirdQRawL1MassAt
            hH3 hClass ht i
          +
        h3TerminalForcingThirdQMoment14MassAt
            hH3 hClass ht i
      )
      +
    h3RawFinLerayOuterProductDivergenceL1Mass
      (
        h3TerminalVelocitySpectralStateAt
          hH3 t
          ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
      )
      (
        h3TerminalVelocitySpectralStateAt
          hH3 t
          ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
      )
      i := by

  let d :=
    h3TerminalFourthQForcingDerivativeLerayDataAt
      hH3 hClass ht j

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 t htAbs

  have hUTerm :
      d.U = U := by
    dsimp only [d, U, htAbs]
    exact
      h3TerminalFourthQForcingDerivativeLerayDataAt_U_eq_terminalVelocity
        hH3 hClass ht j

  have hRPDE :
      (
        (
          h3SpectralScalarRawFourierL2 (d.R i) :
          H3FourierComplexL2
        ) :
        H3FourierPoint3 → ℂ
      )
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        -(h3FourierGradientSquare ξ : ℂ)
            *
          (
            (
              h3SpectralScalarRawFourierL2 (U i) :
              H3FourierComplexL2
            ) ξ
          )
          -
        h3RawFinLerayOuterProductDivergence
          U U i ξ) := by

    have hChosen :=
      h3TerminalFourthQForcingDerivativeLerayDataAt_R_rawFourier_ae_eq_unitPDE
        hH3 hClass ht j i

    simpa only [d, hUTerm] using hChosen

  have hRraw :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 (d.R i))

  have hRnorm :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier (d.R i) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact hRraw.norm

  have hUraw :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 (U i))

  have hUnorm :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier (U i) ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hUraw.norm

  have hU14 :
      H3RawFourierMomentIntegrable
        (14 : ℝ)
        (U i) := by
    dsimp only [U]
    exact
      h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_nat
        hH3 hClass ht 14 (by norm_num) i

  have hU14norm :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 14 *
            ‖h3SpectralScalarRawFourier (U i) ξ‖)
        (volume : Measure H3FourierPoint3) := by

    unfold H3RawFourierMomentIntegrable at hU14

    refine hU14.congr ?_

    filter_upwards with ξ

    change
      h3FourierMomentWeight (((14 : ℕ) : ℝ)) ξ *
          ‖h3SpectralScalarRawFourier (U i) ξ‖
        =
      ‖ξ‖ ^ 14 *
          ‖h3SpectralScalarRawFourier (U i) ξ‖

    rw [h3FourierMomentWeight_natCast 14 ξ]

  have hForce :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3RawFinLerayOuterProductDivergence U U i ξ)
        (volume : Measure H3FourierPoint3) :=
    h3RawFinLerayOuterProductDivergence_integrable
      U U i

  have hForceNorm :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3RawFinLerayOuterProductDivergence U U i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hForce.norm

  let Cq : ℝ :=
    (2 * Real.pi) ^ 2

  have hCq0 :
      0 ≤ Cq := by
    dsimp only [Cq]
    positivity

  let major : H3FourierPoint3 → ℝ :=
    fun ξ =>
      Cq *
        (
          ‖h3SpectralScalarRawFourier (U i) ξ‖
            +
          ‖ξ‖ ^ 14 *
            ‖h3SpectralScalarRawFourier (U i) ξ‖
        )
        +
      ‖h3RawFinLerayOuterProductDivergence U U i ξ‖

  have hMajor :
      Integrable major
        (volume : Measure H3FourierPoint3) := by

    dsimp only [major]

    exact
      (hUnorm.add hU14norm).const_mul Cq
        |>.add hForceNorm

  have hPoint :
      ∀ᵐ ξ : H3FourierPoint3 ∂volume,
        ‖h3SpectralScalarRawFourier (d.R i) ξ‖
          ≤
        major ξ := by

    have hRawRep :
        (
          (
            h3SpectralScalarRawFourierL2 (d.R i) :
            H3FourierComplexL2
          ) :
          H3FourierPoint3 → ℂ
        )
          =ᵐ[(volume : Measure H3FourierPoint3)]
        h3SpectralScalarRawFourier (d.R i) := by

      simpa [h3SpectralScalarRawFourierL2] using
        MemLp.coeFn_toLp
          (h3SpectralScalarRawFourier_memLp2 (d.R i))

    have hURep :
        (
          (
            h3SpectralScalarRawFourierL2 (U i) :
            H3FourierComplexL2
          ) :
          H3FourierPoint3 → ℂ
        )
          =ᵐ[(volume : Measure H3FourierPoint3)]
        h3SpectralScalarRawFourier (U i) := by

      simpa [h3SpectralScalarRawFourierL2] using
        MemLp.coeFn_toLp
          (h3SpectralScalarRawFourier_memLp2 (U i))

    filter_upwards [hRawRep, hURep, hRPDE]
      with ξ hRawξ hUξ hPDEξ

    rw [← hRawξ]
    rw [hPDEξ]

    have hq0 :
        0 ≤ h3FourierGradientSquare ξ :=
      h3FourierGradientSquare_nonneg ξ

    have hRadial :=
      norm_sq_le_one_add_pow_fourteen ξ

    have hqBound :
        h3FourierGradientSquare ξ
          ≤
        Cq * (1 + ‖ξ‖ ^ 14) := by

      dsimp only [Cq]

      unfold h3FourierGradientSquare

      have hCoeff0 :
          0 ≤ (2 * Real.pi) ^ 2 := by
        positivity

      exact
        mul_le_mul_of_nonneg_left
          hRadial
          hCoeff0

    have hUnorm0 :
        0 ≤
          ‖(
            h3SpectralScalarRawFourierL2 (U i) :
            H3FourierComplexL2
          ) ξ‖ :=
      norm_nonneg _

    let A : ℂ :=
      -(h3FourierGradientSquare ξ : ℂ) *
        ((h3SpectralScalarRawFourierL2 (U i) : H3FourierComplexL2) ξ)

    let B : ℂ :=
      h3RawFinLerayOuterProductDivergence U U i ξ

    have hDiff :
        ‖A - B‖
          ≤
        h3FourierGradientSquare ξ *
            ‖((h3SpectralScalarRawFourierL2 (U i) : H3FourierComplexL2) ξ)‖
          +
        ‖B‖ := by

      calc
        ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le A B
        _ =
          h3FourierGradientSquare ξ *
              ‖((h3SpectralScalarRawFourierL2 (U i) : H3FourierComplexL2) ξ)‖
            +
          ‖B‖ := by
            dsimp only [A]
            rw [norm_mul]
            simp only [
              norm_neg,
              Complex.norm_real,
              Real.norm_eq_abs,
              abs_of_nonneg hq0
            ]

    have hQMul :
        h3FourierGradientSquare ξ
            *
          ‖(
            h3SpectralScalarRawFourierL2 (U i) :
            H3FourierComplexL2
          ) ξ‖
          ≤
        Cq * (1 + ‖ξ‖ ^ 14)
            *
          ‖(
            h3SpectralScalarRawFourierL2 (U i) :
            H3FourierComplexL2
          ) ξ‖ :=
      mul_le_mul_of_nonneg_right
        hqBound
        hUnorm0

    change ‖A - B‖ ≤ major ξ

    calc
      ‖A - B‖
          ≤
        h3FourierGradientSquare ξ *
            ‖((h3SpectralScalarRawFourierL2 (U i) : H3FourierComplexL2) ξ)‖
          +
        ‖B‖ :=
        hDiff
      _ ≤
        Cq * (1 + ‖ξ‖ ^ 14) *
            ‖((h3SpectralScalarRawFourierL2 (U i) : H3FourierComplexL2) ξ)‖
          +
        ‖B‖ :=
        add_le_add hQMul (le_refl _)
      _ = major ξ := by
        dsimp only [major, B]
        rw [hUξ]
        ring

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
        ‖h3SpectralScalarRawFourier (d.R i) ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3, major ξ := by

    exact
      integral_mono_ae
        hRnorm
        hMajor
        hPoint

  have hMajorIntegral :
      (∫ ξ : H3FourierPoint3, major ξ)
        =
      Cq *
        (
          h3SpectralScalarRawFourierL1Mass (U i)
            +
          h3SpectralScalarRawFourierMomentMass (14 : ℝ) (U i)
        )
        +
      h3RawFinLerayOuterProductDivergenceL1Mass
        U U i := by

    dsimp only [major]

    calc
      (∫ ξ : H3FourierPoint3,
          Cq *
              (
                ‖h3SpectralScalarRawFourier (U i) ξ‖
                  +
                ‖ξ‖ ^ 14 *
                  ‖h3SpectralScalarRawFourier (U i) ξ‖
              )
            +
          ‖h3RawFinLerayOuterProductDivergence U U i ξ‖)
          =
        (∫ ξ : H3FourierPoint3,
          Cq *
            (
              ‖h3SpectralScalarRawFourier (U i) ξ‖
                +
              ‖ξ‖ ^ 14 *
                ‖h3SpectralScalarRawFourier (U i) ξ‖
            ))
          +
        ∫ ξ : H3FourierPoint3,
          ‖h3RawFinLerayOuterProductDivergence U U i ξ‖ := by
            exact
              integral_add
                ((hUnorm.add hU14norm).const_mul Cq)
                hForceNorm
      _ =
        Cq *
          (∫ ξ : H3FourierPoint3,
            (
              ‖h3SpectralScalarRawFourier (U i) ξ‖
                +
              ‖ξ‖ ^ 14 *
                ‖h3SpectralScalarRawFourier (U i) ξ‖
            ))
          +
        ∫ ξ : H3FourierPoint3,
          ‖h3RawFinLerayOuterProductDivergence U U i ξ‖ := by
            rw [integral_const_mul]
      _ =
        Cq *
          (
            (∫ ξ : H3FourierPoint3,
              ‖h3SpectralScalarRawFourier (U i) ξ‖)
              +
            ∫ ξ : H3FourierPoint3,
              ‖ξ‖ ^ 14 *
                ‖h3SpectralScalarRawFourier (U i) ξ‖
          )
          +
        ∫ ξ : H3FourierPoint3,
          ‖h3RawFinLerayOuterProductDivergence U U i ξ‖ := by
            rw [integral_add hUnorm hU14norm]
      _ =
        Cq *
          (
            h3SpectralScalarRawFourierL1Mass (U i)
              +
            h3SpectralScalarRawFourierMomentMass (14 : ℝ) (U i)
          )
          +
        h3RawFinLerayOuterProductDivergenceL1Mass U U i := by

            unfold
              h3SpectralScalarRawFourierL1Mass
              h3SpectralScalarRawFourierMomentMass
              h3RawFinLerayOuterProductDivergenceL1Mass

            have hMomentIntegral :
                (∫ ξ : H3FourierPoint3,
                  h3FourierMomentWeight (14 : ℝ) ξ *
                    ‖h3SpectralScalarRawFourier (U i) ξ‖)
                  =
                ∫ ξ : H3FourierPoint3,
                  ‖ξ‖ ^ 14 *
                    ‖h3SpectralScalarRawFourier (U i) ξ‖ := by

              apply integral_congr_ae

              filter_upwards with ξ

              change
                h3FourierMomentWeight (((14 : ℕ) : ℝ)) ξ *
                    ‖h3SpectralScalarRawFourier (U i) ξ‖
                  =
                ‖ξ‖ ^ 14 *
                    ‖h3SpectralScalarRawFourier (U i) ξ‖

              rw [h3FourierMomentWeight_natCast 14 ξ]

            rw [hMomentIntegral]

  rw [hMajorIntegral] at hIntegral

  have hIntegralNamed :
      h3SpectralScalarRawFourierL1Mass (d.R i)
        ≤
      Cq *
        (
          h3SpectralScalarRawFourierL1Mass (U i)
            +
          h3SpectralScalarRawFourierMomentMass (14 : ℝ) (U i)
        )
        +
      h3RawFinLerayOuterProductDivergenceL1Mass U U i := by
    change
      (∫ ξ : H3FourierPoint3,
        ‖h3SpectralScalarRawFourier (d.R i) ξ‖)
        ≤
      Cq *
        (
          h3SpectralScalarRawFourierL1Mass (U i)
            +
          h3SpectralScalarRawFourierMomentMass (14 : ℝ) (U i)
        )
        +
      h3RawFinLerayOuterProductDivergenceL1Mass U U i
    exact hIntegral

  change
    h3SpectralScalarRawFourierL1Mass (d.R i)
      ≤
    (2 * Real.pi) ^ 2 *
      (
        h3SpectralScalarRawFourierL1Mass (U i)
          +
        h3SpectralScalarRawFourierMomentMass (14 : ℝ) (U i)
      )
      +
    h3RawFinLerayOuterProductDivergenceL1Mass U U i

  simpa only [Cq] using hIntegralNamed

/-! ## Convert the pointwise bound into energy + order-fourteen moment -/

noncomputable def h3TerminalFourthQProjectedRHSRawL1EnergyCoefficient : ℝ :=
  (2 * Real.pi) ^ 2 * h3RawFourierL1DeweightingCoefficient
    +
  h3NonlinearForcingL1Coefficient

theorem h3TerminalFourthQProjectedRHSRawL1EnergyCoefficient_nonneg :
    0 ≤ h3TerminalFourthQProjectedRHSRawL1EnergyCoefficient := by
  unfold h3TerminalFourthQProjectedRHSRawL1EnergyCoefficient
  positivity [
    h3RawFourierL1DeweightingCoefficient_nonneg,
    h3NonlinearForcingL1Coefficient_nonneg
  ]

theorem h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt_le_energy_add_moment14
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j i : Fin 3) :
    h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
        hH3 hClass ht j i
      ≤
    h3TerminalFourthQProjectedRHSRawL1EnergyCoefficient
        *
      velocityH3EnergyAt u t
      +
    (2 * Real.pi) ^ 2
        *
      h3TerminalForcingThirdQMoment14MassAt
        hH3 hClass ht i := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 t htAbs

  have hBase :=
    h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt_le_velocityL1_moment14_forcing
      hH3 hClass ht j i

  have hL1 :=
    h3TerminalForcingThirdQRawL1MassAt_le_deweight_sqrt_energy
      hH3 hClass ht i

  have hEOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt u t

  have hE0 :
      0 ≤ velocityH3EnergyAt u t :=
    le_trans zero_le_one hEOne

  have hSqrtLe :
      Real.sqrt (velocityH3EnergyAt u t)
        ≤
      velocityH3EnergyAt u t := by

    have hSq :
        (Real.sqrt (velocityH3EnergyAt u t)) ^ 2
          =
        velocityH3EnergyAt u t :=
      Real.sq_sqrt hE0

    have hRoot0 :
        0 ≤ Real.sqrt (velocityH3EnergyAt u t) :=
      Real.sqrt_nonneg _

    nlinarith

  have hL1E :
      h3TerminalForcingThirdQRawL1MassAt
          hH3 hClass ht i
        ≤
      h3RawFourierL1DeweightingCoefficient
        *
      velocityH3EnergyAt u t := by

    exact
      hL1.trans
        (
          mul_le_mul_of_nonneg_left
            hSqrtLe
            h3RawFourierL1DeweightingCoefficient_nonneg
        )

  have hState :
      ‖U‖
        ≤
      Real.sqrt (velocityH3EnergyAt u t) := by

    dsimp only [U, htAbs]

    exact
      norm_h3TerminalVelocitySpectralStateAt_le_sqrt_energy_for_fourthQProjectedRHS
        hH3 hClass ht

  have hStateSq :
      ‖U‖ * ‖U‖
        ≤
      velocityH3EnergyAt u t := by

    have hMul :
        ‖U‖ * ‖U‖
          ≤
        Real.sqrt (velocityH3EnergyAt u t)
          *
        Real.sqrt (velocityH3EnergyAt u t) :=
      mul_le_mul
        hState hState
        (norm_nonneg U)
        (Real.sqrt_nonneg _)

    have hSq :
        Real.sqrt (velocityH3EnergyAt u t)
          *
        Real.sqrt (velocityH3EnergyAt u t)
          =
        velocityH3EnergyAt u t := by
      nlinarith [Real.sq_sqrt hE0]

    simpa [hSq] using hMul

  have hForce :=
    h3RawFinLerayOuterProductDivergenceL1Mass_le
      U U i

  have hForceE :
      h3RawFinLerayOuterProductDivergenceL1Mass
          U U i
        ≤
      h3NonlinearForcingL1Coefficient
        *
      velocityH3EnergyAt u t := by

    calc
      h3RawFinLerayOuterProductDivergenceL1Mass
          U U i
          ≤
        h3NonlinearForcingL1Coefficient * ‖U‖ * ‖U‖ :=
        hForce
      _ =
        h3NonlinearForcingL1Coefficient * (‖U‖ * ‖U‖) := by
        ring
      _ ≤
        h3NonlinearForcingL1Coefficient
          *
        velocityH3EnergyAt u t :=
        mul_le_mul_of_nonneg_left
          hStateSq
          h3NonlinearForcingL1Coefficient_nonneg

  have hCq0 :
      0 ≤ (2 * Real.pi) ^ 2 := by
    positivity

  have hScaled :
      (2 * Real.pi) ^ 2
          *
        (
          h3TerminalForcingThirdQRawL1MassAt
              hH3 hClass ht i
            +
          h3TerminalForcingThirdQMoment14MassAt
              hH3 hClass ht i
        )
        ≤
      (2 * Real.pi) ^ 2
          *
        (
          h3RawFourierL1DeweightingCoefficient
              *
            velocityH3EnergyAt u t
            +
          h3TerminalForcingThirdQMoment14MassAt
              hH3 hClass ht i
        ) := by

    apply mul_le_mul_of_nonneg_left
    · exact
        add_le_add
          hL1E
          (le_refl _)
    · exact hCq0

  calc
    h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
        hH3 hClass ht j i
        ≤
      (2 * Real.pi) ^ 2 *
        (
          h3TerminalForcingThirdQRawL1MassAt
              hH3 hClass ht i
            +
          h3TerminalForcingThirdQMoment14MassAt
              hH3 hClass ht i
        )
        +
      h3RawFinLerayOuterProductDivergenceL1Mass
        U U i := by
          simpa only [U, htAbs] using hBase
    _ ≤
      (2 * Real.pi) ^ 2
          *
        (
          h3RawFourierL1DeweightingCoefficient
              *
            velocityH3EnergyAt u t
            +
          h3TerminalForcingThirdQMoment14MassAt
              hH3 hClass ht i
        )
        +
      h3NonlinearForcingL1Coefficient
          *
        velocityH3EnergyAt u t :=
      add_le_add hScaled hForceE
    _ =
      h3TerminalFourthQProjectedRHSRawL1EnergyCoefficient
          *
        velocityH3EnergyAt u t
        +
      (2 * Real.pi) ^ 2
          *
        h3TerminalForcingThirdQMoment14MassAt
          hH3 hClass ht i := by
      unfold h3TerminalFourthQProjectedRHSRawL1EnergyCoefficient
      ring

/-! ## Escape resolver -/

noncomputable def h3TerminalFourthQProjectedRHSRawL1ResolverAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (i : Fin 3)
    (q : Fin 2) : ℝ :=
  if q = 0 then
    velocityH3EnergyAt u t
  else
    h3TerminalForcingThirdQMoment14MassAt
      hH3 hClass ht i

theorem h3TerminalFourthQProjectedRHSRawL1ResolverMax_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j i : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hRawTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
            hH3 hClass (hτ n) j i)
        atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        max
          (velocityH3EnergyAt u (τ n))
          (h3TerminalForcingThirdQMoment14MassAt
            hH3 hClass (hτ n) i))
      atTop atTop := by

  refine tendsto_atTop.2 ?_

  intro M

  let R0 : ℝ :=
    max M 0

  let A : ℝ :=
    h3TerminalFourthQProjectedRHSRawL1EnergyCoefficient

  let B : ℝ :=
    (2 * Real.pi) ^ 2

  have hMLe :
      M ≤ R0 := by
    dsimp only [R0]
    exact le_max_left M 0

  have hA0 :
      0 ≤ A := by
    dsimp only [A]
    exact
      h3TerminalFourthQProjectedRHSRawL1EnergyCoefficient_nonneg

  have hB0 :
      0 ≤ B := by
    dsimp only [B]
    positivity

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        (A + B) * R0 + 1
          <
        h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
          hH3 hClass (hτ n) j i :=
    hRawTop.eventually
      (eventually_gt_atTop ((A + B) * R0 + 1))

  filter_upwards [hLarge] with n hn

  let E : ℝ :=
    velocityH3EnergyAt u (τ n)

  let H : ℝ :=
    h3TerminalForcingThirdQMoment14MassAt
      hH3 hClass (hτ n) i

  let K : ℝ :=
    max E H

  have hEK :
      E ≤ K := by
    dsimp only [K]
    exact le_max_left E H

  have hHK :
      H ≤ K := by
    dsimp only [K]
    exact le_max_right E H

  have hBound :=
    h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt_le_energy_add_moment14
      hH3 hClass (hτ n) j i

  have hR0LtK :
      R0 < K := by

    by_contra hNot

    have hKLe :
        K ≤ R0 :=
      le_of_not_gt hNot

    have hELe :
        E ≤ R0 :=
      hEK.trans hKLe

    have hHLe :
        H ≤ R0 :=
      hHK.trans hKLe

    have hAE :
        A * E ≤ A * R0 :=
      mul_le_mul_of_nonneg_left hELe hA0

    have hBH :
        B * H ≤ B * R0 :=
      mul_le_mul_of_nonneg_left hHLe hB0

    have hSum :
        A * E + B * H
          ≤
        (A + B) * R0 := by
      calc
        A * E + B * H
            ≤
          A * R0 + B * R0 :=
          add_le_add hAE hBH
        _ =
          (A + B) * R0 := by
          ring

    have hPrimitiveLe :
        h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
            hH3 hClass (hτ n) j i
          ≤
        (A + B) * R0 := by

      dsimp only [A, B, E, H] at hBound hSum

      exact
        hBound.trans hSum

    linarith

  change
    M ≤
      max
        (velocityH3EnergyAt u (τ n))
        (h3TerminalForcingThirdQMoment14MassAt
          hH3 hClass (hτ n) i)

  exact
    hMLe.trans
      (le_of_lt hR0LtK)

theorem exists_fixed_h3TerminalFourthQProjectedRHSRawL1Resolver_subsequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j i : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hRawTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
            hH3 hClass (hτ n) j i)
        atTop atTop) :
    ∃ q : Fin 2,
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
        Tendsto
          (fun n : ℕ =>
            h3TerminalFourthQProjectedRHSRawL1ResolverAt
              hH3 hClass (hτ (s n)) i q)
          atTop atTop := by

  classical

  have hMaxTop :=
    h3TerminalFourthQProjectedRHSRawL1ResolverMax_tendstoAtTop
      hH3 hClass j i τ hτ hRawTop

  let q : ℕ → Fin 2 :=
    fun n =>
      if
        h3TerminalForcingThirdQMoment14MassAt
            hH3 hClass (hτ n) i
          ≤
        velocityH3EnergyAt u (τ n)
      then 0
      else 1

  have hChosen :
      ∀ n : ℕ,
        h3TerminalFourthQProjectedRHSRawL1ResolverAt
            hH3 hClass (hτ n) i (q n)
          =
        max
          (velocityH3EnergyAt u (τ n))
          (h3TerminalForcingThirdQMoment14MassAt
            hH3 hClass (hτ n) i) := by

    intro n

    dsimp only [q]

    by_cases h :
        h3TerminalForcingThirdQMoment14MassAt
            hH3 hClass (hτ n) i
          ≤
        velocityH3EnergyAt u (τ n)

    · simp only [if_pos h]

      unfold h3TerminalFourthQProjectedRHSRawL1ResolverAt

      simp only [if_pos]

      exact
        (max_eq_left h).symm

    · simp only [if_neg h]

      have hReverse :
          velocityH3EnergyAt u (τ n)
            ≤
          h3TerminalForcingThirdQMoment14MassAt
            hH3 hClass (hτ n) i :=
        le_of_lt
          (lt_of_not_ge h)

      unfold h3TerminalFourthQProjectedRHSRawL1ResolverAt

      simp only [if_neg, one_ne_zero]

      exact
        (max_eq_right hReverse).symm

  have hChosenTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalFourthQProjectedRHSRawL1ResolverAt
            hH3 hClass (hτ n) i (q n))
        atTop atTop := by
    simpa only [hChosen] using hMaxTop

  have hFrequentlySome :
      ∃ᶠ n : ℕ in atTop,
        ∃ q0 : Fin 2,
          q n = q0 :=
    Frequently.of_forall
      (fun n => ⟨q n, rfl⟩)

  obtain
    ⟨q0, hFrequently⟩ :=
    (Filter.frequently_exists).1
      hFrequentlySome

  obtain
    ⟨s, hMono, hFixed⟩ :=
    extraction_of_frequently_atTop
      hFrequently

  have hs :
      ∀ n : ℕ, n ≤ s n := by
    intro n
    exact hMono.le_apply

  have hsTop :
      Tendsto s atTop atTop :=
    hMono.tendsto_atTop

  have hTauSub :
      Tendsto
        (fun n : ℕ => τ (s n))
        atTop
        (𝓝 T) :=
    hTauTendsto.comp hsTop

  have hTopBeforeRewrite :
      Tendsto
        (fun n : ℕ =>
          h3TerminalFourthQProjectedRHSRawL1ResolverAt
            hH3 hClass (hτ (s n)) i (q (s n)))
        atTop atTop :=
    hChosenTop.comp hsTop

  have hTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalFourthQProjectedRHSRawL1ResolverAt
            hH3 hClass (hτ (s n)) i q0)
        atTop atTop := by
    simpa only [hFixed] using hTopBeforeRewrite

  exact
    ⟨q0, s, hs, hsTop, hTauSub, hTop⟩

/--
Projected-RHS raw-`L¹` escape is absorbed into physical H³ energy or the
already-existing extended higher-radial hierarchy.
-/
theorem h3TerminalFourthQProjectedRHSRawL1_escape_energy_or_fixedExtendedHigherRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j i : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hRawTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
            hH3 hClass (hτ n) j i)
        atTop atTop) :
    (
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
        Tendsto
          (fun n : ℕ => velocityH3EnergyAt u (τ (s n)))
          atTop atTop
    )
      ∨
    (
      ∃ m : ℕ,
        m ≠ 0 ∧
        ∃ s : ℕ → ℕ,
          (∀ n : ℕ, n ≤ s n) ∧
          Tendsto s atTop atTop ∧
          Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
          Tendsto
            (fun n : ℕ =>
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass m
                (τ (s n))
                (hτ (s n)))
            atTop (𝓝 ∞)
    ) := by

  obtain
    ⟨q, s, hs, hsTop, hTauSub, hResolverTop⟩ :=
    exists_fixed_h3TerminalFourthQProjectedRHSRawL1Resolver_subsequence
      hH3 hClass j i τ hτ hTauTendsto hRawTop

  fin_cases q

  · have hEnergyTop :
        Tendsto
          (fun n : ℕ =>
            velocityH3EnergyAt u (τ (s n)))
          atTop atTop := by
      simpa [
        h3TerminalFourthQProjectedRHSRawL1ResolverAt
      ] using hResolverTop

    exact
      Or.inl
        ⟨s, hs, hsTop, hTauSub, hEnergyTop⟩

  · have hMoment14Top :
        Tendsto
          (fun n : ℕ =>
            h3TerminalForcingThirdQMoment14MassAt
              hH3 hClass (hτ (s n)) i)
          atTop atTop := by
      simpa [
        h3TerminalFourthQProjectedRHSRawL1ResolverAt
      ] using hResolverTop

    obtain
      ⟨qRadial, v, hv, hvTop, hTauFinal, hSquareTop⟩ :=
      exists_fixed_h3TerminalForcingThirdQMoment14RadialSquareChannel_subsequence
        hH3 hClass i
        (fun n : ℕ => τ (s n))
        (fun n : ℕ => hτ (s n))
        hTauSub
        hMoment14Top

    have hHigherTop :=
      h3TerminalForcingThirdQMoment14RadialSquareChannel_escape_resolves_higherRadial
        hH3 hClass i qRadial
        (fun n : ℕ => τ (s (v n)))
        (fun n : ℕ => hτ (s (v n)))
        hSquareTop

    have hComp :
        ∀ n : ℕ, n ≤ s (v n) := by
      intro n
      exact le_trans (hv n) (hs (v n))

    have hCompTop :
        Tendsto (fun n : ℕ => s (v n)) atTop atTop :=
      hsTop.comp hvTop

    have hShiftNe :
        h3TerminalForcingThirdQHigherRadialShift qRadial ≠ 0 := by
      fin_cases qRadial <;>
        norm_num [h3TerminalForcingThirdQHigherRadialShift]

    exact
      Or.inr
        ⟨
          h3TerminalForcingThirdQHigherRadialShift qRadial,
          hShiftNe,
          (fun n : ℕ => s (v n)),
          hComp,
          hCompTop,
          hTauFinal,
          hHigherTop
        ⟩

/-! ## The sole residual projected-RHS primitive is now M10(R) -/

/--
Fourth-temporal escape now has only three alternatives: physical H³ energy,
one fixed nonzero extended higher-radial velocity moment, or one fixed
projected-RHS order-ten raw Fourier moment.
-/
theorem fourthTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial_or_fixedProjectedRHSMoment10
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hFourth :
      Tendsto
        (fun n : ℕ =>
          h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
            hH3 hClass j
            H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
            (τ n))
        atTop atTop) :
    (
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
        Tendsto
          (fun n : ℕ => velocityH3EnergyAt u (τ (s n)))
          atTop atTop
    )
      ∨
    (
      ∃ m : ℕ,
        m ≠ 0 ∧
        ∃ s : ℕ → ℕ,
          (∀ n : ℕ, n ≤ s n) ∧
          Tendsto s atTop atTop ∧
          Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
          Tendsto
            (fun n : ℕ =>
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass m
                (τ (s n))
                (hτ (s n)))
            atTop (𝓝 ∞)
    )
      ∨
    (
      ∃ i : Fin 3,
        ∃ s : ℕ → ℕ,
          (∀ n : ℕ, n ≤ s n) ∧
          Tendsto s atTop atTop ∧
          Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
          Tendsto
            (fun n : ℕ =>
              h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
                hH3 hClass (hτ (s n)) j i)
            atTop atTop
    ) := by

  rcases
    fourthTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial_or_fixedProjectedRHSHighPrimitive
      hH3 hClass j τ hτ hTauTendsto hFourth
  with hEnergy | hRest

  · exact Or.inl hEnergy

  · rcases hRest with hHigher | hRHS

    · exact Or.inr (Or.inl hHigher)

    · rcases hRHS with
        ⟨c, i, s, hs, hsTop, hTauSub, hPrimitiveTop⟩

      cases c with

      | moment10 =>

          exact
            Or.inr
              (
                Or.inr
                  ⟨
                    i,
                    s,
                    hs,
                    hsTop,
                    hTauSub,
                    by
                      simpa [
                        h3TerminalFourthQForcingDerivativeProjectedRHSHighObstructionAt
                      ] using hPrimitiveTop
                  ⟩
              )

      | rawL1 =>

          have hRawTop :
              Tendsto
                (fun n : ℕ =>
                  h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
                    hH3 hClass (hτ (s n)) j i)
                atTop atTop := by

            simpa [
              h3TerminalFourthQForcingDerivativeProjectedRHSHighObstructionAt
            ] using hPrimitiveTop

          rcases
            h3TerminalFourthQProjectedRHSRawL1_escape_energy_or_fixedExtendedHigherRadial
              hH3 hClass j i
              (fun n : ℕ => τ (s n))
              (fun n : ℕ => hτ (s n))
              hTauSub
              hRawTop
          with hEnergySub | hHigherSub

          · rcases hEnergySub with
              ⟨v, hv, hvTop, hTauFinal, hEnergyTop⟩

            have hComp :
                ∀ n : ℕ, n ≤ s (v n) := by
              intro n
              exact le_trans (hv n) (hs (v n))

            have hCompTop :
                Tendsto (fun n : ℕ => s (v n)) atTop atTop :=
              hsTop.comp hvTop

            exact
              Or.inl
                ⟨
                  (fun n : ℕ => s (v n)),
                  hComp,
                  hCompTop,
                  hTauFinal,
                  hEnergyTop
                ⟩

          · rcases hHigherSub with
              ⟨m, hm, v, hv, hvTop, hTauFinal, hHigherTop⟩

            have hComp :
                ∀ n : ℕ, n ≤ s (v n) := by
              intro n
              exact le_trans (hv n) (hs (v n))

            have hCompTop :
                Tendsto (fun n : ℕ => s (v n)) atTop atTop :=
              hsTop.comp hvTop

            exact
              Or.inr
                (
                  Or.inl
                    ⟨
                      m,
                      hm,
                      (fun n : ℕ => s (v n)),
                      hComp,
                      hCompTop,
                      hTauFinal,
                      hHigherTop
                    ⟩
                )

end

end Euclidean
end Bridge
end PrimeTensor
