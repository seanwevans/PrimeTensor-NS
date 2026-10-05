import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Higher.Subtail.StateMass.Group.Factor.Primitive.Origin.Higher.RawL2.RawL1
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.Moment.Forcing

/-!
# Projected-RHS order-ten moment: exact PDE reduction

After the raw `L²` and raw `L¹` projected-RHS primitives have been absorbed,
the sole residual fourth-q projected-RHS primitive is

    M₁₀(Rᵢ).

The canonical chosen datum records the exact unit-viscosity PDE identity

    Rᵢ = -q Uᵢ - P div(U ⊗ U)ᵢ

in raw Fourier variables.  Multiplying by the order-ten Fourier weight gives
the sharp bookkeeping reduction

    M₁₀(Rᵢ)
      ≤ (2π)² M₁₂(Uᵢ)
        + M₁₀(P div(U ⊗ U)ᵢ).

No escape extraction occurs in this file.  The next step is purely generic
moment algebra: the forcing term costs only order-eleven velocity moments and
raw `L¹`, while order eleven and twelve are both below the already-classified
order-fourteen velocity moment up to raw `L¹`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 3000000

noncomputable local instance axisFintypeH3TerminalFourthQProjectedRHSMomentTen
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

noncomputable local instance point3MeasureSpaceH3TerminalFourthQProjectedRHSMomentTen :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (axisFintypeH3TerminalFourthQProjectedRHSMomentTen Depth.three)
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
The exact selected projected-RHS PDE raises the velocity moment by exactly two
powers and leaves the nonlinear forcing at the original moment order.
-/
theorem h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt_le_velocityMoment12_add_forcingMoment10
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j i : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
        hH3 hClass ht j i
      ≤
    (2 * Real.pi) ^ 2 *
      h3SpectralScalarRawFourierMomentMass (12 : ℝ) (U i)
      +
    h3RawFinLerayOuterProductDivergenceMomentMass
      (10 : ℝ) U U i := by

  dsimp only

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
        h3RawFinLerayOuterProductDivergence U U i ξ) := by

    have hChosen :=
      h3TerminalFourthQForcingDerivativeLerayDataAt_R_rawFourier_ae_eq_unitPDE
        hH3 hClass ht j i

    simpa only [d, hUTerm] using hChosen

  have hR10 :
      H3RawFourierMomentIntegrable
        (10 : ℝ)
        (d.R i) := by
    have h := d.hR i
    convert h using 1 <;> norm_num

  have hU12 :
      H3RawFourierMomentIntegrable
        (12 : ℝ)
        (U i) := by
    dsimp only [U]
    exact
      h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_nat
        hH3 hClass ht 12 (by norm_num) i

  have hU11 :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (11 : ℝ)
          (U k) := by
    intro k
    dsimp only [U]
    exact
      h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_nat
        hH3 hClass ht 11 (by norm_num) k

  have hForce10 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (10 : ℝ) ξ *
            ‖h3RawFinLerayOuterProductDivergence U U i ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      h3RawFinLerayOuterProductDivergence_moment_integrable_of_nextMoments
        (q := (10 : ℝ))
        (by norm_num)
        U U
        (by
          intro k
          convert hU11 k using 1 <;> norm_num)
        (by
          intro k
          convert hU11 k using 1 <;> norm_num)
        i

  let Cq : ℝ :=
    (2 * Real.pi) ^ 2

  let major : H3FourierPoint3 → ℝ :=
    fun ξ =>
      Cq *
        (
          h3FourierMomentWeight (12 : ℝ) ξ *
            ‖h3SpectralScalarRawFourier (U i) ξ‖
        )
        +
      h3FourierMomentWeight (10 : ℝ) ξ *
        ‖h3RawFinLerayOuterProductDivergence U U i ξ‖

  have hMajor :
      Integrable major
        (volume : Measure H3FourierPoint3) := by
    dsimp only [major]
    exact
      hU12.const_mul Cq
        |>.add hForce10

  have hPoint :
      ∀ᵐ ξ : H3FourierPoint3 ∂volume,
        h3FourierMomentWeight (10 : ℝ) ξ *
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
        ‖A - B‖ ≤ ‖A‖ + ‖B‖ :=
          norm_sub_le A B
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

    have hW10 :
        0 ≤ h3FourierMomentWeight (10 : ℝ) ξ :=
      h3FourierMomentWeight_nonneg (10 : ℝ) ξ

    have hWeighted :=
      mul_le_mul_of_nonneg_left
        hDiff
        hW10

    change
      h3FourierMomentWeight (10 : ℝ) ξ *
          ‖A - B‖
        ≤
      major ξ

    calc
      h3FourierMomentWeight (10 : ℝ) ξ *
          ‖A - B‖
          ≤
        h3FourierMomentWeight (10 : ℝ) ξ *
          (
            h3FourierGradientSquare ξ *
                ‖((h3SpectralScalarRawFourierL2 (U i) : H3FourierComplexL2) ξ)‖
              +
            ‖B‖
          ) :=
        hWeighted
      _ = major ξ := by
        dsimp only [major, Cq, B]
        rw [hUξ]

        have hWeight10 :
            h3FourierMomentWeight (10 : ℝ) ξ = ‖ξ‖ ^ 10 := by
          have h :=
            h3FourierMomentWeight_natCast 10 ξ
          norm_num at h ⊢
          exact h

        have hWeight12 :
            h3FourierMomentWeight (12 : ℝ) ξ = ‖ξ‖ ^ 12 := by
          have h :=
            h3FourierMomentWeight_natCast 12 ξ
          norm_num at h ⊢
          exact h

        rw [hWeight10, hWeight12]
        unfold h3FourierGradientSquare
        ring

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight (10 : ℝ) ξ *
          ‖h3SpectralScalarRawFourier (d.R i) ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3, major ξ := by

    exact
      integral_mono_ae
        hR10
        hMajor
        hPoint

  have hMajorIntegral :
      (∫ ξ : H3FourierPoint3, major ξ)
        =
      Cq *
        h3SpectralScalarRawFourierMomentMass
          (12 : ℝ) (U i)
        +
      h3RawFinLerayOuterProductDivergenceMomentMass
        (10 : ℝ) U U i := by

    dsimp only [major]

    calc
      (∫ ξ : H3FourierPoint3,
          Cq *
              (
                h3FourierMomentWeight (12 : ℝ) ξ *
                  ‖h3SpectralScalarRawFourier (U i) ξ‖
              )
            +
          h3FourierMomentWeight (10 : ℝ) ξ *
            ‖h3RawFinLerayOuterProductDivergence U U i ξ‖)
          =
        (∫ ξ : H3FourierPoint3,
          Cq *
            (
              h3FourierMomentWeight (12 : ℝ) ξ *
                ‖h3SpectralScalarRawFourier (U i) ξ‖
            ))
          +
        ∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (10 : ℝ) ξ *
            ‖h3RawFinLerayOuterProductDivergence U U i ξ‖ := by
              exact
                integral_add
                  (hU12.const_mul Cq)
                  hForce10
      _ =
        Cq *
          (∫ ξ : H3FourierPoint3,
            h3FourierMomentWeight (12 : ℝ) ξ *
              ‖h3SpectralScalarRawFourier (U i) ξ‖)
          +
        ∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (10 : ℝ) ξ *
            ‖h3RawFinLerayOuterProductDivergence U U i ξ‖ := by
              rw [integral_const_mul]
      _ =
        Cq *
          h3SpectralScalarRawFourierMomentMass
            (12 : ℝ) (U i)
          +
        h3RawFinLerayOuterProductDivergenceMomentMass
          (10 : ℝ) U U i := by
              rfl

  rw [hMajorIntegral] at hIntegral

  change
    h3SpectralScalarRawFourierMomentMass
        (10 : ℝ) (d.R i)
      ≤
    Cq *
      h3SpectralScalarRawFourierMomentMass
        (12 : ℝ) (U i)
      +
    h3RawFinLerayOuterProductDivergenceMomentMass
      (10 : ℝ) U U i

  exact hIntegral

end

end Euclidean
end Bridge
end PrimeTensor
