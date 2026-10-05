import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.StateMass
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Higher.Subtail.StateMass.Group.Factor.Primitive.Origin.Higher.ProjectedRHSMoment10Closure

/-!
# Bridge the second-q projected RHS to the closed fourth-q projected RHS

The second-q and fourth-q forcing-derivative constructions choose their own
local restart representatives `R`, but both representatives satisfy the same
canonical physical projected-RHS equation at the same strict time.  Hence their
raw Fourier representatives agree almost everywhere.

This lets the lower-order second-q projected-RHS masses reuse the already
closed fourth-q analysis.  In particular,

    M₆(R_second) ≤ L¹(R_fourth) + M₁₀(R_fourth).

Thus no new high projected-RHS primitive is created by the second-q branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalSecondQProjectedRHSBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalSecondQProjectedRHSBridge :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

set_option maxHeartbeats 2200000

noncomputable def h3TerminalSecondQForcingDerivativeProjectedRHSRawL2MassAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j i : Fin 3) : ℝ :=
  let d :=
    h3TerminalSecondQForcingDerivativeLerayDataAt
      hH3 hClass ht j
  ‖h3SpectralScalarRawFourierL2 (d.R i)‖

noncomputable def h3TerminalSecondQForcingDerivativeProjectedRHSRawL1MassAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j i : Fin 3) : ℝ :=
  let d :=
    h3TerminalSecondQForcingDerivativeLerayDataAt
      hH3 hClass ht j
  h3SpectralScalarRawFourierL1Mass (d.R i)

noncomputable def h3TerminalSecondQForcingDerivativeProjectedRHSMoment6MassAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j i : Fin 3) : ℝ :=
  let d :=
    h3TerminalSecondQForcingDerivativeLerayDataAt
      hH3 hClass ht j
  h3SpectralScalarRawFourierMomentMass (6 : ℝ) (d.R i)

/--
The second-q and fourth-q chosen projected-RHS coordinates have the same raw
Fourier representative almost everywhere.
-/
theorem h3TerminalSecondQForcingDerivativeProjectedRHSRawFourier_ae_eq_fourthQ
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j₂ j₄ i : Fin 3) :
    let d₂ :=
      h3TerminalSecondQForcingDerivativeLerayDataAt
        hH3 hClass ht j₂
    let d₄ :=
      h3TerminalFourthQForcingDerivativeLerayDataAt
        hH3 hClass ht j₄
    h3SpectralScalarRawFourier (d₂.R i)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3SpectralScalarRawFourier (d₄.R i) := by

  dsimp only

  let d₂ :=
    h3TerminalSecondQForcingDerivativeLerayDataAt
      hH3 hClass ht j₂

  let d₄ :=
    h3TerminalFourthQForcingDerivativeLerayDataAt
      hH3 hClass ht j₄

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  have hU₂ :
      d₂.U = U := by
    dsimp only [d₂, U, htAbs]
    exact
      h3TerminalSecondQForcingDerivativeLerayDataAt_U_eq_terminalVelocity
        hH3 hClass ht j₂

  have hU₄ :
      d₄.U = U := by
    dsimp only [d₄, U, htAbs]
    exact
      h3TerminalFourthQForcingDerivativeLerayDataAt_U_eq_terminalVelocity
        hH3 hClass ht j₄

  have hPDE₂ :=
    h3TerminalSecondQForcingDerivativeLerayDataAt_R_rawFourier_ae_eq_unitPDE
      hH3 hClass ht j₂ i

  have hPDE₄ :=
    h3TerminalFourthQForcingDerivativeLerayDataAt_R_rawFourier_ae_eq_unitPDE
      hH3 hClass ht j₄ i

  have hPDE₂U :
      (
        (
          h3SpectralScalarRawFourierL2 (d₂.R i) :
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
    simpa only [d₂, hU₂] using hPDE₂

  have hPDE₄U :
      (
        (
          h3SpectralScalarRawFourierL2 (d₄.R i) :
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
    simpa only [d₄, hU₄] using hPDE₄

  have hRaw₂ :
      (
        (
          h3SpectralScalarRawFourierL2 (d₂.R i) :
          H3FourierComplexL2
        ) :
        H3FourierPoint3 → ℂ
      )
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralScalarRawFourier (d₂.R i) := by
    simpa [h3SpectralScalarRawFourierL2] using
      MemLp.coeFn_toLp
        (h3SpectralScalarRawFourier_memLp2 (d₂.R i))

  have hRaw₄ :
      (
        (
          h3SpectralScalarRawFourierL2 (d₄.R i) :
          H3FourierComplexL2
        ) :
        H3FourierPoint3 → ℂ
      )
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralScalarRawFourier (d₄.R i) := by
    simpa [h3SpectralScalarRawFourierL2] using
      MemLp.coeFn_toLp
        (h3SpectralScalarRawFourier_memLp2 (d₄.R i))

  exact
    hRaw₂.symm.trans
      (hPDE₂U.trans
        (hPDE₄U.symm.trans hRaw₄))

/-- The raw-L¹ masses of the two chosen projected-RHS representatives agree. -/
theorem h3TerminalSecondQForcingDerivativeProjectedRHSRawL1MassAt_eq_fourthQ
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j₂ j₄ i : Fin 3) :
    h3TerminalSecondQForcingDerivativeProjectedRHSRawL1MassAt
        hH3 hClass ht j₂ i
      =
    h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
      hH3 hClass ht j₄ i := by

  let d₂ :=
    h3TerminalSecondQForcingDerivativeLerayDataAt
      hH3 hClass ht j₂

  let d₄ :=
    h3TerminalFourthQForcingDerivativeLerayDataAt
      hH3 hClass ht j₄

  have hRaw :=
    h3TerminalSecondQForcingDerivativeProjectedRHSRawFourier_ae_eq_fourthQ
      hH3 hClass ht j₂ j₄ i

  unfold
    h3TerminalSecondQForcingDerivativeProjectedRHSRawL1MassAt
    h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
    h3SpectralScalarRawFourierL1Mass

  dsimp only [d₂, d₄]

  apply integral_congr_ae

  filter_upwards [hRaw] with ξ hξ

  rw [hξ]

/-- The raw-L² masses of the two chosen projected-RHS representatives agree. -/
theorem h3TerminalSecondQForcingDerivativeProjectedRHSRawL2MassAt_eq_fourthQ
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j₂ j₄ i : Fin 3) :
    h3TerminalSecondQForcingDerivativeProjectedRHSRawL2MassAt
        hH3 hClass ht j₂ i
      =
    h3TerminalFourthQForcingDerivativeProjectedRHSRawL2MassAt
      hH3 hClass ht j₄ i := by

  let d₂ :=
    h3TerminalSecondQForcingDerivativeLerayDataAt
      hH3 hClass ht j₂

  let d₄ :=
    h3TerminalFourthQForcingDerivativeLerayDataAt
      hH3 hClass ht j₄

  have hRaw :=
    h3TerminalSecondQForcingDerivativeProjectedRHSRawFourier_ae_eq_fourthQ
      hH3 hClass ht j₂ j₄ i

  have hL2 :
      h3SpectralScalarRawFourierL2 (d₂.R i)
        =
      h3SpectralScalarRawFourierL2 (d₄.R i) := by

    apply MeasureTheory.Lp.ext

    have hRaw₂ :
        (
          (
            h3SpectralScalarRawFourierL2 (d₂.R i) :
            H3FourierComplexL2
          ) :
          H3FourierPoint3 → ℂ
        )
          =ᵐ[(volume : Measure H3FourierPoint3)]
        h3SpectralScalarRawFourier (d₂.R i) := by
      simpa [h3SpectralScalarRawFourierL2] using
        MemLp.coeFn_toLp
          (h3SpectralScalarRawFourier_memLp2 (d₂.R i))

    have hRaw₄ :
        (
          (
            h3SpectralScalarRawFourierL2 (d₄.R i) :
            H3FourierComplexL2
          ) :
          H3FourierPoint3 → ℂ
        )
          =ᵐ[(volume : Measure H3FourierPoint3)]
        h3SpectralScalarRawFourier (d₄.R i) := by
      simpa [h3SpectralScalarRawFourierL2] using
        MemLp.coeFn_toLp
          (h3SpectralScalarRawFourier_memLp2 (d₄.R i))

    filter_upwards [hRaw₂, hRaw₄, hRaw]
      with ξ h₂ h₄ hEq

    rw [h₂, h₄, hEq]

  unfold
    h3TerminalSecondQForcingDerivativeProjectedRHSRawL2MassAt
    h3TerminalFourthQForcingDerivativeProjectedRHSRawL2MassAt

  dsimp only [d₂, d₄]

  rw [hL2]

theorem norm_pow_six_le_one_add_pow_ten
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 6 ≤ 1 + ‖ξ‖ ^ 10 := by

  have hx0 :
      0 ≤ ‖ξ‖ :=
    norm_nonneg ξ

  by_cases hx1 : ‖ξ‖ ≤ 1

  · have hpow :
        ‖ξ‖ ^ 6 ≤ (1 : ℝ) ^ 6 :=
      pow_le_pow_left₀ hx0 hx1 6

    have hpowOne :
        ‖ξ‖ ^ 6 ≤ 1 := by
      simpa using hpow

    have h10 :
        0 ≤ ‖ξ‖ ^ 10 :=
      pow_nonneg hx0 10

    linarith

  · have hx1' :
        1 ≤ ‖ξ‖ :=
      le_of_lt (lt_of_not_ge hx1)

    have hfour :
        (1 : ℝ) ^ 4 ≤ ‖ξ‖ ^ 4 :=
      pow_le_pow_left₀
        (by norm_num : 0 ≤ (1 : ℝ))
        hx1'
        4

    have hfour' :
        1 ≤ ‖ξ‖ ^ 4 := by
      simpa using hfour

    have h6 :
        0 ≤ ‖ξ‖ ^ 6 :=
      pow_nonneg hx0 6

    have hmul :=
      mul_le_mul_of_nonneg_left
        hfour'
        h6

    have h6le10 :
        ‖ξ‖ ^ 6 ≤ ‖ξ‖ ^ 10 := by
      calc
        ‖ξ‖ ^ 6
            =
          ‖ξ‖ ^ 6 * 1 := by ring
        _ ≤
          ‖ξ‖ ^ 6 * ‖ξ‖ ^ 4 := hmul
        _ =
          ‖ξ‖ ^ 10 := by ring

    exact
      le_add_of_nonneg_of_le
        zero_le_one
        h6le10

/--
The second-q projected-RHS order-six moment is bounded by the already-closed
fourth-q raw-L¹ plus order-ten projected-RHS masses.
-/
theorem h3TerminalSecondQForcingDerivativeProjectedRHSMoment6MassAt_le_fourthQ_rawL1_add_moment10
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j₂ j₄ i : Fin 3) :
    h3TerminalSecondQForcingDerivativeProjectedRHSMoment6MassAt
        hH3 hClass ht j₂ i
      ≤
    h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
        hH3 hClass ht j₄ i
      +
    h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
      hH3 hClass ht j₄ i := by

  let d₂ :=
    h3TerminalSecondQForcingDerivativeLerayDataAt
      hH3 hClass ht j₂

  let d₄ :=
    h3TerminalFourthQForcingDerivativeLerayDataAt
      hH3 hClass ht j₄

  have hRaw :=
    h3TerminalSecondQForcingDerivativeProjectedRHSRawFourier_ae_eq_fourthQ
      hH3 hClass ht j₂ j₄ i

  have hLeft :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (6 : ℝ) ξ *
            ‖h3SpectralScalarRawFourier (d₂.R i) ξ‖)
        (volume : Measure H3FourierPoint3) := by

    have h :=
      d₂.hR i

    unfold H3RawFourierMomentIntegrable at h

    convert h using 1 <;> norm_num

  have hRaw₄ :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier (d₄.R i) ξ‖)
        (volume : Measure H3FourierPoint3) := by

    have h :=
      MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1 (d₄.R i))

    exact h.norm

  have hMoment10 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (10 : ℝ) ξ *
            ‖h3SpectralScalarRawFourier (d₄.R i) ξ‖)
        (volume : Measure H3FourierPoint3) := by

    have h :=
      d₄.hR i

    unfold H3RawFourierMomentIntegrable at h

    convert h using 1 <;> norm_num

  let major : H3FourierPoint3 → ℝ :=
    fun ξ =>
      ‖h3SpectralScalarRawFourier (d₄.R i) ξ‖
        +
      h3FourierMomentWeight (10 : ℝ) ξ *
        ‖h3SpectralScalarRawFourier (d₄.R i) ξ‖

  have hMajor :
      Integrable major
        (volume : Measure H3FourierPoint3) := by
    dsimp only [major]
    exact hRaw₄.add hMoment10

  have hPoint :
      ∀ᵐ ξ : H3FourierPoint3 ∂volume,
        h3FourierMomentWeight (6 : ℝ) ξ *
            ‖h3SpectralScalarRawFourier (d₂.R i) ξ‖
          ≤
        major ξ := by

    filter_upwards [hRaw] with ξ hξ

    rw [hξ]

    have hNorm0 :
        0 ≤
          ‖h3SpectralScalarRawFourier (d₄.R i) ξ‖ :=
      norm_nonneg _

    have hPow :=
      mul_le_mul_of_nonneg_right
        (norm_pow_six_le_one_add_pow_ten ξ)
        hNorm0

    dsimp only [major]

    change
      h3FourierMomentWeight (6 : ℝ) ξ *
          ‖h3SpectralScalarRawFourier (d₄.R i) ξ‖
        ≤
      ‖h3SpectralScalarRawFourier (d₄.R i) ξ‖
        +
      h3FourierMomentWeight (10 : ℝ) ξ *
        ‖h3SpectralScalarRawFourier (d₄.R i) ξ‖

    have hWeight6 :
        h3FourierMomentWeight (6 : ℝ) ξ = ‖ξ‖ ^ 6 := by
      have h :=
        h3FourierMomentWeight_natCast 6 ξ
      norm_num at h ⊢
      exact h

    have hWeight10 :
        h3FourierMomentWeight (10 : ℝ) ξ = ‖ξ‖ ^ 10 := by
      have h :=
        h3FourierMomentWeight_natCast 10 ξ
      norm_num at h ⊢
      exact h

    rw [hWeight6, hWeight10]

    calc
      ‖ξ‖ ^ 6 *
          ‖h3SpectralScalarRawFourier (d₄.R i) ξ‖
          ≤
        (1 + ‖ξ‖ ^ 10) *
          ‖h3SpectralScalarRawFourier (d₄.R i) ξ‖ :=
        hPow
      _ =
        ‖h3SpectralScalarRawFourier (d₄.R i) ξ‖
          +
        ‖ξ‖ ^ 10 *
          ‖h3SpectralScalarRawFourier (d₄.R i) ξ‖ := by
        ring

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight (6 : ℝ) ξ *
          ‖h3SpectralScalarRawFourier (d₂.R i) ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3, major ξ := by

    exact
      integral_mono_ae
        hLeft
        hMajor
        hPoint

  have hMajorIntegral :
      (∫ ξ : H3FourierPoint3, major ξ)
        =
      h3SpectralScalarRawFourierL1Mass (d₄.R i)
        +
      h3SpectralScalarRawFourierMomentMass
        (10 : ℝ) (d₄.R i) := by

    dsimp only [major]

    rw [integral_add hRaw₄ hMoment10]

    rfl

  rw [hMajorIntegral] at hIntegral

  unfold
    h3TerminalSecondQForcingDerivativeProjectedRHSMoment6MassAt
    h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
    h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt

  dsimp only [d₂, d₄]

  exact hIntegral

end

end Euclidean
end Bridge
end PrimeTensor
