import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Higher.Subtail.StateMass.Group.Factor.Primitive.Origin.Higher.ProjectedRHSMoment10

/-!
# Projected-RHS order-ten moment: terminal state envelope

The exact PDE reduction leaves only two ingredients:

* the terminal velocity order-twelve moment;
* the order-ten nonlinear forcing moment, whose generic estimate costs only
  order-eleven terminal velocity moments and raw `L¹`.

Both orders eleven and twelve lie below the already-classified terminal
envelope

    L¹(U_k) + M₁₄(U_k).

This file packages that reduction quantitatively.  No new PDE identity and no
new escape channel is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 3000000

noncomputable local instance axisFintypeH3TerminalFourthQProjectedRHSMomentTenStateEnvelope
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

noncomputable local instance point3MeasureSpaceH3TerminalFourthQProjectedRHSMomentTenStateEnvelope :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (axisFintypeH3TerminalFourthQProjectedRHSMomentTenStateEnvelope Depth.three)
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Lower natural moments are controlled by L¹ + M14 -/

private theorem h3SpectralScalarRawFourierMomentMass_nat_le_L1Mass_add_fourteen_of_pointwise
    (m : ℕ)
    (H : H3SpectralScalarState)
    (hH14 : H3RawFourierMomentIntegrable (14 : ℝ) H)
    (hPow :
      ∀ ξ : H3FourierPoint3,
        ‖ξ‖ ^ m ≤ 1 + ‖ξ‖ ^ 14) :
    h3SpectralScalarRawFourierMomentMass (m : ℝ) H
      ≤
    h3SpectralScalarRawFourierL1Mass H
      +
    h3SpectralScalarRawFourierMomentMass (14 : ℝ) H := by

  have hWeightM :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (m : ℝ) ξ = ‖ξ‖ ^ m := by
    intro ξ
    exact h3FourierMomentWeight_natCast m ξ

  have hWeight14 :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (14 : ℝ) ξ = ‖ξ‖ ^ 14 := by
    intro ξ
    exact h3FourierMomentWeight_natCast 14 ξ

  have hRaw0 :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 H)

  have hRaw :
      Integrable
        (h3SpectralScalarRawFourier H)
        (volume : Measure H3FourierPoint3) := by
    simpa only [
      axisFintypeH3TerminalFourthQProjectedRHSMomentTenStateEnvelope,
      axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
      axisFintypeH3SpectralL1,
      axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
    ] using hRaw0

  have hRawNorm :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hRaw.norm

  have hH14' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 14 *
            ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3) := by

    unfold H3RawFourierMomentIntegrable at hH14

    refine hH14.congr ?_

    filter_upwards with ξ

    rw [hWeight14 ξ]

  let major : H3FourierPoint3 → ℝ :=
    fun ξ =>
      ‖h3SpectralScalarRawFourier H ξ‖
        +
      ‖ξ‖ ^ 14 *
        ‖h3SpectralScalarRawFourier H ξ‖

  have hMajor :
      Integrable major
        (volume : Measure H3FourierPoint3) := by
    dsimp only [major]
    exact hRawNorm.add hH14'

  have hLeftMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ m *
            ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3) := by

    exact
      ((continuous_norm.pow m).aestronglyMeasurable.mul
        hRawNorm.aestronglyMeasurable)

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖ξ‖ ^ m *
            ‖h3SpectralScalarRawFourier H ξ‖
          ≤
        major ξ := by

    intro ξ

    have hNorm0 :
        0 ≤ ‖h3SpectralScalarRawFourier H ξ‖ :=
      norm_nonneg _

    have hMul :=
      mul_le_mul_of_nonneg_right
        (hPow ξ)
        hNorm0

    dsimp only [major]

    calc
      ‖ξ‖ ^ m *
          ‖h3SpectralScalarRawFourier H ξ‖
          ≤
        (1 + ‖ξ‖ ^ 14) *
          ‖h3SpectralScalarRawFourier H ξ‖ :=
        hMul
      _ =
        ‖h3SpectralScalarRawFourier H ξ‖
          +
        ‖ξ‖ ^ 14 *
          ‖h3SpectralScalarRawFourier H ξ‖ := by
        ring

  have hLeft :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ m *
            ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3) := by

    refine hMajor.mono' hLeftMeas ?_

    filter_upwards with ξ

    have hNonneg :
        0 ≤
          ‖ξ‖ ^ m *
            ‖h3SpectralScalarRawFourier H ξ‖ :=
      mul_nonneg
        (pow_nonneg (norm_nonneg ξ) m)
        (norm_nonneg _)

    simpa only [
      Real.norm_eq_abs,
      abs_of_nonneg hNonneg
    ] using hPoint ξ

  have hInt :
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ m *
          ‖h3SpectralScalarRawFourier H ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3, major ξ := by

    apply integral_mono_ae hLeft hMajor

    filter_upwards with ξ

    exact hPoint ξ

  have hMassM :
      h3SpectralScalarRawFourierMomentMass (m : ℝ) H
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ m *
          ‖h3SpectralScalarRawFourier H ξ‖ := by

    unfold h3SpectralScalarRawFourierMomentMass

    apply integral_congr_ae

    filter_upwards with ξ

    rw [hWeightM ξ]

  have hMass14 :
      h3SpectralScalarRawFourierMomentMass (14 : ℝ) H
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 14 *
          ‖h3SpectralScalarRawFourier H ξ‖ := by

    unfold h3SpectralScalarRawFourierMomentMass

    apply integral_congr_ae

    filter_upwards with ξ

    rw [hWeight14 ξ]

  have hMass0 :
      h3SpectralScalarRawFourierL1Mass H
        =
      ∫ ξ : H3FourierPoint3,
        ‖h3SpectralScalarRawFourier H ξ‖ := by

    unfold h3SpectralScalarRawFourierL1Mass

    simp only [
      axisFintypeH3TerminalFourthQProjectedRHSMomentTenStateEnvelope,
      axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
      axisFintypeH3SpectralL1,
      axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
    ]

  have hMajorIntegral :
      (∫ ξ : H3FourierPoint3, major ξ)
        =
      h3SpectralScalarRawFourierL1Mass H
        +
      h3SpectralScalarRawFourierMomentMass (14 : ℝ) H := by

    dsimp only [major]

    rw [integral_add hRawNorm hH14']

    rw [hMass0, hMass14]

  rw [hMassM]

  rw [hMajorIntegral] at hInt

  exact hInt

theorem norm_pow_eleven_le_one_add_pow_fourteen
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 11 ≤ 1 + ‖ξ‖ ^ 14 := by

  have hx0 : 0 ≤ ‖ξ‖ :=
    norm_nonneg ξ

  by_cases hx1 : ‖ξ‖ ≤ 1

  · have hpow :
        ‖ξ‖ ^ 11 ≤ (1 : ℝ) ^ 11 :=
      pow_le_pow_left₀ hx0 hx1 11

    have hpowOne :
        ‖ξ‖ ^ 11 ≤ 1 := by
      simpa using hpow

    have h14 :
        0 ≤ ‖ξ‖ ^ 14 :=
      pow_nonneg hx0 14

    linarith

  · have hx1' :
        1 ≤ ‖ξ‖ :=
      le_of_lt (lt_of_not_ge hx1)

    have hthree :
        (1 : ℝ) ^ 3 ≤ ‖ξ‖ ^ 3 :=
      pow_le_pow_left₀
        (by norm_num : 0 ≤ (1 : ℝ))
        hx1'
        3

    have hthree' :
        1 ≤ ‖ξ‖ ^ 3 := by
      simpa using hthree

    have h11 :
        0 ≤ ‖ξ‖ ^ 11 :=
      pow_nonneg hx0 11

    have hmul :=
      mul_le_mul_of_nonneg_left
        hthree'
        h11

    have h11le14 :
        ‖ξ‖ ^ 11 ≤ ‖ξ‖ ^ 14 := by
      calc
        ‖ξ‖ ^ 11
            =
          ‖ξ‖ ^ 11 * 1 := by ring
        _ ≤
          ‖ξ‖ ^ 11 * ‖ξ‖ ^ 3 := hmul
        _ =
          ‖ξ‖ ^ 14 := by ring

    exact
      le_add_of_nonneg_of_le
        zero_le_one
        h11le14

theorem norm_pow_twelve_le_one_add_pow_fourteen
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 12 ≤ 1 + ‖ξ‖ ^ 14 := by

  have hx0 : 0 ≤ ‖ξ‖ :=
    norm_nonneg ξ

  by_cases hx1 : ‖ξ‖ ≤ 1

  · have hpow :
        ‖ξ‖ ^ 12 ≤ (1 : ℝ) ^ 12 :=
      pow_le_pow_left₀ hx0 hx1 12

    have hpowOne :
        ‖ξ‖ ^ 12 ≤ 1 := by
      simpa using hpow

    have h14 :
        0 ≤ ‖ξ‖ ^ 14 :=
      pow_nonneg hx0 14

    linarith

  · have hx1' :
        1 ≤ ‖ξ‖ :=
      le_of_lt (lt_of_not_ge hx1)

    have htwo :
        (1 : ℝ) ^ 2 ≤ ‖ξ‖ ^ 2 :=
      pow_le_pow_left₀
        (by norm_num : 0 ≤ (1 : ℝ))
        hx1'
        2

    have htwo' :
        1 ≤ ‖ξ‖ ^ 2 := by
      simpa using htwo

    have h12 :
        0 ≤ ‖ξ‖ ^ 12 :=
      pow_nonneg hx0 12

    have hmul :=
      mul_le_mul_of_nonneg_left
        htwo'
        h12

    have h12le14 :
        ‖ξ‖ ^ 12 ≤ ‖ξ‖ ^ 14 := by
      calc
        ‖ξ‖ ^ 12
            =
          ‖ξ‖ ^ 12 * 1 := by ring
        _ ≤
          ‖ξ‖ ^ 12 * ‖ξ‖ ^ 2 := hmul
        _ =
          ‖ξ‖ ^ 14 := by ring

    exact
      le_add_of_nonneg_of_le
        zero_le_one
        h12le14

theorem h3SpectralScalarRawFourierMomentMass_eleven_le_L1Mass_add_fourteen
    (H : H3SpectralScalarState)
    (hH14 : H3RawFourierMomentIntegrable (14 : ℝ) H) :
    h3SpectralScalarRawFourierMomentMass (11 : ℝ) H
      ≤
    h3SpectralScalarRawFourierL1Mass H
      +
    h3SpectralScalarRawFourierMomentMass (14 : ℝ) H := by

  exact
    h3SpectralScalarRawFourierMomentMass_nat_le_L1Mass_add_fourteen_of_pointwise
      11 H hH14 norm_pow_eleven_le_one_add_pow_fourteen

theorem h3SpectralScalarRawFourierMomentMass_twelve_le_L1Mass_add_fourteen
    (H : H3SpectralScalarState)
    (hH14 : H3RawFourierMomentIntegrable (14 : ℝ) H) :
    h3SpectralScalarRawFourierMomentMass (12 : ℝ) H
      ≤
    h3SpectralScalarRawFourierL1Mass H
      +
    h3SpectralScalarRawFourierMomentMass (14 : ℝ) H := by

  exact
    h3SpectralScalarRawFourierMomentMass_nat_le_L1Mass_add_fourteen_of_pointwise
      12 H hH14 norm_pow_twelve_le_one_add_pow_fourteen

/-! ## Terminal coordinate envelope -/

noncomputable def h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k : Fin 3) : ℝ :=
  h3TerminalForcingThirdQRawL1MassAt
      hH3 hClass ht k
    +
  h3TerminalForcingThirdQMoment14MassAt
      hH3 hClass ht k

theorem h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k : Fin 3) :
    0 ≤
      h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
        hH3 hClass ht k := by

  unfold h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt

  exact
    add_nonneg
      (h3TerminalForcingThirdQRawL1MassAt_nonneg
        hH3 hClass ht k)
      (h3TerminalForcingThirdQMoment14MassAt_nonneg
        hH3 hClass ht k)

theorem h3TerminalVelocityMoment11_le_projectedRHSMoment10StateEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    h3SpectralScalarRawFourierMomentMass (11 : ℝ) (U k)
      ≤
    h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
      hH3 hClass ht k := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  have hH14 :
      H3RawFourierMomentIntegrable
        (14 : ℝ)
        (U k) := by
    dsimp only [U]
    exact
      h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_nat
        hH3 hClass ht 14 (by norm_num) k

  have hBound :=
    h3SpectralScalarRawFourierMomentMass_eleven_le_L1Mass_add_fourteen
      (U k) hH14

  unfold h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
  unfold
    h3TerminalForcingThirdQRawL1MassAt
    h3TerminalForcingThirdQMoment14MassAt

  dsimp only [U, htAbs] at hBound ⊢

  exact hBound

theorem h3TerminalVelocityMoment12_le_projectedRHSMoment10StateEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    h3SpectralScalarRawFourierMomentMass (12 : ℝ) (U k)
      ≤
    h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
      hH3 hClass ht k := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  have hH14 :
      H3RawFourierMomentIntegrable
        (14 : ℝ)
        (U k) := by
    dsimp only [U]
    exact
      h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_nat
        hH3 hClass ht 14 (by norm_num) k

  have hBound :=
    h3SpectralScalarRawFourierMomentMass_twelve_le_L1Mass_add_fourteen
      (U k) hH14

  unfold h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
  unfold
    h3TerminalForcingThirdQRawL1MassAt
    h3TerminalForcingThirdQMoment14MassAt

  dsimp only [U, htAbs] at hBound ⊢

  exact hBound

theorem h3TerminalVelocityRawL1_le_projectedRHSMoment10StateEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k : Fin 3) :
    h3TerminalForcingThirdQRawL1MassAt
        hH3 hClass ht k
      ≤
    h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
      hH3 hClass ht k := by

  unfold h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt

  exact
    le_add_of_nonneg_right
      (h3TerminalForcingThirdQMoment14MassAt_nonneg
        hH3 hClass ht k)

/-! ## Full projected-RHS M10 bound by the finite state envelope -/

/--
The sole residual projected-RHS primitive is bounded by a fixed finite
quadratic expression in the three terminal coordinate envelopes
`L¹(U_k) + M₁₄(U_k)`.
-/
theorem h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt_le_stateEnvelopePolynomial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j i : Fin 3) :
    h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
        hH3 hClass ht j i
      ≤
    (2 * Real.pi) ^ 2 *
      h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
        hH3 hClass ht i
      +
    2 *
      ∑ k : Fin 3,
        ∑ l : Fin 3,
          (2 * Real.pi) *
            (
              h3FourierMomentSplitCoefficient (11 : ℝ) *
                (
                  h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
                      hH3 hClass ht k
                    *
                  h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
                      hH3 hClass ht l
                    +
                  h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
                      hH3 hClass ht k
                    *
                  h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
                      hH3 hClass ht l
                )
            ) := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  have hPDE :=
    h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt_le_velocityMoment12_add_forcingMoment10
      hH3 hClass ht j i

  have hU11Int :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          ((10 : ℝ) + 1)
          (U k) := by
    intro k
    have h :=
      h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_nat
        hH3 hClass ht 11 (by norm_num) k

    change
      H3RawFourierMomentIntegrable
        ((10 : ℝ) + 1)
        (h3TerminalVelocitySpectralStateAt hH3 t htAbs k)

    convert h using 1 <;> norm_num

  have hForce :=
    h3RawFinLerayOuterProductDivergenceMomentMass_le_stateMoments
      (q := (10 : ℝ))
      (by norm_num)
      U U
      hU11Int
      hU11Int
      i

  have hMoment11 :
      ∀ k : Fin 3,
        h3SpectralScalarRawFourierMomentMass
            ((10 : ℝ) + 1)
            (U k)
          ≤
        h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
          hH3 hClass ht k := by

    intro k

    have h :=
      h3TerminalVelocityMoment11_le_projectedRHSMoment10StateEnvelope
        hH3 hClass ht k

    change
      h3SpectralScalarRawFourierMomentMass
          ((10 : ℝ) + 1)
          (h3TerminalVelocitySpectralStateAt hH3 t htAbs k)
        ≤
      h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
        hH3 hClass ht k

    convert h using 1 <;> norm_num

  have hL1 :
      ∀ k : Fin 3,
        h3SpectralScalarRawFourierL1Mass (U k)
          ≤
        h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
          hH3 hClass ht k := by

    intro k

    have h :=
      h3TerminalVelocityRawL1_le_projectedRHSMoment10StateEnvelope
        hH3 hClass ht k

    unfold h3TerminalForcingThirdQRawL1MassAt at h

    simpa only [U, htAbs] using h

  have hMoment12 :
      h3SpectralScalarRawFourierMomentMass
          (12 : ℝ)
          (U i)
        ≤
      h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
        hH3 hClass ht i := by

    have h :=
      h3TerminalVelocityMoment12_le_projectedRHSMoment10StateEnvelope
        hH3 hClass ht i

    simpa only [U, htAbs] using h

  have hEach :
      ∀ k l : Fin 3,
        h3SpectralScalarRawFourierMomentMass
              ((10 : ℝ) + 1)
              (U k)
            *
          h3SpectralScalarRawFourierL1Mass (U l)
          +
        h3SpectralScalarRawFourierL1Mass (U k)
            *
          h3SpectralScalarRawFourierMomentMass
            ((10 : ℝ) + 1)
            (U l)
          ≤
        h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
              hH3 hClass ht k
            *
          h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
              hH3 hClass ht l
          +
        h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
              hH3 hClass ht k
            *
          h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
              hH3 hClass ht l := by

    intro k l

    have hEk0 :=
      h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt_nonneg
        hH3 hClass ht k

    have hEl0 :=
      h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt_nonneg
        hH3 hClass ht l

    have hL1k0 :
        0 ≤ h3SpectralScalarRawFourierL1Mass (U k) :=
      h3SpectralScalarRawFourierL1Mass_nonneg _

    have hL1l0 :
        0 ≤ h3SpectralScalarRawFourierL1Mass (U l) :=
      h3SpectralScalarRawFourierL1Mass_nonneg _

    have hM11k0 :
        0 ≤
          h3SpectralScalarRawFourierMomentMass
            ((10 : ℝ) + 1) (U k) :=
      h3SpectralScalarRawFourierMomentMass_nonneg _ _

    have hM11l0 :
        0 ≤
          h3SpectralScalarRawFourierMomentMass
            ((10 : ℝ) + 1) (U l) :=
      h3SpectralScalarRawFourierMomentMass_nonneg _ _

    have hLeft :
        h3SpectralScalarRawFourierMomentMass
              ((10 : ℝ) + 1)
              (U k)
            *
          h3SpectralScalarRawFourierL1Mass (U l)
          ≤
        h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
              hH3 hClass ht k
            *
          h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
              hH3 hClass ht l :=
      mul_le_mul
        (hMoment11 k)
        (hL1 l)
        hL1l0
        hEk0

    have hRight :
        h3SpectralScalarRawFourierL1Mass (U k)
            *
          h3SpectralScalarRawFourierMomentMass
            ((10 : ℝ) + 1)
            (U l)
          ≤
        h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
              hH3 hClass ht k
            *
          h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
              hH3 hClass ht l :=
      mul_le_mul
        (hL1 k)
        (hMoment11 l)
        hM11l0
        hEk0

    exact add_le_add hLeft hRight

  have hCoeff0 :
      0 ≤
        (2 * Real.pi) *
          h3FourierMomentSplitCoefficient (11 : ℝ) := by
    apply mul_nonneg
    · positivity
    · exact
        h3FourierMomentSplitCoefficient_nonneg (11 : ℝ)

  have hForceEnvelope :
      h3RawFinLerayOuterProductDivergenceMomentMass
          (10 : ℝ) U U i
        ≤
      2 *
        ∑ k : Fin 3,
          ∑ l : Fin 3,
            (2 * Real.pi) *
              (
                h3FourierMomentSplitCoefficient (11 : ℝ) *
                  (
                    h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
                        hH3 hClass ht k
                      *
                    h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
                        hH3 hClass ht l
                      +
                    h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
                        hH3 hClass ht k
                      *
                    h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
                        hH3 hClass ht l
                  )
              ) := by

    have hSum :
        (∑ k : Fin 3,
          ∑ l : Fin 3,
            (2 * Real.pi) *
              (
                h3FourierMomentSplitCoefficient ((10 : ℝ) + 1) *
                  (
                    h3SpectralScalarRawFourierMomentMass
                          ((10 : ℝ) + 1)
                          (U k)
                        *
                      h3SpectralScalarRawFourierL1Mass (U l)
                      +
                    h3SpectralScalarRawFourierL1Mass (U k)
                        *
                      h3SpectralScalarRawFourierMomentMass
                        ((10 : ℝ) + 1)
                        (U l)
                  )
              ))
          ≤
        ∑ k : Fin 3,
          ∑ l : Fin 3,
            (2 * Real.pi) *
              (
                h3FourierMomentSplitCoefficient (11 : ℝ) *
                  (
                    h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
                        hH3 hClass ht k
                      *
                    h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
                        hH3 hClass ht l
                      +
                    h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
                        hH3 hClass ht k
                      *
                    h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
                        hH3 hClass ht l
                  )
              ) := by

      apply Finset.sum_le_sum
      intro k hk

      apply Finset.sum_le_sum
      intro l hl

      have hPair :=
        hEach k l

      have hCoeffEq :
          h3FourierMomentSplitCoefficient ((10 : ℝ) + 1)
            =
          h3FourierMomentSplitCoefficient (11 : ℝ) := by
        norm_num

      rw [hCoeffEq]

      exact
        mul_le_mul_of_nonneg_left
          (
            mul_le_mul_of_nonneg_left
              hPair
              (h3FourierMomentSplitCoefficient_nonneg (11 : ℝ))
          )
          (by positivity : 0 ≤ 2 * Real.pi)

    have hForceNormalized :
        h3RawFinLerayOuterProductDivergenceMomentMass
            (10 : ℝ) U U i
          ≤
        2 *
          ∑ k : Fin 3,
            ∑ l : Fin 3,
              (2 * Real.pi) *
                (
                  h3FourierMomentSplitCoefficient ((10 : ℝ) + 1) *
                    (
                      h3SpectralScalarRawFourierMomentMass
                            ((10 : ℝ) + 1)
                            (U k)
                          *
                        h3SpectralScalarRawFourierL1Mass (U l)
                        +
                      h3SpectralScalarRawFourierL1Mass (U k)
                          *
                        h3SpectralScalarRawFourierMomentMass
                            ((10 : ℝ) + 1)
                            (U l)
                    )
                ) :=
      hForce

    exact
      hForceNormalized.trans
        (
          mul_le_mul_of_nonneg_left
            hSum
            (by norm_num)
        )

  have hCq0 :
      0 ≤ (2 * Real.pi) ^ 2 := by
    positivity

  have hDiffusionEnvelope :
      (2 * Real.pi) ^ 2 *
          h3SpectralScalarRawFourierMomentMass
            (12 : ℝ) (U i)
        ≤
      (2 * Real.pi) ^ 2 *
        h3TerminalFourthQProjectedRHSMoment10StateEnvelopeAt
          hH3 hClass ht i :=
    mul_le_mul_of_nonneg_left
      hMoment12
      hCq0

  have hPDE' :
      h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
          hH3 hClass ht j i
        ≤
      (2 * Real.pi) ^ 2 *
          h3SpectralScalarRawFourierMomentMass
            (12 : ℝ) (U i)
        +
      h3RawFinLerayOuterProductDivergenceMomentMass
        (10 : ℝ) U U i := by
    simpa only [U, htAbs] using hPDE

  exact
    hPDE'.trans
      (add_le_add hDiffusionEnvelope hForceEnvelope)

end

end Euclidean
end Bridge
end PrimeTensor
