import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Higher

/-!
# Absorb the order-10/12 fourth-q radial L² obstruction into the higher hierarchy

The preceding checkpoint reduced the remaining order-ten forcing moment to one
fixed intrinsic velocity square mass

    ∫ |ξ|^(2p) |û_j(ξ)|² dξ

with `p = 10` or `p = 12`.

Since `q(ξ) = (2π)² |ξ|²`, multiplication by `(2π)^20` or `(2π)^24`
identifies these masses with one component of the aggregate `q^10` and `q^12`
moments.  Those are exactly shifts `m = 6` and `m = 8` in the existing
extended higher-radial hierarchy `q^(4+m)`.

Thus the fourth-q forcing-side high-moment obstruction is absorbed into the
already-existing higher-radial velocity hierarchy.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2200000

noncomputable local instance axisFintypeH3TerminalFourthQRadialHigher
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalFourthQRadialHigher :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
The fourth-q intrinsic radial square mass is the same finite integral written
with the canonical physical base-Fourier component.
-/
theorem h3TerminalForcingFourthQRawRadialSquareMassAt_eq_baseFourier_integral
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (p : ℕ)
    (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let hInt : VelocityH3IntegrableAt u t :=
      hH3.velocity_h3_integrable t htAbs
    let hMeas : VelocityH3MeasurableAt u t :=
      velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
        hH3.navier_stokes htAbs
    h3TerminalForcingFourthQRawRadialSquareMassAt
        hH3 hClass ht p j
      =
    ∫ ξ : H3FourierPoint3,
      (‖ξ‖ ^ p) ^ 2
        *
      ‖velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2
      ∂(volume : Measure H3FourierPoint3) := by

  simpa [
    h3TerminalForcingFourthQRawRadialSquareMassAt
  ] using
    h3TerminalForcingThirdQRawRadialSquareMassAt_eq_baseFourier_integral
      hH3 hClass ht p j

/--
The order-ten raw radial square mass becomes the `q^10` component mass after
multiplication by `(2π)^20`.
-/
theorem h3TerminalForcingFourthQRawRadialSquareMass10_scaled_eq_q10_component
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let hInt : VelocityH3IntegrableAt u t :=
      hH3.velocity_h3_integrable t htAbs
    let hMeas : VelocityH3MeasurableAt u t :=
      velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
        hH3.navier_stokes htAbs
    ((2 * Real.pi) ^ 20 : ℝ)
      *
    h3TerminalForcingFourthQRawRadialSquareMassAt
      hH3 hClass ht 10 j
      =
    ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ ^ 10
        *
      ‖velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2
      ∂(volume : Measure H3FourierPoint3) := by

  dsimp only

  rw [
    h3TerminalForcingFourthQRawRadialSquareMassAt_eq_baseFourier_integral
      hH3 hClass ht 10 j
  ]

  rw [← integral_const_mul]

  apply integral_congr_ae

  filter_upwards with ξ

  unfold h3FourierGradientSquare

  ring

/--
The order-twelve raw radial square mass becomes the `q^12` component mass after
multiplication by `(2π)^24`.
-/
theorem h3TerminalForcingFourthQRawRadialSquareMass12_scaled_eq_q12_component
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let hInt : VelocityH3IntegrableAt u t :=
      hH3.velocity_h3_integrable t htAbs
    let hMeas : VelocityH3MeasurableAt u t :=
      velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
        hH3.navier_stokes htAbs
    ((2 * Real.pi) ^ 24 : ℝ)
      *
    h3TerminalForcingFourthQRawRadialSquareMassAt
      hH3 hClass ht 12 j
      =
    ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ ^ 12
        *
      ‖velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2
      ∂(volume : Measure H3FourierPoint3) := by

  dsimp only

  rw [
    h3TerminalForcingFourthQRawRadialSquareMassAt_eq_baseFourier_integral
      hH3 hClass ht 12 j
  ]

  rw [← integral_const_mul]

  apply integral_congr_ae

  filter_upwards with ξ

  unfold h3FourierGradientSquare

  ring

/--
The scaled order-ten component mass is dominated by shift `6` of the existing
extended higher-radial moment.
-/
theorem ofReal_scaled_h3TerminalForcingFourthQRawRadialSquareMass10_le_extendedHigherSix
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ENNReal.ofReal
      (
        ((2 * Real.pi) ^ 20 : ℝ)
          *
        h3TerminalForcingFourthQRawRadialSquareMassAt
          hH3 hClass ht 10 j
      )
      ≤
    h3TerminalPhysicalExtendedHigherRadialMomentAt
      hH3 hClass 6 t ht := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs

  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs

  let f : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3FourierGradientSquare ξ ^ 10
        *
      ‖velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2

  let higher : H3FourierPoint3 → ℝ :=
    h3TerminalPhysicalHigherRadialDensityAt
      hH3 hClass 6 t ht

  obtain ⟨G10, hG10⟩ :=
    exists_h3TerminalVelocityNatRadialFourierL2
      hH3 hClass ht 10 (by norm_num) j

  have hGInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖G10 ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.Lp.memLp G10).norm.integrable_sq

  have hScaledGInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ((2 * Real.pi) ^ 20 : ℝ)
            *
          ‖G10 ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) :=
    hGInt.const_mul
      ((2 * Real.pi) ^ 20 : ℝ)

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs hInt

  have hRaw :
      h3SpectralScalarRawFourierL2 (U j)
        =
      velocityH3BaseFourierAt
        u t hInt hMeas j := by

    dsimp only [U]

    unfold h3TerminalVelocitySpectralStateAt

    exact
      h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
        hFourier j

  have hRawAE :=
    h3SpectralScalarRawFourierL2_ae
      (U j)

  have hBaseAE :
      ((velocityH3BaseFourierAt
          u t hInt hMeas j :
        H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralScalarRawFourier (U j) := by
    simpa only [hRaw] using hRawAE

  have hFInt :
      Integrable f
        (volume : Measure H3FourierPoint3) := by

    refine hScaledGInt.congr ?_

    filter_upwards [hG10, hBaseAE]
      with ξ hGξ hBaseξ

    rw [hGξ, ← hBaseξ]

    dsimp only [f]

    have hp0 :
        0 ≤ ‖ξ‖ ^ (10 : ℕ) :=
      pow_nonneg
        (norm_nonneg ξ)
        10

    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg hp0,
      mul_pow
    ]

    unfold h3FourierGradientSquare
    ring

  have hFNonneg :
      0 ≤ᵐ[(volume : Measure H3FourierPoint3)] f := by

    filter_upwards with ξ

    dsimp only [f]

    exact
      mul_nonneg
        (pow_nonneg
          (h3FourierGradientSquare_nonneg ξ)
          10)
        (sq_nonneg
          ‖velocityH3BaseFourierAt
              u t hInt hMeas j ξ‖)

  have hMass :
      ((2 * Real.pi) ^ 20 : ℝ)
          *
        h3TerminalForcingFourthQRawRadialSquareMassAt
          hH3 hClass ht 10 j
        =
      ∫ ξ : H3FourierPoint3,
        f ξ
        ∂(volume : Measure H3FourierPoint3) := by

    dsimp only [f, hInt, hMeas, htAbs]

    exact
      h3TerminalForcingFourthQRawRadialSquareMass10_scaled_eq_q10_component
        hH3 hClass ht j

  have hBridge :
      ENNReal.ofReal
        (
          ∫ ξ : H3FourierPoint3,
            f ξ
            ∂(volume : Measure H3FourierPoint3)
        )
        =
      ∫⁻ ξ : H3FourierPoint3,
        ENNReal.ofReal (f ξ)
        ∂(volume : Measure H3FourierPoint3) :=
    ofReal_integral_eq_lintegral_ofReal
      hFInt
      hFNonneg

  have hPointwise :
      ∀ ξ : H3FourierPoint3,
        f ξ ≤ higher ξ := by

    intro ξ

    have hComponent :
        ‖velocityH3BaseFourierAt
            u t hInt hMeas j ξ‖ ^ 2
          ≤
        velocityH3FourierMassDensityAt
          u t hInt hMeas ξ := by

      unfold velocityH3FourierMassDensityAt

      exact
        Finset.single_le_sum
          (fun k _ =>
            sq_nonneg
              ‖velocityH3BaseFourierAt
                  u t hInt hMeas k ξ‖)
          (Finset.mem_univ j)

    have hq :
        0 ≤ h3FourierGradientSquare ξ ^ 10 :=
      pow_nonneg
        (h3FourierGradientSquare_nonneg ξ)
        10

    dsimp only [f, higher]

    unfold h3TerminalPhysicalHigherRadialDensityAt

    dsimp only [htAbs, hInt, hMeas]

    norm_num

    exact
      mul_le_mul_of_nonneg_left
        hComponent
        hq

  rw [hMass, hBridge]

  unfold h3TerminalPhysicalExtendedHigherRadialMomentAt

  apply lintegral_mono

  intro ξ

  exact
    ENNReal.ofReal_le_ofReal
      (hPointwise ξ)

/--
The scaled order-twelve component mass is dominated by shift `8` of the
existing extended higher-radial moment.
-/
theorem ofReal_scaled_h3TerminalForcingFourthQRawRadialSquareMass12_le_extendedHigherEight
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ENNReal.ofReal
      (
        ((2 * Real.pi) ^ 24 : ℝ)
          *
        h3TerminalForcingFourthQRawRadialSquareMassAt
          hH3 hClass ht 12 j
      )
      ≤
    h3TerminalPhysicalExtendedHigherRadialMomentAt
      hH3 hClass 8 t ht := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs

  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs

  let f : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3FourierGradientSquare ξ ^ 12
        *
      ‖velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2

  let higher : H3FourierPoint3 → ℝ :=
    h3TerminalPhysicalHigherRadialDensityAt
      hH3 hClass 8 t ht

  obtain ⟨G12, hG12⟩ :=
    exists_h3TerminalVelocityNatRadialFourierL2
      hH3 hClass ht 12 (by norm_num) j

  have hGInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖G12 ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.Lp.memLp G12).norm.integrable_sq

  have hScaledGInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ((2 * Real.pi) ^ 24 : ℝ)
            *
          ‖G12 ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) :=
    hGInt.const_mul
      ((2 * Real.pi) ^ 24 : ℝ)

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs hInt

  have hRaw :
      h3SpectralScalarRawFourierL2 (U j)
        =
      velocityH3BaseFourierAt
        u t hInt hMeas j := by

    dsimp only [U]

    unfold h3TerminalVelocitySpectralStateAt

    exact
      h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
        hFourier j

  have hRawAE :=
    h3SpectralScalarRawFourierL2_ae
      (U j)

  have hBaseAE :
      ((velocityH3BaseFourierAt
          u t hInt hMeas j :
        H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralScalarRawFourier (U j) := by
    simpa only [hRaw] using hRawAE

  have hFInt :
      Integrable f
        (volume : Measure H3FourierPoint3) := by

    refine hScaledGInt.congr ?_

    filter_upwards [hG12, hBaseAE]
      with ξ hGξ hBaseξ

    rw [hGξ, ← hBaseξ]

    dsimp only [f]

    have hp0 :
        0 ≤ ‖ξ‖ ^ (12 : ℕ) :=
      pow_nonneg
        (norm_nonneg ξ)
        12

    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg hp0,
      mul_pow
    ]

    unfold h3FourierGradientSquare
    ring

  have hFNonneg :
      0 ≤ᵐ[(volume : Measure H3FourierPoint3)] f := by

    filter_upwards with ξ

    dsimp only [f]

    exact
      mul_nonneg
        (pow_nonneg
          (h3FourierGradientSquare_nonneg ξ)
          12)
        (sq_nonneg
          ‖velocityH3BaseFourierAt
              u t hInt hMeas j ξ‖)

  have hMass :
      ((2 * Real.pi) ^ 24 : ℝ)
          *
        h3TerminalForcingFourthQRawRadialSquareMassAt
          hH3 hClass ht 12 j
        =
      ∫ ξ : H3FourierPoint3,
        f ξ
        ∂(volume : Measure H3FourierPoint3) := by

    dsimp only [f, hInt, hMeas, htAbs]

    exact
      h3TerminalForcingFourthQRawRadialSquareMass12_scaled_eq_q12_component
        hH3 hClass ht j

  have hBridge :
      ENNReal.ofReal
        (
          ∫ ξ : H3FourierPoint3,
            f ξ
            ∂(volume : Measure H3FourierPoint3)
        )
        =
      ∫⁻ ξ : H3FourierPoint3,
        ENNReal.ofReal (f ξ)
        ∂(volume : Measure H3FourierPoint3) :=
    ofReal_integral_eq_lintegral_ofReal
      hFInt
      hFNonneg

  have hPointwise :
      ∀ ξ : H3FourierPoint3,
        f ξ ≤ higher ξ := by

    intro ξ

    have hComponent :
        ‖velocityH3BaseFourierAt
            u t hInt hMeas j ξ‖ ^ 2
          ≤
        velocityH3FourierMassDensityAt
          u t hInt hMeas ξ := by

      unfold velocityH3FourierMassDensityAt

      exact
        Finset.single_le_sum
          (fun k _ =>
            sq_nonneg
              ‖velocityH3BaseFourierAt
                  u t hInt hMeas k ξ‖)
          (Finset.mem_univ j)

    have hq :
        0 ≤ h3FourierGradientSquare ξ ^ 12 :=
      pow_nonneg
        (h3FourierGradientSquare_nonneg ξ)
        12

    dsimp only [f, higher]

    unfold h3TerminalPhysicalHigherRadialDensityAt

    dsimp only [htAbs, hInt, hMeas]

    norm_num

    exact
      mul_le_mul_of_nonneg_left
        hComponent
        hq

  rw [hMass, hBridge]

  unfold h3TerminalPhysicalExtendedHigherRadialMomentAt

  apply lintegral_mono

  intro ξ

  exact
    ENNReal.ofReal_le_ofReal
      (hPointwise ξ)

/-! ## Escape transfer -/

theorem extendedHigherRadialMoment_six_tendsto_top_of_rawRadialSquareMass10_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hMassTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalForcingFourthQRawRadialSquareMassAt
            hH3 hClass (hτ n) 10 j)
        atTop
        atTop) :
    Tendsto
      (fun n : ℕ =>
        h3TerminalPhysicalExtendedHigherRadialMomentAt
          hH3 hClass 6 (τ n) (hτ n))
      atTop
      (𝓝 ∞) := by

  have hC :
      0 < ((2 * Real.pi) ^ 20 : ℝ) := by
    positivity

  have hScaled :
      Tendsto
        (fun n : ℕ =>
          ((2 * Real.pi) ^ 20 : ℝ)
            *
          h3TerminalForcingFourthQRawRadialSquareMassAt
            hH3 hClass (hτ n) 10 j)
        atTop
        atTop := by

    exact
      hMassTop.const_mul_atTop
        hC

  have hOfReal :
      Tendsto
        (fun n : ℕ =>
          ENNReal.ofReal
            (
              ((2 * Real.pi) ^ 20 : ℝ)
                *
              h3TerminalForcingFourthQRawRadialSquareMassAt
                hH3 hClass (hτ n) 10 j
            ))
        atTop
        (𝓝 ∞) :=
    ENNReal.tendsto_ofReal_atTop.comp
      hScaled

  have hLe :
      ∀ n : ℕ,
        ENNReal.ofReal
          (
            ((2 * Real.pi) ^ 20 : ℝ)
              *
            h3TerminalForcingFourthQRawRadialSquareMassAt
              hH3 hClass (hτ n) 10 j
          )
          ≤
        h3TerminalPhysicalExtendedHigherRadialMomentAt
          hH3 hClass 6 (τ n) (hτ n) := by

    intro n

    exact
      ofReal_scaled_h3TerminalForcingFourthQRawRadialSquareMass10_le_extendedHigherSix
        hH3 hClass (hτ n) j

  exact
    tendsto_nhds_top_mono'
      hOfReal
      hLe

theorem extendedHigherRadialMoment_eight_tendsto_top_of_rawRadialSquareMass12_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hMassTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalForcingFourthQRawRadialSquareMassAt
            hH3 hClass (hτ n) 12 j)
        atTop
        atTop) :
    Tendsto
      (fun n : ℕ =>
        h3TerminalPhysicalExtendedHigherRadialMomentAt
          hH3 hClass 8 (τ n) (hτ n))
      atTop
      (𝓝 ∞) := by

  have hC :
      0 < ((2 * Real.pi) ^ 24 : ℝ) := by
    positivity

  have hScaled :
      Tendsto
        (fun n : ℕ =>
          ((2 * Real.pi) ^ 24 : ℝ)
            *
          h3TerminalForcingFourthQRawRadialSquareMassAt
            hH3 hClass (hτ n) 12 j)
        atTop
        atTop := by

    exact
      hMassTop.const_mul_atTop
        hC

  have hOfReal :
      Tendsto
        (fun n : ℕ =>
          ENNReal.ofReal
            (
              ((2 * Real.pi) ^ 24 : ℝ)
                *
              h3TerminalForcingFourthQRawRadialSquareMassAt
                hH3 hClass (hτ n) 12 j
            ))
        atTop
        (𝓝 ∞) :=
    ENNReal.tendsto_ofReal_atTop.comp
      hScaled

  have hLe :
      ∀ n : ℕ,
        ENNReal.ofReal
          (
            ((2 * Real.pi) ^ 24 : ℝ)
              *
            h3TerminalForcingFourthQRawRadialSquareMassAt
              hH3 hClass (hτ n) 12 j
          )
          ≤
        h3TerminalPhysicalExtendedHigherRadialMomentAt
          hH3 hClass 8 (τ n) (hτ n) := by

    intro n

    exact
      ofReal_scaled_h3TerminalForcingFourthQRawRadialSquareMass12_le_extendedHigherEight
        hH3 hClass (hτ n) j

  exact
    tendsto_nhds_top_mono'
      hOfReal
      hLe

/-! ## Fixed higher-radial channel -/

/-- Channel `0` selects shift `6`; channel `1` selects shift `8`. -/
def h3TerminalForcingFourthQHigherRadialShift
    (q : Fin 2) : ℕ :=
  if q = 0 then 6 else 8

/--
A fixed order-10/12 radial square escape is a fixed escape in the existing
extended higher-radial hierarchy.
-/
theorem h3TerminalForcingFourthQMoment10RadialSquareChannel_escape_resolves_higherRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (q : Fin 2)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalForcingFourthQMoment10RadialSquareChannelAt
            hH3 hClass (hτ n) j q)
        atTop
        atTop) :
    Tendsto
      (fun n : ℕ =>
        h3TerminalPhysicalExtendedHigherRadialMomentAt
          hH3 hClass
          (h3TerminalForcingFourthQHigherRadialShift q)
          (τ n)
          (hτ n))
      atTop
      (𝓝 ∞) := by

  fin_cases q

  · apply
      extendedHigherRadialMoment_six_tendsto_top_of_rawRadialSquareMass10_tendstoAtTop
        hH3 hClass j τ hτ

    simpa [
      h3TerminalForcingFourthQMoment10RadialSquareChannelAt,
      h3TerminalForcingFourthQHigherRadialShift
    ] using hTop

  · apply
      extendedHigherRadialMoment_eight_tendsto_top_of_rawRadialSquareMass12_tendstoAtTop
        hH3 hClass j τ hτ

    simpa [
      h3TerminalForcingFourthQMoment10RadialSquareChannelAt,
      h3TerminalForcingFourthQHigherRadialShift
    ] using hTop

/--
The fourth-temporal frontier now consists only of physical H³-energy escape or
escape inside the pre-existing extended higher-radial hierarchy (shift `2`,
`6`, or `8`).
-/
theorem fourthTemporal_amplitude_escape_extendedHigherTwo_or_energy_or_fixedHigherRadial6_8
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hAmplitudeTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalResolvedPhysicalPDEChannelAmplitude
            hH3 hClass j
            H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
            (τ n))
        atTop
        atTop) :
    (
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n)
          ∧
        Tendsto s atTop atTop
          ∧
        Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T)
          ∧
        Tendsto
          (fun n : ℕ =>
            h3TerminalPhysicalExtendedHigherRadialMomentAt
              hH3 hClass 2
              (τ (s n))
              (hτ (s n)))
          atTop
          (𝓝 ∞)
    )
      ∨
    (
      (
        ∃ s : ℕ → ℕ,
          (∀ n : ℕ, n ≤ s n)
            ∧
          Tendsto s atTop atTop
            ∧
          Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T)
            ∧
          Tendsto
            (fun n : ℕ =>
              velocityH3EnergyAt u (τ (s n)))
            atTop
            atTop
      )
        ∨
      (
        ∃ q : Fin 2,
          ∃ s : ℕ → ℕ,
            (∀ n : ℕ, n ≤ s n)
              ∧
            Tendsto s atTop atTop
              ∧
            Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T)
              ∧
            Tendsto
              (fun n : ℕ =>
                h3TerminalPhysicalExtendedHigherRadialMomentAt
                  hH3 hClass
                  (h3TerminalForcingFourthQHigherRadialShift q)
                  (τ (s n))
                  (hτ (s n)))
              atTop
              (𝓝 ∞)
      )
    ) := by

  rcases
    fourthTemporal_amplitude_escape_extendedHigherTwo_or_energy_or_fixedRadial10_12
      hH3 hClass j τ hτ hTauTendsto hAmplitudeTop
  with
    hHigherTwo
    |
    hRest

  · exact Or.inl hHigherTwo

  · rcases hRest with
      hEnergy
      |
      hRadial

    · exact
        Or.inr
          (Or.inl hEnergy)

    · rcases hRadial with
        ⟨m, q, s, hs, hsTop, hTauSub, hSquareTop⟩

      have hHigherTop :=
        h3TerminalForcingFourthQMoment10RadialSquareChannel_escape_resolves_higherRadial
          hH3 hClass m q
          (fun n : ℕ => τ (s n))
          (fun n : ℕ => hτ (s n))
          hSquareTop

      exact
        Or.inr
          (
            Or.inr
              ⟨
                q,
                s,
                hs,
                hsTop,
                hTauSub,
                hHigherTop
              ⟩
          )

end

end Euclidean
end Bridge
end PrimeTensor
