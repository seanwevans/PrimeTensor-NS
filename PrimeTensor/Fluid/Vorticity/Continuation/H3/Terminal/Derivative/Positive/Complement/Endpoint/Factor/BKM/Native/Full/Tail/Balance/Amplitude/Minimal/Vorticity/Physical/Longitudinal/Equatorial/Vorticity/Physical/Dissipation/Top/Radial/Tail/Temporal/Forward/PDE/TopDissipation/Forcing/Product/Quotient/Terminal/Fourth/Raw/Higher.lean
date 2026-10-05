import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Mass.Higher.Moment.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Extended.Higher.Radial.Moment.Cascade

/-!
# Absorb the order-14/16 radial L² forcing obstruction into the higher hierarchy

The preceding checkpoint reduced the remaining order-fourteen forcing moment
to one fixed intrinsic velocity square mass

    ∫ |ξ|^(2p) |û_j(ξ)|² dξ

with `p = 14` or `p = 16`.

Since

    q(ξ) = (2π)² |ξ|²,

multiplication by the fixed positive factors `(2π)^28` and `(2π)^32`
identifies these masses with one component of the aggregate `q^14` and `q^16`
moments.  Those are exactly shifts `m = 10` and `m = 12` in the existing
extended higher-radial hierarchy `q^(4+m)`.

Thus the forcing-side high-moment obstruction introduces no new type of
terminal object: it is absorbed into the already-existing higher-radial
velocity hierarchy.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2200000

noncomputable local instance axisFintypeH3TerminalThirdQRadialHigher
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalThirdQRadialHigher :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Base-Fourier form of the intrinsic radial square mass -/

/--
The intrinsic raw radial square mass is the same finite integral written with
the canonical physical base-Fourier component.
-/
theorem h3TerminalForcingThirdQRawRadialSquareMassAt_eq_baseFourier_integral
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
    h3TerminalForcingThirdQRawRadialSquareMassAt
        hH3 hClass ht p j
      =
    ∫ ξ : H3FourierPoint3,
      (‖ξ‖ ^ p) ^ 2
        *
      ‖velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2
      ∂(volume : Measure H3FourierPoint3) := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs

  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs

  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs hInt

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

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

  unfold h3TerminalForcingThirdQRawRadialSquareMassAt
  dsimp only [U]

  apply integral_congr_ae

  filter_upwards [hBaseAE] with ξ hξ

  rw [← hξ]

  have hp0 :
      0 ≤ ‖ξ‖ ^ p :=
    pow_nonneg
      (norm_nonneg ξ)
      p

  rw [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hp0,
    mul_pow
  ]

/-! ## Exact scaling into q^14 and q^16 -/

/--
The order-fourteen raw radial square mass becomes the `q^14` component mass
after multiplication by `(2π)^28`.
-/
theorem h3TerminalForcingThirdQRawRadialSquareMass14_scaled_eq_q14_component
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
    ((2 * Real.pi) ^ 28 : ℝ)
      *
    h3TerminalForcingThirdQRawRadialSquareMassAt
      hH3 hClass ht 14 j
      =
    ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ ^ 14
        *
      ‖velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2
      ∂(volume : Measure H3FourierPoint3) := by

  dsimp only

  rw [
    h3TerminalForcingThirdQRawRadialSquareMassAt_eq_baseFourier_integral
      hH3 hClass ht 14 j
  ]

  rw [← integral_const_mul]

  apply integral_congr_ae

  filter_upwards with ξ

  unfold h3FourierGradientSquare

  ring

/--
The order-sixteen raw radial square mass becomes the `q^16` component mass
after multiplication by `(2π)^32`.
-/
theorem h3TerminalForcingThirdQRawRadialSquareMass16_scaled_eq_q16_component
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
    ((2 * Real.pi) ^ 32 : ℝ)
      *
    h3TerminalForcingThirdQRawRadialSquareMassAt
      hH3 hClass ht 16 j
      =
    ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ ^ 16
        *
      ‖velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2
      ∂(volume : Measure H3FourierPoint3) := by

  dsimp only

  rw [
    h3TerminalForcingThirdQRawRadialSquareMassAt_eq_baseFourier_integral
      hH3 hClass ht 16 j
  ]

  rw [← integral_const_mul]

  apply integral_congr_ae

  filter_upwards with ξ

  unfold h3FourierGradientSquare

  ring

/-! ## Domination by shifts 10 and 12 -/

/--
The scaled order-fourteen component mass is dominated by the existing shift-10
extended higher-radial moment.
-/
theorem ofReal_scaled_h3TerminalForcingThirdQRawRadialSquareMass14_le_extendedHigherTen
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ENNReal.ofReal
      (
        ((2 * Real.pi) ^ 28 : ℝ)
          *
        h3TerminalForcingThirdQRawRadialSquareMassAt
          hH3 hClass ht 14 j
      )
      ≤
    h3TerminalPhysicalExtendedHigherRadialMomentAt
      hH3 hClass 10 t ht := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs

  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs

  let f : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3FourierGradientSquare ξ ^ 14
        *
      ‖velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2

  let higher : H3FourierPoint3 → ℝ :=
    h3TerminalPhysicalHigherRadialDensityAt
      hH3 hClass 10 t ht

  obtain ⟨G14, hG14⟩ :=
    exists_h3TerminalVelocityNatRadialFourierL2
      hH3 hClass ht 14 (by norm_num) j

  have hGInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖G14 ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.Lp.memLp G14).norm.integrable_sq

  have hScaledGInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ((2 * Real.pi) ^ 28 : ℝ)
            *
          ‖G14 ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) :=
    hGInt.const_mul
      ((2 * Real.pi) ^ 28 : ℝ)

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

    filter_upwards [hG14, hBaseAE]
      with ξ hGξ hBaseξ

    rw [hGξ, ← hBaseξ]

    dsimp only [f]

    have hp0 :
        0 ≤ ‖ξ‖ ^ (14 : ℕ) :=
      pow_nonneg
        (norm_nonneg ξ)
        14

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
          14)
        (sq_nonneg
          ‖velocityH3BaseFourierAt
              u t hInt hMeas j ξ‖)

  have hMass :
      ((2 * Real.pi) ^ 28 : ℝ)
          *
        h3TerminalForcingThirdQRawRadialSquareMassAt
          hH3 hClass ht 14 j
        =
      ∫ ξ : H3FourierPoint3,
        f ξ
        ∂(volume : Measure H3FourierPoint3) := by

    dsimp only [f, hInt, hMeas, htAbs]

    exact
      h3TerminalForcingThirdQRawRadialSquareMass14_scaled_eq_q14_component
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
        0 ≤ h3FourierGradientSquare ξ ^ 14 :=
      pow_nonneg
        (h3FourierGradientSquare_nonneg ξ)
        14

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
The scaled order-sixteen component mass is dominated by the existing shift-12
extended higher-radial moment.
-/
theorem ofReal_scaled_h3TerminalForcingThirdQRawRadialSquareMass16_le_extendedHigherTwelve
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ENNReal.ofReal
      (
        ((2 * Real.pi) ^ 32 : ℝ)
          *
        h3TerminalForcingThirdQRawRadialSquareMassAt
          hH3 hClass ht 16 j
      )
      ≤
    h3TerminalPhysicalExtendedHigherRadialMomentAt
      hH3 hClass 12 t ht := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs

  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs

  let f : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3FourierGradientSquare ξ ^ 16
        *
      ‖velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2

  let higher : H3FourierPoint3 → ℝ :=
    h3TerminalPhysicalHigherRadialDensityAt
      hH3 hClass 12 t ht

  obtain ⟨G16, hG16⟩ :=
    exists_h3TerminalVelocityNatRadialFourierL2
      hH3 hClass ht 16 (by norm_num) j

  have hGInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖G16 ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.Lp.memLp G16).norm.integrable_sq

  have hScaledGInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ((2 * Real.pi) ^ 32 : ℝ)
            *
          ‖G16 ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) :=
    hGInt.const_mul
      ((2 * Real.pi) ^ 32 : ℝ)

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

    filter_upwards [hG16, hBaseAE]
      with ξ hGξ hBaseξ

    rw [hGξ, ← hBaseξ]

    dsimp only [f]

    have hp0 :
        0 ≤ ‖ξ‖ ^ (16 : ℕ) :=
      pow_nonneg
        (norm_nonneg ξ)
        16

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
          16)
        (sq_nonneg
          ‖velocityH3BaseFourierAt
              u t hInt hMeas j ξ‖)

  have hMass :
      ((2 * Real.pi) ^ 32 : ℝ)
          *
        h3TerminalForcingThirdQRawRadialSquareMassAt
          hH3 hClass ht 16 j
        =
      ∫ ξ : H3FourierPoint3,
        f ξ
        ∂(volume : Measure H3FourierPoint3) := by

    dsimp only [f, hInt, hMeas, htAbs]

    exact
      h3TerminalForcingThirdQRawRadialSquareMass16_scaled_eq_q16_component
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
        0 ≤ h3FourierGradientSquare ξ ^ 16 :=
      pow_nonneg
        (h3FourierGradientSquare_nonneg ξ)
        16

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

theorem extendedHigherRadialMoment_ten_tendsto_top_of_rawRadialSquareMass14_tendstoAtTop
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
          h3TerminalForcingThirdQRawRadialSquareMassAt
            hH3 hClass (hτ n) 14 j)
        atTop
        atTop) :
    Tendsto
      (fun n : ℕ =>
        h3TerminalPhysicalExtendedHigherRadialMomentAt
          hH3 hClass 10 (τ n) (hτ n))
      atTop
      (𝓝 ∞) := by

  have hC :
      0 < ((2 * Real.pi) ^ 28 : ℝ) := by
    positivity

  have hScaled :
      Tendsto
        (fun n : ℕ =>
          ((2 * Real.pi) ^ 28 : ℝ)
            *
          h3TerminalForcingThirdQRawRadialSquareMassAt
            hH3 hClass (hτ n) 14 j)
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
              ((2 * Real.pi) ^ 28 : ℝ)
                *
              h3TerminalForcingThirdQRawRadialSquareMassAt
                hH3 hClass (hτ n) 14 j
            ))
        atTop
        (𝓝 ∞) :=
    ENNReal.tendsto_ofReal_atTop.comp
      hScaled

  have hLe :
      ∀ n : ℕ,
        ENNReal.ofReal
          (
            ((2 * Real.pi) ^ 28 : ℝ)
              *
            h3TerminalForcingThirdQRawRadialSquareMassAt
              hH3 hClass (hτ n) 14 j
          )
          ≤
        h3TerminalPhysicalExtendedHigherRadialMomentAt
          hH3 hClass 10 (τ n) (hτ n) := by

    intro n

    exact
      ofReal_scaled_h3TerminalForcingThirdQRawRadialSquareMass14_le_extendedHigherTen
        hH3 hClass (hτ n) j

  exact
    tendsto_nhds_top_mono'
      hOfReal
      hLe

theorem extendedHigherRadialMoment_twelve_tendsto_top_of_rawRadialSquareMass16_tendstoAtTop
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
          h3TerminalForcingThirdQRawRadialSquareMassAt
            hH3 hClass (hτ n) 16 j)
        atTop
        atTop) :
    Tendsto
      (fun n : ℕ =>
        h3TerminalPhysicalExtendedHigherRadialMomentAt
          hH3 hClass 12 (τ n) (hτ n))
      atTop
      (𝓝 ∞) := by

  have hC :
      0 < ((2 * Real.pi) ^ 32 : ℝ) := by
    positivity

  have hScaled :
      Tendsto
        (fun n : ℕ =>
          ((2 * Real.pi) ^ 32 : ℝ)
            *
          h3TerminalForcingThirdQRawRadialSquareMassAt
            hH3 hClass (hτ n) 16 j)
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
              ((2 * Real.pi) ^ 32 : ℝ)
                *
              h3TerminalForcingThirdQRawRadialSquareMassAt
                hH3 hClass (hτ n) 16 j
            ))
        atTop
        (𝓝 ∞) :=
    ENNReal.tendsto_ofReal_atTop.comp
      hScaled

  have hLe :
      ∀ n : ℕ,
        ENNReal.ofReal
          (
            ((2 * Real.pi) ^ 32 : ℝ)
              *
            h3TerminalForcingThirdQRawRadialSquareMassAt
              hH3 hClass (hτ n) 16 j
          )
          ≤
        h3TerminalPhysicalExtendedHigherRadialMomentAt
          hH3 hClass 12 (τ n) (hτ n) := by

    intro n

    exact
      ofReal_scaled_h3TerminalForcingThirdQRawRadialSquareMass16_le_extendedHigherTwelve
        hH3 hClass (hτ n) j

  exact
    tendsto_nhds_top_mono'
      hOfReal
      hLe

/-! ## Fixed higher-radial channel -/

/-- Channel `0` selects shift `10`; channel `1` selects shift `12`. -/
def h3TerminalForcingThirdQHigherRadialShift
    (q : Fin 2) : ℕ :=
  if q = 0 then 10 else 12

/--
A fixed order-14/16 radial square escape is therefore a fixed escape in the
existing extended higher-radial hierarchy.
-/
theorem h3TerminalForcingThirdQMoment14RadialSquareChannel_escape_resolves_higherRadial
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
          h3TerminalForcingThirdQMoment14RadialSquareChannelAt
            hH3 hClass (hτ n) j q)
        atTop
        atTop) :
    Tendsto
      (fun n : ℕ =>
        h3TerminalPhysicalExtendedHigherRadialMomentAt
          hH3 hClass
          (h3TerminalForcingThirdQHigherRadialShift q)
          (τ n)
          (hτ n))
      atTop
      (𝓝 ∞) := by

  fin_cases q

  · apply
      extendedHigherRadialMoment_ten_tendsto_top_of_rawRadialSquareMass14_tendstoAtTop
        hH3 hClass j τ hτ

    simpa [
      h3TerminalForcingThirdQMoment14RadialSquareChannelAt
    ] using hTop

  · apply
      extendedHigherRadialMoment_twelve_tendsto_top_of_rawRadialSquareMass16_tendstoAtTop
        hH3 hClass j τ hτ

    simpa [
      h3TerminalForcingThirdQMoment14RadialSquareChannelAt
    ] using hTop

/--
The sixth-diffusion frontier now consists only of physical H³-energy escape or
escape inside the pre-existing extended higher-radial hierarchy (shift `4`,
`10`, or `12`).
-/
theorem sixthDiffusion_hilbertDerivativeNorm_escape_extendedHigherFour_or_energy_or_fixedHigherRadial10_12
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hSixth :
      Tendsto
        (fun n : ℕ =>
          h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
            hH3 hClass j
            H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion
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
              hH3 hClass 4
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
                  (h3TerminalForcingThirdQHigherRadialShift q)
                  (τ (s n))
                  (hτ (s n)))
              atTop
              (𝓝 ∞)
      )
    ) := by

  rcases
    sixthDiffusion_hilbertDerivativeNorm_escape_extendedHigherFour_or_energy_or_fixedRadial14_16
      hH3 hClass j τ hτ hTauTendsto hSixth
  with
    hHigherFour
    |
    hRest

  · exact Or.inl hHigherFour

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
        h3TerminalForcingThirdQMoment14RadialSquareChannel_escape_resolves_higherRadial
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
