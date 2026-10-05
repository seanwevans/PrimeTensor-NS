import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Mass
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Extended.Higher.Radial.Moment.Cascade

/-!
# Embed the terminal fourth-q velocity mass into the higher-radial hierarchy

The fourth-q terminal velocity factor has squared norm

    ∫ q(ξ)^8 |û_j(ξ)|² dξ.

The already-existing extended higher-radial hierarchy at shift `m = 4` is

    ∫⁺ q(ξ)^8 ∑ₖ |û_k(ξ)|² dξ.

Hence one component is pointwise dominated by the existing aggregate.  This
file records that exact embedding and transfers fourth-q velocity mass escape
to the established `m = 4` extended higher-radial moment.

The consequence is structural: the velocity side of the sixth-diffusion
factor split introduces no new kind of terminal obstruction.  Only the
third-q forcing raw mass remains outside that pre-existing velocity hierarchy.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3TerminalSixthRawMassHigher
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalSixthRawMassHigher :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Canonical base-Fourier representative -/

/--
The fourth-q velocity raw mass is exactly the finite real integral of the
`j`-th canonical base-Fourier component with weight `q^8`.
-/
theorem h3TerminalPhysicalTopDissipationVelocityFourthQRawMassAt_eq_baseFourier_integral
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
    h3TerminalPhysicalTopDissipationVelocityFourthQRawMassAt
        hH3 hClass ht j
      =
    ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ ^ 8
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

  rw [
    h3TerminalPhysicalTopDissipationVelocityFourthQRawMassAt_eq_integral
      hH3 hClass ht j
  ]

  change
    (∫ ξ : H3FourierPoint3,
      ‖((h3FourierGradientSquare ξ ^ 4 : ℝ) : ℂ) *
          h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2
      ∂(volume : Measure H3FourierPoint3))
      =
    ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ ^ 8
        *
      ‖velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2
      ∂(volume : Measure H3FourierPoint3)

  rw [hRaw]

  apply integral_congr_ae

  filter_upwards with ξ

  have hq :
      0 ≤ h3FourierGradientSquare ξ :=
    h3FourierGradientSquare_nonneg ξ

  rw [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hq 4),
    mul_pow
  ]

  ring

/-! ## Domination by the existing m = 4 higher moment -/

/--
The `j`-th fourth-q velocity raw mass is dominated by the pre-existing
aggregate extended higher-radial moment with shift `m = 4`.
-/
theorem ofReal_h3TerminalPhysicalTopDissipationVelocityFourthQRawMassAt_le_extendedHigherRadialMoment_four
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ENNReal.ofReal
      (
        h3TerminalPhysicalTopDissipationVelocityFourthQRawMassAt
          hH3 hClass ht j
      )
      ≤
    h3TerminalPhysicalExtendedHigherRadialMomentAt
      hH3 hClass 4 t ht := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs

  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs

  let f : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3FourierGradientSquare ξ ^ 8
        *
      ‖velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2

  let higher : H3FourierPoint3 → ℝ :=
    h3TerminalPhysicalHigherRadialDensityAt
      hH3 hClass 4 t ht

  let V4 : H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationVelocityFourthQFourierL2At
      hH3 hClass ht j

  have hV4AE :=
    h3TerminalPhysicalTopDissipationVelocityFourthQFourierL2At_ae
      hH3 hClass ht j

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

  have hFInt :
      Integrable f
        (volume : Measure H3FourierPoint3) := by

    have hLpInt :
        Integrable
          (fun ξ : H3FourierPoint3 => ‖V4 ξ‖ ^ 2)
          (volume : Measure H3FourierPoint3) :=
      (MeasureTheory.Lp.memLp V4).norm.integrable_sq

    refine hLpInt.congr ?_

    filter_upwards [hV4AE] with ξ hξ

    rw [hξ]

    change
      ‖((h3FourierGradientSquare ξ ^ 4 : ℝ) : ℂ) *
          h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2
        =
      f ξ

    rw [hRaw]

    dsimp only [f]

    have hq :
        0 ≤ h3FourierGradientSquare ξ :=
      h3FourierGradientSquare_nonneg ξ

    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hq 4),
      mul_pow
    ]

    ring

  have hFNonneg :
      0 ≤ᵐ[(volume : Measure H3FourierPoint3)] f := by

    filter_upwards with ξ

    dsimp only [f]

    exact
      mul_nonneg
        (pow_nonneg
          (h3FourierGradientSquare_nonneg ξ)
          8)
        (sq_nonneg
          ‖velocityH3BaseFourierAt
              u t hInt hMeas j ξ‖)

  have hMass :
      h3TerminalPhysicalTopDissipationVelocityFourthQRawMassAt
          hH3 hClass ht j
        =
      ∫ ξ : H3FourierPoint3,
        f ξ
        ∂(volume : Measure H3FourierPoint3) := by

    dsimp only [f, hInt, hMeas, htAbs]

    exact
      h3TerminalPhysicalTopDissipationVelocityFourthQRawMassAt_eq_baseFourier_integral
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
        ∂(volume : Measure H3FourierPoint3) := by

    exact
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

    have hq8 :
        0 ≤ h3FourierGradientSquare ξ ^ 8 :=
      pow_nonneg
        (h3FourierGradientSquare_nonneg ξ)
        8

    dsimp only [f, higher]

    unfold h3TerminalPhysicalHigherRadialDensityAt

    dsimp only [htAbs, hInt, hMeas]

    norm_num

    exact
      mul_le_mul_of_nonneg_left
        hComponent
        hq8

  rw [hMass, hBridge]

  unfold
    h3TerminalPhysicalExtendedHigherRadialMomentAt

  apply lintegral_mono

  intro ξ

  exact
    ENNReal.ofReal_le_ofReal
      (hPointwise ξ)

/-! ## Sequence transfer -/

/--
Fourth-q velocity raw-mass escape forces the existing shift-four extended
higher-radial moment to diverge on the same sequence.
-/
theorem extendedHigherRadialMoment_four_tendsto_top_of_velocityFourthQRawMass_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hMassTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalPhysicalTopDissipationVelocityFourthQRawMassAt
              hH3 hClass (hτ n) j
        )
        atTop
        atTop) :
    Tendsto
      (
        fun n : ℕ =>
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass 4 (τ n) (hτ n)
      )
      atTop
      (𝓝 ∞) := by

  have hOfReal :
      Tendsto
        (
          fun n : ℕ =>
            ENNReal.ofReal
              (
                h3TerminalPhysicalTopDissipationVelocityFourthQRawMassAt
                  hH3 hClass (hτ n) j
              )
        )
        atTop
        (𝓝 ∞) :=
    ENNReal.tendsto_ofReal_atTop.comp
      hMassTop

  have hLe :
      ∀ n : ℕ,
        ENNReal.ofReal
          (
            h3TerminalPhysicalTopDissipationVelocityFourthQRawMassAt
              hH3 hClass (hτ n) j
          )
          ≤
        h3TerminalPhysicalExtendedHigherRadialMomentAt
          hH3 hClass 4 (τ n) (hτ n) := by

    intro n

    exact
      ofReal_h3TerminalPhysicalTopDissipationVelocityFourthQRawMassAt_le_extendedHigherRadialMoment_four
        hH3 hClass (hτ n) j

  exact
    tendsto_nhds_top_mono'
      hOfReal
      hLe

/--
The sixth-diffusion derivative frontier can therefore be stated entirely as:

* escape of the already-existing shift-four extended velocity moment on a
  cofinal subsequence, or
* escape of the canonical third-q forcing raw mass on the original sequence.
-/
theorem sixthDiffusion_hilbertDerivativeNorm_escape_extendedHigherFour_or_forcingThirdQRawMass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hTauTendsto :
      Tendsto τ atTop (𝓝 T))
    (hSixth :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
              hH3 hClass j
              H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion
              (τ n)
        )
        atTop
        atTop) :
    (
      ∃ k : ℕ → ℕ,
        (∀ n : ℕ, n ≤ k n)
          ∧
        Tendsto k atTop atTop
          ∧
        Tendsto
          (fun n : ℕ => τ (k n))
          atTop
          (𝓝 T)
          ∧
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass 4
                (τ (k n))
                (hτ (k n))
          )
          atTop
          (𝓝 ∞)
    )
      ∨
    Tendsto
      (
        fun n : ℕ =>
          h3TerminalPhysicalTopDissipationForcingThirdQRawMassAt
            hH3 hClass (hτ n) j
      )
      atTop
      atTop := by

  rcases
    sixthDiffusion_hilbertDerivativeNorm_escape_velocityFourthQRawMass_or_forcingThirdQRawMass
      hH3 hClass j τ hτ hTauTendsto hSixth
  with
    ⟨k, hk, hkTop, hTauK, hVelocityMassTop⟩
    |
    hForcingMassTop

  · left

    refine
      ⟨
        k,
        hk,
        hkTop,
        hTauK,
        ?_
      ⟩

    exact
      extendedHigherRadialMoment_four_tendsto_top_of_velocityFourthQRawMass_tendstoAtTop
        hH3
        hClass
        j
        (fun n : ℕ => τ (k n))
        (fun n : ℕ => hτ (k n))
        hVelocityMassTop

  · exact
      Or.inr hForcingMassTop

end

end Euclidean
end Bridge
end PrimeTensor
