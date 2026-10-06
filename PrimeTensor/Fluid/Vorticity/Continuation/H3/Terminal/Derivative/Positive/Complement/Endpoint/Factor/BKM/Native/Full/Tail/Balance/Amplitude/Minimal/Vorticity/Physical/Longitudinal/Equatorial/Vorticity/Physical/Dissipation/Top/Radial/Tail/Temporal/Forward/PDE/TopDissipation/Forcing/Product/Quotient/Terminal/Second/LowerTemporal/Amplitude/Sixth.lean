import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Extended.Higher.Radial.Moment.Cascade

/-!
# Close the sixth-diffusion state-size branch of fourth-temporal amplitude escape

The sixth-diffusion Hilbert state is exactly

    q³ û_j.

Its squared `L²` norm therefore has density

    q⁶ |û_j|².

The existing extended higher-radial hierarchy at shift `m = 2` has density

    q^(4+2) ∑ₖ |û_k|²
      =
    q⁶ ∑ₖ |û_k|².

Thus the sixth-diffusion amplitude is pointwise dominated by the existing
`m = 2` extended higher-radial moment.  Escape of the former forces escape of
the latter on the same sequence.

Combining this with the preceding fourth-temporal amplitude split leaves only
the canonical fourth-q forcing mass as the unresolved state-size forcing
branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalFourthTemporalAmplitudeSixthClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalFourthTemporalAmplitudeSixthClosure :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

set_option maxHeartbeats 1800000

/--
At every strict physical time, the sixth-diffusion channel amplitude is
dominated by the existing shift-two extended higher-radial moment.
-/
theorem ofReal_h3TerminalResolvedSixthDiffusionChannelAmplitude_le_extendedHigherRadialMoment_two
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ENNReal.ofReal
      (
        h3TerminalResolvedPhysicalPDEChannelAmplitude
          hH3 hClass j
          H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion
          t
      )
      ≤
    h3TerminalPhysicalExtendedHigherRadialMomentAt
      hH3 hClass 2 t ht := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs

  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs

  let V3 : H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2At
      hH3 hClass ht j

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  let f : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3FourierGradientSquare ξ ^ 6
        *
      ‖velocityH3BaseFourierAt
          u t hInt hMeas j ξ‖ ^ 2

  let higher : H3FourierPoint3 → ℝ :=
    h3TerminalPhysicalHigherRadialDensityAt
      hH3 hClass 2 t ht

  have hV3AE :=
    h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2At_ae
      hH3 hClass ht j

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

  have hFInt :
      Integrable f
        (volume : Measure H3FourierPoint3) := by

    have hLpInt :
        Integrable
          (fun ξ : H3FourierPoint3 => ‖V3 ξ‖ ^ 2)
          (volume : Measure H3FourierPoint3) :=
      (MeasureTheory.Lp.memLp V3).norm.integrable_sq

    refine hLpInt.congr ?_

    filter_upwards [hV3AE] with ξ hξ

    rw [hξ]

    change
      ‖((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ) *
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
      abs_of_nonneg (pow_nonneg hq 3),
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
          6)
        (sq_nonneg
          ‖velocityH3BaseFourierAt
              u t hInt hMeas j ξ‖)

  have hAmplitude :
      h3TerminalResolvedPhysicalPDEChannelAmplitude
          hH3 hClass j
          H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion
          t
        =
      ∫ ξ : H3FourierPoint3,
        f ξ
        ∂(volume : Measure H3FourierPoint3) := by

    rw [
      resolvedSixthDiffusionChannelAmplitude_eq_norm_sq_hilbertState
    ]

    change
      ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
          hH3 hClass j t‖ ^ 2
        =
      ∫ ξ : H3FourierPoint3,
        f ξ
        ∂(volume : Measure H3FourierPoint3)

    rw [
      h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path_eq
        hH3 hClass ht j,
      h3FourierComplexL2_norm_sq_eq_integral_norm_sq
    ]

    apply integral_congr_ae

    filter_upwards [hV3AE] with ξ hξ

    rw [hξ]

    change
      ‖((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ) *
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
      abs_of_nonneg (pow_nonneg hq 3),
      mul_pow
    ]

    ring

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

    have hq6 :
        0 ≤ h3FourierGradientSquare ξ ^ 6 :=
      pow_nonneg
        (h3FourierGradientSquare_nonneg ξ)
        6

    dsimp only [f, higher]

    unfold h3TerminalPhysicalHigherRadialDensityAt

    dsimp only [htAbs, hInt, hMeas]

    norm_num

    exact
      mul_le_mul_of_nonneg_left
        hComponent
        hq6

  rw [hAmplitude, hBridge]

  unfold
    h3TerminalPhysicalExtendedHigherRadialMomentAt

  apply lintegral_mono

  intro ξ

  exact
    ENNReal.ofReal_le_ofReal
      (hPointwise ξ)

/--
Escape of the sixth-diffusion state amplitude forces escape of the existing
shift-two extended higher-radial moment on the same sequence.
-/
theorem extendedHigherRadialMoment_two_tendsto_top_of_sixthDiffusionAmplitude_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hAmplitudeTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalResolvedPhysicalPDEChannelAmplitude
            hH3 hClass j
            H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion
            (τ n))
        atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        h3TerminalPhysicalExtendedHigherRadialMomentAt
          hH3 hClass 2
          (τ n)
          (hτ n))
      atTop
      (𝓝 ∞) := by

  have hOfReal :
      Tendsto
        (fun n : ℕ =>
          ENNReal.ofReal
            (
              h3TerminalResolvedPhysicalPDEChannelAmplitude
                hH3 hClass j
                H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion
                (τ n)
            ))
        atTop
        (𝓝 ∞) :=
    ENNReal.tendsto_ofReal_atTop.comp
      hAmplitudeTop

  have hLe :
      ∀ n : ℕ,
        ENNReal.ofReal
          (
            h3TerminalResolvedPhysicalPDEChannelAmplitude
              hH3 hClass j
              H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion
              (τ n)
          )
          ≤
        h3TerminalPhysicalExtendedHigherRadialMomentAt
          hH3 hClass 2
          (τ n)
          (hτ n) := by

    intro n

    exact
      ofReal_h3TerminalResolvedSixthDiffusionChannelAmplitude_le_extendedHigherRadialMoment_two
        hH3 hClass (hτ n) j

  exact
    tendsto_nhds_top_mono'
      hOfReal
      hLe

/--
After closing the sixth-diffusion state-size side, fourth-temporal amplitude
escape leaves only:

* the existing shift-two extended higher-radial velocity moment; or
* the canonical fourth-q forcing mass.
-/
theorem fourthTemporal_amplitude_escape_extendedHigherTwo_or_forcingFourthQMass
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
    (hAmplitudeTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalResolvedPhysicalPDEChannelAmplitude
            hH3 hClass j
            H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
            (τ n))
        atTop atTop) :
    (
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto
          (fun n : ℕ => τ (s n))
          atTop
          (𝓝 T) ∧
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
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto
          (fun n : ℕ => τ (s n))
          atTop
          (𝓝 T) ∧
        Tendsto
          (fun n : ℕ =>
            h3TerminalPhysicalTopDissipationForcingFourthQMassPath
              hH3 hClass j (τ (s n)))
          atTop
          atTop
    ) := by

  rcases
    fourthTemporal_amplitude_escape_sixthDiffusionAmplitude_or_forcingFourthQMass
      hH3 hClass j τ hτ hTauTendsto hAmplitudeTop
  with hSixth | hForcing

  · rcases hSixth with
      ⟨s, hs, hsTop, hTauSub, hSixthTop⟩

    have hHigherTop :=
      extendedHigherRadialMoment_two_tendsto_top_of_sixthDiffusionAmplitude_tendstoAtTop
        hH3 hClass j
        (fun n : ℕ => τ (s n))
        (fun n : ℕ => hτ (s n))
        hSixthTop

    exact
      Or.inl
        ⟨
          s,
          hs,
          hsTop,
          hTauSub,
          hHigherTop
        ⟩

  · exact
      Or.inr hForcing

end

end Euclidean
end Bridge
end PrimeTensor
