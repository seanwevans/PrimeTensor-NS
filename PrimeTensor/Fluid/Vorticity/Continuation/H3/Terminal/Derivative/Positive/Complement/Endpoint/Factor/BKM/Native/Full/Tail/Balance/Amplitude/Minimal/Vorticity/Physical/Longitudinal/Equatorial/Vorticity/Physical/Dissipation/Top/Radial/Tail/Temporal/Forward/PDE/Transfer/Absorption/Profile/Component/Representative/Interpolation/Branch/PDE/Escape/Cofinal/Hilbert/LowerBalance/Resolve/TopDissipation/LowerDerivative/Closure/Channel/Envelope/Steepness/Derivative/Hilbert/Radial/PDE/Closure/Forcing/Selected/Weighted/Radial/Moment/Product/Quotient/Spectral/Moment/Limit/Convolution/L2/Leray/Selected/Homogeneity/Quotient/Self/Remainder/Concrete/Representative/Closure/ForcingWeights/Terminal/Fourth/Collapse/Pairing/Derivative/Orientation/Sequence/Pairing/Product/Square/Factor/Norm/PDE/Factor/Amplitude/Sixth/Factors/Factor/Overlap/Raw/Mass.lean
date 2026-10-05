import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete.Representative.Closure.ForcingWeights.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square.Factor.Norm.PDE.Factor.Amplitude.Sixth.Factors.Factor.Overlap.Raw

/-!
# Terminal sixth-factor raw masses

The two terminal factors from the sixth-diffusion split now have intrinsic raw
Fourier representatives. Package their squared `L²` norms as canonical scalar
masses and transfer the sixth-diffusion escape alternative to those masses.

No uniform terminal bound is asserted here: the available selected radial
bounds depend on the local restart energy and restart window. This file only
performs the exact norm-to-mass conversion.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1200000

noncomputable local instance axisFintypeH3TerminalSixthRawMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalSixthRawMass :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

noncomputable def h3TerminalPhysicalTopDissipationVelocityFourthQRawMassAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ℝ :=
  ‖h3TerminalPhysicalTopDissipationVelocityFourthQFourierL2At
      hH3 hClass ht j‖ ^ 2

noncomputable def h3TerminalPhysicalTopDissipationForcingThirdQRawMassAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ℝ :=
  ‖h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At
      hH3 hClass ht j‖ ^ 2

theorem h3TerminalPhysicalTopDissipationVelocityFourthQRawMassAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    0 ≤
      h3TerminalPhysicalTopDissipationVelocityFourthQRawMassAt
        hH3 hClass ht j := by

  unfold h3TerminalPhysicalTopDissipationVelocityFourthQRawMassAt
  positivity

theorem h3TerminalPhysicalTopDissipationForcingThirdQRawMassAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    0 ≤
      h3TerminalPhysicalTopDissipationForcingThirdQRawMassAt
        hH3 hClass ht j := by

  unfold h3TerminalPhysicalTopDissipationForcingThirdQRawMassAt
  positivity

theorem h3TerminalPhysicalTopDissipationVelocityFourthQRawMassAt_eq_integral
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
    h3TerminalPhysicalTopDissipationVelocityFourthQRawMassAt
        hH3 hClass ht j
      =
    ∫ ξ : H3FourierPoint3,
      ‖((h3FourierGradientSquare ξ ^ 4 : ℝ) : ℂ) *
        h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2 := by

  dsimp only
  unfold h3TerminalPhysicalTopDissipationVelocityFourthQRawMassAt
  exact
    norm_sq_h3TerminalPhysicalTopDissipationVelocityFourthQFourierL2At
      hH3 hClass ht j

theorem h3TerminalPhysicalTopDissipationForcingThirdQRawMassAt_eq_integral
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
    h3TerminalPhysicalTopDissipationForcingThirdQRawMassAt
        hH3 hClass ht j
      =
    ∫ ξ : H3FourierPoint3,
      ‖((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ) *
        h3RawFinLerayOuterProductDivergence U U j ξ‖ ^ 2 := by

  dsimp only
  unfold h3TerminalPhysicalTopDissipationForcingThirdQRawMassAt
  exact
    norm_sq_h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At
      hH3 hClass ht j

private theorem tendsto_sq_atTop_of_nonneg_tendstoAtTop_mass
    (f : ℕ → ℝ)
    (hf0 : ∀ n : ℕ, 0 ≤ f n)
    (hf :
      Tendsto f atTop atTop) :
    Tendsto
      (fun n : ℕ => (f n) ^ 2)
      atTop
      atTop := by

  refine
    tendsto_atTop.2
      ?_

  intro M

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        max 1 M
          ≤
        f n :=
    (tendsto_atTop.1 hf)
      (max 1 M)

  filter_upwards [hLarge] with n hn

  have hOne :
      (1 : ℝ) ≤ f n :=
    le_trans
      (le_max_left 1 M)
      hn

  have hM :
      M ≤ f n :=
    le_trans
      (le_max_right 1 M)
      hn

  nlinarith [hf0 n]

theorem sixthDiffusion_hilbertDerivativeNorm_escape_velocityFourthQRawMass_or_forcingThirdQRawMass
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
              h3TerminalPhysicalTopDissipationVelocityFourthQRawMassAt
                hH3 hClass (hτ (k n)) j
          )
          atTop
          atTop
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
    sixthDiffusion_hilbertDerivativeNorm_escape_velocityFourthQ_or_forcingThirdQ
      hH3 hClass j τ hτ hTauTendsto hSixth
  with
    ⟨k, hk, hkTop, hTauK, hVelocityTop⟩
    |
    hForcingTop

  · left

    let f : ℕ → ℝ :=
      fun n =>
        ‖h3TerminalPhysicalTopDissipationVelocityFourthQFourierL2At
          hH3 hClass (hτ (k n)) j‖

    have hf0 :
        ∀ n : ℕ,
          0 ≤ f n := by
      intro n
      dsimp only [f]
      exact norm_nonneg _

    have hfTop :
        Tendsto f atTop atTop := by
      simpa only [f] using hVelocityTop

    have hSqTop :=
      tendsto_sq_atTop_of_nonneg_tendstoAtTop_mass
        f hf0 hfTop

    refine
      ⟨
        k,
        hk,
        hkTop,
        hTauK,
        ?_
      ⟩

    simpa only [
      f,
      h3TerminalPhysicalTopDissipationVelocityFourthQRawMassAt
    ] using hSqTop

  · right

    let f : ℕ → ℝ :=
      fun n =>
        ‖h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At
          hH3 hClass (hτ n) j‖

    have hf0 :
        ∀ n : ℕ,
          0 ≤ f n := by
      intro n
      dsimp only [f]
      exact norm_nonneg _

    have hfTop :
        Tendsto f atTop atTop := by
      simpa only [f] using hForcingTop

    have hSqTop :=
      tendsto_sq_atTop_of_nonneg_tendstoAtTop_mass
        f hf0 hfTop

    simpa only [
      f,
      h3TerminalPhysicalTopDissipationForcingThirdQRawMassAt
    ] using hSqTop

end

end Euclidean
end Bridge
end PrimeTensor
