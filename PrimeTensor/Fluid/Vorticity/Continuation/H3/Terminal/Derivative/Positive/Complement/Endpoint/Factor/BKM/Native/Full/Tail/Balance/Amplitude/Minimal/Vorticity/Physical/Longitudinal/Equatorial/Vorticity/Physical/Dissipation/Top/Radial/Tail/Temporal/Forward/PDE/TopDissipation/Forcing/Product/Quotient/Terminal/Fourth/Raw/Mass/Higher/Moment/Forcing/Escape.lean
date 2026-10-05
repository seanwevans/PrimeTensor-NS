import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Mass.Higher
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Mass.Higher.Moment.Forcing

/-!
# Third-q forcing escape reduces to the terminal radial Leray envelope

The preceding checkpoint bounds the canonical terminal third-q forcing raw
mass by the square of the order-six radial Leray envelope.  This file names
that envelope and transfers any forcing raw-mass escape to genuine escape of
the already-compiled radial convolution bound.

Thus the sixth-diffusion frontier becomes:

* escape of the existing shift-four extended higher-radial velocity moment on
  a cofinal subsequence, or
* escape of the terminal order-six radial Leray envelope on the original
  sequence.

No new analytic estimate is introduced here.  The step is purely quantitative:
a nonnegative quantity whose square dominates something tending to `+∞` must
itself tend to `+∞`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3TerminalThirdQForcingRadialLerayEscape
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalThirdQForcingRadialLerayEscape :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
The explicit nonnegative radial-Leray envelope controlling the canonical
terminal third-q forcing coordinate.
-/
noncomputable def h3TerminalForcingThirdQRadialLerayEnvelopeAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let h14 :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (6 + 1) : ℕ) : ℝ))
          (U k) :=
    h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLeraySix
      hH3 hClass ht
  ((2 * Real.pi) ^ 6 : ℝ)
    *
  (
    ∑ k : Fin 3,
      2 *
        (
          ∑ l : Fin 3,
            (2 * Real.pi) *
              ‖h3RawProductConvolutionRadialFourierL2
                  7
                  (U k) (U l)
                  (h14 k) (h14 l)‖
        )
  )

/--
The terminal third-q radial-Leray envelope is nonnegative.
-/
theorem h3TerminalForcingThirdQRadialLerayEnvelopeAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    0 ≤
      h3TerminalForcingThirdQRadialLerayEnvelopeAt
        hH3 hClass ht j := by

  unfold h3TerminalForcingThirdQRadialLerayEnvelopeAt
  dsimp only

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

/--
The previous raw-mass estimate is exactly the square bound by the named
terminal radial-Leray envelope.
-/
theorem h3TerminalPhysicalTopDissipationForcingThirdQRawMassAt_le_sq_radialLerayEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalTopDissipationForcingThirdQRawMassAt
        hH3 hClass ht j
      ≤
    (
      h3TerminalForcingThirdQRadialLerayEnvelopeAt
        hH3 hClass ht j
    ) ^ 2 := by

  simpa only [h3TerminalForcingThirdQRadialLerayEnvelopeAt] using
    h3TerminalPhysicalTopDissipationForcingThirdQRawMassAt_le_sq_radialLeray
      hH3 hClass ht j

/--
Escape of the canonical third-q forcing raw mass forces escape of the named
terminal radial-Leray envelope on the same sequence.
-/
theorem h3TerminalForcingThirdQRadialLerayEnvelopeAt_tendstoAtTop_of_rawMass_tendstoAtTop
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
            h3TerminalPhysicalTopDissipationForcingThirdQRawMassAt
              hH3 hClass (hτ n) j
        )
        atTop
        atTop) :
    Tendsto
      (
        fun n : ℕ =>
          h3TerminalForcingThirdQRadialLerayEnvelopeAt
            hH3 hClass (hτ n) j
      )
      atTop
      atTop := by

  refine
    tendsto_atTop.2
      ?_

  intro M

  let M0 : ℝ :=
    max M 0

  have hM0Nonneg :
      0 ≤ M0 := by
    dsimp only [M0]
    exact le_max_right M 0

  have hMLe :
      M ≤ M0 := by
    dsimp only [M0]
    exact le_max_left M 0

  have hMassLarge :
      ∀ᶠ n : ℕ in atTop,
        M0 ^ 2
          <
        h3TerminalPhysicalTopDissipationForcingThirdQRawMassAt
          hH3 hClass (hτ n) j :=
    hMassTop.eventually
      (eventually_gt_atTop (M0 ^ 2))

  filter_upwards [hMassLarge] with n hn

  have hBound :=
    h3TerminalPhysicalTopDissipationForcingThirdQRawMassAt_le_sq_radialLerayEnvelope
      hH3 hClass (hτ n) j

  have hEnvelopeNonneg :=
    h3TerminalForcingThirdQRadialLerayEnvelopeAt_nonneg
      hH3 hClass (hτ n) j

  have hM0Lt :
      M0
        <
      h3TerminalForcingThirdQRadialLerayEnvelopeAt
        hH3 hClass (hτ n) j := by
    nlinarith

  exact
    le_of_lt
      (
        lt_of_le_of_lt
          hMLe
          hM0Lt
      )

/--
The sixth-diffusion derivative frontier can now be stated using only the
existing higher-radial velocity hierarchy and the explicit terminal radial
Leray envelope.
-/
theorem sixthDiffusion_hilbertDerivativeNorm_escape_extendedHigherFour_or_forcingThirdQRadialLerayEnvelope
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
          h3TerminalForcingThirdQRadialLerayEnvelopeAt
            hH3 hClass (hτ n) j
      )
      atTop
      atTop := by

  rcases
    sixthDiffusion_hilbertDerivativeNorm_escape_extendedHigherFour_or_forcingThirdQRawMass
      hH3 hClass j τ hτ hTauTendsto hSixth
  with
    hHigher
    |
    hForcingMassTop

  · exact
      Or.inl hHigher

  · exact
      Or.inr
        (
          h3TerminalForcingThirdQRadialLerayEnvelopeAt_tendstoAtTop_of_rawMass_tendstoAtTop
            hH3 hClass j τ hτ hForcingMassTop
        )

end

end Euclidean
end Bridge
end PrimeTensor
