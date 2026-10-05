import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Collapse.Pairing

/-!
# Identify resolved-channel Hilbert pairing with amplitude derivative

The four surviving terminal channels are now represented twice on the same
finite enum:

* `h3TerminalResolvedPhysicalPDEChannelAmplitude` is the canonical scalar
  channel amplitude;
* `h3TerminalResolvedPhysicalPDEChannelHilbertPairing` is its canonical
  Hilbert derivative pairing.

The weighted forcing derivative closures make the lower- and fourth-temporal
Hilbert states differentiable at every strict preterminal time.  The
sixth-diffusion state was already closed, and top dissipation already has its
finite-sum derivative formula.

Therefore, for every resolved channel and every strict preterminal time,

    d/dt amplitude(channel,t) = pairing(channel,t).

This converts the pairing escape obtained under hypothetical nonextension into
cofinal unboundedness of the ordinary derivative of one fixed scalar channel.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

/-! ## Close differentiability of the two formerly forcing-limited states -/

/--
The lower-temporal Hilbert state is differentiable at every strict preterminal
time now that the terminal `q F_j` path is differentiable there.
-/
theorem h3TerminalResolvedLowerTemporalHilbertState_differentiableAt_closed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    DifferentiableAt ℝ
      (h3TerminalResolvedLowerTemporalHilbertState
        hH3 hClass j)
      t := by

  exact
    h3TerminalResolvedLowerTemporalHilbertState_differentiableAt_of_forcingSecondQ_differentiableAt
      hH3 hClass ht j
      (
        h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path_differentiableAt
          hH3 hClass ht j
      )

/--
The fourth-temporal Hilbert state is differentiable at every strict preterminal
time now that the terminal `q² F_j` path is differentiable there.
-/
theorem h3TerminalResolvedFourthTemporalHilbertState_differentiableAt_closed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    DifferentiableAt ℝ
      (h3TerminalResolvedFourthTemporalHilbertState
        hH3 hClass j)
      t := by

  exact
    h3TerminalResolvedFourthTemporalHilbertState_differentiableAt_of_forcingFourthQ_differentiableAt
      hH3 hClass ht j
      (
        h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path_differentiableAt
          hH3 hClass ht j
      )

/-! ## Channel amplitude derivative = canonical Hilbert pairing -/

/--
At every strict preterminal time, the ordinary derivative of the canonical
resolved-channel amplitude is exactly its canonical Hilbert pairing.
-/
theorem deriv_h3TerminalResolvedPhysicalPDEChannelAmplitude_eq_hilbertPairing
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (channel : H3TerminalResolvedPhysicalPDEChannel)
    (ht : t ∈ Set.Ioo a T) :
    deriv
        (
          h3TerminalResolvedPhysicalPDEChannelAmplitude
            hH3 hClass j channel
        )
        t
      =
    h3TerminalResolvedPhysicalPDEChannelHilbertPairing
      hH3 hClass j channel t := by

  cases channel with

  | lowerTemporal =>

      let X : ℝ → H3FourierComplexL2 :=
        h3TerminalResolvedLowerTemporalHilbertState
          hH3 hClass j

      have hXDiff :
          DifferentiableAt ℝ X t := by
        dsimp only [X]
        exact
          h3TerminalResolvedLowerTemporalHilbertState_differentiableAt_closed
            hH3 hClass ht j

      have hX :
          HasDerivAt
            X
            (deriv X t)
            t :=
        hXDiff.hasDerivAt

      have hNormSq :=
        hX.norm_sq

      change
        deriv
            (fun s : ℝ => (‖X s‖ : ℝ) ^ 2)
            t
          =
        2 *
          inner ℝ
            (X t)
            (deriv X t)

      exact
        hNormSq.deriv

  | topDissipation =>

      change
        deriv
            (h3TerminalPhysicalTopDissipation3Path hClass)
            t
          =
        ∑ k : Fin 3,
          2 *
            inner ℝ
              (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                hH3 hClass k t)
              (
                deriv
                  (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                    hH3 hClass k)
                  t
              )

      exact
        deriv_h3TerminalPhysicalTopDissipation3Path_eq_sum_inner
          hH3 hClass ht

  | fourthTemporal =>

      let X : ℝ → H3FourierComplexL2 :=
        h3TerminalResolvedFourthTemporalHilbertState
          hH3 hClass j

      have hXDiff :
          DifferentiableAt ℝ X t := by
        dsimp only [X]
        exact
          h3TerminalResolvedFourthTemporalHilbertState_differentiableAt_closed
            hH3 hClass ht j

      have hX :
          HasDerivAt
            X
            (deriv X t)
            t :=
        hXDiff.hasDerivAt

      have hNormSq :=
        hX.norm_sq

      change
        deriv
            (fun s : ℝ => (‖X s‖ : ℝ) ^ 2)
            t
          =
        2 *
          inner ℝ
            (X t)
            (deriv X t)

      exact
        hNormSq.deriv

  | sixthDiffusion =>

      let X : ℝ → H3FourierComplexL2 :=
        h3TerminalResolvedSixthDiffusionHilbertState
          hH3 hClass j

      have hXDiff :
          DifferentiableAt ℝ X t := by
        dsimp only [X]
        exact
          h3TerminalResolvedSixthDiffusionHilbertState_differentiableAt
            hH3 hClass ht j

      have hX :
          HasDerivAt
            X
            (deriv X t)
            t :=
        hXDiff.hasDerivAt

      have hNormSq :=
        hX.norm_sq

      change
        deriv
            (fun s : ℝ => (‖X s‖ : ℝ) ^ 2)
            t
          =
        2 *
          inner ℝ
            (X t)
            (deriv X t)

      exact
        hNormSq.deriv

/-! ## Canonical scalar derivative escape -/

/--
One fixed resolved physical PDE channel has cofinally unbounded scalar
amplitude derivative magnitude.
-/
def H3TerminalResolvedPhysicalPDEChannelAmplitudeDerivativeCofinallyUnbounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (channel : H3TerminalResolvedPhysicalPDEChannel) :
    Prop :=
  ∀ c : ℝ,
    c ∈ Set.Ioo a T →
    ∀ M : ℝ,
      ∃ r : ℝ,
        r ∈ Set.Ioo c T
          ∧
        M
          <
        abs
          (
            deriv
              (
                h3TerminalResolvedPhysicalPDEChannelAmplitude
                  hH3 hClass j channel
              )
              r
          )

/--
Cofinal escape of the canonical Hilbert pairing is exactly enough to force
cofinal escape of the ordinary derivative of the same scalar channel.
-/
theorem amplitudeDerivativeCofinallyUnbounded_of_hilbertPairingCofinallyUnbounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (channel : H3TerminalResolvedPhysicalPDEChannel)
    (hPairing :
      H3TerminalResolvedPhysicalPDEChannelHilbertPairingCofinallyUnbounded
        hH3 hClass j channel) :
    H3TerminalResolvedPhysicalPDEChannelAmplitudeDerivativeCofinallyUnbounded
      hH3 hClass j channel := by

  intro c hc M

  obtain
    ⟨r, hr, hLarge⟩ :=
    hPairing c hc M

  have hrClass :
      r ∈ Set.Ioo a T :=
    ⟨
      lt_trans hc.1 hr.1,
      hr.2
    ⟩

  have hDerivative :=
    deriv_h3TerminalResolvedPhysicalPDEChannelAmplitude_eq_hilbertPairing
      hH3 hClass j channel hrClass

  rw [← hDerivative] at hLarge

  exact
    ⟨
      r,
      hr,
      hLarge
    ⟩

/--
Under hypothetical nonextension, one fixed coordinate and one fixed resolved
physical PDE channel have cofinally unbounded scalar amplitude derivative.
-/
theorem exists_fixed_resolvedPhysicalPDEChannel_amplitudeDerivativeCofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T) :
    ∃ j₀ : Fin 3,
      ∃ channel : H3TerminalResolvedPhysicalPDEChannel,
        H3TerminalResolvedPhysicalPDEChannelAmplitudeDerivativeCofinallyUnbounded
          hH3 hClass j₀ channel := by

  obtain
    ⟨j₀, channel, hPairing⟩ :=
    exists_fixed_resolvedPhysicalPDEChannel_hilbertPairingCofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3 hClass hPhysical hCauchy hNoExtension

  exact
    ⟨
      j₀,
      channel,
      amplitudeDerivativeCofinallyUnbounded_of_hilbertPairingCofinallyUnbounded
        hH3 hClass j₀ channel hPairing
    ⟩

/--
Neutral continuation form after identifying the canonical Hilbert pairing with
the derivative of the canonical scalar channel amplitude.
-/
theorem smoothContinuationExtension_or_fixed_resolvedPhysicalPDEChannel_amplitudeDerivativeCofinallyUnbounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      ∃ j₀ : Fin 3,
        ∃ channel : H3TerminalResolvedPhysicalPDEChannel,
          H3TerminalResolvedPhysicalPDEChannelAmplitudeDerivativeCofinallyUnbounded
            hH3 hClass j₀ channel
    ) := by

  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl hExtension

  · exact
      Or.inr
        (
          exists_fixed_resolvedPhysicalPDEChannel_amplitudeDerivativeCofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
            hH3 hClass hPhysical hCauchy hExtension
        )

end

end Euclidean
end Bridge
end PrimeTensor
