import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Relative.Tail.Cascade

/-!
# Resolve the quadratic Hilbert factor into amplitude or derivative growth

The preceding checkpoint produced one fixed resolved physical PDE channel and a
strict terminal sequence on which

    stateSquare + derivativeSquare -> +∞.

For this channel the state-square term is exactly the already-defined canonical
resolved-channel amplitude.  This file isolates the remaining factor without
losing that intrinsic channel identity.

Apply the existing bounded-or-cofinal tail extraction to the amplitude along the
selected sequence.

* If the amplitude is cofinally unbounded, a cofinal index map makes the same
  fixed channel amplitude tend to `+∞`.
* If the amplitude is eventually bounded above, the divergent quadratic sum
  forces the Hilbert-state derivative-square envelope itself to tend to `+∞`
  along the full original sequence.

No claim is made that both factors diverge.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1500000

/--
Square magnitude of the time derivative of the Hilbert state behind one
resolved physical PDE channel.

For top dissipation this is the sum over the three fourth-radial components.
-/
noncomputable def h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeSquareEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (channel : H3TerminalResolvedPhysicalPDEChannel)
    (t : ℝ) :
    ℝ :=
  match channel with
  | .lowerTemporal =>
      ‖deriv
        (h3TerminalResolvedLowerTemporalHilbertState
          hH3 hClass j)
        t‖ ^ 2
  | .topDissipation =>
      ∑ k : Fin 3,
        ‖deriv
          (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
            hH3 hClass k)
          t‖ ^ 2
  | .fourthTemporal =>
      ‖deriv
        (h3TerminalResolvedFourthTemporalHilbertState
          hH3 hClass j)
        t‖ ^ 2
  | .sixthDiffusion =>
      ‖deriv
        (h3TerminalResolvedSixthDiffusionHilbertState
          hH3 hClass j)
        t‖ ^ 2

/--
The quadratic Hilbert factor envelope splits exactly into the canonical scalar
channel amplitude plus the Hilbert-state derivative-square envelope.
-/
theorem h3TerminalResolvedPhysicalPDEChannelHilbertFactorSquareEnvelope_eq_amplitude_add_derivativeSquare
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (channel : H3TerminalResolvedPhysicalPDEChannel) :
    h3TerminalResolvedPhysicalPDEChannelHilbertFactorSquareEnvelope
        hH3 hClass j channel t
      =
    h3TerminalResolvedPhysicalPDEChannelAmplitude
        hH3 hClass j channel t
      +
    h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeSquareEnvelope
      hH3 hClass j channel t := by

  cases channel with

  | lowerTemporal =>
      simp [
        h3TerminalResolvedPhysicalPDEChannelHilbertFactorSquareEnvelope,
        h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeSquareEnvelope
      ]

  | topDissipation =>

      change
        (∑ k : Fin 3,
          (
            ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
              hH3 hClass k t‖ ^ 2
              +
            ‖deriv
              (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                hH3 hClass k)
              t‖ ^ 2
          ))
          =
        h3TerminalPhysicalTopDissipation3Path hClass t
          +
        ∑ k : Fin 3,
          ‖deriv
            (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
              hH3 hClass k)
            t‖ ^ 2

      have hTop :=
        congrFun
          (
            h3TerminalPhysicalTopDissipation3Path_eq_sum_norm_sq_fourthRadialPath
              hH3 hClass
          )
          t

      rw [hTop]

      exact
        Finset.sum_add_distrib

  | fourthTemporal =>
      simp [
        h3TerminalResolvedPhysicalPDEChannelHilbertFactorSquareEnvelope,
        h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeSquareEnvelope
      ]

  | sixthDiffusion =>
      simp [
        h3TerminalResolvedPhysicalPDEChannelHilbertFactorSquareEnvelope,
        h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeSquareEnvelope
      ]

/--
Under hypothetical nonextension, the fixed-channel quadratic escape resolves
into one of two exhaustive factor mechanisms.

Either a cofinal extraction makes the canonical channel amplitude diverge, or
the Hilbert-state derivative-square envelope diverges along the entire original
terminal sequence.
-/
theorem exists_fixed_resolvedPhysicalPDEChannel_amplitude_or_hilbertDerivativeSquare_escapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
        ∃ τ : ℕ → ℝ,
          (
            ∀ n : ℕ,
              τ n ∈ Set.Ioo a T
                ∧
              τ n ∈
                Set.Ioo
                  (T - (1 : ℝ) / ((n : ℝ) + 1))
                  T
          )
            ∧
          Tendsto τ atTop (𝓝 T)
            ∧
          (
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
                      h3TerminalResolvedPhysicalPDEChannelAmplitude
                        hH3 hClass j₀ channel (τ (k n))
                  )
                  atTop
                  atTop
            )
              ∨
            Tendsto
              (
                fun n : ℕ =>
                  h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeSquareEnvelope
                    hH3 hClass j₀ channel (τ n)
              )
              atTop
              atTop
          ) := by

  obtain
    ⟨
      j₀,
      channel,
      τ,
      hτ,
      hTauTendsto,
      hSquareTendsto
    ⟩ :=
    exists_fixed_resolvedPhysicalPDEChannel_hilbertFactorSquareEnvelopeEscapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3 hClass hPhysical hCauchy hNoExtension

  let A : ℕ → ℝ :=
    fun n =>
      h3TerminalResolvedPhysicalPDEChannelAmplitude
        hH3 hClass j₀ channel (τ n)

  let D : ℕ → ℝ :=
    fun n =>
      h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeSquareEnvelope
        hH3 hClass j₀ channel (τ n)

  have hIdentity :
      ∀ᶠ n : ℕ in atTop,
        (1 + A n : ℝ) = 1 + A n :=
    Eventually.of_forall
      (fun _ => rfl)

  have hTail :=
    relativeTailAlternative_of_eventually_ratio_identity
      A
      (fun n => 1 + A n)
      hIdentity

  unfold H3TerminalRelativeTailAlternative at hTail

  refine
    ⟨
      j₀,
      channel,
      τ,
      (fun n => ⟨(hτ n).1, (hτ n).2.1⟩),
      hTauTendsto,
      ?_
    ⟩

  rcases hTail with
    ⟨C, hBound⟩
    |
    ⟨k, hk, hkTop, hATop, hRatioTop⟩

  · right

    have hABound :
        ∀ᶠ n : ℕ in atTop,
          A n ≤ C :=
      hBound.mono
        (fun n hn => hn.1)

    refine
      tendsto_atTop.2
        ?_

    intro M

    have hSquareLarge :
        ∀ᶠ n : ℕ in atTop,
          M + C + 1
            ≤
          h3TerminalResolvedPhysicalPDEChannelHilbertFactorSquareEnvelope
            hH3 hClass j₀ channel (τ n) :=
      (tendsto_atTop.1 hSquareTendsto)
        (M + C + 1)

    filter_upwards
      [hABound, hSquareLarge]
      with n hAn hLarge

    have hSplit :=
      h3TerminalResolvedPhysicalPDEChannelHilbertFactorSquareEnvelope_eq_amplitude_add_derivativeSquare
        (t := τ n)
        hH3 hClass j₀ channel

    have hDLower :
        M
          ≤
        D n := by

      dsimp only [A, D] at hAn ⊢

      rw [hSplit] at hLarge

      linarith

    exact hDLower

  · left

    refine
      ⟨
        k,
        (fun n => (hk n).1),
        hkTop,
        hTauTendsto.comp hkTop,
        ?_
      ⟩

    simpa only [A] using hATop

/--
Neutral continuation form of the fixed-channel factor alternative.
-/
theorem smoothContinuationExtension_or_fixed_resolvedPhysicalPDEChannel_amplitude_or_hilbertDerivativeSquare_escapeSequence
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
          ∃ τ : ℕ → ℝ,
            (
              ∀ n : ℕ,
                τ n ∈ Set.Ioo a T
                  ∧
                τ n ∈
                  Set.Ioo
                    (T - (1 : ℝ) / ((n : ℝ) + 1))
                    T
            )
              ∧
            Tendsto τ atTop (𝓝 T)
              ∧
            (
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
                        h3TerminalResolvedPhysicalPDEChannelAmplitude
                          hH3 hClass j₀ channel (τ (k n))
                    )
                    atTop
                    atTop
              )
                ∨
              Tendsto
                (
                  fun n : ℕ =>
                    h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeSquareEnvelope
                      hH3 hClass j₀ channel (τ n)
                )
                atTop
                atTop
            )
    ) := by

  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact Or.inl hExtension

  · exact
      Or.inr
        (
          exists_fixed_resolvedPhysicalPDEChannel_amplitude_or_hilbertDerivativeSquare_escapeSequence_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
            hH3 hClass hPhysical hCauchy hExtension
        )

end

end Euclidean
end Bridge
end PrimeTensor
