import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.TopDissipation

/-!
# Resolve the remaining derivative obstruction into Hilbert-state frontiers

The top-dissipation derivative branch is already closed: its scalar amplitude
is differentiable at every strict time and its derivative is one explicit
finite Hilbert pairing.

Three resolved physical PDE channels remain:

* lower temporal:
    `X₁,j(t) = d/dt (q û_j)(t)`;
* fourth temporal:
    `X₂,j(t) = d/dt (q² û_j)(t)`;
* sixth diffusion:
    `X₃,j(t) = q³ û_j(t)`.

Each corresponding scalar channel amplitude is literally

    ‖X(t)‖².

For any Hilbert-valued path `X`, differentiability of `X` gives, by
`HasDerivAt.norm_sq`,

    d/dt ‖X(t)‖²
      =
    2 ⟪X(t), X'(t)⟫_ℝ.

Consequently the scalar derivative obstruction from the previous checkpoint
has an exact Hilbert interpretation:

on every strict terminal tail, either the relevant Hilbert state itself loses
one more strong time derivative at some strict time, or the real pairing

    2 ⟪X(t), X'(t)⟫_ℝ

is arbitrarily large in absolute value.

This file makes that statement simultaneously for the three remaining
channels.  No additional differentiability is assumed or asserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1200000

/-! ## Canonical Hilbert states behind the three quadratic channels -/

noncomputable def h3TerminalResolvedLowerTemporalHilbertState
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (t : ℝ) :
    H3FourierComplexL2 :=
  deriv
    (h3TerminalPhysicalLowerWeightedVelocityFourierL2Path
      hH3 hClass j)
    t

noncomputable def h3TerminalResolvedFourthTemporalHilbertState
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (t : ℝ) :
    H3FourierComplexL2 :=
  deriv
    (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
      hH3 hClass j)
    t

noncomputable def h3TerminalResolvedSixthDiffusionHilbertState
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (t : ℝ) :
    H3FourierComplexL2 :=
  h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
    hH3 hClass j t

@[simp]
theorem resolvedLowerTemporalChannelAmplitude_eq_norm_sq_hilbertState
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (t : ℝ) :
    h3TerminalResolvedPhysicalPDEChannelAmplitude
        hH3 hClass j
        H3TerminalResolvedPhysicalPDEChannel.lowerTemporal
        t
      =
    (
      ‖h3TerminalResolvedLowerTemporalHilbertState
          hH3 hClass j t‖ : ℝ
    ) ^ 2 := by
  rfl

@[simp]
theorem resolvedFourthTemporalChannelAmplitude_eq_norm_sq_hilbertState
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (t : ℝ) :
    h3TerminalResolvedPhysicalPDEChannelAmplitude
        hH3 hClass j
        H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
        t
      =
    (
      ‖h3TerminalResolvedFourthTemporalHilbertState
          hH3 hClass j t‖ : ℝ
    ) ^ 2 := by
  rfl

@[simp]
theorem resolvedSixthDiffusionChannelAmplitude_eq_norm_sq_hilbertState
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (t : ℝ) :
    h3TerminalResolvedPhysicalPDEChannelAmplitude
        hH3 hClass j
        H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion
        t
      =
    (
      ‖h3TerminalResolvedSixthDiffusionHilbertState
          hH3 hClass j t‖ : ℝ
    ) ^ 2 := by
  rfl

/-! ## Generic Hilbert norm-square derivative obstruction -/

def H3TerminalHilbertNormSqDerivativeObstruction
    {a T : ℝ}
    (X : ℝ → H3FourierComplexL2) :
    Prop :=
  ∀ c : ℝ,
    c ∈ Set.Ioo a T →
    (
      ∃ t : ℝ,
        t ∈ Set.Ioo c T
          ∧
        ¬ DifferentiableAt ℝ X t
    )
      ∨
    (
      ∀ M : ℝ,
        ∃ r : ℝ,
          r ∈ Set.Ioo c T
            ∧
          M
            <
          abs
            (
              2 *
                inner ℝ
                  (X r)
                  (deriv X r)
            )
    )

private theorem hilbertNormSqDerivativeObstruction_of_scalarDerivativeObstruction
    {a T : ℝ}
    (X : ℝ → H3FourierComplexL2)
    (hScalar :
      ∀ c : ℝ,
        c ∈ Set.Ioo a T →
        (
          ∃ t : ℝ,
            t ∈ Set.Ioo c T
              ∧
            ¬ DifferentiableAt ℝ
                (fun s : ℝ => (‖X s‖ : ℝ) ^ 2)
                t
        )
          ∨
        (
          ∀ M : ℝ,
            ∃ r : ℝ,
              r ∈ Set.Ioo c T
                ∧
              M
                <
              abs
                (
                  deriv
                    (fun s : ℝ => (‖X s‖ : ℝ) ^ 2)
                    r
                )
        )) :
    H3TerminalHilbertNormSqDerivativeObstruction
      (a := a) (T := T) X := by

  intro c hc

  classical

  by_cases hStateFail :
      ∃ t : ℝ,
        t ∈ Set.Ioo c T
          ∧
        ¬ DifferentiableAt ℝ X t

  · exact
      Or.inl hStateFail

  · right

    have hStateDiff :
        ∀ t : ℝ,
          t ∈ Set.Ioo c T →
          DifferentiableAt ℝ X t := by

      intro t ht

      by_contra hNotDiff

      exact
        hStateFail
          ⟨
            t,
            ht,
            hNotDiff
          ⟩

    rcases
      hScalar c hc
    with hScalarFail | hScalarLarge

    · obtain
        ⟨t, ht, hNotDiffSq⟩ :=
        hScalarFail

      have hX :
          HasDerivAt
            X
            (deriv X t)
            t :=
        (hStateDiff t ht).hasDerivAt

      have hNormSq :=
        hX.norm_sq

      exact
        False.elim
          (
            hNotDiffSq
              hNormSq.differentiableAt
          )

    · intro M

      obtain
        ⟨r, hr, hLarge⟩ :=
        hScalarLarge M

      have hX :
          HasDerivAt
            X
            (deriv X r)
            r :=
        (hStateDiff r hr).hasDerivAt

      have hNormSq :=
        hX.norm_sq

      have hDerivative :
          deriv
              (fun s : ℝ => (‖X s‖ : ℝ) ^ 2)
              r
            =
          2 *
            inner ℝ
              (X r)
              (deriv X r) :=
        hNormSq.deriv

      rw [hDerivative] at hLarge

      exact
        ⟨
          r,
          hr,
          hLarge
        ⟩

/-! ## Resolve each remaining channel -/

theorem lowerTemporal_hilbertNormSqDerivativeObstruction_of_channelDerivativeObstruction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (hObstruction :
      H3TerminalResolvedPhysicalPDEChannelDerivativeObstruction
        hH3 hClass j
        H3TerminalResolvedPhysicalPDEChannel.lowerTemporal) :
    H3TerminalHilbertNormSqDerivativeObstruction
      (a := a) (T := T)
      (h3TerminalResolvedLowerTemporalHilbertState
        hH3 hClass j) := by

  let X : ℝ → H3FourierComplexL2 :=
    h3TerminalResolvedLowerTemporalHilbertState
      hH3 hClass j

  have hEq :
      h3TerminalResolvedPhysicalPDEChannelAmplitude
          hH3 hClass j
          H3TerminalResolvedPhysicalPDEChannel.lowerTemporal
        =
      fun t : ℝ => (‖X t‖ : ℝ) ^ 2 := by

    funext t
    rfl

  change
    ∀ c : ℝ,
      c ∈ Set.Ioo a T →
      (
        ∃ t : ℝ,
          t ∈ Set.Ioo c T
            ∧
          ¬ DifferentiableAt ℝ
              (fun s : ℝ => (‖X s‖ : ℝ) ^ 2)
              t
      )
        ∨
      (
        ∀ M : ℝ,
          ∃ r : ℝ,
            r ∈ Set.Ioo c T
              ∧
            M
              <
            abs
              (
                deriv
                  (fun s : ℝ => (‖X s‖ : ℝ) ^ 2)
                  r
              )
      )
    at hObstruction

  exact
    hilbertNormSqDerivativeObstruction_of_scalarDerivativeObstruction
      X
      hObstruction

theorem fourthTemporal_hilbertNormSqDerivativeObstruction_of_channelDerivativeObstruction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (hObstruction :
      H3TerminalResolvedPhysicalPDEChannelDerivativeObstruction
        hH3 hClass j
        H3TerminalResolvedPhysicalPDEChannel.fourthTemporal) :
    H3TerminalHilbertNormSqDerivativeObstruction
      (a := a) (T := T)
      (h3TerminalResolvedFourthTemporalHilbertState
        hH3 hClass j) := by

  let X : ℝ → H3FourierComplexL2 :=
    h3TerminalResolvedFourthTemporalHilbertState
      hH3 hClass j

  have hEq :
      h3TerminalResolvedPhysicalPDEChannelAmplitude
          hH3 hClass j
          H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
        =
      fun t : ℝ => (‖X t‖ : ℝ) ^ 2 := by

    funext t
    rfl

  change
    ∀ c : ℝ,
      c ∈ Set.Ioo a T →
      (
        ∃ t : ℝ,
          t ∈ Set.Ioo c T
            ∧
          ¬ DifferentiableAt ℝ
              (fun s : ℝ => (‖X s‖ : ℝ) ^ 2)
              t
      )
        ∨
      (
        ∀ M : ℝ,
          ∃ r : ℝ,
            r ∈ Set.Ioo c T
              ∧
            M
              <
            abs
              (
                deriv
                  (fun s : ℝ => (‖X s‖ : ℝ) ^ 2)
                  r
              )
      )
    at hObstruction

  exact
    hilbertNormSqDerivativeObstruction_of_scalarDerivativeObstruction
      X
      hObstruction

theorem sixthDiffusion_hilbertNormSqDerivativeObstruction_of_channelDerivativeObstruction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (hObstruction :
      H3TerminalResolvedPhysicalPDEChannelDerivativeObstruction
        hH3 hClass j
        H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion) :
    H3TerminalHilbertNormSqDerivativeObstruction
      (a := a) (T := T)
      (h3TerminalResolvedSixthDiffusionHilbertState
        hH3 hClass j) := by

  let X : ℝ → H3FourierComplexL2 :=
    h3TerminalResolvedSixthDiffusionHilbertState
      hH3 hClass j

  have hEq :
      h3TerminalResolvedPhysicalPDEChannelAmplitude
          hH3 hClass j
          H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion
        =
      fun t : ℝ => (‖X t‖ : ℝ) ^ 2 := by

    funext t
    rfl

  change
    ∀ c : ℝ,
      c ∈ Set.Ioo a T →
      (
        ∃ t : ℝ,
          t ∈ Set.Ioo c T
            ∧
          ¬ DifferentiableAt ℝ
              (fun s : ℝ => (‖X s‖ : ℝ) ^ 2)
              t
      )
        ∨
      (
        ∀ M : ℝ,
          ∃ r : ℝ,
            r ∈ Set.Ioo c T
              ∧
            M
              <
            abs
              (
                deriv
                  (fun s : ℝ => (‖X s‖ : ℝ) ^ 2)
                  r
              )
      )
    at hObstruction

  exact
    hilbertNormSqDerivativeObstruction_of_scalarDerivativeObstruction
      X
      hObstruction

/-! ## Fully Hilbert-resolved nonextension alternative -/

theorem exists_fixed_resolvedPhysicalPDEChannel_hilbertDerivativeObstruction_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
      (
        H3TerminalHilbertNormSqDerivativeObstruction
          (a := a) (T := T)
          (h3TerminalResolvedLowerTemporalHilbertState
            hH3 hClass j₀)
      )
        ∨
      (
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
                  ∑ k : Fin 3,
                    2 *
                      inner ℝ
                        (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                          hH3 hClass k r)
                        (
                          deriv
                            (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                              hH3 hClass k)
                            r
                        )
                )
      )
        ∨
      (
        H3TerminalHilbertNormSqDerivativeObstruction
          (a := a) (T := T)
          (h3TerminalResolvedFourthTemporalHilbertState
            hH3 hClass j₀)
      )
        ∨
      (
        H3TerminalHilbertNormSqDerivativeObstruction
          (a := a) (T := T)
          (h3TerminalResolvedSixthDiffusionHilbertState
            hH3 hClass j₀)
      ) := by

  obtain
    ⟨j₀, hBranch⟩ :=
    exists_fixed_resolvedPhysicalPDEChannel_derivativeObstruction_topDissipationClosed_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3 hClass hPhysical hCauchy hNoExtension

  refine
    ⟨
      j₀,
      ?_
    ⟩

  rcases hBranch with hLower | hTop | hFourth | hSixth

  · exact
      Or.inl
        (
          lowerTemporal_hilbertNormSqDerivativeObstruction_of_channelDerivativeObstruction
            hH3 hClass j₀ hLower
        )

  · exact
      Or.inr
        (
          Or.inl hTop
        )

  · exact
      Or.inr
        (
          Or.inr
            (
              Or.inl
                (
                  fourthTemporal_hilbertNormSqDerivativeObstruction_of_channelDerivativeObstruction
                    hH3 hClass j₀ hFourth
                )
            )
        )

  · exact
      Or.inr
        (
          Or.inr
            (
              Or.inr
                (
                  sixthDiffusion_hilbertNormSqDerivativeObstruction_of_channelDerivativeObstruction
                    hH3 hClass j₀ hSixth
                )
            )
        )

theorem smoothContinuationExtension_or_fixed_resolvedPhysicalPDEChannel_hilbertDerivativeObstruction
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
        (
          H3TerminalHilbertNormSqDerivativeObstruction
            (a := a) (T := T)
            (h3TerminalResolvedLowerTemporalHilbertState
              hH3 hClass j₀)
        )
          ∨
        (
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
                    ∑ k : Fin 3,
                      2 *
                        inner ℝ
                          (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                            hH3 hClass k r)
                          (
                            deriv
                              (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                                hH3 hClass k)
                              r
                          )
                  )
        )
          ∨
        (
          H3TerminalHilbertNormSqDerivativeObstruction
            (a := a) (T := T)
            (h3TerminalResolvedFourthTemporalHilbertState
              hH3 hClass j₀)
        )
          ∨
        (
          H3TerminalHilbertNormSqDerivativeObstruction
            (a := a) (T := T)
            (h3TerminalResolvedSixthDiffusionHilbertState
              hH3 hClass j₀)
        )
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
          exists_fixed_resolvedPhysicalPDEChannel_hilbertDerivativeObstruction_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
            hH3 hClass hPhysical hCauchy hExtension
        )

end

end Euclidean
end Bridge
end PrimeTensor
