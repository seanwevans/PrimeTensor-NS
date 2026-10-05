import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Collapse.Pairing.Derivative

/-!
# Freeze an orientation of the resolved-channel amplitude derivative

The preceding checkpoint reduced hypothetical nonextension to one fixed
coordinate and one fixed resolved physical PDE channel whose scalar amplitude
derivative is cofinally unbounded in absolute value.

Absolute-value escape still allows the sign to vary from witness to witness.
This file removes that last two-sided ambiguity.  The argument is the
continuous-time analogue of
`exists_orientation_of_scalarSeq_absTailCofinallyUnbounded`:

* if the positive orientation is already cofinally unbounded, keep it;
* otherwise it is bounded above on one strict terminal tail;
* absolute-value escape farther inside that tail must then occur through the
  negative orientation.

Thus one fixed sign of the derivative is cofinally unbounded on every strict
terminal tail.  No monotonicity is assumed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1200000

/--
One orientation of the ordinary derivative of a fixed resolved-channel
amplitude is cofinally unbounded on every strict terminal tail.
-/
def H3TerminalResolvedPhysicalPDEChannelAmplitudeDerivativeOrientedCofinallyUnbounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (channel : H3TerminalResolvedPhysicalPDEChannel)
    (s : H3TerminalOrientation) :
    Prop :=
  ∀ c : ℝ,
    c ∈ Set.Ioo a T →
    ∀ M : ℝ,
      ∃ r : ℝ,
        r ∈ Set.Ioo c T
          ∧
        M
          <
        h3TerminalOrientedValue
          s
          (
            deriv
              (
                h3TerminalResolvedPhysicalPDEChannelAmplitude
                  hH3 hClass j channel
              )
              r
          )

/--
Cofinal unboundedness of the derivative magnitude freezes to one fixed
orientation on every strict terminal tail.
-/
theorem exists_orientation_of_amplitudeDerivativeCofinallyUnbounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (channel : H3TerminalResolvedPhysicalPDEChannel)
    (hAbs :
      H3TerminalResolvedPhysicalPDEChannelAmplitudeDerivativeCofinallyUnbounded
        hH3 hClass j channel) :
    ∃ s : H3TerminalOrientation,
      H3TerminalResolvedPhysicalPDEChannelAmplitudeDerivativeOrientedCofinallyUnbounded
        hH3 hClass j channel s := by

  classical

  by_cases hPos :
      H3TerminalResolvedPhysicalPDEChannelAmplitudeDerivativeOrientedCofinallyUnbounded
        hH3 hClass j channel
        H3TerminalOrientation.positive

  · exact
      ⟨
        H3TerminalOrientation.positive,
        hPos
      ⟩

  have hPosBound := hPos

  unfold
    H3TerminalResolvedPhysicalPDEChannelAmplitudeDerivativeOrientedCofinallyUnbounded
    at hPosBound

  push Not at hPosBound

  obtain
    ⟨
      c₀,
      hc₀,
      M₀,
      hFailPos
    ⟩ :=
    hPosBound

  refine
    ⟨
      H3TerminalOrientation.negative,
      ?_
    ⟩

  unfold
    H3TerminalResolvedPhysicalPDEChannelAmplitudeDerivativeOrientedCofinallyUnbounded

  intro c hc M

  let d : ℝ :=
    max c c₀

  have hd :
      d ∈ Set.Ioo a T := by
    constructor

    · dsimp only [d]
      exact
        lt_of_lt_of_le
          hc.1
          (le_max_left c c₀)

    · dsimp only [d]
      exact
        max_lt
          hc.2
          hc₀.2

  let K : ℝ :=
    max
      (max M M₀)
      0

  obtain
    ⟨
      r,
      hr,
      hAbsLarge
    ⟩ :=
    hAbs d hd K

  have hcLe :
      c ≤ d := by
    dsimp only [d]
    exact le_max_left _ _

  have hc₀Le :
      c₀ ≤ d := by
    dsimp only [d]
    exact le_max_right _ _

  have hrC :
      r ∈ Set.Ioo c T :=
    ⟨
      lt_of_le_of_lt
        hcLe
        hr.1,
      hr.2
    ⟩

  have hrC₀ :
      r ∈ Set.Ioo c₀ T :=
    ⟨
      lt_of_le_of_lt
        hc₀Le
        hr.1,
      hr.2
    ⟩

  let D : ℝ :=
    deriv
      (
        h3TerminalResolvedPhysicalPDEChannelAmplitude
          hH3 hClass j channel
      )
      r

  have hDle :
      D ≤ M₀ := by

    have hAt :=
      hFailPos r hrC₀

    dsimp only [D]

    simpa only [
      h3TerminalOrientedValue_positive
    ] using hAt

  have hMleK :
      M ≤ K := by
    dsimp only [K]
    exact
      le_trans
        (le_max_left M M₀)
        (le_max_left _ _)

  have hM₀leK :
      M₀ ≤ K := by
    dsimp only [K]
    exact
      le_trans
        (le_max_right M M₀)
        (le_max_left _ _)

  have hDneg :
      D < 0 := by

    by_contra hNotNeg

    have hDnonneg :
        0 ≤ D :=
      le_of_not_gt hNotNeg

    have hAbsEq :
        abs D = D :=
      abs_of_nonneg hDnonneg

    have hAbsLe :
        abs D ≤ K := by
      rw [hAbsEq]
      exact
        le_trans
          hDle
          hM₀leK

    have hLargeD :
        K < abs D := by
      dsimp only [D]
      exact hAbsLarge

    exact
      (not_lt_of_ge hAbsLe)
        hLargeD

  have hNegLarge :
      K < -D := by

    have hLargeD :
        K < abs D := by
      dsimp only [D]
      exact hAbsLarge

    rw [abs_of_neg hDneg] at hLargeD

    exact hLargeD

  refine
    ⟨
      r,
      hrC,
      ?_
    ⟩

  have hFinal :
      M < -D :=
    lt_of_le_of_lt
      hMleK
      hNegLarge

  dsimp only [D] at hFinal ⊢

  simpa only [
    h3TerminalOrientedValue_negative
  ] using hFinal

/--
Under hypothetical nonextension, one fixed coordinate, one fixed resolved
physical PDE channel, and one fixed derivative orientation are cofinally
unbounded on every strict terminal tail.
-/
theorem exists_fixed_oriented_resolvedPhysicalPDEChannel_amplitudeDerivativeCofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
        ∃ s : H3TerminalOrientation,
          H3TerminalResolvedPhysicalPDEChannelAmplitudeDerivativeOrientedCofinallyUnbounded
            hH3 hClass j₀ channel s := by

  obtain
    ⟨
      j₀,
      channel,
      hAbs
    ⟩ :=
    exists_fixed_resolvedPhysicalPDEChannel_amplitudeDerivativeCofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3 hClass hPhysical hCauchy hNoExtension

  obtain
    ⟨
      s,
      hOriented
    ⟩ :=
    exists_orientation_of_amplitudeDerivativeCofinallyUnbounded
      hH3 hClass j₀ channel hAbs

  exact
    ⟨
      j₀,
      channel,
      s,
      hOriented
    ⟩

/--
Neutral continuation form with the surviving scalar derivative escape frozen
to one fixed orientation.
-/
theorem smoothContinuationExtension_or_fixed_oriented_resolvedPhysicalPDEChannel_amplitudeDerivativeCofinallyUnbounded
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
          ∃ s : H3TerminalOrientation,
            H3TerminalResolvedPhysicalPDEChannelAmplitudeDerivativeOrientedCofinallyUnbounded
              hH3 hClass j₀ channel s
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
          exists_fixed_oriented_resolvedPhysicalPDEChannel_amplitudeDerivativeCofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
            hH3 hClass hPhysical hCauchy hExtension
        )

end

end Euclidean
end Bridge
end PrimeTensor
