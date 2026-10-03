import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Sequence

/-!
# Terminal steepness of the global resolved physical PDE envelope

The global envelope has already been reduced to one scalar obstruction and,
under hypothetical nonextension, an explicit sequence tending to the terminal
time along which that scalar tends to `+∞`.

The next issue is spike width.

A finite Lipschitz constant on even one strict terminal tail would prevent the
envelope from forming arbitrarily high narrowing spikes there: fixing one
interior reference time immediately gives a finite uniform bound on the whole
tail.  The existing scalar continuation criterion would then force smooth
continuation.

Therefore hypothetical nonextension has a stronger necessary consequence than
mere envelope unboundedness:

* no strict terminal tail admits a finite global Lipschitz constant for the
  resolved physical PDE envelope;
* equivalently, on every strict terminal tail and for every finite slope
  `K >= 0`, there are two physical times whose envelope increment is steeper
  than `K`.

This does not yet prove a contradiction.  It isolates the quantitative
temporal concentration that any surviving nonextension branch must exhibit.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 900000

/--
There is a strict terminal tail on which the global resolved physical PDE
envelope has one finite real Lipschitz constant.

The predicate is written directly with absolute values so that the next PDE
layer can establish it from whatever temporal increment estimate is most
natural, without committing to an auxiliary metric-space wrapper.
-/
def H3TerminalResolvedPhysicalPDEEnvelopeLipschitzOnTerminalTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Prop :=
  ∃ c : ℝ,
    c ∈ Set.Ioo a T
      ∧
    ∃ K : ℝ,
      0 ≤ K
        ∧
      ∀ s : ℝ,
        s ∈ Set.Ioo c T →
        ∀ t : ℝ,
          t ∈ Set.Ioo c T →
          abs
            (
              h3TerminalResolvedPhysicalPDEEnvelope
                  hH3 hClass t
                -
              h3TerminalResolvedPhysicalPDEEnvelope
                  hH3 hClass s
            )
            ≤
          K * abs (t - s)

/--
A finite terminal-tail Lipschitz constant gives a finite uniform bound for the
global resolved physical PDE envelope on the same tail.
-/
theorem resolvedPhysicalPDEEnvelope_bounded_on_terminalTail_of_lipschitzOn_terminalTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hLip :
      H3TerminalResolvedPhysicalPDEEnvelopeLipschitzOnTerminalTail
        hH3 hClass) :
    ∃ c : ℝ,
      c ∈ Set.Ioo a T
        ∧
      ∃ M : ℝ,
        ∀ t : ℝ,
          t ∈ Set.Ioo c T →
          h3TerminalResolvedPhysicalPDEEnvelope
              hH3 hClass t
            ≤
          M := by

  obtain
    ⟨c, hc, K, hK, hLip⟩ :=
    hLip

  let s : ℝ :=
    (c + T) / 2

  have hs :
      s ∈ Set.Ioo c T := by

    dsimp only [s]

    constructor <;> linarith [hc.2]

  let E : ℝ → ℝ :=
    h3TerminalResolvedPhysicalPDEEnvelope
      hH3 hClass

  let M : ℝ :=
    abs (E s) + K * (T - c)

  refine
    ⟨
      c,
      hc,
      M,
      ?_
    ⟩

  intro t ht

  have hDelta :
      abs (E t - E s)
        ≤
      K * abs (t - s) := by

    dsimp only [E]

    exact
      hLip s hs t ht

  have hTime :
      abs (t - s)
        ≤
      T - c := by

    rw [abs_le]

    constructor

    · dsimp only [s]
      linarith [ht.1, ht.2, hc.2]

    · dsimp only [s]
      linarith [ht.1, ht.2, hc.2]

  have hScaled :
      K * abs (t - s)
        ≤
      K * (T - c) :=
    mul_le_mul_of_nonneg_left
      hTime
      hK

  have hDiff :
      E t - E s
        ≤
      K * (T - c) := by

    exact
      le_trans
        (le_abs_self (E t - E s))
        (
          le_trans
            hDelta
            hScaled
        )

  have hBase :
      E s ≤ abs (E s) :=
    le_abs_self
      (E s)

  dsimp only [M]

  linarith

/--
Terminal-tail Lipschitz control of the global envelope is already a smooth
continuation criterion.
-/
theorem smoothContinuationExtension_of_resolvedPhysicalPDEEnvelope_lipschitzOn_terminalTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hLip :
      H3TerminalResolvedPhysicalPDEEnvelopeLipschitzOnTerminalTail
        hH3 hClass) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by

  apply
    smoothContinuationExtension_of_resolvedPhysicalPDEEnvelope_bounded_on_terminalTail
      hH3 hClass hPhysical hCauchy

  exact
    resolvedPhysicalPDEEnvelope_bounded_on_terminalTail_of_lipschitzOn_terminalTail
      hH3 hClass hLip

/--
Hypothetical nonextension rules out every finite global Lipschitz constant on
every strict terminal tail.
-/
theorem not_resolvedPhysicalPDEEnvelope_lipschitzOn_terminalTail_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
    ¬ H3TerminalResolvedPhysicalPDEEnvelopeLipschitzOnTerminalTail
        hH3 hClass := by

  intro hLip

  exact
    hNoExtension
      (
        smoothContinuationExtension_of_resolvedPhysicalPDEEnvelope_lipschitzOn_terminalTail
          hH3 hClass hPhysical hCauchy hLip
      )

/--
Under hypothetical nonextension, the global envelope has arbitrarily steep
increments on every strict terminal tail.

For every finite slope `K >= 0`, two times can be found on the tail whose
envelope difference exceeds `K` times their temporal separation.
-/
theorem resolvedPhysicalPDEEnvelope_arbitrarilySteep_on_every_terminalTail_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
    ∀ c : ℝ,
      c ∈ Set.Ioo a T →
      ∀ K : ℝ,
        0 ≤ K →
        ∃ s : ℝ,
          s ∈ Set.Ioo c T
            ∧
          ∃ t : ℝ,
            t ∈ Set.Ioo c T
              ∧
            K * abs (t - s)
              <
            abs
              (
                h3TerminalResolvedPhysicalPDEEnvelope
                    hH3 hClass t
                  -
                h3TerminalResolvedPhysicalPDEEnvelope
                    hH3 hClass s
              ) := by

  intro c hc K hK

  classical

  by_contra hNoSteep

  have hBound :
      ∀ s : ℝ,
        s ∈ Set.Ioo c T →
        ∀ t : ℝ,
          t ∈ Set.Ioo c T →
          abs
            (
              h3TerminalResolvedPhysicalPDEEnvelope
                  hH3 hClass t
                -
              h3TerminalResolvedPhysicalPDEEnvelope
                  hH3 hClass s
            )
            ≤
          K * abs (t - s) := by

    intro s hs t ht

    by_contra hNotLe

    have hSteep :
        K * abs (t - s)
          <
        abs
          (
            h3TerminalResolvedPhysicalPDEEnvelope
                hH3 hClass t
              -
            h3TerminalResolvedPhysicalPDEEnvelope
                hH3 hClass s
          ) :=
      lt_of_not_ge
        hNotLe

    exact
      hNoSteep
        ⟨
          s,
          hs,
          t,
          ht,
          hSteep
        ⟩

  have hLip :
      H3TerminalResolvedPhysicalPDEEnvelopeLipschitzOnTerminalTail
        hH3 hClass :=
    ⟨
      c,
      hc,
      K,
      hK,
      hBound
    ⟩

  exact
    (
      not_resolvedPhysicalPDEEnvelope_lipschitzOn_terminalTail_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
        hH3 hClass hPhysical hCauchy hNoExtension
    )
      hLip

/--
Neutral steepness formulation.

Either the path extends smoothly through `T`, or the one global resolved
physical PDE envelope develops arbitrarily steep increments on every strict
terminal tail.
-/
theorem smoothContinuationExtension_or_resolvedPhysicalPDEEnvelope_arbitrarilySteep_on_every_terminalTail
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
      ∀ c : ℝ,
        c ∈ Set.Ioo a T →
        ∀ K : ℝ,
          0 ≤ K →
          ∃ s : ℝ,
            s ∈ Set.Ioo c T
              ∧
            ∃ t : ℝ,
              t ∈ Set.Ioo c T
                ∧
              K * abs (t - s)
                <
              abs
                (
                  h3TerminalResolvedPhysicalPDEEnvelope
                      hH3 hClass t
                    -
                  h3TerminalResolvedPhysicalPDEEnvelope
                      hH3 hClass s
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
          resolvedPhysicalPDEEnvelope_arbitrarilySteep_on_every_terminalTail_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
            hH3 hClass hPhysical hCauchy hExtension
        )

end

end Euclidean
end Bridge
end PrimeTensor
