import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Channel
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Derivative obstruction from terminal channel steepness

The preceding checkpoint freezes one resolved physical PDE channel whose scalar
amplitude is arbitrarily steep on every strict terminal tail.

This file converts that increment obstruction into the corresponding
first-derivative obstruction.

For an ordinary real path `F`, suppose

    K |t - s| < |F(t) - F(s)|

for two points in one strict terminal tail.  If `F` is differentiable throughout
that tail, the real mean value theorem produces an intermediate point `r` with

    K < |F'(r)|.

Applying this for arbitrarily large `K` gives cofinal unboundedness of the
scalar derivative.

We do not assume the frozen physical channel amplitude is differentiable.
Instead the unconditional conclusion is the exact neutral alternative on every
strict terminal tail:

* either the frozen amplitude fails to be differentiable at some strict time;
* or the absolute value of its derivative is unbounded on that tail.

Thus any hypothetical nonextension must either lose one additional temporal
derivative in the frozen channel or drive that additional derivative to
arbitrarily large magnitude arbitrarily close to `T`.

No higher regularity is asserted here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 900000

/-! ## Scalar mean-value escalation -/

/--
An increment steeper than `K` on a differentiable real path forces an
intermediate derivative with magnitude larger than `K`.
-/
private theorem exists_abs_deriv_gt_of_abs_increment_gt
    {F : ℝ → ℝ}
    {c T K s t : ℝ}
    (hs : s ∈ Set.Ioo c T)
    (ht : t ∈ Set.Ioo c T)
    (hDiff :
      ∀ r : ℝ,
        r ∈ Set.Ioo c T →
        DifferentiableAt ℝ F r)
    (hSteep :
      K * abs (t - s)
        <
      abs (F t - F s)) :
    ∃ r : ℝ,
      r ∈ Set.Ioo c T
        ∧
      K < abs (deriv F r) := by

  rcases lt_trichotomy s t with hst | hEq | hts

  · have hIccSubset :
        Set.Icc s t
          ⊆
        Set.Ioo c T := by

      intro r hr

      exact
        ⟨
          lt_of_lt_of_le
            hs.1
            hr.1,
          lt_of_le_of_lt
            hr.2
            ht.2
        ⟩

    have hIooSubset :
        Set.Ioo s t
          ⊆
        Set.Ioo c T := by

      intro r hr

      exact
        ⟨
          lt_trans
            hs.1
            hr.1,
          lt_trans
            hr.2
            ht.2
        ⟩

    have hContinuous :
        ContinuousOn F (Set.Icc s t) := by

      intro r hr

      exact
        (hDiff r (hIccSubset hr)).continuousAt.continuousWithinAt

    have hDifferentiable :
        DifferentiableOn ℝ F (Set.Ioo s t) := by

      intro r hr

      exact
        (hDiff r (hIooSubset hr)).differentiableWithinAt

    obtain
      ⟨r, hr, hSlope⟩ :=
      exists_deriv_eq_slope
        F
        hst
        hContinuous
        hDifferentiable

    have hDen :
        0 < t - s := by
      exact sub_pos.mpr hst

    have hTimeAbs :
        abs (t - s)
          =
        t - s := by
      exact abs_of_pos hDen

    have hSteep' :
        K * (t - s)
          <
        abs (F t - F s) := by
      simpa only [hTimeAbs] using
        hSteep

    have hRatio :
        K
          <
        abs
          (
            (F t - F s)
              /
            (t - s)
          ) := by

      rw [
        abs_div,
        abs_of_pos hDen
      ]

      exact
        (lt_div_iff₀ hDen).2
          hSteep'

    have hLarge :
        K < abs (deriv F r) := by
      rw [hSlope]
      exact hRatio

    exact
      ⟨
        r,
        hIooSubset hr,
        hLarge
      ⟩

  · subst t

    exfalso

    simpa using
      hSteep

  · have hIccSubset :
        Set.Icc t s
          ⊆
        Set.Ioo c T := by

      intro r hr

      exact
        ⟨
          lt_of_lt_of_le
            ht.1
            hr.1,
          lt_of_le_of_lt
            hr.2
            hs.2
        ⟩

    have hIooSubset :
        Set.Ioo t s
          ⊆
        Set.Ioo c T := by

      intro r hr

      exact
        ⟨
          lt_trans
            ht.1
            hr.1,
          lt_trans
            hr.2
            hs.2
        ⟩

    have hContinuous :
        ContinuousOn F (Set.Icc t s) := by

      intro r hr

      exact
        (hDiff r (hIccSubset hr)).continuousAt.continuousWithinAt

    have hDifferentiable :
        DifferentiableOn ℝ F (Set.Ioo t s) := by

      intro r hr

      exact
        (hDiff r (hIooSubset hr)).differentiableWithinAt

    obtain
      ⟨r, hr, hSlope⟩ :=
      exists_deriv_eq_slope
        F
        hts
        hContinuous
        hDifferentiable

    have hDen :
        0 < s - t := by
      exact sub_pos.mpr hts

    have hTimeAbs :
        abs (t - s)
          =
        s - t := by

      rw [
        abs_of_neg
          (sub_neg.mpr hts)
      ]

      ring

    have hValueAbs :
        abs (F t - F s)
          =
        abs (F s - F t) :=
      abs_sub_comm
        (F t)
        (F s)

    have hSteep' :
        K * (s - t)
          <
        abs (F s - F t) := by

      rw [
        hTimeAbs,
        hValueAbs
      ] at hSteep

      exact hSteep

    have hRatio :
        K
          <
        abs
          (
            (F s - F t)
              /
            (s - t)
          ) := by

      rw [
        abs_div,
        abs_of_pos hDen
      ]

      exact
        (lt_div_iff₀ hDen).2
          hSteep'

    have hLarge :
        K < abs (deriv F r) := by
      rw [hSlope]
      exact hRatio

    exact
      ⟨
        r,
        hIooSubset hr,
        hLarge
      ⟩

/-! ## Frozen-channel derivative obstruction -/

/--
If one arbitrarily steep resolved channel remains differentiable on a strict
terminal tail, then the magnitude of its scalar derivative is unbounded on
that same tail.
-/
theorem resolvedPhysicalPDEChannelAmplitude_deriv_cofinallyUnbounded_on_tail_of_arbitrarilySteep_of_differentiable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a c : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (channel : H3TerminalResolvedPhysicalPDEChannel)
    (hSteep :
      H3TerminalResolvedPhysicalPDEChannelArbitrarilySteep
        hH3 hClass j channel)
    (hc : c ∈ Set.Ioo a T)
    (hDiff :
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
        DifferentiableAt ℝ
          (h3TerminalResolvedPhysicalPDEChannelAmplitude
            hH3 hClass j channel)
          t) :
    ∀ M : ℝ,
      ∃ r : ℝ,
        r ∈ Set.Ioo c T
          ∧
        M
          <
        abs
          (
            deriv
              (h3TerminalResolvedPhysicalPDEChannelAmplitude
                hH3 hClass j channel)
              r
          ) := by

  intro M

  let K : ℝ :=
    max M 0

  have hK :
      0 ≤ K := by
    dsimp only [K]
    exact le_max_right _ _

  obtain
    ⟨s, hs, t, ht, hIncrement⟩ :=
    hSteep
      c
      hc
      K
      hK

  obtain
    ⟨r, hr, hDeriv⟩ :=
    exists_abs_deriv_gt_of_abs_increment_gt
      hs
      ht
      hDiff
      hIncrement

  have hMK :
      M ≤ K := by
    dsimp only [K]
    exact le_max_left _ _

  exact
    ⟨
      r,
      hr,
      lt_of_le_of_lt
        hMK
        hDeriv
    ⟩

/--
The exact one-more-time-derivative obstruction for one fixed resolved physical
PDE channel.

On every strict terminal tail, either the channel amplitude loses ordinary
real differentiability at some strict time or its derivative magnitude is
unbounded on that tail.
-/
def H3TerminalResolvedPhysicalPDEChannelDerivativeObstruction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (channel : H3TerminalResolvedPhysicalPDEChannel) :
    Prop :=
  ∀ c : ℝ,
    c ∈ Set.Ioo a T →
    (
      ∃ t : ℝ,
        t ∈ Set.Ioo c T
          ∧
        ¬ DifferentiableAt ℝ
            (h3TerminalResolvedPhysicalPDEChannelAmplitude
              hH3 hClass j channel)
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
                (h3TerminalResolvedPhysicalPDEChannelAmplitude
                  hH3 hClass j channel)
                r
            )
    )

/--
Arbitrary terminal steepness of one fixed resolved channel implies its
one-more-time-derivative obstruction.
-/
theorem resolvedPhysicalPDEChannelDerivativeObstruction_of_arbitrarilySteep
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (channel : H3TerminalResolvedPhysicalPDEChannel)
    (hSteep :
      H3TerminalResolvedPhysicalPDEChannelArbitrarilySteep
        hH3 hClass j channel) :
    H3TerminalResolvedPhysicalPDEChannelDerivativeObstruction
      hH3 hClass j channel := by

  intro c hc

  classical

  by_cases hDiff :
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
        DifferentiableAt ℝ
          (h3TerminalResolvedPhysicalPDEChannelAmplitude
            hH3 hClass j channel)
          t

  · exact
      Or.inr
        (
          resolvedPhysicalPDEChannelAmplitude_deriv_cofinallyUnbounded_on_tail_of_arbitrarilySteep_of_differentiable
            hH3
            hClass
            j
            channel
            hSteep
            hc
            hDiff
        )

  · left

    simp only [
      not_forall
    ] at hDiff

    obtain
      ⟨t, ht, hNotDiff⟩ :=
      hDiff

    exact
      ⟨
        t,
        ht,
        hNotDiff
      ⟩

/--
Under the retained endpoint hypotheses and hypothetical nonextension, one fixed
coordinate and one fixed resolved physical PDE channel satisfy the
one-more-time-derivative obstruction on every strict terminal tail.
-/
theorem exists_fixed_resolvedPhysicalPDEChannel_derivativeObstruction_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
      ∃ channel₀ : H3TerminalResolvedPhysicalPDEChannel,
        H3TerminalResolvedPhysicalPDEChannelDerivativeObstruction
          hH3 hClass j₀ channel₀ := by

  obtain
    ⟨j₀, channel₀, hSteep⟩ :=
    exists_fixed_resolvedPhysicalPDEChannel_arbitrarilySteep_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension

  exact
    ⟨
      j₀,
      channel₀,
      resolvedPhysicalPDEChannelDerivativeObstruction_of_arbitrarilySteep
        hH3 hClass j₀ channel₀ hSteep
    ⟩

/--
Neutral derivative-level terminal formulation.

Either the H³ path extends smoothly through `T`, or one fixed resolved physical
PDE channel must, on every strict terminal tail, either lose one more ordinary
time derivative or have that derivative attain arbitrarily large magnitude.
-/
theorem smoothContinuationExtension_or_fixed_resolvedPhysicalPDEChannel_derivativeObstruction
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
        ∃ channel₀ : H3TerminalResolvedPhysicalPDEChannel,
          H3TerminalResolvedPhysicalPDEChannelDerivativeObstruction
            hH3 hClass j₀ channel₀
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
          exists_fixed_resolvedPhysicalPDEChannel_derivativeObstruction_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
            hH3 hClass hPhysical hCauchy hExtension
        )

end

end Euclidean
end Bridge
end PrimeTensor
