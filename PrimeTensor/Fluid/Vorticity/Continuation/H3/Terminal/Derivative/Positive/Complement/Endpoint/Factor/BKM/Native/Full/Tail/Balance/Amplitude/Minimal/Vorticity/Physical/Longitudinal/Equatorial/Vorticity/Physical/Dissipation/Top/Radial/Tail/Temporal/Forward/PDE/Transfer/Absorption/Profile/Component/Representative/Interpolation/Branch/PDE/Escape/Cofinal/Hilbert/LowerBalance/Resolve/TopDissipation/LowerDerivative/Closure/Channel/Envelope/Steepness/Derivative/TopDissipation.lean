import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Old.Regularity
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Close the top-dissipation differentiability branch

The derivative obstruction for the frozen resolved physical PDE channel has
four possible channel types.

The top-dissipation branch can already be pushed one full step farther with no
new hypothesis.  The physical fourth-radial coordinate paths

    V_j(t) = q² û_j(t)

are already locally `C¹` at every strict preterminal time.  Meanwhile the full
top H³ dissipation is exactly

    D₃(t) = Σ_j ‖V_j(t)‖².

Therefore `HasDerivAt.norm_sq` and finite summation give

    D₃'(t)
      =
    Σ_j 2 ⟪V_j(t), V_j'(t)⟫_ℝ

at every strict time.

Consequences:

* the top-dissipation channel cannot realize the "loss of differentiability"
  side of the derivative obstruction;
* if it is the frozen channel under hypothetical nonextension, then the above
  Hilbert pairing is cofinally unbounded in absolute value on every strict
  terminal tail.

This is an actual analytic closure of one of the four derivative-obstruction
branches; the other three still require one additional Hilbert-time derivative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopDissipationDerivativeClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1200000

/-! ## Full top dissipation as a finite Hilbert norm-square sum -/

/--
At every strict preterminal time, the named physical top H³ dissipation is the
sum of the three squared fourth-radial Fourier `L²` norms.
-/
theorem h3TerminalPhysicalTopDissipation3Path_eq_sum_norm_sq_fourthRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3TerminalPhysicalTopDissipation3Path
        hClass t
      =
    ∑ j : Fin 3,
      (
        ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
            hH3 hClass j t‖ : ℝ
      ) ^ 2 := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs

  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs

  have hTop :
      h3TerminalPhysicalTopDissipation3Path hClass t
        =
      velocityH3Dissipation3At u t :=
    h3TerminalPhysicalTopDissipation3Path_eq
      hClass ht

  have hMoment :
      velocityH3Dissipation3At u t
        =
      velocityH3FourierFourthRadialMomentAt
        u t hInt hMeas := by

    simpa only [htAbs, hInt, hMeas] using
      (
        velocityH3Dissipation3At_eq_fourierFourthRadialMoment_on_h3Path
          hH3 hClass ht
      )

  rw [
    hTop,
    hMoment
  ]

  unfold
    velocityH3FourierFourthRadialMomentAt

  apply Finset.sum_congr rfl

  intro j hj

  rw [
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_eq
      hH3 hClass ht j
  ]

  exact
    (
      norm_sq_h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
        hH3 hClass ht j
    ).symm

/--
Global ordinary-function form of the preceding identity.

Both sides are zero outside the strict energy-class interval.
-/
theorem h3TerminalPhysicalTopDissipation3Path_eq_sum_norm_sq_fourthRadialPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    h3TerminalPhysicalTopDissipation3Path hClass
      =
    fun t : ℝ =>
      ∑ j : Fin 3,
        (
          ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
              hH3 hClass j t‖ : ℝ
        ) ^ 2 := by

  funext t

  by_cases ht :
      t ∈ Set.Ioo a T

  · exact
      h3TerminalPhysicalTopDissipation3Path_eq_sum_norm_sq_fourthRadial
        hH3 hClass ht

  · unfold
      h3TerminalPhysicalTopDissipation3Path
      h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path

    simp [ht]

/-! ## Exact top-dissipation derivative -/

/--
The full physical top H³ dissipation is differentiable at every strict time,
with derivative equal to the finite Hilbert pairing of the fourth-radial state
with its already-constructed strong temporal derivative.
-/
theorem h3TerminalPhysicalTopDissipation3Path_hasDerivAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    HasDerivAt
      (h3TerminalPhysicalTopDissipation3Path hClass)
      (
        ∑ j : Fin 3,
          2 *
            inner ℝ
              (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                hH3 hClass j t)
              (
                deriv
                  (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                    hH3 hClass j)
                  t
              )
      )
      t := by

  have hEach :
      ∀ j : Fin 3,
        HasDerivAt
          (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
            hH3 hClass j)
          (
            deriv
              (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                hH3 hClass j)
              t
          )
          t := by

    intro j

    have hC1 :
        ContDiffAt ℝ 1
          (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
            hH3 hClass j)
          t :=
      h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_contDiffAt_one
        hH3 hClass ht j

    exact
      hC1.differentiableAt_one.hasDerivAt

  have hSum :
      HasDerivAt
        (
          fun s : ℝ =>
            ∑ j : Fin 3,
              (
                ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                    hH3 hClass j s‖ : ℝ
              ) ^ 2
        )
        (
          ∑ j : Fin 3,
            2 *
              inner ℝ
                (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                  hH3 hClass j t)
                (
                  deriv
                    (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                      hH3 hClass j)
                    t
                )
        )
        t := by

    exact
      HasDerivAt.fun_sum
        (u := (Finset.univ : Finset (Fin 3)))
        (fun j hj =>
          (hEach j).norm_sq)

  rw [
    h3TerminalPhysicalTopDissipation3Path_eq_sum_norm_sq_fourthRadialPath
      hH3 hClass
  ]

  exact hSum

/--
The top-dissipation scalar is differentiable at every strict preterminal time.
-/
theorem h3TerminalPhysicalTopDissipation3Path_differentiableAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    DifferentiableAt ℝ
      (h3TerminalPhysicalTopDissipation3Path hClass)
      t :=
  (
    h3TerminalPhysicalTopDissipation3Path_hasDerivAt
      hH3 hClass ht
  ).differentiableAt

/--
Ordinary derivative formula for the full physical top H³ dissipation.
-/
theorem deriv_h3TerminalPhysicalTopDissipation3Path_eq_sum_inner
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    deriv
        (h3TerminalPhysicalTopDissipation3Path hClass)
        t
      =
    ∑ j : Fin 3,
      2 *
        inner ℝ
          (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
            hH3 hClass j t)
          (
            deriv
              (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                hH3 hClass j)
              t
          ) :=
  (
    h3TerminalPhysicalTopDissipation3Path_hasDerivAt
      hH3 hClass ht
  ).deriv

/-! ## Eliminate loss of differentiability in the top-dissipation channel -/

/--
The canonical resolved-channel amplitude for `.topDissipation` is
differentiable at every strict preterminal time.
-/
theorem resolvedPhysicalPDETopDissipationChannelAmplitude_differentiableAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (ht : t ∈ Set.Ioo a T) :
    DifferentiableAt ℝ
      (
        h3TerminalResolvedPhysicalPDEChannelAmplitude
          hH3 hClass j
          H3TerminalResolvedPhysicalPDEChannel.topDissipation
      )
      t := by

  change
    DifferentiableAt ℝ
      (h3TerminalPhysicalTopDissipation3Path hClass)
      t

  exact
    h3TerminalPhysicalTopDissipation3Path_differentiableAt
      hH3 hClass ht

/--
If the fixed derivative obstruction lands in the top-dissipation channel, its
nondifferentiability alternative is impossible.  Hence the derivative of
`D₃` is cofinally unbounded in absolute value on every strict terminal tail.
-/
theorem topDissipation_deriv_cofinallyUnbounded_of_channelDerivativeObstruction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (hObstruction :
      H3TerminalResolvedPhysicalPDEChannelDerivativeObstruction
        hH3 hClass j
        H3TerminalResolvedPhysicalPDEChannel.topDissipation) :
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
                (h3TerminalPhysicalTopDissipation3Path hClass)
                r
            ) := by

  intro c hc

  rcases
    hObstruction c hc
  with hFail | hLarge

  · obtain
      ⟨t, htTail, hNotDiff⟩ :=
      hFail

    have ht :
        t ∈ Set.Ioo a T :=
      ⟨
        lt_trans hc.1 htTail.1,
        htTail.2
      ⟩

    have hDiff :=
      resolvedPhysicalPDETopDissipationChannelAmplitude_differentiableAt
        hH3 hClass j ht

    exact
      False.elim
        (
          hNotDiff hDiff
        )

  · intro M

    obtain
      ⟨r, hr, hLargeR⟩ :=
      hLarge M

    have hrClass :
        r ∈ Set.Ioo a T :=
      ⟨
        lt_trans hc.1 hr.1,
        hr.2
      ⟩

    refine
      ⟨
        r,
        hr,
        ?_
      ⟩

    change
      M
        <
      abs
        (
          deriv
            (h3TerminalPhysicalTopDissipation3Path hClass)
            r
        )
      at hLargeR

    exact hLargeR

/--
Concrete Hilbert-pairing form of the preceding top-dissipation derivative
escape.
-/
theorem topDissipation_pairing_cofinallyUnbounded_of_channelDerivativeObstruction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (hObstruction :
      H3TerminalResolvedPhysicalPDEChannelDerivativeObstruction
        hH3 hClass j
        H3TerminalResolvedPhysicalPDEChannel.topDissipation) :
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
            ) := by

  intro c hc M

  obtain
    ⟨r, hr, hLarge⟩ :=
    topDissipation_deriv_cofinallyUnbounded_of_channelDerivativeObstruction
      hH3 hClass j hObstruction c hc M

  have hrClass :
      r ∈ Set.Ioo a T :=
    ⟨
      lt_trans hc.1 hr.1,
      hr.2
    ⟩

  rw [
    deriv_h3TerminalPhysicalTopDissipation3Path_eq_sum_inner
      hH3 hClass hrClass
  ] at hLarge

  exact
    ⟨
      r,
      hr,
      hLarge
    ⟩

/-! ## Refined fixed-channel alternative -/

/--
Under hypothetical nonextension, the fixed derivative obstruction can be
resolved by channel type.  In the top-dissipation case the branch is already
fully concrete: the physical Hilbert pairing for `D₃'` is cofinally unbounded.

The other three channel types retain their exact one-more-time-derivative
obstruction.
-/
theorem exists_fixed_resolvedPhysicalPDEChannel_derivativeObstruction_topDissipationClosed_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
        H3TerminalResolvedPhysicalPDEChannelDerivativeObstruction
          hH3 hClass j₀
          H3TerminalResolvedPhysicalPDEChannel.lowerTemporal
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
        H3TerminalResolvedPhysicalPDEChannelDerivativeObstruction
          hH3 hClass j₀
          H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
      )
        ∨
      (
        H3TerminalResolvedPhysicalPDEChannelDerivativeObstruction
          hH3 hClass j₀
          H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion
      ) := by

  obtain
    ⟨j₀, channel₀, hObstruction⟩ :=
    exists_fixed_resolvedPhysicalPDEChannel_derivativeObstruction_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3 hClass hPhysical hCauchy hNoExtension

  refine
    ⟨
      j₀,
      ?_
    ⟩

  cases channel₀ with

  | lowerTemporal =>
      exact
        Or.inl hObstruction

  | topDissipation =>
      exact
        Or.inr
          (
            Or.inl
              (
                topDissipation_pairing_cofinallyUnbounded_of_channelDerivativeObstruction
                  hH3 hClass j₀ hObstruction
              )
          )

  | fourthTemporal =>
      exact
        Or.inr
          (
            Or.inr
              (Or.inl hObstruction)
          )

  | sixthDiffusion =>
      exact
        Or.inr
          (
            Or.inr
              (Or.inr hObstruction)
          )

/--
Neutral continuation alternative with the top-dissipation derivative branch
closed to its concrete Hilbert pairing.
-/
theorem smoothContinuationExtension_or_fixed_resolvedPhysicalPDEChannel_derivativeObstruction_topDissipationClosed
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
          H3TerminalResolvedPhysicalPDEChannelDerivativeObstruction
            hH3 hClass j₀
            H3TerminalResolvedPhysicalPDEChannel.lowerTemporal
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
          H3TerminalResolvedPhysicalPDEChannelDerivativeObstruction
            hH3 hClass j₀
            H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
        )
          ∨
        (
          H3TerminalResolvedPhysicalPDEChannelDerivativeObstruction
            hH3 hClass j₀
            H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion
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
          exists_fixed_resolvedPhysicalPDEChannel_derivativeObstruction_topDissipationClosed_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
            hH3 hClass hPhysical hCauchy hExtension
        )

end

end Euclidean
end Bridge
end PrimeTensor
