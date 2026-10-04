import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Old.Regularity

/-!
# Reduce the last two Hilbert derivative branches to forcing-time derivatives

After the sixth-diffusion closure, only two abstract Hilbert derivative
frontiers remain:

* lower temporal:
      X₁,j(t) = d/dt (q û_j)(t);
* fourth temporal:
      X₂,j(t) = d/dt (q² û_j)(t).

Both are already exact physical PDE states.

For the lower channel,

    X₁,j = -q² û_j - q F_j.

The `q² û_j` path is already `C¹`.  Therefore any failure of
differentiability of `X₁,j` can only come from failure of differentiability of
the canonical `q F_j` forcing path.

For the fourth channel,

    X₂,j = -q³ û_j - q² F_j.

The preceding sixth-diffusion closure proves that the terminal `q³ û_j` path is
differentiable at every strict time.  Hence any failure of differentiability of
`X₂,j` can only come from the canonical `q² F_j` forcing path.

This file packages that reduction.  It does not assume or assert the missing
forcing-time derivatives.  Instead it sharpens the fixed-channel nonextension
alternative so that the only remaining nondifferentiability witnesses are

    q F_j
or
    q² F_j.

The top-dissipation and sixth-diffusion branches remain explicit cofinally
unbounded Hilbert pairings.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

/-! ## Generic forcing-driven norm-square obstruction -/

/--
A Hilbert norm-square derivative obstruction whose only possible
nondifferentiability is delegated to one forcing path `F`.

The second branch retains the exact Hilbert pairing for the state `X`.
-/
def H3TerminalForcingDrivenHilbertDerivativeObstruction
    {a T : ℝ}
    (F X : ℝ → H3FourierComplexL2) :
    Prop :=
  ∀ c : ℝ,
    c ∈ Set.Ioo a T →
    (
      ∃ t : ℝ,
        t ∈ Set.Ioo c T
          ∧
        ¬ DifferentiableAt ℝ F t
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

/-! ## Lower-temporal state: only q F can lose the next derivative -/

/--
At a strict terminal time, differentiability of the canonical `q F_j` forcing
path implies differentiability of the resolved lower-temporal Hilbert state

    d/dt(q û_j).

The other term in its PDE decomposition, `q² û_j`, is already `C¹`.
-/
theorem h3TerminalResolvedLowerTemporalHilbertState_differentiableAt_of_forcingSecondQ_differentiableAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (hForcing :
      DifferentiableAt ℝ
        (h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
          hH3 hClass j)
        t) :
    DifferentiableAt ℝ
      (h3TerminalResolvedLowerTemporalHilbertState
        hH3 hClass j)
      t := by

  let V2 : ℝ → H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
      hH3 hClass j

  let F1 : ℝ → H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
      hH3 hClass j

  let X : ℝ → H3FourierComplexL2 :=
    h3TerminalResolvedLowerTemporalHilbertState
      hH3 hClass j

  have hV2 :
      DifferentiableAt ℝ V2 t := by
    dsimp only [V2]
    exact
      (
        h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_contDiffAt_one
          hH3 hClass ht j
      ).differentiableAt_one

  have hRHS :
      DifferentiableAt ℝ
        (fun r : ℝ => -V2 r - F1 r)
        t :=
    hV2.neg.sub hForcing

  have hDerivative :=
    h3TerminalPhysicalLowerWeightedHilbertDerivativeAtEndpoint_closed
      hH3 hClass

  have hEq :
      X =ᶠ[𝓝 t]
        (fun r : ℝ => -V2 r - F1 r) := by

    filter_upwards [
      Ioo_mem_nhds ht.1 ht.2
    ] with r hr

    have hDeriv :=
      deriv_h3TerminalPhysicalLowerWeightedVelocityFourierL2Path_eq_lowerWeightedPDERHS
        hH3 hClass hDerivative hr j

    dsimp only [X, h3TerminalResolvedLowerTemporalHilbertState]

    rw [hDeriv]

    unfold
      h3TerminalPhysicalLowerWeightedPDERHSFourierL2At

    dsimp only [V2, F1]

    rw [
      h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_eq
        hH3 hClass hr j,
      h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path_eq
        hH3 hClass hr j
    ]

  exact
    (
      hRHS.hasDerivAt.congr_of_eventuallyEq
        hEq
    ).differentiableAt

/--
The lower-temporal Hilbert obstruction can therefore be sharpened to a
`q F_j` forcing-time obstruction.
-/
theorem lowerTemporal_forcingDrivenHilbertDerivativeObstruction_of_hilbertDerivativeObstruction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (hObstruction :
      H3TerminalHilbertNormSqDerivativeObstruction
        (a := a) (T := T)
        (h3TerminalResolvedLowerTemporalHilbertState
          hH3 hClass j)) :
    H3TerminalForcingDrivenHilbertDerivativeObstruction
      (a := a) (T := T)
      (h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
        hH3 hClass j)
      (h3TerminalResolvedLowerTemporalHilbertState
        hH3 hClass j) := by

  intro c hc

  rcases
    hObstruction c hc
  with hFail | hLarge

  · left

    obtain
      ⟨t, htTail, hNotDiff⟩ :=
      hFail

    have ht :
        t ∈ Set.Ioo a T :=
      ⟨
        lt_trans hc.1 htTail.1,
        htTail.2
      ⟩

    refine
      ⟨
        t,
        htTail,
        ?_
      ⟩

    intro hForcing

    exact
      hNotDiff
        (
          h3TerminalResolvedLowerTemporalHilbertState_differentiableAt_of_forcingSecondQ_differentiableAt
            hH3 hClass ht j hForcing
        )

  · exact
      Or.inr hLarge

/-! ## Fourth-temporal state: only q² F can lose the next derivative -/

/--
At a strict terminal time, differentiability of the canonical `q² F_j`
forcing path implies differentiability of the resolved fourth-temporal Hilbert
state

    d/dt(q² û_j).

Its diffusion term `q³ û_j` is differentiable by the sixth-diffusion closure.
-/
theorem h3TerminalResolvedFourthTemporalHilbertState_differentiableAt_of_forcingFourthQ_differentiableAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (hForcing :
      DifferentiableAt ℝ
        (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
          hH3 hClass j)
        t) :
    DifferentiableAt ℝ
      (h3TerminalResolvedFourthTemporalHilbertState
        hH3 hClass j)
      t := by

  let V3 : ℝ → H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
      hH3 hClass j

  let F2 : ℝ → H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
      hH3 hClass j

  let X : ℝ → H3FourierComplexL2 :=
    h3TerminalResolvedFourthTemporalHilbertState
      hH3 hClass j

  have hV3 :
      DifferentiableAt ℝ V3 t := by
    dsimp only [V3]
    exact
      h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path_differentiableAt
        hH3 hClass ht j

  have hRHS :
      DifferentiableAt ℝ
        (fun r : ℝ => -V3 r - F2 r)
        t :=
    hV3.neg.sub hForcing

  have hEq :
      X =ᶠ[𝓝 t]
        (fun r : ℝ => -V3 r - F2 r) := by

    filter_upwards [
      Ioo_mem_nhds ht.1 ht.2
    ] with r hr

    dsimp only [X, h3TerminalResolvedFourthTemporalHilbertState]

    dsimp only [V3, F2]

    rw [
      h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path_eq
        hH3 hClass hr j,
      h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path_eq
        hH3 hClass hr j
    ]

    unfold
      h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2At

    abel

  exact
    (
      hRHS.hasDerivAt.congr_of_eventuallyEq
        hEq
    ).differentiableAt

/--
The fourth-temporal Hilbert obstruction can therefore be sharpened to a
`q² F_j` forcing-time obstruction.
-/
theorem fourthTemporal_forcingDrivenHilbertDerivativeObstruction_of_hilbertDerivativeObstruction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (hObstruction :
      H3TerminalHilbertNormSqDerivativeObstruction
        (a := a) (T := T)
        (h3TerminalResolvedFourthTemporalHilbertState
          hH3 hClass j)) :
    H3TerminalForcingDrivenHilbertDerivativeObstruction
      (a := a) (T := T)
      (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
        hH3 hClass j)
      (h3TerminalResolvedFourthTemporalHilbertState
        hH3 hClass j) := by

  intro c hc

  rcases
    hObstruction c hc
  with hFail | hLarge

  · left

    obtain
      ⟨t, htTail, hNotDiff⟩ :=
      hFail

    have ht :
        t ∈ Set.Ioo a T :=
      ⟨
        lt_trans hc.1 htTail.1,
        htTail.2
      ⟩

    refine
      ⟨
        t,
        htTail,
        ?_
      ⟩

    intro hForcing

    exact
      hNotDiff
        (
          h3TerminalResolvedFourthTemporalHilbertState_differentiableAt_of_forcingFourthQ_differentiableAt
            hH3 hClass ht j hForcing
        )

  · exact
      Or.inr hLarge

/-! ## Final reduction of the fixed-channel alternative -/

/--
Under hypothetical nonextension, every remaining nondifferentiability witness
has now been pushed entirely into one of the two weighted forcing paths.

For one fixed coordinate, exactly one of four channel types survives:

1. `q F_j` fails to be differentiable arbitrarily close to the terminal time,
   or the lower-temporal norm-square pairing is cofinally unbounded;
2. the top-dissipation pairing is cofinally unbounded;
3. `q² F_j` fails to be differentiable arbitrarily close to the terminal time,
   or the fourth-temporal norm-square pairing is cofinally unbounded;
4. the sixth-diffusion pairing is cofinally unbounded.
-/
theorem exists_fixed_resolvedPhysicalPDEChannel_forcingDerivativeReduced_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
        H3TerminalForcingDrivenHilbertDerivativeObstruction
          (a := a) (T := T)
          (h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
            hH3 hClass j₀)
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
        H3TerminalForcingDrivenHilbertDerivativeObstruction
          (a := a) (T := T)
          (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
            hH3 hClass j₀)
          (h3TerminalResolvedFourthTemporalHilbertState
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
                  2 *
                    inner ℝ
                      (h3TerminalResolvedSixthDiffusionHilbertState
                        hH3 hClass j₀ r)
                      (
                        deriv
                          (h3TerminalResolvedSixthDiffusionHilbertState
                            hH3 hClass j₀)
                          r
                      )
                )
      ) := by

  obtain
    ⟨j₀, hBranch⟩ :=
    exists_fixed_resolvedPhysicalPDEChannel_hilbertDerivativeObstruction_topAndSixthClosed_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
          lowerTemporal_forcingDrivenHilbertDerivativeObstruction_of_hilbertDerivativeObstruction
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
                  fourthTemporal_forcingDrivenHilbertDerivativeObstruction_of_hilbertDerivativeObstruction
                    hH3 hClass j₀ hFourth
                )
            )
        )

  · exact
      Or.inr
        (
          Or.inr
            (
              Or.inr hSixth
            )
        )

/--
Neutral continuation form of the forcing-time reduction.
-/
theorem smoothContinuationExtension_or_fixed_resolvedPhysicalPDEChannel_forcingDerivativeReduced
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
          H3TerminalForcingDrivenHilbertDerivativeObstruction
            (a := a) (T := T)
            (h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
              hH3 hClass j₀)
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
          H3TerminalForcingDrivenHilbertDerivativeObstruction
            (a := a) (T := T)
            (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
              hH3 hClass j₀)
            (h3TerminalResolvedFourthTemporalHilbertState
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
                    2 *
                      inner ℝ
                        (h3TerminalResolvedSixthDiffusionHilbertState
                          hH3 hClass j₀ r)
                        (
                          deriv
                            (h3TerminalResolvedSixthDiffusionHilbertState
                              hH3 hClass j₀)
                            r
                        )
                  )
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
          exists_fixed_resolvedPhysicalPDEChannel_forcingDerivativeReduced_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
            hH3 hClass hPhysical hCauchy hExtension
        )

end

end Euclidean
end Bridge
end PrimeTensor
