import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete.Representative.Closure.ForcingWeights.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square.Factor.Norm.Top

/-!
# Next PDE identities for the resolved Hilbert-state derivatives

The normalized Hilbert derivative escape should now be expressed in the actual
PDE variables rather than left as an abstract derivative of an abstract
Hilbert state.

For the lower-temporal state

    X₁,j = d/dt (q û_j),

the already-closed terminal PDE identity is

    X₁,j = -V₂,j - F₁,j,

where `V₂,j = q² û_j` and `F₁,j = q F_j`.  Since both terms are now
differentiable at every strict time,

    X₁,j' = -X₂,j - F₁,j',

where `X₂,j = d/dt(q² û_j)` is exactly the fourth-temporal Hilbert state.

For the fourth-temporal state

    X₂,j = -V₃,j - F₂,j,

with `V₃,j = q³ û_j` and `F₂,j = q² F_j`.  Both terms are differentiable, so

    X₂,j' = -X₃,j' - F₂,j',

where `X₃,j = q³ û_j` is the sixth-diffusion Hilbert state.

These are exact strict-time identities.  They expose the concrete factors that
can carry the new derivative-norm escape.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

/-! ## Named next-order PDE RHS states -/

/--
Next PDE right-hand side for the derivative of the lower-temporal Hilbert
state:

    -X₂,j - d/dt(q F_j).
-/
noncomputable def h3TerminalResolvedLowerTemporalHilbertDerivativePDERHS
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (t : ℝ) :
    H3FourierComplexL2 :=
  -
    h3TerminalResolvedFourthTemporalHilbertState
      hH3 hClass j t
  -
    deriv
      (h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
        hH3 hClass j)
      t

/--
Next PDE right-hand side for the derivative of the fourth-temporal Hilbert
state:

    -X₃,j' - d/dt(q² F_j).
-/
noncomputable def h3TerminalResolvedFourthTemporalHilbertDerivativePDERHS
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (t : ℝ) :
    H3FourierComplexL2 :=
  -
    deriv
      (h3TerminalResolvedSixthDiffusionHilbertState
        hH3 hClass j)
      t
  -
    deriv
      (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
        hH3 hClass j)
      t

/-! ## Exact lower-temporal derivative identity -/

/--
At every strict preterminal time,

    d/dt X₁,j = -X₂,j - d/dt(q F_j).
-/
theorem deriv_h3TerminalResolvedLowerTemporalHilbertState_eq_pdeRHS
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    deriv
        (h3TerminalResolvedLowerTemporalHilbertState
          hH3 hClass j)
        t
      =
    h3TerminalResolvedLowerTemporalHilbertDerivativePDERHS
      hH3 hClass j t := by

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

  have hF1 :
      DifferentiableAt ℝ F1 t := by
    dsimp only [F1]
    exact
      h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path_differentiableAt
        hH3 hClass ht j

  have hRHS :
      HasDerivAt
        (fun r : ℝ => -V2 r - F1 r)
        (-deriv V2 t - deriv F1 t)
        t :=
    hV2.hasDerivAt.neg.sub
      hF1.hasDerivAt

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

    dsimp only [
      X,
      h3TerminalResolvedLowerTemporalHilbertState
    ]

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

  have hX :
      HasDerivAt
        X
        (-deriv V2 t - deriv F1 t)
        t :=
    hRHS.congr_of_eventuallyEq
      hEq

  have hDX :
      deriv X t
        =
      -deriv V2 t - deriv F1 t :=
    hX.deriv

  unfold
    h3TerminalResolvedLowerTemporalHilbertDerivativePDERHS

  dsimp only [X, V2, F1] at hDX ⊢

  simpa only [
    h3TerminalResolvedFourthTemporalHilbertState
  ] using hDX

/--
The lower-channel Hilbert derivative norm envelope is therefore exactly the
norm of its named next PDE RHS.
-/
theorem h3TerminalResolvedLowerTemporalHilbertDerivativeNormEnvelope_eq_norm_pdeRHS
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
        hH3 hClass j
        H3TerminalResolvedPhysicalPDEChannel.lowerTemporal
        t
      =
    ‖h3TerminalResolvedLowerTemporalHilbertDerivativePDERHS
      hH3 hClass j t‖ := by

  rw [
    h3TerminalResolvedLowerTemporalHilbertDerivativeNormEnvelope_eq
  ]

  rw [
    deriv_h3TerminalResolvedLowerTemporalHilbertState_eq_pdeRHS
      hH3 hClass ht j
  ]

/-! ## Exact fourth-temporal derivative identity -/

/--
At every strict preterminal time,

    d/dt X₂,j = -d/dt X₃,j - d/dt(q² F_j).
-/
theorem deriv_h3TerminalResolvedFourthTemporalHilbertState_eq_pdeRHS
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    deriv
        (h3TerminalResolvedFourthTemporalHilbertState
          hH3 hClass j)
        t
      =
    h3TerminalResolvedFourthTemporalHilbertDerivativePDERHS
      hH3 hClass j t := by

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

  have hF2 :
      DifferentiableAt ℝ F2 t := by
    dsimp only [F2]
    exact
      h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path_differentiableAt
        hH3 hClass ht j

  have hRHS :
      HasDerivAt
        (fun r : ℝ => -V3 r - F2 r)
        (-deriv V3 t - deriv F2 t)
        t :=
    hV3.hasDerivAt.neg.sub
      hF2.hasDerivAt

  have hEq :
      X =ᶠ[𝓝 t]
        (fun r : ℝ => -V3 r - F2 r) := by

    filter_upwards [
      Ioo_mem_nhds ht.1 ht.2
    ] with r hr

    dsimp only [
      X,
      h3TerminalResolvedFourthTemporalHilbertState
    ]

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

  have hX :
      HasDerivAt
        X
        (-deriv V3 t - deriv F2 t)
        t :=
    hRHS.congr_of_eventuallyEq
      hEq

  have hDX :
      deriv X t
        =
      -deriv V3 t - deriv F2 t :=
    hX.deriv

  have hSixthPath :
      h3TerminalResolvedSixthDiffusionHilbertState
          hH3 hClass j
        =
      h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
        hH3 hClass j := by

    funext r
    rfl

  unfold
    h3TerminalResolvedFourthTemporalHilbertDerivativePDERHS

  rw [hSixthPath]

  dsimp only [X, V3, F2] at hDX ⊢

  exact hDX

/--
The fourth-temporal Hilbert derivative norm envelope is exactly the norm of its
named next PDE RHS.
-/
theorem h3TerminalResolvedFourthTemporalHilbertDerivativeNormEnvelope_eq_norm_pdeRHS
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
        hH3 hClass j
        H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
        t
      =
    ‖h3TerminalResolvedFourthTemporalHilbertDerivativePDERHS
      hH3 hClass j t‖ := by

  rw [
    h3TerminalResolvedFourthTemporalHilbertDerivativeNormEnvelope_eq
  ]

  rw [
    deriv_h3TerminalResolvedFourthTemporalHilbertState_eq_pdeRHS
      hH3 hClass ht j
  ]

end

end Euclidean
end Bridge
end PrimeTensor
