import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldL2DifferenceInitial

/-!
# Split the selected/old L² difference derivative into the two branch derivatives

`SelectedOldL2DifferenceInitial` reduced physical restart uniqueness to a
Grönwall package for the concrete selected-minus-old three-component physical
`L²` difference.

This file removes one final piece of bookkeeping from that frontier.  Instead
of asking directly for a derivative of the difference path, we may provide
ordinary real-time liftings of the selected and old physical `L²` velocity
paths separately, together with their derivatives.  Linearity then gives the
difference derivative automatically.

Thus the remaining PDE work is branch-local:

* identify the selected physical `L²` time derivative;
* identify the old physical `L²` time derivative;
* prove the standard Navier--Stokes difference bound

      ‖S'(s) - O'(s)‖ ≤ K ‖S(s) - O(s)‖.

No new endpoint or initial-value hypothesis is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldL2SeparateDerivatives
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Separate strong `L²` derivative data for the selected and old physical
velocity paths on one fixed strict elapsed interval. -/
def H3PreterminalSelectedOldL2SeparateDerivativeDataOnElapsed
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∃
    (S O S' O' : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (K : ℝ),
      (∀ q : Set.Icc (0 : ℝ) tau,
        S (q : ℝ)
          =
        h3PreterminalSelectedVelocityPhysicalL2HilbertAt
          hν hNS ht hE hTail (q : ℝ))
      ∧
      (∀ q : Set.Icc (0 : ℝ) tau,
        O (q : ℝ)
          =
        h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail q)
      ∧
      ContinuousOn S (Set.Icc (0 : ℝ) tau)
      ∧
      ContinuousOn O (Set.Icc (0 : ℝ) tau)
      ∧
      (∀ s ∈ Set.Ico (0 : ℝ) tau,
        HasDerivWithinAt
          S (S' s) (Set.Ici s) s)
      ∧
      (∀ s ∈ Set.Ico (0 : ℝ) tau,
        HasDerivWithinAt
          O (O' s) (Set.Ici s) s)
      ∧
      (∀ s ∈ Set.Ico (0 : ℝ) tau,
        ‖S' s - O' s‖
          ≤
        K * ‖S s - O s‖)

/-- Separate selected/old derivative data produces the concrete difference
derivative/bound package by subtraction. -/
theorem h3PreterminalSelectedOldL2DifferenceDerivativeBoundDataOnElapsed_of_separateDerivatives
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hSeparate :
      H3PreterminalSelectedOldL2SeparateDerivativeDataOnElapsed
        hν hNS ht hEnd hE hTail) :
    H3PreterminalSelectedOldL2DifferenceDerivativeBoundDataOnElapsed
      hν hNS ht hEnd hE hTail := by
  rcases hSeparate with
    ⟨S, O, S', O', K,
      hSConcrete, hOConcrete,
      hSCont, hOCont,
      hSDeriv, hODeriv,
      hBound⟩

  let D : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    fun s => S s - O s

  let D' : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    fun s => S' s - O' s

  refine
    ⟨D, D', K, ?_, ?_, ?_, ?_⟩

  · intro q
    dsimp only [D]

    rw [hSConcrete q, hOConcrete q]

    rfl

  · dsimp only [D]
    exact hSCont.sub hOCont

  · intro s hs
    dsimp only [D, D']

    exact
      (hSDeriv s hs).sub
        (hODeriv s hs)

  · intro s hs
    dsimp only [D, D']

    exact hBound s hs

/-- Separate branch derivative data already closes pointwise physical agreement
on every positive time of the fixed strict interval. -/
theorem h3PreterminalSelectedPhysicalAgreementAt_of_l2SeparateDerivatives
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius ν E)
    (hSeparate :
      H3PreterminalSelectedOldL2SeparateDerivativeDataOnElapsed
        hν hNS ht hEnd hE hTail)
    (q : Set.Ioc (0 : ℝ) tau) :
    H3PreterminalSelectedPhysicalAgreementAt
      hν (q : ℝ) hNS ht hE hTail := by
  exact
    h3PreterminalSelectedPhysicalAgreementAt_of_l2DifferenceDerivativeBound
      hν
      hNS
      ht
      htau
      hEnd
      hE
      hTail
      htauR
      (h3PreterminalSelectedOldL2DifferenceDerivativeBoundDataOnElapsed_of_separateDerivatives
        hν
        hNS
        ht
        hEnd
        hE
        hTail
        hSeparate)
      q

end

end Euclidean
end Bridge
end PrimeTensor
