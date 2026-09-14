import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.RHSBound

/-!
# Zeroth-order endpoint continuity reduced to one Fourier increment estimate

The endpoint-independent projected RHS is now known to satisfy the uniform
Fourier `L²` bound

    ‖R_i(q)‖₂
      ≤ 2E + 2304 π C_deweight E².

This file removes all remaining topology and Plancherel bookkeeping from the
zeroth-order continuation frontier.

The sole new analytic target is the corresponding two-time estimate for the
old preterminal zeroth Fourier jet:

    dist(F_i(q), F_i(r))
      ≤ (2E + 2304 π C_deweight E²) * dist(q,r).

Once this estimate is available, scalar Plancherel preserves the distance
exactly, hence every physical zeroth-order `L²` coordinate is Lipschitz on the
closed elapsed interval.  `Zero.Lipschitz` then supplies the required endpoint
continuity and the already-closed continuation chain applies.

Thus after this file the zeroth-order branch is reduced to proving one
quantitative Fourier increment inequality from the preterminal Navier--Stokes
equation and the RHS bound already established in `Zero.RHSBound`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroIncrement
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The explicit unit-viscosity zeroth-order `L²` time-Lipschitz constant
supplied by the preceding projected-RHS estimate. -/
noncomputable def h3UnitViscosityZeroRHSBound
    (E : ℝ) : ℝ :=
  2 * E
    +
  2304 * Real.pi * h3SobolevDeweightingConstant * E ^ 2

/-- The explicit zeroth-order RHS constant is nonnegative at every admissible
energy ceiling. -/
theorem h3UnitViscosityZeroRHSBound_nonneg
    {E : ℝ}
    (hE : 1 ≤ E) :
    0 ≤ h3UnitViscosityZeroRHSBound E := by
  unfold h3UnitViscosityZeroRHSBound
  have hE0 : 0 ≤ E := le_trans (by norm_num) hE
  positivity [h3SobolevDeweightingConstant_nonneg]

/-- Repackage the preceding coordinatewise projected-RHS estimate using the
named constant that will serve as the Lipschitz constant. -/
theorem norm_h3PreterminalTailCanonicalZeroProjectedRHSFourierL2OnElapsed_le_bound
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    ‖h3PreterminalTailCanonicalZeroProjectedRHSFourierL2OnElapsed
        hNS ht hEnd hTail q i‖
      ≤
    h3UnitViscosityZeroRHSBound E := by
  exact
    norm_h3PreterminalTailCanonicalZeroProjectedRHSFourierL2OnElapsed_le
      hNS ht hEnd hE hTail q i

/-- Exact remaining zeroth-order analytic estimate on one closed elapsed
interval.

The right-hand side is precisely the uniform Fourier `L²` bound for the
unit-viscosity projected Navier--Stokes RHS proved in `Zero.RHSBound`. -/
def H3PreterminalCanonicalFourierZeroIncrementBoundOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀
    (j : Fin 3)
    (q r : Set.Icc (0 : ℝ) tau),
      dist
          (h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot0 j) q)
          (h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot0 j) r)
        ≤
      h3UnitViscosityZeroRHSBound E * dist q r

/-- The Fourier increment estimate transports exactly through scalar Plancherel
to a physical `L²` Lipschitz estimate. -/
theorem h3PreterminalCanonicalL2ZeroLipschitzOnElapsed_of_fourierIncrement
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hIncrement :
      H3PreterminalCanonicalFourierZeroIncrementBoundOnElapsed
        hNS ht hEnd hE hTail) :
    H3PreterminalCanonicalL2ZeroLipschitzOnElapsed
      hNS ht hEnd hTail := by
  let K : ℝ≥0 :=
    ⟨
      h3UnitViscosityZeroRHSBound E,
      h3UnitViscosityZeroRHSBound_nonneg hE
    ⟩

  refine ⟨K, ?_⟩
  intro j

  apply LipschitzWith.of_dist_le_mul
  intro q r

  change
    dist
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot0 j) q)
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot0 j) r)
      ≤
    h3UnitViscosityZeroRHSBound E * dist q r

  rw [← dist_h3ScalarFourierL2]

  rw [
    ← h3PreterminalCanonicalFourierJetOnElapsed_eq_scalarFourierL2
      hNS ht hEnd hTail (h3JetSlot0 j) q,
    ← h3PreterminalCanonicalFourierJetOnElapsed_eq_scalarFourierL2
      hNS ht hEnd hTail (h3JetSlot0 j) r
  ]

  exact hIncrement j q r

/-- Radius-wide Fourier increment frontier replacing the previous zeroth-order
continuity/Lipschitz frontier. -/
def H3PreterminalTailUnitViscosityZeroFourierIncrementFrontierOnRestartRadius
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ q : Set.Icc
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E),
    ∀ hqPos : 0 < (q : ℝ),
      ∀ hEnd : t + (q : ℝ) < T,
        H3PreterminalCanonicalFourierZeroIncrementBoundOnElapsed
          hNS ht hEnd hE hTail

/-- Radius-wide Fourier increment control supplies radius-wide physical
zeroth-order Lipschitz control. -/
theorem h3PreterminalTailUnitViscosityZeroLipschitzFrontierOnRestartRadius_of_fourierIncrement
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hIncrement :
      H3PreterminalTailUnitViscosityZeroFourierIncrementFrontierOnRestartRadius
        E u T t hNS ht hE hTail) :
    H3PreterminalTailUnitViscosityZeroLipschitzFrontierOnRestartRadius
      E u T t hNS ht hE hTail := by
  intro q hqPos hEnd

  exact
    h3PreterminalCanonicalL2ZeroLipschitzOnElapsed_of_fourierIncrement
      hNS ht hEnd hE hTail
      (hIncrement q hqPos hEnd)

/-- Global unit-viscosity zeroth-order Fourier increment frontier. -/
def H3PreterminalTailUnitViscosityZeroFourierIncrementFrontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailUnitViscosityZeroFourierIncrementFrontierOnRestartRadius
        E u T t hNS ht hE hTail

/-- The global Fourier increment frontier closes the previous global
zeroth-order Lipschitz frontier. -/
theorem h3PreterminalTailUnitViscosityZeroLipschitzFrontier_of_fourierIncrement
    (hIncrement :
      H3PreterminalTailUnitViscosityZeroFourierIncrementFrontier) :
    H3PreterminalTailUnitViscosityZeroLipschitzFrontier := by
  intro E hE u T t hNS ht hTail

  exact
    h3PreterminalTailUnitViscosityZeroLipschitzFrontierOnRestartRadius_of_fourierIncrement
      hNS ht hE hTail
      (hIncrement E hE u T t hNS ht hTail)

/-- Current continuation theorem with the entire zeroth-order branch reduced to
one explicit Fourier increment estimate.  The ordered-third-order continuity
frontier remains independent. -/
theorem h3ControlProducesExtension_of_unitViscosityZeroFourierIncrementThirdContinuityClosed
    (hZeroIncrement :
      H3PreterminalTailUnitViscosityZeroFourierIncrementFrontier)
    (hThird :
      H3PreterminalTailUnitViscosityThirdContinuityFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityZeroLipschitzThirdContinuityClosed
      (h3PreterminalTailUnitViscosityZeroLipschitzFrontier_of_fourierIncrement
        hZeroIncrement)
      hThird

end

end Euclidean
end Bridge
end PrimeTensor
