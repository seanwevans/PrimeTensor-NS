import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongSelectedWeakCoordinatePairingDerivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongSelectedWeakElapsedLocalEvolution
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Differentiate the complete selected weak velocity pairing

The coordinatewise parametric-integral step is now closed.  This file performs
the finite-dimensional assembly.

Define the ambient-real selected weak velocity pairing

    P(r) = Σ_i ∫ φ_i(x) S_i(r,x) dx

and its temporal pairing

    D(r) = Σ_i ∫ φ_i(x) ∂ₜS_i(r,x) dx.

At every strict elapsed time `r ∈ (0,tau)`:

* `HasDerivAt.fun_sum` assembles the three coordinate derivative theorems into
  `P'(r) = D(r)`;
* the already-proved elapsed local evolution identifies `D(r)` with the
  quotient-safe physical selected projected-RHS pairing.

Hence

    P'(r) = ⟪Φ, R_sel^elapsed(r)⟫.

No endpoint argument or interval integration occurs here.  The next layer can
feed this derivative statement, closed-interval velocity-pairing continuity,
and projected-RHS interval integrability directly into scalar FTC.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongSelectedWeakPairingDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Complete ambient-real compact-test pairing with the canonical selected
restart velocity. -/
noncomputable def h3PreterminalSelectedUnitWeakVelocityPairingReal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (r : ℝ) :
    ℝ :=
  ∑ i : Fin 3,
    h3PreterminalSelectedUnitWeakVelocityCoordinatePairingReal
      hNS ht hE hTail (φ i) i r

/-- Complete ambient-real compact-test pairing with the actual pointwise
selected temporal derivative. -/
noncomputable def h3PreterminalSelectedUnitWeakTemporalPairingReal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (r : ℝ) :
    ℝ :=
  ∑ i : Fin 3,
    h3PreterminalSelectedUnitWeakTemporalCoordinatePairingReal
      hNS ht hE hTail (φ i) i r

/-- The complete selected weak velocity pairing differentiates to the complete
selected weak temporal pairing at every strict elapsed time. -/
theorem h3PreterminalSelectedUnitWeakVelocityPairingReal_hasDerivAt_temporalPairing
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau r : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hr : r ∈ Set.Ioo (0 : ℝ) tau)
    (φ : H3WeakTestVector) :
    HasDerivAt
      (h3PreterminalSelectedUnitWeakVelocityPairingReal
        hNS ht hE hTail φ)
      (h3PreterminalSelectedUnitWeakTemporalPairingReal
        hNS ht hE hTail φ r)
      r := by
  unfold h3PreterminalSelectedUnitWeakVelocityPairingReal
  unfold h3PreterminalSelectedUnitWeakTemporalPairingReal

  apply HasDerivAt.fun_sum

  intro i hi

  exact
    h3PreterminalSelectedUnitWeakVelocityCoordinatePairingReal_hasDerivAt
      hNS ht htau hE hTail htauR hr φ i

/-- At every strict elapsed time, the derivative of the complete selected weak
velocity pairing is exactly the physical selected projected-RHS pairing. -/
theorem h3PreterminalSelectedUnitWeakVelocityPairingReal_hasDerivAt_projectedRHSRealOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau r : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hr : r ∈ Set.Ioo (0 : ℝ) tau)
    (φ : H3WeakTestVector) :
    HasDerivAt
      (h3PreterminalSelectedUnitWeakVelocityPairingReal
        hNS ht hE hTail φ)
      (inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
          hNS ht hE hTail htauR r))
      r := by
  have hDeriv :=
    h3PreterminalSelectedUnitWeakVelocityPairingReal_hasDerivAt_temporalPairing
      hNS ht htau hE hTail htauR hr φ

  have hTemporalEq :
      h3PreterminalSelectedUnitWeakTemporalPairingReal
          hNS ht hE hTail φ r
        =
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
          hNS ht hE hTail htauR r) := by
    unfold h3PreterminalSelectedUnitWeakTemporalPairingReal
    unfold h3PreterminalSelectedUnitWeakTemporalCoordinatePairingReal
    dsimp only

    exact
      h3PreterminalSelectedUnitRealVelocity_weakTemporalPairing_eq_projectedRHSRealOnElapsed
        hNS ht htau hE hTail htauR hr φ

  rw [hTemporalEq] at hDeriv

  exact hDeriv

end

end Euclidean
end Bridge
end PrimeTensor
