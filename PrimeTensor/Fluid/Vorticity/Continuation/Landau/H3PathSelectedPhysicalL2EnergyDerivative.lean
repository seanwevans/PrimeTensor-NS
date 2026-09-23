import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedPhysicalL2Derivative
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Selected restart: physical L² kinetic-energy derivative

The selected physical `L²` velocity path now has a genuine strong derivative in
its native real Hilbert space.  The standard Hilbert-space square-norm calculus
therefore gives the scalar kinetic-energy identity

    d/dq ‖S(q)‖² = 2 ⟪S(q), R(q)⟫_ℝ.

This is the zeroth-order scalar energy identity on the selected restart branch.
It is obtained directly from the strong evolution theorem; no differentiation
under a spatial integral is needed here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedPhysicalL2EnergyDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The squared physical `L²` norm of the selected unit-viscosity velocity path
has derivative twice the Hilbert pairing with the selected projected RHS. -/
theorem h3PreterminalSelectedUnitPhysicalL2Energy_hasDerivAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hq : q ∈ Set.Ioo (0 : ℝ) tau) :
    HasDerivAt
      (fun s : ℝ =>
        ‖h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail s‖ ^ 2)
      (2 * inner ℝ
        (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail q)
        (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
          hNS ht hE hTail htauR q))
      q := by
  exact
    (h3PreterminalSelectedVelocityPhysicalL2HilbertAt_hasDerivAt_unit
      hNS ht htau hE hTail htauR hq).norm_sq

/-- Interior form with the projected RHS written directly at the corresponding
closed restart-radius point. -/
theorem h3PreterminalSelectedUnitPhysicalL2Energy_hasDerivAt_radius
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hq : q ∈ Set.Ioo (0 : ℝ) tau) :
    HasDerivAt
      (fun s : ℝ =>
        ‖h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail s‖ ^ 2)
      (2 * inner ℝ
        (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail q)
        (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
          hNS ht hE hTail
          (h3PreterminalElapsedToSelectedUnitRadius
            htauR
            ⟨q, hq.1.le, hq.2.le⟩)))
      q := by
  have h :=
    h3PreterminalSelectedUnitPhysicalL2Energy_hasDerivAt
      hNS ht htau hE hTail htauR hq

  rw [
    h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed_apply_of_mem
      hNS ht hE hTail htauR ⟨hq.1.le, hq.2.le⟩
  ] at h

  exact h

/-- Ordinary `deriv` form of the selected physical `L²` kinetic-energy
identity. -/
theorem deriv_h3PreterminalSelectedUnitPhysicalL2Energy
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hq : q ∈ Set.Ioo (0 : ℝ) tau) :
    deriv
        (fun s : ℝ =>
          ‖h3PreterminalSelectedVelocityPhysicalL2HilbertAt
              (one_pos : (0 : ℝ) < 1)
              hNS ht hE hTail s‖ ^ 2)
        q
      =
    2 * inner ℝ
      (h3PreterminalSelectedVelocityPhysicalL2HilbertAt
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail q)
      (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
        hNS ht hE hTail htauR q) := by
  exact
    (h3PreterminalSelectedUnitPhysicalL2Energy_hasDerivAt
      hNS ht htau hE hTail htauR hq).deriv

end

end Euclidean
end Bridge
end PrimeTensor
