import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakEnergySquareIncrement
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldL2DifferenceInitial

/-!
# Finite partition weak-energy estimate

`SelectedOldWeakStrongWeakEnergySquareIncrement` gives the squared-energy
increment estimate on one ordered interval `[a,b]`.  This file performs the
finite telescoping step needed before the mesh limit.

For a monotone node family

    x 0 <= x 1 <= ... <= x n

inside `[0,tau]`, summing the local inequalities gives

    ||D(x n)||^2 - ||D(x 0)||^2
      <= sum over cells of
           2 * energy integral
         + weak-test approximation error
         + quadratic increment remainder.

Mathlib's `Finset.sum_range_sub` closes the left-hand telescope exactly.
The second theorem specializes to `x 0 = 0`, uses the already-proved canonical
identity `D(0)=0`, and exposes the endpoint energy estimate in the form needed
for the later mesh-limit argument.

No limiting argument is performed here, and no strong old `L2` time derivative
is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergyPartition
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Sum the local squared-energy estimate over an arbitrary finite monotone
partition contained in `[0,tau]`.  The energy increments telescope exactly. -/
theorem norm_sq_selectedOldDifferenceReal_sub_le_partitionApproximateEnergyIncrement
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail)
    (n : ℕ)
    (x : ℕ → ℝ)
    (hxmem :
      ∀ k : ℕ,
        k ≤ n →
          x k ∈ Set.Icc (0 : ℝ) tau)
    (hxmono :
      ∀ k : ℕ,
        k < n →
          x k ≤ x (k + 1))
    {ε : ℝ}
    (hε : 0 < ε) :
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
        hNS ht hEnd hE hTail (x n)‖ ^ 2
      -
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
        hNS ht hEnd hE hTail (x 0)‖ ^ 2
      ≤
    ∑ k ∈ Finset.range n,
      (2 *
        (∫ r in x k..x (k + 1),
          3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
              ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                hNS ht hEnd hE hTail r‖ ^ 2
            +
          (ε +
            ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                  hNS ht hEnd hE hTail (x k)
              -
              h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                  hNS ht hEnd hE hTail r‖)
            *
          (6 * h3UnitViscosityZeroRHSBound E))
        +
      2 * ε *
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail (x (k + 1))
          -
          h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail (x k)‖
        +
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
            hNS ht hEnd hE hTail (x (k + 1))
          -
        h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
            hNS ht hEnd hE hTail (x k)‖ ^ 2) := by
  let D : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
      hNS ht hEnd hE hTail

  let R : ℕ → ℝ :=
    fun k : ℕ =>
      2 *
        (∫ r in x k..x (k + 1),
          3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
              ‖D r‖ ^ 2
            +
          (ε + ‖D (x k) - D r‖) *
            (6 * h3UnitViscosityZeroRHSBound E))
        +
      2 * ε * ‖D (x (k + 1)) - D (x k)‖
        +
      ‖D (x (k + 1)) - D (x k)‖ ^ 2

  have hCell :
      ∀ k ∈ Finset.range n,
        ‖D (x (k + 1))‖ ^ 2 - ‖D (x k)‖ ^ 2
          ≤ R k := by
    intro k hk

    have hklt : k < n :=
      Finset.mem_range.mp hk

    have hk_le : k ≤ n :=
      Nat.le_of_lt hklt

    have hksucc_le : k + 1 ≤ n := by
      omega

    dsimp only [D, R]

    exact
      norm_sq_selectedOldDifferenceReal_sub_le_approximateEnergyIncrement_of_mem
        hNS ht htau hEnd hE hTail htauR hPressure
        (hxmem k hk_le)
        (hxmem (k + 1) hksucc_le)
        (hxmono k hklt)
        hε

  have hSum :
      (∑ k ∈ Finset.range n,
        (‖D (x (k + 1))‖ ^ 2 - ‖D (x k)‖ ^ 2))
        ≤
      ∑ k ∈ Finset.range n, R k := by
    exact Finset.sum_le_sum hCell

  rw [
    Finset.sum_range_sub
      (fun k : ℕ => ‖D (x k)‖ ^ 2)
      n
  ] at hSum

  simpa only [D, R] using hSum

/-- Partition estimate anchored at elapsed time zero.

The initial selected and old physical states coincide exactly, so the left side
of the telescoping estimate reduces to the terminal squared difference alone. -/
theorem norm_sq_selectedOldDifferenceReal_le_partitionApproximateEnergyIncrement
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail)
    (n : ℕ)
    (x : ℕ → ℝ)
    (hx0 : x 0 = 0)
    (hxn : x n = q)
    (hxmem :
      ∀ k : ℕ,
        k ≤ n →
          x k ∈ Set.Icc (0 : ℝ) tau)
    (hxmono :
      ∀ k : ℕ,
        k < n →
          x k ≤ x (k + 1))
    {ε : ℝ}
    (hε : 0 < ε) :
    ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
        hNS ht hEnd hE hTail q‖ ^ 2
      ≤
    ∑ k ∈ Finset.range n,
      (2 *
        (∫ r in x k..x (k + 1),
          3 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
              ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                hNS ht hEnd hE hTail r‖ ^ 2
            +
          (ε +
            ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                  hNS ht hEnd hE hTail (x k)
              -
              h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
                  hNS ht hEnd hE hTail r‖)
            *
          (6 * h3UnitViscosityZeroRHSBound E))
        +
      2 * ε *
        ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail (x (k + 1))
          -
          h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
              hNS ht hEnd hE hTail (x k)‖
        +
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
            hNS ht hEnd hE hTail (x (k + 1))
          -
        h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
            hNS ht hEnd hE hTail (x k)‖ ^ 2) := by
  have hPartition :=
    norm_sq_selectedOldDifferenceReal_sub_le_partitionApproximateEnergyIncrement
      hNS ht htau hEnd hE hTail htauR hPressure
      n x hxmem hxmono hε

  have hZeroMem :
      (0 : ℝ) ∈ Set.Icc (0 : ℝ) tau :=
    ⟨le_rfl, htau.le⟩

  have hDZero :
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail 0
        =
      0 := by
    rw [
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed_apply_of_mem
        hNS ht hEnd hE hTail hZeroMem
    ]

    exact
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed_zero
        (one_pos : (0 : ℝ) < 1)
        hNS ht htau hEnd hE hTail

  rw [hx0, hxn] at hPartition

  have hInitialEnergy :
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceRealOnElapsed
          hNS ht hEnd hE hTail 0‖ ^ 2
        =
      0 := by
    rw [hDZero]
    norm_num

  rw [hInitialEnergy, sub_zero] at hPartition

  exact hPartition

end

end Euclidean
end Bridge
end PrimeTensor
