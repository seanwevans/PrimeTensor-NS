import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Transport.Concrete.Square.Density

/-!
# Selected--old weak--strong transport: physical L² bound

The previous increments established two independent facts:

* the weak--strong interaction satisfies the integrated pointwise estimate

      ∫ interaction ≤ 3 B ∫ |S - O|²;

* the concrete selected-minus-old square-density integral is exactly

      ∫ |S - O|² = ‖D‖²

  for the physical three-component `L²` difference state `D`.

This file joins those two statements for the actual selected restart and old
preterminal branch, written in the common elapsed-time variable `s`.

The resulting estimate is the exact quadratic form needed by the relative
energy argument:

    ∫ interaction ≤ 3 B ‖D(q)‖².

The only analytic hypotheses left explicit here are:

* a uniform coordinate gradient bound `B` for the selected branch at time `q`;
* integrability of the absolute interaction density.

No Leray-pairing identification is used in this file.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongTransportPhysicalL2Bound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance]
  point3MeasureSpaceH3SelectedOldWeakStrongTransportIntegralBound

/-- The actual selected restart velocity, viewed as a real spacetime vector
field in restart-relative time. -/
noncomputable def h3PreterminalSelectedWeakStrongVelocity
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
  h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
    hν
    (h3PreterminalSelectedDecoderAnchorState hNS ht hTail)
    (lt_of_lt_of_le zero_lt_one hE)
    (norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht hE hTail)

/-- The old logged preterminal velocity, reparametrized by elapsed time from
the selected restart time `t`. -/
noncomputable def h3PreterminalOldElapsedWeakStrongVelocity
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
  fun s x =>
    logSpaceTimeVectorField u (t + s) x

/-- The generic selected-minus-old pointwise square density becomes exactly the
concrete density from the previous file after inserting the actual selected
restart and elapsed old branch. -/
theorem selectedOldVelocityDifferenceSquarePointwise_actual_eq
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    selectedOldVelocityDifferenceSquarePointwise
        (h3PreterminalSelectedWeakStrongVelocity
          hν hNS ht hE hTail)
        (h3PreterminalOldElapsedWeakStrongVelocity u t)
        (q : ℝ)
      =
    h3PreterminalSelectedOldVelocitySquareDensity
      hν hNS ht hEnd hE hTail q := by
  funext x

  unfold
    selectedOldVelocityDifferenceSquarePointwise
    h3PreterminalSelectedOldVelocitySquareDensity
    h3PreterminalSelectedWeakStrongVelocity
    h3PreterminalOldElapsedWeakStrongVelocity
    loggedVelocityComponent

  rfl

/-- The actual selected-minus-old square density used by the generic transport
bound is integrable. -/
theorem selectedOldVelocityDifferenceSquarePointwise_actual_integrable
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    MeasureTheory.Integrable
      (selectedOldVelocityDifferenceSquarePointwise
        (h3PreterminalSelectedWeakStrongVelocity
          hν hNS ht hE hTail)
        (h3PreterminalOldElapsedWeakStrongVelocity u t)
        (q : ℝ))
      (volume : Measure Point3) := by
  rw [
    selectedOldVelocityDifferenceSquarePointwise_actual_eq
      hν hNS ht hEnd hE hTail q
  ]

  have hNative :
      MeasureTheory.Integrable
        (h3PhysicalRealFinVectorL2SquareDensity
          (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
            hν hNS ht hEnd hE hTail q))
        (volume : Measure Point3) :=
    h3PhysicalRealFinVectorL2SquareDensity_integrable
      (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        hν hNS ht hEnd hE hTail q)

  exact
    hNative.congr
      (h3PreterminalSelectedOldVelocitySquareDensity_ae_eq_physicalL2
        hν hNS ht hEnd hE hTail q).symm

/-- Absolute weak--strong interaction density for the actual selected restart
and old elapsed branch. -/
noncomputable def h3PreterminalSelectedOldWeakStrongAbsInteractionDensity
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : ℝ)
    (x : Point3) : ℝ :=
  selectedOldWeakStrongAbsInteractionDensity
    (h3PreterminalSelectedWeakStrongVelocity
      hν hNS ht hE hTail)
    (h3PreterminalOldElapsedWeakStrongVelocity u t)
    q x

/-- The actual weak--strong interaction is quadratically controlled by the
physical selected-minus-old `L²` difference:

    ∫ interaction ≤ 3 B ‖D(q)‖².

This is the integrated transport estimate in exactly the norm language used by
the relative-energy reduction. -/
theorem integral_h3PreterminalSelectedOldWeakStrongAbsInteractionDensity_le_norm_sq
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hGradient :
      ∀
        (x : Point3)
        (j i : PrimeTensor.Axis Depth.three),
        abs
          (spatial3.d
            i
            (fun y =>
              ((h3PreterminalSelectedWeakStrongVelocity
                hν hNS ht hE hTail)
                (q : ℝ) y).component j)
            x)
          ≤ B)
    (hInteraction :
      MeasureTheory.Integrable
        (h3PreterminalSelectedOldWeakStrongAbsInteractionDensity
          hν hNS ht hE hTail (q : ℝ))
        (volume : Measure Point3)) :
    (∫ x : Point3,
      h3PreterminalSelectedOldWeakStrongAbsInteractionDensity
        hν hNS ht hE hTail (q : ℝ) x)
      ≤
    3 * B *
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          hν hNS ht hEnd hE hTail q‖ ^ 2 := by
  have hSquare :
      MeasureTheory.Integrable
        (selectedOldVelocityDifferenceSquarePointwise
          (h3PreterminalSelectedWeakStrongVelocity
            hν hNS ht hE hTail)
          (h3PreterminalOldElapsedWeakStrongVelocity u t)
          (q : ℝ))
        (volume : Measure Point3) :=
    selectedOldVelocityDifferenceSquarePointwise_actual_integrable
      hν hNS ht hEnd hE hTail q

  have hBound :=
    integral_selectedOldWeakStrongAbsInteractionDensity_le
      (h3PreterminalSelectedWeakStrongVelocity
        hν hNS ht hE hTail)
      (h3PreterminalOldElapsedWeakStrongVelocity u t)
      (q : ℝ)
      B
      hB
      hGradient
      (by
        change
          MeasureTheory.Integrable
            (selectedOldWeakStrongAbsInteractionDensity
              (h3PreterminalSelectedWeakStrongVelocity
                hν hNS ht hE hTail)
              (h3PreterminalOldElapsedWeakStrongVelocity u t)
              (q : ℝ))
            (volume : Measure Point3)
          at hInteraction
        exact hInteraction)
      hSquare

  rw [
    selectedOldVelocityDifferenceSquarePointwise_actual_eq
      hν hNS ht hEnd hE hTail q,
    integral_h3PreterminalSelectedOldVelocitySquareDensity_eq_norm_sq
      hν hNS ht hEnd hE hTail q
  ] at hBound

  change
    (∫ x : Point3,
      selectedOldWeakStrongAbsInteractionDensity
        (h3PreterminalSelectedWeakStrongVelocity
          hν hNS ht hE hTail)
        (h3PreterminalOldElapsedWeakStrongVelocity u t)
        (q : ℝ) x)
      ≤
    3 * B *
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          hν hNS ht hEnd hE hTail q‖ ^ 2

  exact hBound

end

end Euclidean
end Bridge
end PrimeTensor
