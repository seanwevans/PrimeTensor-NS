import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.Envelope
import PrimeTensor.Fluid.Vorticity.H3.Energy.Functional

/-!
# Uniform endpoint H³ square bounds for the vorticity Fubini estimate

`Envelope` supplied the pointwise factors needed for the nonlinear part of the
pressure-free vorticity RHS.  The complementary factors are ordinary spatial
`L²` terms.

The retained canonical H³ tail already contains exactly those square bounds.
This file packages them on an arbitrary closed elapsed interval and normalizes
the common ceiling to `2E`, matching the endpoint spectral path bound used by
`Envelope`.

The result is a uniform family of `SpatialL2SquareBound` statements for every
velocity component and every ordered spatial derivative through order three.
No new estimate is introduced: this is only the componentwise extraction of
the canonical H³ energy bound.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

private theorem h3SpatialL2SquareBound_mono
    {f : ScalarField3}
    {A B : ℝ}
    (h : SpatialL2SquareBound f A)
    (hAB : A ≤ B) :
    SpatialL2SquareBound f B := by
  exact ⟨h.1, h.2.trans hAB⟩

/-- The retained canonical tail gives a uniform `2E` H³ square bound at every
closed elapsed slice. -/
theorem h3PreterminalEndpoint_velocityH3BoundAt_twoE
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    VelocityH3BoundAt
      u
      (t + (q : ℝ))
      (2 * E) := by
  have hCanonical :=
    velocityH3BoundAt_canonical
      u
      (t + (q : ℝ))
      (canonicalH3TailDataFrom_integrableOnElapsed
        hEnd hTail q)

  have hEnergy :
      velocityH3EnergyAt u (t + (q : ℝ)) ≤ 2 * E :=
    canonicalH3TailDataFrom_energyOnElapsed_le_twoE
      hE hEnd hTail q

  unfold VelocityH3BoundAt at hCanonical ⊢
  intro j
  dsimp only at hCanonical ⊢

  have hj := hCanonical j

  refine ⟨?_, ?_, ?_, ?_⟩

  · exact
      h3SpatialL2SquareBound_mono
        hj.1
        hEnergy

  · intro a
    exact
      h3SpatialL2SquareBound_mono
        (hj.2.1 a)
        hEnergy

  · intro a b
    exact
      h3SpatialL2SquareBound_mono
        (hj.2.2.1 a b)
        hEnergy

  · intro a b c
    exact
      h3SpatialL2SquareBound_mono
        (hj.2.2.2 a b c)
        hEnergy

/-- Zeroth-order endpoint velocity square bound. -/
theorem loggedVelocityComponent_spatialL2SquareBound_endpoint_twoE
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j : PrimeTensor.Axis Depth.three) :
    SpatialL2SquareBound
      (loggedVelocityComponent
        u (t + (q : ℝ)) j)
      (2 * E) := by
  have hBound :=
    h3PreterminalEndpoint_velocityH3BoundAt_twoE
      hEnd hE hTail q

  unfold VelocityH3BoundAt at hBound
  exact (hBound j).1

/-- First-order endpoint velocity square bound. -/
theorem loggedVelocityComponent_spatial_d_spatialL2SquareBound_endpoint_twoE
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (a j : PrimeTensor.Axis Depth.three) :
    SpatialL2SquareBound
      (spatial3.d
        a
        (loggedVelocityComponent
          u (t + (q : ℝ)) j))
      (2 * E) := by
  have hBound :=
    h3PreterminalEndpoint_velocityH3BoundAt_twoE
      hEnd hE hTail q

  unfold VelocityH3BoundAt at hBound
  exact (hBound j).2.1 a

/-- Second-order endpoint velocity square bound. -/
theorem loggedVelocityComponent_spatial_d2_spatialL2SquareBound_endpoint_twoE
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (a b j : PrimeTensor.Axis Depth.three) :
    SpatialL2SquareBound
      (spatial3.d
        a
        (spatial3.d
          b
          (loggedVelocityComponent
            u (t + (q : ℝ)) j)))
      (2 * E) := by
  have hBound :=
    h3PreterminalEndpoint_velocityH3BoundAt_twoE
      hEnd hE hTail q

  unfold VelocityH3BoundAt at hBound
  exact (hBound j).2.2.1 a b

/-- Third-order endpoint velocity square bound. -/
theorem loggedVelocityComponent_spatial_d3_spatialL2SquareBound_endpoint_twoE
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (a b c j : PrimeTensor.Axis Depth.three) :
    SpatialL2SquareBound
      (spatial3.d
        a
        (spatial3.d
          b
          (spatial3.d
            c
            (loggedVelocityComponent
              u (t + (q : ℝ)) j))))
      (2 * E) := by
  have hBound :=
    h3PreterminalEndpoint_velocityH3BoundAt_twoE
      hEnd hE hTail q

  unfold VelocityH3BoundAt at hBound
  exact (hBound j).2.2.2 a b c

end

end Euclidean
end Bridge
end PrimeTensor
