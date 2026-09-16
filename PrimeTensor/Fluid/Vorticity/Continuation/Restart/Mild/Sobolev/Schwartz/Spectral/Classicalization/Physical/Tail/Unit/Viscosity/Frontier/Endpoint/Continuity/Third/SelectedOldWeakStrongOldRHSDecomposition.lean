import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongOldRHSHilbert
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.RHSPhysicalWeak

/-!
# Hilbert-vector decomposition of the endpoint-independent old projected RHS

`SelectedOldWeakStrongOldRHSHilbert` packages the old unit-viscosity projected
RHS as a genuine three-component physical `L²` Hilbert vector.

Coordinatewise, `Zero.RHSPhysicalWeak` has already proved the exact identity

    R_old,i = Δu_i - P div(u ⊗ u)_i

at the level of genuine physical `L²` classes.

This file only bundles those two coordinate families into Hilbert vectors and
lifts the existing scalar equality to

    R_old = L_old - N_old.

This is the decomposition required by the relative-energy/weak--strong
uniqueness calculation.  No endpoint continuity or temporal differentiability
is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongOldRHSDecomposition
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Endpoint-independent old physical Laplacian, bundled coordinatewise in the
native three-component physical `L²` Hilbert space. -/
noncomputable def h3PreterminalTailCanonicalOldLaplacianPhysicalL2HilbertOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    H3PhysicalRealFinVectorL2Hilbert :=
  WithLp.toLp 2
    (fun i : Fin 3 =>
      h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
        hNS ht hEnd hTail q i)

@[simp]
theorem h3PreterminalTailCanonicalOldLaplacianPhysicalL2HilbertOnElapsed_apply
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    h3PreterminalTailCanonicalOldLaplacianPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q i
      =
    h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
      hNS ht hEnd hTail q i := by
  rfl

/-- Endpoint-independent old real physical Leray forcing, bundled
coordinatewise in the native physical `L²` Hilbert space. -/
noncomputable def h3PreterminalTailCanonicalOldLerayForcingPhysicalL2HilbertOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    H3PhysicalRealFinVectorL2Hilbert :=
  WithLp.toLp 2
    (fun i : Fin 3 =>
      h3PreterminalTailCanonicalZeroLerayForcingPhysicalL2OnElapsed
        hNS ht hEnd hTail q i)

@[simp]
theorem h3PreterminalTailCanonicalOldLerayForcingPhysicalL2HilbertOnElapsed_apply
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    h3PreterminalTailCanonicalOldLerayForcingPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q i
      =
    h3PreterminalTailCanonicalZeroLerayForcingPhysicalL2OnElapsed
      hNS ht hEnd hTail q i := by
  rfl

/-- Exact Hilbert-vector decomposition of the endpoint-independent old
projected RHS into diffusion minus Leray transport. -/
theorem h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed_eq_laplacian_sub_leray
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q
      =
    h3PreterminalTailCanonicalOldLaplacianPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q
      -
    h3PreterminalTailCanonicalOldLerayForcingPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q := by
  apply PiLp.ext
  intro i

  change
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
        hNS ht hEnd hTail q i
      =
    h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
        hNS ht hEnd hTail q i
      -
    h3PreterminalTailCanonicalZeroLerayForcingPhysicalL2OnElapsed
        hNS ht hEnd hTail q i

  exact
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed_eq_decomposed
      hNS ht hEnd hTail q i

/-- Pairing against the old projected RHS splits into the diffusion pairing
minus the old Leray-transport pairing. -/
theorem inner_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed_eq
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (D : H3PhysicalRealFinVectorL2Hilbert) :
    inner ℝ D
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail q)
      =
    inner ℝ D
        (h3PreterminalTailCanonicalOldLaplacianPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail q)
      -
    inner ℝ D
        (h3PreterminalTailCanonicalOldLerayForcingPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail q) := by
  rw [
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed_eq_laplacian_sub_leray
      hNS ht hEnd hTail q,
    inner_sub_right
  ]

end

end Euclidean
end Bridge
end PrimeTensor
