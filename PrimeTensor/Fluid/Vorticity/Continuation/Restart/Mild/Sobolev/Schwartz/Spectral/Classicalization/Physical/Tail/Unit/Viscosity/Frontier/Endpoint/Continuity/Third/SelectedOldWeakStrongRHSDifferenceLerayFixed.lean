import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongSelectedRHSLerayFixed
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongRHSDifference

/-!
# Endpoint-independent selected--old projected RHS difference is Leray-fixed

The selected projected RHS is now known to be Leray-fixed in genuine physical
`L²`.  This file closes the matching endpoint-independent old statement and
then subtracts.

For one old elapsed slice, let

    U = canonical weighted H³ old snapshot.

Its exact quotient-safe Fourier projected RHS is

    R̂_old = Δ̂U - P div(U ⊗ U).

The encoded old snapshot is Fourier divergence-free.  The common Laplacian
multiplier preserves divergence-freeness, and the nonlinear forcing lies in
the range of the finite Leray projector.  Hence `R̂_old` is divergence-free,
therefore Leray-fixed.

The endpoint-independent real physical old RHS has exact scalar Plancherel
transform `R̂_old`, so the physical Hilbert vector is Leray-fixed as well.

Finally

    RΔ = R_sel - R_old

is Leray-fixed on every closed strict elapsed interval inside the selected
unit-viscosity restart radius.

No endpoint continuity or strong old `L²` time derivative is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongRHSDifferenceLerayFixed
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Endpoint-independent old quotient-safe projected RHS, bundled as a finite
Fourier `L²` vector. -/
noncomputable def h3PreterminalTailCanonicalZeroProjectedRHSFourierL2HilbertOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    H3SpectralFinVectorState :=
  fun i : Fin 3 =>
    h3PreterminalTailCanonicalZeroProjectedRHSFourierL2OnElapsed
      hNS ht hEnd hTail q i

/-- The endpoint-independent old quotient-safe Fourier projected RHS is
divergence-free. -/
theorem h3PreterminalTailCanonicalZeroProjectedRHSFourierL2HilbertOnElapsed_divergenceFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    H3SpectralFinDivergenceFree
      (h3PreterminalTailCanonicalZeroProjectedRHSFourierL2HilbertOnElapsed
        hNS ht hEnd hTail q) := by
  let U : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q

  have hU :
      H3SpectralFinDivergenceFree U := by
    dsimp only [U]
    unfold h3PreterminalTailCanonicalSpectralStateOnElapsed

    exact
      velocityH3SpectralStateAt_divergenceFree_of_loggedPreterminalNavierStokes
        hNS
        (h3PreterminalElapsedTime_mem_Ioo ht hEnd q)
        (h3PreterminalTailIntegrableOnElapsed hEnd hTail q)

  have hLap :
      H3SpectralFinDivergenceFree
        (fun i : Fin 3 =>
          h3SpectralScalarLaplacianRawFourierL2 (U i)) :=
    h3SpectralFinLaplacianRawFourierL2_divergenceFree hU

  have hForcing :
      H3SpectralFinDivergenceFree
        (fun i : Fin 3 =>
          h3RawFinLerayOuterProductDivergenceFourierL2
            U U i) :=
    h3RawFinLerayOuterProductDivergenceFourierL2_divergenceFree
      U U

  unfold
    h3PreterminalTailCanonicalZeroProjectedRHSFourierL2HilbertOnElapsed
    h3PreterminalTailCanonicalZeroProjectedRHSFourierL2OnElapsed

  dsimp only [U]

  exact hLap.sub hForcing

/-- Hence the endpoint-independent old Fourier projected RHS is fixed by the
finite Leray projector. -/
theorem h3PreterminalTailCanonicalZeroProjectedRHSFourierL2HilbertOnElapsed_lerayFixed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    h3SpectralFinLerayApply
        (h3PreterminalTailCanonicalZeroProjectedRHSFourierL2HilbertOnElapsed
          hNS ht hEnd hTail q)
      =
    h3PreterminalTailCanonicalZeroProjectedRHSFourierL2HilbertOnElapsed
      hNS ht hEnd hTail q := by
  exact
    h3SpectralFinLerayApply_eq_of_divergenceFree
      (h3PreterminalTailCanonicalZeroProjectedRHSFourierL2HilbertOnElapsed_divergenceFree
        hNS ht hEnd hTail q)

/-- The canonical raw Fourier vector of the endpoint-independent physical old
RHS is exactly its quotient-safe Fourier RHS vector. -/
theorem h3PhysicalRealFinVectorL2HilbertRawFourier_zeroProjectedRHSPhysicalL2HilbertOnElapsed_eq
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PhysicalRealFinVectorL2HilbertRawFourier
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail q)
      =
    h3PreterminalTailCanonicalZeroProjectedRHSFourierL2HilbertOnElapsed
      hNS ht hEnd hTail q := by
  funext i

  unfold
    h3PhysicalRealFinVectorL2HilbertRawFourier
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
    h3PreterminalTailCanonicalZeroProjectedRHSFourierL2HilbertOnElapsed

  simp only [PiLp.toLp_apply]

  exact
    h3ScalarFourierL2_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
      hNS ht hEnd hTail q i

/-- The endpoint-independent old projected physical RHS is Leray-fixed at every
closed elapsed slice. -/
theorem h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed_lerayFixed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    H3PhysicalRealFinVectorL2HilbertLerayFixed
      (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q) := by
  unfold H3PhysicalRealFinVectorL2HilbertLerayFixed

  rw [
    h3PhysicalRealFinVectorL2HilbertRawFourier_zeroProjectedRHSPhysicalL2HilbertOnElapsed_eq
      hNS ht hEnd hTail q
  ]

  exact
    h3PreterminalTailCanonicalZeroProjectedRHSFourierL2HilbertOnElapsed_lerayFixed
      hNS ht hEnd hTail q

/-- The actual endpoint-independent selected-minus-old projected RHS difference
is Leray-fixed on every closed strict elapsed interval. -/
theorem h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed_lerayFixed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau) :
    H3PhysicalRealFinVectorL2HilbertLerayFixed
      (h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
        hNS ht hEnd hE hTail htauR q) := by
  unfold
    h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed

  apply H3PhysicalRealFinVectorL2HilbertLerayFixed.sub

  · exact
      h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius_lerayFixed
        hNS ht hE hTail
        (h3PreterminalElapsedToSelectedUnitRadius htauR q)

  · exact
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed_lerayFixed
        hNS ht hEnd hTail q

end

end Euclidean
end Bridge
end PrimeTensor
