import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongSelectedRHSHilbert

/-!
# Selected-minus-old unit-viscosity RHS difference

Both branches now have endpoint-independent physical `L²` Hilbert RHS packages
with the same unit viscosity:

    R_sel = L_sel - N_sel
    R_old = L_old - N_old.

On any strict elapsed interval `[0,τ]` contained in the canonical selected
restart radius, this file places the selected objects on that same elapsed
interval and forms the three difference vectors

    RΔ = R_sel - R_old
    LΔ = L_sel - L_old
    NΔ = N_sel - N_old.

Pure Hilbert-space algebra then gives

    RΔ = LΔ - NΔ.

This is exactly the RHS decomposition needed by the weak--strong relative-energy
argument.  No old strong derivative or endpoint continuity is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongRHSDifference
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Regard a closed elapsed time `q ∈ [0,τ]` as a selected restart-radius time
when `τ` lies inside the unit-viscosity restart radius. -/
def h3PreterminalElapsedToSelectedUnitRadius
    {E tau : ℝ}
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau) :
    Set.Icc
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
  ⟨
    (q : ℝ),
    q.property.1,
    q.property.2.trans htauR
  ⟩

@[simp]
theorem h3PreterminalElapsedToSelectedUnitRadius_coe
    {E tau : ℝ}
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau) :
    (h3PreterminalElapsedToSelectedUnitRadius htauR q : ℝ)
      =
    (q : ℝ) := by
  rfl

/-- Selected-minus-old projected RHS on one closed strict elapsed interval. -/
noncomputable def h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
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
    H3PhysicalRealFinVectorL2Hilbert :=
  h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
      hNS ht hE hTail
      (h3PreterminalElapsedToSelectedUnitRadius htauR q)
    -
  h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
      hNS ht hEnd hTail q

/-- Selected-minus-old physical Laplacian difference on one closed strict
elapsed interval. -/
noncomputable def h3PreterminalSelectedOldUnitLaplacianDifferenceOnElapsed
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
    H3PhysicalRealFinVectorL2Hilbert :=
  h3PreterminalSelectedUnitLaplacianPhysicalL2HilbertOnRadius
      hNS ht hE hTail
      (h3PreterminalElapsedToSelectedUnitRadius htauR q)
    -
  h3PreterminalTailCanonicalOldLaplacianPhysicalL2HilbertOnElapsed
      hNS ht hEnd hTail q

/-- Selected-minus-old physical Leray-forcing difference on one closed strict
elapsed interval. -/
noncomputable def h3PreterminalSelectedOldUnitLerayForcingDifferenceOnElapsed
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
    H3PhysicalRealFinVectorL2Hilbert :=
  h3PreterminalSelectedUnitLerayForcingPhysicalL2HilbertOnRadius
      hNS ht hE hTail
      (h3PreterminalElapsedToSelectedUnitRadius htauR q)
    -
  h3PreterminalTailCanonicalOldLerayForcingPhysicalL2HilbertOnElapsed
      hNS ht hEnd hTail q

/-- Exact selected-minus-old projected-RHS decomposition:

    R_sel - R_old = (L_sel - L_old) - (N_sel - N_old).
-/
theorem h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed_eq_laplacian_sub_leray
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
    h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
        hNS ht hEnd hE hTail htauR q
      =
    h3PreterminalSelectedOldUnitLaplacianDifferenceOnElapsed
        hNS ht hEnd hE hTail htauR q
      -
    h3PreterminalSelectedOldUnitLerayForcingDifferenceOnElapsed
        hNS ht hEnd hE hTail htauR q := by
  unfold
    h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
    h3PreterminalSelectedOldUnitLaplacianDifferenceOnElapsed
    h3PreterminalSelectedOldUnitLerayForcingDifferenceOnElapsed

  rw [
    h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius_eq_laplacian_sub_leray
      hNS ht hE hTail
      (h3PreterminalElapsedToSelectedUnitRadius htauR q),
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed_eq_laplacian_sub_leray
      hNS ht hEnd hTail q
  ]

  abel

/-- Pairing with the selected-minus-old projected RHS splits into diffusion
difference minus Leray-forcing difference. -/
theorem inner_h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed_eq
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
    (q : Set.Icc (0 : ℝ) tau)
    (D : H3PhysicalRealFinVectorL2Hilbert) :
    inner ℝ D
        (h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
          hNS ht hEnd hE hTail htauR q)
      =
    inner ℝ D
        (h3PreterminalSelectedOldUnitLaplacianDifferenceOnElapsed
          hNS ht hEnd hE hTail htauR q)
      -
    inner ℝ D
        (h3PreterminalSelectedOldUnitLerayForcingDifferenceOnElapsed
          hNS ht hEnd hE hTail htauR q) := by
  rw [
    h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed_eq_laplacian_sub_leray
      hNS ht hEnd hE hTail htauR q,
    inner_sub_right
  ]

end

end Euclidean
end Bridge
end PrimeTensor
