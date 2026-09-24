import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Difference.Leray.Fixed
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Selected.RHS.Hilbert

/-!
# Selected unit-viscosity projected RHS is Leray-fixed

The endpoint-independent weak--strong route ultimately needs the temporal RHS
difference to live in the same solenoidal physical Hilbert subspace as the
velocity difference.

This file closes the selected half of that statement.

At every closed selected restart-radius time `q`, define the quotient-safe
Fourier vector

    R̂_sel(q) = Δ̂U_sel(q) - N̂_sel(q).

The selected spectral velocity is already Fourier divergence-free.  The common
raw Laplacian multiplier preserves that property, while the nonlinear forcing
is literally in the range of the finite Leray projector.  Hence `R̂_sel(q)` is
divergence-free and therefore Leray-fixed.

The selected physical RHS was reconstructed coordinatewise as a genuine real
`L²` state.  Existing exact scalar Plancherel identities show that its canonical
raw Fourier vector is exactly `R̂_sel(q)`, so Leray-fixedness transports to the
physical three-component Hilbert state.

No temporal derivative, endpoint continuity, or selected--old agreement is
used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongSelectedRHSLerayFixed
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Quotient-safe Fourier `L²` selected projected RHS vector at one closed
unit-viscosity restart-radius time. -/
noncomputable def h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E)) :
    H3SpectralFinVectorState :=
  fun i : Fin 3 =>
    h3PreterminalSelectedUnitLaplacianFourierL2OnRadius
        hNS ht hE hTail q i
      -
    h3PreterminalSelectedUnitLerayForcingFourierL2OnRadius
        hNS ht hE hTail q i

/-- The selected quotient-safe Fourier projected RHS is divergence-free. -/
theorem h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius_divergenceFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E)) :
    H3SpectralFinDivergenceFree
      (h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
        hNS ht hE hTail q) := by
  let U : H3SpectralFinVectorState :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht hE hTail q

  have hU :
      H3SpectralFinDivergenceFree U := by
    dsimp only [U]

    exact
      h3PreterminalSelectedUnitSpectralStateOnRadius_divergenceFree
        hNS ht hE hTail q

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

  have hLapEq :
      (fun i : Fin 3 =>
        h3PreterminalSelectedUnitLaplacianFourierL2OnRadius
          hNS ht hE hTail q i)
        =
      (fun i : Fin 3 =>
        h3SpectralScalarLaplacianRawFourierL2 (U i)) := by
    funext i
    rfl

  have hForcingEq :
      (fun i : Fin 3 =>
        h3PreterminalSelectedUnitLerayForcingFourierL2OnRadius
          hNS ht hE hTail q i)
        =
      (fun i : Fin 3 =>
        h3RawFinLerayOuterProductDivergenceFourierL2
          U U i) := by
    funext i
    rfl

  unfold h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius

  apply H3SpectralFinDivergenceFree.sub

  · change
      H3SpectralFinDivergenceFree
        (fun i : Fin 3 =>
          h3PreterminalSelectedUnitLaplacianFourierL2OnRadius
            hNS ht hE hTail q i)

    exact hLapEq.symm ▸ hLap

  · change
      H3SpectralFinDivergenceFree
        (fun i : Fin 3 =>
          h3PreterminalSelectedUnitLerayForcingFourierL2OnRadius
            hNS ht hE hTail q i)

    exact hForcingEq.symm ▸ hForcing

/-- Hence the selected quotient-safe Fourier projected RHS is fixed by the
finite Leray projector. -/
theorem h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius_lerayFixed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E)) :
    h3SpectralFinLerayApply
        (h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
          hNS ht hE hTail q)
      =
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
      hNS ht hE hTail q := by
  exact
    h3SpectralFinLerayApply_eq_of_divergenceFree
      (h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius_divergenceFree
        hNS ht hE hTail q)

/-- The canonical raw Fourier vector of the genuine real physical selected RHS
is exactly the quotient-safe selected Fourier RHS vector above. -/
theorem h3PhysicalRealFinVectorL2HilbertRawFourier_selectedUnitProjectedRHSPhysicalL2HilbertOnRadius_eq
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E)) :
    h3PhysicalRealFinVectorL2HilbertRawFourier
        (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
          hNS ht hE hTail q)
      =
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
      hNS ht hE hTail q := by
  funext i

  unfold
    h3PhysicalRealFinVectorL2HilbertRawFourier
    h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius

  simp only [PiLp.toLp_apply]

  unfold h3PreterminalSelectedUnitProjectedRHSPhysicalL2OnRadius

  rw [
    h3ScalarFourierL2_sub,
    h3ScalarFourierL2_h3PreterminalSelectedUnitLaplacianPhysicalL2OnRadius,
    h3ScalarFourierL2_h3PreterminalSelectedUnitLerayForcingPhysicalL2OnRadius
  ]

/-- The genuine selected unit-viscosity projected physical RHS is Leray-fixed
at every point of the complete closed selected restart radius. -/
theorem h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius_lerayFixed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E)) :
    H3PhysicalRealFinVectorL2HilbertLerayFixed
      (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
        hNS ht hE hTail q) := by
  unfold H3PhysicalRealFinVectorL2HilbertLerayFixed

  rw [
    h3PhysicalRealFinVectorL2HilbertRawFourier_selectedUnitProjectedRHSPhysicalL2HilbertOnRadius_eq
      hNS ht hE hTail q
  ]

  exact
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius_lerayFixed
      hNS ht hE hTail q

end

end Euclidean
end Bridge
end PrimeTensor
