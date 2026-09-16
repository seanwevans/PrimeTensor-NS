import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldRealizableRawHermitian
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.RHS.Leray.Fixed

/-!
# Unit-viscosity selected projected RHS in the physical L² Hilbert space

The old branch is now packaged endpoint-independently as

    R_old = L_old - N_old

in the native three-component real physical `L²` Hilbert space.

This file builds the matching selected object at the viscosity actually shared
with the normalized old Navier--Stokes equation: `ν = 1`.

The selected spectral restart is already realizable on its entire canonical
radius, and the preceding file upgrades realizability to exact raw-Hermitian
symmetry.  We first show that the generic weighted-state Fourier Laplacian

    raw(ΔG)(ξ) = -q(ξ) raw(G)(ξ)

preserves Hermitian symmetry.  The existing nonlinear reality theorem supplies
the same fact for the Leray forcing.  Hence both Fourier terms reconstruct
canonically as real physical `L²` classes.

Coordinatewise we define

    L_sel,i = physical reconstruction of ΔU_sel,i
    N_sel,i = physical reconstruction of P div(U_sel ⊗ U_sel)_i
    R_sel,i = L_sel,i - N_sel,i

and bundle them into the same `H3PhysicalRealFinVectorL2Hilbert` used by the
old branch.

No old endpoint continuity and no selected/old agreement is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongSelectedRHSHilbert
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The generic raw Fourier Laplacian preserves Hermitian symmetry. -/
theorem h3SpectralScalarLaplacianRawFourierL2_preserves_hermitian
    {G : H3SpectralScalarState}
    (hG : H3SpectralScalarRawHermitian G) :
    H3FourierL2Hermitian
      (h3SpectralScalarLaplacianRawFourierL2 G) := by
  unfold H3SpectralScalarRawHermitian at hG
  unfold H3FourierL2Hermitian at hG ⊢

  have hLap :=
    h3SpectralScalarLaplacianRawFourierL2_ae_eq_gradientSquare_mul_raw
      G

  have hLapNeg :=
    h3Fourier_ae_neg hLap

  filter_upwards [hLap, hLapNeg, hG] with ξ hAt hNeg hHerm

  rw [hNeg, hAt, h3FourierGradientSquare_neg, hHerm]

  simp

/-- Canonical unit-viscosity selected weighted H³ state at one closed restart
radius time. -/
noncomputable def h3PreterminalSelectedUnitSpectralStateOnRadius
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
    H3SpectralVelocityState :=
  h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
    (one_pos : (0 : ℝ) < 1)
    (h3PreterminalSelectedDecoderAnchorState
      hNS ht hTail)
    (lt_of_lt_of_le zero_lt_one hE)
    (norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht hE hTail)
    (q : ℝ)

/-- The canonical unit-viscosity selected state is raw-Hermitian on the whole
closed restart radius. -/
theorem h3PreterminalSelectedUnitSpectralStateOnRadius_rawHermitian
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
    H3SpectralVelocityRawHermitian
      (h3PreterminalSelectedUnitSpectralStateOnRadius
        hNS ht hE hTail q) := by
  unfold h3PreterminalSelectedUnitSpectralStateOnRadius

  exact
    h3PreterminalSelectedPhysicalExtension_rawHermitian
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail q

/-- Selected unit-viscosity Fourier Laplacian coordinate. -/
noncomputable def h3PreterminalSelectedUnitLaplacianFourierL2OnRadius
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
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (i : Fin 3) :
    H3FourierComplexL2 :=
  h3SpectralScalarLaplacianRawFourierL2
    ((h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht hE hTail q) i)

/-- Selected unit-viscosity Fourier Leray-forcing coordinate. -/
noncomputable def h3PreterminalSelectedUnitLerayForcingFourierL2OnRadius
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
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (i : Fin 3) :
    H3FourierComplexL2 :=
  let U :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht hE hTail q
  h3RawFinLerayOuterProductDivergenceFourierL2
    U U i

/-- The selected Fourier Laplacian is Hermitian. -/
theorem h3PreterminalSelectedUnitLaplacianFourierL2OnRadius_hermitian
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
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (i : Fin 3) :
    H3FourierL2Hermitian
      (h3PreterminalSelectedUnitLaplacianFourierL2OnRadius
        hNS ht hE hTail q i) := by
  unfold h3PreterminalSelectedUnitLaplacianFourierL2OnRadius

  exact
    h3SpectralScalarLaplacianRawFourierL2_preserves_hermitian
      ((h3PreterminalSelectedUnitSpectralStateOnRadius_rawHermitian
        hNS ht hE hTail q) i)

/-- The selected Fourier Leray forcing is Hermitian. -/
theorem h3PreterminalSelectedUnitLerayForcingFourierL2OnRadius_hermitian
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
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (i : Fin 3) :
    H3FourierL2Hermitian
      (h3PreterminalSelectedUnitLerayForcingFourierL2OnRadius
        hNS ht hE hTail q i) := by
  let U :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht hE hTail q

  have hU :
      H3SpectralVelocityRawHermitian U := by
    dsimp only [U]
    exact
      h3PreterminalSelectedUnitSpectralStateOnRadius_rawHermitian
        hNS ht hE hTail q

  unfold h3PreterminalSelectedUnitLerayForcingFourierL2OnRadius
  dsimp only

  exact
    h3RawFinLerayOuterProductDivergenceFourierL2_preserves_hermitian
      hU hU i

/-- Canonical real physical `L²` reconstruction of the selected Laplacian. -/
noncomputable def h3PreterminalSelectedUnitLaplacianPhysicalL2OnRadius
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
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (i : Fin 3) :
    H3ScalarL2 :=
  h3FromFourierRealL2
    (h3RealPartFourierL2
      ((MeasureTheory.Lp.fourierTransformₗᵢ
        H3FourierPoint3 ℂ).symm
        (h3PreterminalSelectedUnitLaplacianFourierL2OnRadius
          hNS ht hE hTail q i)))

/-- Canonical real physical `L²` reconstruction of the selected Leray forcing. -/
noncomputable def h3PreterminalSelectedUnitLerayForcingPhysicalL2OnRadius
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
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (i : Fin 3) :
    H3ScalarL2 :=
  h3FromFourierRealL2
    (h3RealPartFourierL2
      ((MeasureTheory.Lp.fourierTransformₗᵢ
        H3FourierPoint3 ℂ).symm
        (h3PreterminalSelectedUnitLerayForcingFourierL2OnRadius
          hNS ht hE hTail q i)))

/-- Forward scalar Plancherel recovers the exact selected Fourier Laplacian. -/
theorem h3ScalarFourierL2_h3PreterminalSelectedUnitLaplacianPhysicalL2OnRadius
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
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (i : Fin 3) :
    h3ScalarFourierL2
        (h3PreterminalSelectedUnitLaplacianPhysicalL2OnRadius
          hNS ht hE hTail q i)
      =
    h3PreterminalSelectedUnitLaplacianFourierL2OnRadius
      hNS ht hE hTail q i := by
  unfold h3PreterminalSelectedUnitLaplacianPhysicalL2OnRadius

  exact
    h3ScalarFourierL2_realPhysicalReconstruction_eq_of_hermitian
      (h3PreterminalSelectedUnitLaplacianFourierL2OnRadius
        hNS ht hE hTail q i)
      (h3PreterminalSelectedUnitLaplacianFourierL2OnRadius_hermitian
        hNS ht hE hTail q i)

/-- Forward scalar Plancherel recovers the exact selected Fourier Leray forcing. -/
theorem h3ScalarFourierL2_h3PreterminalSelectedUnitLerayForcingPhysicalL2OnRadius
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
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (i : Fin 3) :
    h3ScalarFourierL2
        (h3PreterminalSelectedUnitLerayForcingPhysicalL2OnRadius
          hNS ht hE hTail q i)
      =
    h3PreterminalSelectedUnitLerayForcingFourierL2OnRadius
      hNS ht hE hTail q i := by
  unfold h3PreterminalSelectedUnitLerayForcingPhysicalL2OnRadius

  exact
    h3ScalarFourierL2_realPhysicalReconstruction_eq_of_hermitian
      (h3PreterminalSelectedUnitLerayForcingFourierL2OnRadius
        hNS ht hE hTail q i)
      (h3PreterminalSelectedUnitLerayForcingFourierL2OnRadius_hermitian
        hNS ht hE hTail q i)

/-- Selected unit-viscosity projected physical RHS coordinate. -/
noncomputable def h3PreterminalSelectedUnitProjectedRHSPhysicalL2OnRadius
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
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (i : Fin 3) :
    H3ScalarL2 :=
  h3PreterminalSelectedUnitLaplacianPhysicalL2OnRadius
      hNS ht hE hTail q i
    -
  h3PreterminalSelectedUnitLerayForcingPhysicalL2OnRadius
      hNS ht hE hTail q i

/-- Bundled selected physical Laplacian. -/
noncomputable def h3PreterminalSelectedUnitLaplacianPhysicalL2HilbertOnRadius
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
    H3PhysicalRealFinVectorL2Hilbert :=
  WithLp.toLp 2
    (fun i : Fin 3 =>
      h3PreterminalSelectedUnitLaplacianPhysicalL2OnRadius
        hNS ht hE hTail q i)

/-- Bundled selected physical Leray forcing. -/
noncomputable def h3PreterminalSelectedUnitLerayForcingPhysicalL2HilbertOnRadius
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
    H3PhysicalRealFinVectorL2Hilbert :=
  WithLp.toLp 2
    (fun i : Fin 3 =>
      h3PreterminalSelectedUnitLerayForcingPhysicalL2OnRadius
        hNS ht hE hTail q i)

/-- Bundled selected unit-viscosity projected physical RHS. -/
noncomputable def h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
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
    H3PhysicalRealFinVectorL2Hilbert :=
  WithLp.toLp 2
    (fun i : Fin 3 =>
      h3PreterminalSelectedUnitProjectedRHSPhysicalL2OnRadius
        hNS ht hE hTail q i)

/-- Exact Hilbert-vector decomposition of the selected unit-viscosity projected
RHS into diffusion minus Leray transport. -/
theorem h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius_eq_laplacian_sub_leray
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
    h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
        hNS ht hE hTail q
      =
    h3PreterminalSelectedUnitLaplacianPhysicalL2HilbertOnRadius
        hNS ht hE hTail q
      -
    h3PreterminalSelectedUnitLerayForcingPhysicalL2HilbertOnRadius
        hNS ht hE hTail q := by
  apply PiLp.ext
  intro i
  rfl

end

end Euclidean
end Bridge
end PrimeTensor
