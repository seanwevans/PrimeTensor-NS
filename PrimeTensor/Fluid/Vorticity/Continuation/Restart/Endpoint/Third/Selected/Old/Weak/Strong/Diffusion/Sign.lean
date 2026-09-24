import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.RHS.Difference

/-!
# Concrete selected--old diffusion dissipation

The selected and old unit-viscosity RHS packages are now aligned in the same
physical `L²` Hilbert space.  This file closes the diffusion half of the
relative-energy estimate.

For one scalar realizable weighted H³ state `G`, the canonical real physical
decoder has scalar Plancherel transform exactly equal to the deweighted raw
Fourier state.  Applying this to the selected restart and combining it with the
existing old-snapshot Fourier identity shows that every coordinate of the
concrete selected-minus-old physical velocity difference has Fourier transform

    raw(U_sel - U_old).

Likewise, the selected-minus-old physical Laplacian difference transforms to

    raw(Δ(U_sel - U_old)).

The previously proved Plancherel diffusion sign theorem then gives

    ⟪D_i, LΔ_i⟫ ≤ 0

for each coordinate, and finite-product Hilbert summation gives

    ⟪D, LΔ⟫ ≤ 0.

No temporal derivative and no endpoint continuity is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongDiffusionSign
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- For a realizable weighted scalar H³ state, the scalar Plancherel transform
of its canonical real physical decoder is exactly its deweighted raw Fourier
state. -/
theorem h3ScalarFourierL2_h3FromFourierRealL2_decodeReal_eq_raw_of_realizable
    {G : H3SpectralScalarState}
    (hG : H3SpectralScalarRealizable G) :
    h3ScalarFourierL2
        (h3FromFourierRealL2
          (h3SpectralScalarDecodeRealL2 G))
      =
    h3SpectralScalarRawFourierL2 G := by
  unfold h3ScalarFourierL2

  rw [h3ToFourierRealL2_h3FromFourierRealL2]

  have h :=
    congrArg
      (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
      hG

  rw [h3Fourier_h3SpectralScalarDecodeComplexL2] at h

  exact h.symm

/-- One selected unit-viscosity physical velocity coordinate transforms exactly
to the raw Fourier state of the corresponding selected weighted H³ component. -/
theorem h3ScalarFourierL2_h3PreterminalSelectedUnitVelocityPhysicalL2OnRadius
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
        ((h3PreterminalSelectedVelocityPhysicalL2HilbertAt
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail (q : ℝ)) i)
      =
    h3SpectralScalarRawFourierL2
      ((h3PreterminalSelectedUnitSpectralStateOnRadius
        hNS ht hE hTail q) i) := by
  unfold
    h3PreterminalSelectedVelocityPhysicalL2HilbertAt
    h3PreterminalSelectedUnitSpectralStateOnRadius

  apply
    h3ScalarFourierL2_h3FromFourierRealL2_decodeReal_eq_raw_of_realizable

  exact
    h3SpectralScalarRawHermitian_realizable
      ((h3PreterminalSelectedPhysicalExtension_rawHermitian
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail q) i)

/-- Fourier representation of one coordinate of the concrete unit-viscosity
selected-minus-old physical velocity difference. -/
theorem h3ScalarFourierL2_h3PreterminalSelectedOldUnitVelocityDifferenceOnElapsed
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
    (i : Fin 3) :
    h3ScalarFourierL2
        ((h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q) i)
      =
    h3SpectralScalarRawFourierL2
      ((h3PreterminalSelectedUnitSpectralStateOnRadius
          hNS ht hE hTail
          (h3PreterminalElapsedToSelectedUnitRadius htauR q)) i
        -
       (h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q) i) := by
  have hSelected :=
    h3ScalarFourierL2_h3PreterminalSelectedUnitVelocityPhysicalL2OnRadius
      hNS ht hE hTail
      (h3PreterminalElapsedToSelectedUnitRadius htauR q)
      i

  have hOldVector :=
    h3PhysicalRealFinVectorL2HilbertRawFourier_velocityOnElapsed_eq_deweightedSpectral
      hNS ht hEnd hTail q

  have hOld :=
    congrFun hOldVector i

  unfold
    h3PhysicalRealFinVectorL2HilbertRawFourier
    at hOld

  unfold
    h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed

  simp only [PiLp.sub_apply]

  have hSelected' :
      h3ScalarFourierL2
          ((h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail (q : ℝ)) i)
        =
      h3SpectralScalarRawFourierL2
        ((h3PreterminalSelectedUnitSpectralStateOnRadius
          hNS ht hE hTail
          (h3PreterminalElapsedToSelectedUnitRadius htauR q)) i) := by
    simpa only [
      h3PreterminalElapsedToSelectedUnitRadius_coe
    ] using hSelected

  rw [
    h3ScalarFourierL2_sub,
    hSelected',
    hOld,
    ← h3SpectralScalarRawFourierL2_sub
  ]

/-- Fourier representation of one coordinate of the concrete selected-minus-old
physical Laplacian difference. -/
theorem h3ScalarFourierL2_h3PreterminalSelectedOldUnitLaplacianDifferenceOnElapsed
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
    (i : Fin 3) :
    h3ScalarFourierL2
        ((h3PreterminalSelectedOldUnitLaplacianDifferenceOnElapsed
          hNS ht hEnd hE hTail htauR q) i)
      =
    h3SpectralScalarLaplacianRawFourierL2
      ((h3PreterminalSelectedUnitSpectralStateOnRadius
          hNS ht hE hTail
          (h3PreterminalElapsedToSelectedUnitRadius htauR q)) i
        -
       (h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q) i) := by
  unfold
    h3PreterminalSelectedOldUnitLaplacianDifferenceOnElapsed
    h3PreterminalSelectedUnitLaplacianPhysicalL2HilbertOnRadius
    h3PreterminalTailCanonicalOldLaplacianPhysicalL2HilbertOnElapsed

  simp only [PiLp.sub_apply]

  rw [
    h3ScalarFourierL2_sub,
    h3ScalarFourierL2_h3PreterminalSelectedUnitLaplacianPhysicalL2OnRadius,
    h3ScalarFourierL2_h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed,
    h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed_eq_snapshotLaplacian
  ]

  unfold h3PreterminalSelectedUnitLaplacianFourierL2OnRadius

  exact
    (h3SpectralScalarLaplacianRawFourierL2_sub
      ((h3PreterminalSelectedUnitSpectralStateOnRadius
        hNS ht hE hTail
        (h3PreterminalElapsedToSelectedUnitRadius htauR q)) i)
      ((h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q) i)).symm

/-- Each coordinate of the concrete selected-minus-old velocity difference has
nonpositive pairing with the corresponding Laplacian difference. -/
theorem h3PreterminalSelectedOldUnitDiffusionCoordinate_inner_nonpos
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
    (i : Fin 3) :
    inner ℝ
        ((h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q) i)
        ((h3PreterminalSelectedOldUnitLaplacianDifferenceOnElapsed
          hNS ht hEnd hE hTail htauR q) i)
      ≤ 0 := by
  let G : H3SpectralScalarState :=
    (h3PreterminalSelectedUnitSpectralStateOnRadius
        hNS ht hE hTail
        (h3PreterminalElapsedToSelectedUnitRadius htauR q)) i
      -
    (h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q) i

  apply
    h3ScalarL2_inner_nonpos_of_fourier_eq_raw_laplacian
      ((h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail q) i)
      ((h3PreterminalSelectedOldUnitLaplacianDifferenceOnElapsed
        hNS ht hEnd hE hTail htauR q) i)
      G

  · dsimp only [G]
    exact
      h3ScalarFourierL2_h3PreterminalSelectedOldUnitVelocityDifferenceOnElapsed
        hNS ht hEnd hE hTail htauR q i

  · dsimp only [G]
    exact
      h3ScalarFourierL2_h3PreterminalSelectedOldUnitLaplacianDifferenceOnElapsed
        hNS ht hEnd hE hTail htauR q i

/-- Concrete vector diffusion dissipation for the selected-minus-old
unit-viscosity difference. -/
theorem h3PreterminalSelectedOldUnitDiffusion_inner_nonpos
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
    inner ℝ
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q)
        (h3PreterminalSelectedOldUnitLaplacianDifferenceOnElapsed
          hNS ht hEnd hE hTail htauR q)
      ≤ 0 := by
  apply
    h3PhysicalRealFinVectorL2_inner_nonpos_of_coordinate_nonpos

  intro i

  exact
    h3PreterminalSelectedOldUnitDiffusionCoordinate_inner_nonpos
      hNS ht hEnd hE hTail htauR q i

end

end Euclidean
end Bridge
end PrimeTensor
