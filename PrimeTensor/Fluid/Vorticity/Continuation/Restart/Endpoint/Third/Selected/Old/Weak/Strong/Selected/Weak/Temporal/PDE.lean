import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Selected.Weak.Pairing.Bridge

/-!
# Weak spatial form of the canonical selected temporal PDE

The canonical selected restart now has:

* strict-positive pointwise FTC;
* exact pointwise pressure-free temporal PDE;
* physical `L²` velocity and nonlinear weak-pairing bridges.

Before performing any time/space interchange, this file packages the pointwise
PDE under an arbitrary compact smooth vector test.

For every strict positive interior selected time `q`,

    Σᵢ ∫ φᵢ ∂ₜSᵢ
      =
    Σᵢ ∫ φᵢ (ΔSᵢ - Nᵢ(S,S)).

This is deliberately a literal spatial-integral identity.  It uses only
pointwise substitution of the already-proved selected PDE, so no new
integrability, Fubini, endpoint, or quotient argument is introduced.

The next steps can separately identify the diffusion and nonlinear pieces with
the quotient-safe selected physical RHS and then integrate the scalar weak
evolution in time.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongSelectedWeakTemporalPDE
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical selected pointwise temporal PDE integrated against an
arbitrary compact smooth vector test at one strict positive interior restart
time. -/
theorem h3PreterminalSelectedUnitRealVelocity_weakTemporalPairing_eq_spatialRHS
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
    (hq0 : 0 < (q : ℝ))
    (hqR :
      (q : ℝ) <
        h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (φ : H3WeakTestVector) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSelectedRestart
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
            (fun r : ℝ =>
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (W r i) x)
            (q : ℝ))
        ∂volume)
      =
    ∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          ((∑ j : Fin 3,
            spatial3.d
              (h3AxisOfFin3 j)
              (spatial3.d
                (h3AxisOfFin3 j)
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W (q : ℝ) i)))
              x)
            -
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W (q : ℝ))
            (W (q : ℝ))
            i x).re)
        ∂volume := by
  dsimp only

  apply Finset.sum_congr rfl
  intro i hi

  apply integral_congr_ae
  filter_upwards with x

  rw [
    h3PreterminalSelectedUnitRealVelocity_temporal_d_eq_spatialLaplacian_sub_forcing
      hNS ht hE hTail hq0 hqR i x
  ]

end

end Euclidean
end Bridge
end PrimeTensor
