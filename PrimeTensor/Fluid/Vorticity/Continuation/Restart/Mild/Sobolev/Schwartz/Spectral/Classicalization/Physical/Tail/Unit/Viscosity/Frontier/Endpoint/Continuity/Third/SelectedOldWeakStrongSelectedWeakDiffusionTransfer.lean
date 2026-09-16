import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongSelectedWeakTemporalPDE
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Diffusion.Pairing
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Spatial.Regularity

/-!
# Selected weak diffusion transfer

The selected weak temporal PDE is currently written with the literal spatial
Laplacian of the canonical selected restart.  The physical weak--strong layer,
however, stores the selected velocity in the quotient-safe physical `L²`
decoder.

This file closes that seam without constructing any strong time derivative.

First, the two selected anchor names are normalized:

* `h3PreterminalTailCanonicalAnchorSpectralState`;
* `h3PreterminalSelectedDecoderAnchorState`.

Both unfold to exactly the same canonical spectral state.  Hence the selected
physical `L²` velocity decoder has the `W(q)` classical representative used by
the pointwise PDE.

Second, for a positive selected time we use the already-proved spatial `C³`
regularity and the generic compact-test twofold integration-by-parts theorem to
move every pure second derivative from the selected velocity onto the compact
test.

Thus the literal selected diffusion pairing is represented entirely by
zeroth-order selected physical `L²` velocity pairings.

No old-path temporal regularity, old endpoint continuity, or selected--old
agreement is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongSelectedWeakDiffusionTransfer
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldWeakStrongSelectedWeakDiffusionTransfer :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The quotient-safe selected velocity coordinate is represented by the exact
canonical-tail selected restart scalar representative used in the temporal
PDE. -/
theorem h3PreterminalSelectedVelocityPhysicalL2HilbertAt_coordinate_ae_tailCanonicalSelectedRestart
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSelectedRestart
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    (fun x : Point3 =>
      ((h3PreterminalSelectedVelocityPhysicalL2HilbertAt
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail q) i : H3ScalarL2) x)
      =ᵐ[(volume : Measure Point3)]
    h3SpectralScalarRealC1RepresentativeOnPoint3
      (W q i) := by
  dsimp only

  have hAE :=
    h3PreterminalSelectedVelocityPhysicalL2HilbertAt_coordinate_ae_selectedWeakStrong
      (q := q)
      hNS ht hE hTail i

  simpa only [
    h3PreterminalTailCanonicalSelectedRestart,
    h3PreterminalTailCanonicalAnchorSpectralState,
    h3PreterminalSelectedDecoderAnchorState,
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
    h3SpectralRealVelocityOfPath_component_h3AxisOfFin3,
    h3SpectralVelocityRealC1RepresentativeOnPoint3
  ] using hAE

/-- Scalar compact-test pairing with one selected physical `L²` velocity
coordinate equals the literal pairing with the canonical-tail selected
classical representative. -/
theorem h3WeakTestFunctionPhysicalL2_inner_selectedVelocity_eq_tailCanonical
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSelectedRestart
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    inner ℝ
        (h3WeakTestFunctionPhysicalL2 ψ)
        ((h3PreterminalSelectedVelocityPhysicalL2HilbertAt
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail q) i)
      =
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (W q i) x)
      ∂volume := by
  dsimp only

  rw [h3WeakTestFunctionPhysicalL2_inner_eq_integral]

  apply integral_congr_ae

  filter_upwards [
    h3PreterminalSelectedVelocityPhysicalL2HilbertAt_coordinate_ae_tailCanonicalSelectedRestart
      (q := q)
      hNS ht hE hTail i
  ] with x hx

  rw [hx]

/-- Selected weak diffusion pairing at one elapsed time, written only with the
zeroth-order quotient-safe physical `L²` selected velocity. -/
noncomputable def h3PreterminalSelectedUnitWeakDiffusionPairingAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : ℝ)
    (φ : H3WeakTestVector) : ℝ :=
  ∑ i : Fin 3,
    ∑ k : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSecondSpatialDerivative
            (h3AxisOfFin3 k)
            (φ i)))
        ((h3PreterminalSelectedVelocityPhysicalL2HilbertAt
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail q) i)

/-- At every strict positive selected time, the literal selected Laplacian
pairing is exactly the quotient-safe weak diffusion pairing obtained by moving
both spatial derivatives onto the compact test. -/
theorem h3PreterminalSelectedUnitLiteralLaplacianPairing_eq_weakDiffusionPairing
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
    (φ : H3WeakTestVector) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSelectedRestart
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (∑ k : Fin 3,
            spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W (q : ℝ) i)))
              x)
        ∂volume)
      =
    h3PreterminalSelectedUnitWeakDiffusionPairingAt
      hNS ht hE hTail (q : ℝ) φ := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  unfold h3PreterminalSelectedUnitWeakDiffusionPairingAt

  apply Finset.sum_congr rfl
  intro i hi

  have hC3 :
      SpatialC3
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (W (q : ℝ) i)) := by
    unfold SpatialC3
    dsimp only [W]
    unfold h3PreterminalTailCanonicalSelectedRestart

    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_velocityRealC1RepresentativeOnPoint3_contDiff_three
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalTailCanonicalAnchorSpectralState
          hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
          hNS ht hE hTail)
        hq0
        q.property.2
        i

  have hC2 :
      SpatialC2
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (W (q : ℝ) i)) :=
    hC3.toSpatialC2

  have hTerm
      (k : Fin 3) :
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (spatial3.d
            (h3AxisOfFin3 k)
            (spatial3.d
              (h3AxisOfFin3 k)
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (W (q : ℝ) i)))
            x)
        ∂volume)
        =
      inner ℝ
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSecondSpatialDerivative
            (h3AxisOfFin3 k)
            (φ i)))
        ((h3PreterminalSelectedVelocityPhysicalL2HilbertAt
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail (q : ℝ)) i) := by
    have hTransfer :=
      h3SpatialC2_test_pairing_secondSpatialDerivative_eq_testSecondDerivative_pairing
        hC2
        (h3AxisOfFin3 k)
        (φ i)

    have hInner :=
      h3WeakTestFunctionPhysicalL2_inner_selectedVelocity_eq_tailCanonical
        (q := (q : ℝ))
        hNS ht hE hTail
        (h3WeakTestFunctionSecondSpatialDerivative
          (h3AxisOfFin3 k)
          (φ i))
        i

    exact hTransfer.trans hInner.symm

  have hInt
      (k : Fin 3) :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W (q : ℝ) i)))
              x))
        (volume : Measure Point3) :=
    h3SpatialC2_test_mul_secondSpatialDerivative_integrable
      hC2
      (h3AxisOfFin3 k)
      (φ i)

  calc
    (∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ i x)
        (∑ k : Fin 3,
          spatial3.d
            (h3AxisOfFin3 k)
            (spatial3.d
              (h3AxisOfFin3 k)
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (W (q : ℝ) i)))
            x)
      ∂volume)
        =
      ∫ x : Point3,
        ∑ k : Fin 3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W (q : ℝ) i)))
              x)
        ∂volume := by
          apply integral_congr_ae
          filter_upwards with x
          change
            (φ i x) *
                (∑ k : Fin 3,
                  spatial3.d
                    (h3AxisOfFin3 k)
                    (spatial3.d
                      (h3AxisOfFin3 k)
                      (h3SpectralScalarRealC1RepresentativeOnPoint3
                        (W (q : ℝ) i)))
                    x)
              =
            ∑ k : Fin 3,
              (φ i x) *
                spatial3.d
                  (h3AxisOfFin3 k)
                  (spatial3.d
                    (h3AxisOfFin3 k)
                    (h3SpectralScalarRealC1RepresentativeOnPoint3
                      (W (q : ℝ) i)))
                  x
          rw [Finset.mul_sum]
    _ =
      ∑ k : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W (q : ℝ) i)))
              x)
          ∂volume := by
            exact
              integral_finsetSum
                (Finset.univ : Finset (Fin 3))
                (fun k _ => hInt k)
    _ =
      ∑ k : Fin 3,
        inner ℝ
          (h3WeakTestFunctionPhysicalL2
            (h3WeakTestFunctionSecondSpatialDerivative
              (h3AxisOfFin3 k)
              (φ i)))
          ((h3PreterminalSelectedVelocityPhysicalL2HilbertAt
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail (q : ℝ)) i) := by
              apply Finset.sum_congr rfl
              intro k hk
              exact hTerm k

end

end Euclidean
end Bridge
end PrimeTensor
