import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongSelectedWeakDiffusionTransfer

/-!
# Selected weak forcing transfer

The selected weak temporal PDE is written with the literal continuous physical
representative of the Leray-projected nonlinear forcing,

    Re (P div(S \otimes S))_i.

The weak--strong physical layer stores exactly the same object as the
quotient-safe real physical `L²` vector

    h3PreterminalSelectedUnitLerayForcingPhysicalL2HilbertOnRadius.

This file closes that representation seam directly, without first replacing
the projected forcing by ordinary advection.  The generic physical forcing
package already has the continuous C0 forcing representative almost
everywhere, so the proof is only:

* identify the selected forcing package with the generic package at the
  selected spectral slice;
* expand the `PiLp 2` inner product coordinatewise;
* replace each physical `L²` coordinate by its C0 representative a.e.;
* normalize the two names for the canonical selected anchor.

No divergence-free hypothesis is needed for this representation theorem.
Pressure cancellation is therefore kept separate from the quotient bridge.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

attribute [local instance]
  point3MeasureSpaceH3SelectedOldWeakStrongGenericWeakForcingAdvection

noncomputable local instance axisFintypeH3SelectedOldWeakStrongSelectedWeakForcingTransfer
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The selected physical Leray-forcing Hilbert pairing is exactly the literal
compact-test pairing with the continuous forcing representative used by the
selected pointwise PDE. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_selectedUnitLerayForcing_eq_literalC0
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
    (φ : H3WeakTestVector) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSelectedRestart
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedUnitLerayForcingPhysicalL2HilbertOnRadius
          hNS ht hE hTail q)
      =
    ∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W (q : ℝ))
            (W (q : ℝ))
            i x).re)
        ∂volume := by
  dsimp only

  let U : H3SpectralFinVectorState :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht hE hTail q

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  have hUW : U = W (q : ℝ) := by
    dsimp only [U, W]
    unfold
      h3PreterminalSelectedUnitSpectralStateOnRadius
      h3PreterminalTailCanonicalSelectedRestart
      h3PreterminalSelectedDecoderAnchorState
      h3PreterminalTailCanonicalAnchorSpectralState
    rfl

  calc
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedUnitLerayForcingPhysicalL2HilbertOnRadius
          hNS ht hE hTail q)
        =
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3WeakStrongLerayForcingPhysicalL2Hilbert U) := by
          rw [
            h3WeakStrongLerayForcingPhysicalL2Hilbert_selectedUnit_eq
              hNS ht hE hTail q
          ]
    _ =
      ∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              U U i x).re)
          ∂volume := by
            unfold
              h3WeakTestVectorPhysicalL2Hilbert
              h3WeakStrongLerayForcingPhysicalL2Hilbert

            rw [PiLp.inner_apply]

            apply Finset.sum_congr rfl
            intro i hi

            rw [h3WeakTestFunctionPhysicalL2_inner_eq_integral]

            apply integral_congr_ae

            have hAE :=
              h3WeakStrongLerayForcingPhysicalL2_ae U i

            filter_upwards [hAE] with x hx

            rw [hx]
    _ =
      ∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W (q : ℝ))
              (W (q : ℝ))
              i x).re)
          ∂volume := by
            rw [hUW]

end

end Euclidean
end Bridge
end PrimeTensor
