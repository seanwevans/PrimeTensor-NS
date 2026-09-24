import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Selected.Weak.Projected.RHS.Pairing

/-!
# Reduce the selected physical weak RHS bridge to diffusion

The selected strict-positive weak temporal equation is already packaged as

    weak temporal pairing = weak projected-RHS pairing,

and the selected physical projected RHS is already decomposed as

    R_sel = L_sel - N_sel.

The nonlinear term is therefore fully aligned.  This file records that the
only remaining representation statement needed to identify the selected weak
temporal derivative with the physical `L²` projected RHS is

    weak diffusion = <test, L_sel>.

No endpoint passage, time integration, or old-branch input is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongSelectedWeakProjectedRHSPhysicalReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Once the selected weak diffusion pairing is identified with the physical
selected Laplacian pairing, the named weak projected-RHS pairing is exactly the
physical selected projected-RHS Hilbert pairing. -/
theorem h3PreterminalSelectedUnitWeakProjectedRHSPairingAtRadius_eq_inner_projectedRHS_of_diffusion
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
    (φ : H3WeakTestVector)
    (hDiffusion :
      h3PreterminalSelectedUnitWeakDiffusionPairingAt
          hNS ht hE hTail (q : ℝ) φ
        =
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedUnitLaplacianPhysicalL2HilbertOnRadius
          hNS ht hE hTail q)) :
    h3PreterminalSelectedUnitWeakProjectedRHSPairingAtRadius
        hNS ht hE hTail q φ
      =
    inner ℝ
      (h3WeakTestVectorPhysicalL2Hilbert φ)
      (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
        hNS ht hE hTail q) := by
  unfold h3PreterminalSelectedUnitWeakProjectedRHSPairingAtRadius
  rw [hDiffusion]

  symm

  exact
    inner_h3WeakTestVectorPhysicalL2Hilbert_selectedUnitProjectedRHS_eq_laplacian_sub_leray
      hNS ht hE hTail q φ

/-- Strict-positive selected weak temporal evolution is already the physical
projected-RHS pairing once the single diffusion representation seam is
supplied. -/
theorem h3PreterminalSelectedUnitRealVelocity_weakTemporalPairing_eq_inner_projectedRHS_of_diffusion
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
    (φ : H3WeakTestVector)
    (hDiffusion :
      h3PreterminalSelectedUnitWeakDiffusionPairingAt
          hNS ht hE hTail (q : ℝ) φ
        =
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedUnitLaplacianPhysicalL2HilbertOnRadius
          hNS ht hE hTail q)) :
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
    inner ℝ
      (h3WeakTestVectorPhysicalL2Hilbert φ)
      (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
        hNS ht hE hTail q) := by
  dsimp only

  calc
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
            (fun r : ℝ =>
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (h3PreterminalTailCanonicalSelectedRestart
                  (one_pos : (0 : ℝ) < 1)
                  hNS ht hE hTail r i) x)
            (q : ℝ))
        ∂volume)
        =
      h3PreterminalSelectedUnitWeakProjectedRHSPairingAtRadius
        hNS ht hE hTail q φ := by
          exact
            h3PreterminalSelectedUnitRealVelocity_weakTemporalPairing_eq_weakProjectedRHSPairingAtRadius
              hNS ht hE hTail q hq0 hqR φ
    _ =
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
          hNS ht hE hTail q) := by
          exact
            h3PreterminalSelectedUnitWeakProjectedRHSPairingAtRadius_eq_inner_projectedRHS_of_diffusion
              hNS ht hE hTail q φ hDiffusion

end

end Euclidean
end Bridge
end PrimeTensor
