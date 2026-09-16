import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongSelectedWeakLocalEvolution

/-!
# Selected weak projected-RHS pairing

The strict-positive selected weak temporal equation is now available in the
form

    weak temporal derivative = weak diffusion - selected Leray forcing.

The selected physical `L²` projected RHS is already packaged as

    R_sel = L_sel - N_sel.

This file gives the scalar weak RHS a permanent name and records the matching
Hilbert-space decomposition.  Consequently the only remaining representation
seam before the selected weak FTC is

    weak diffusion = <test, L_sel>.

No time integration, endpoint passage, or old-branch input is introduced here.
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

noncomputable local instance axisFintypeH3SelectedOldWeakStrongSelectedWeakProjectedRHSPairing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Scalar selected weak projected-RHS pairing at one restart-radius time. -/
noncomputable def h3PreterminalSelectedUnitWeakProjectedRHSPairingAtRadius
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
    (φ : H3WeakTestVector) : ℝ :=
  h3PreterminalSelectedUnitWeakDiffusionPairingAt
      hNS ht hE hTail (q : ℝ) φ
    -
  inner ℝ
    (h3WeakTestVectorPhysicalL2Hilbert φ)
    (h3PreterminalSelectedUnitLerayForcingPhysicalL2HilbertOnRadius
      hNS ht hE hTail q)

/-- The strict-positive selected temporal weak pairing is exactly the named
selected weak projected-RHS pairing. -/
theorem h3PreterminalSelectedUnitRealVelocity_weakTemporalPairing_eq_weakProjectedRHSPairingAtRadius
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
    h3PreterminalSelectedUnitWeakProjectedRHSPairingAtRadius
      hNS ht hE hTail q φ := by
  dsimp only
  unfold h3PreterminalSelectedUnitWeakProjectedRHSPairingAtRadius
  exact
    h3PreterminalSelectedUnitRealVelocity_weakTemporalPairing_eq_weakDiffusion_sub_leray
      hNS ht hE hTail q hq0 hqR φ

/-- Pairing a compact weak test with the selected physical projected RHS splits
exactly into its physical Laplacian and Leray-forcing pairings. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_selectedUnitProjectedRHS_eq_laplacian_sub_leray
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
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
          hNS ht hE hTail q)
      =
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedUnitLaplacianPhysicalL2HilbertOnRadius
          hNS ht hE hTail q)
      -
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedUnitLerayForcingPhysicalL2HilbertOnRadius
          hNS ht hE hTail q) := by
  rw [
    h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius_eq_laplacian_sub_leray,
    inner_sub_right
  ]

end

end Euclidean
end Bridge
end PrimeTensor
