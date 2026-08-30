import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PreterminalSelectedIncompressibility
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.Bridge

/-!
# Raw Fourier incompressibility of the selected H³ restart

The heat--Leray solver evolves the weighted H³ state

    G_j(ξ) = W₃(ξ) * û_j(ξ).

`PreterminalSelectedIncompressibility` proves that the actual canonical
selected restart is divergence-free in this weighted representation:

    Σ_j d_j(ξ) G_j(ξ) = 0.

The inverse-Fourier reconstruction layer, however, differentiates the genuine
raw Fourier velocity

    û_j(ξ) = W₃(ξ)⁻¹ * G_j(ξ).

Because the inverse H³ weight is a single scalar common to all three
coordinates, divergence-freeness passes immediately from `G` to the raw
Fourier field.

This file isolates that deweighting step.  The next physical reconstruction
theorem can therefore start from exactly

    Σ_j d_j(ξ) û_j(ξ) = 0

for the selected state, with no weighted-spectral algebra left to discharge.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3SelectedRawFourierIncompressibility
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Raw, deweighted Fourier divergence-freeness of a three-component H³
spectral state. -/
def H3SpectralFinRawDivergenceFree
    (G : H3SpectralFinVectorState) : Prop :=
  ∀ᵐ ξ ∂volume,
    (∑ j : Fin 3,
      h3FourierDerivativeSymbol j ξ *
        h3SpectralScalarRawFourier (G j) ξ)
      =
    0

/-- Weighted H³ Fourier divergence-freeness implies raw Fourier
incompressibility after removing the common scalar Sobolev weight. -/
theorem h3SpectralFinRawDivergenceFree_of_divergenceFree
    {G : H3SpectralFinVectorState}
    (hG : H3SpectralFinDivergenceFree G) :
    H3SpectralFinRawDivergenceFree G := by
  filter_upwards [hG] with ξ hDiv

  calc
    (∑ j : Fin 3,
      h3FourierDerivativeSymbol j ξ *
        h3SpectralScalarRawFourier (G j) ξ)
        =
      h3SobolevFrequencyWeightInvComplex ξ *
        (∑ j : Fin 3,
          h3FourierDerivativeSymbol j ξ *
            (G j : H3FourierPoint3 → ℂ) ξ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          unfold h3SpectralScalarRawFourier
          ring
    _ = 0 := by
      rw [hDiv, mul_zero]

/-- The canonical selected restart launched from retained preterminal H³ data
has raw Fourier divergence zero throughout the full restart interval. -/
theorem h3PreterminalTailCanonicalSelectedRestart_rawDivergenceFree
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    {s : ℝ}
    (hs0 : 0 ≤ s)
    (hsR : s ≤ h3FinHeatLerayRestartRadius ν E) :
    H3SpectralFinRawDivergenceFree
      (h3PreterminalTailCanonicalSelectedRestart
        hν hNS ht hE hTail s) := by
  exact
    h3SpectralFinRawDivergenceFree_of_divergenceFree
      (h3PreterminalTailCanonicalSelectedRestart_divergenceFree
        hν hNS ht hE hTail hs0 hsR)

/-- Positive half-open restart-window form used by the selected smooth
inverse-Fourier representative. -/
theorem h3PreterminalTailCanonicalSelectedRestart_rawDivergenceFreeOn_Ioc
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    ∀ s : ℝ,
      s ∈ Set.Ioc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius ν E) →
      H3SpectralFinRawDivergenceFree
        (h3PreterminalTailCanonicalSelectedRestart
          hν hNS ht hE hTail s) := by
  intro s hs

  exact
    h3PreterminalTailCanonicalSelectedRestart_rawDivergenceFree
      hν hNS ht hE hTail
      hs.1.le
      hs.2

end
end Euclidean
end Bridge
end PrimeTensor
