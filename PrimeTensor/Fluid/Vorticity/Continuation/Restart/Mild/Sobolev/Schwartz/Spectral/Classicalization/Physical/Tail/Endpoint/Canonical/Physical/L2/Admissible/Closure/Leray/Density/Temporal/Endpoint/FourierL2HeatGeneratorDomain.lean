import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.FourierL2HeatSemigroup

/-!
# Physical L² temporal admissibility: Fourier L² heat generator domain

The raw Fourier `L²` heat semigroup is now available without choosing
frequency representatives.  The next issue is the unbounded heat generator:
the Laplacian is not a bounded operator on arbitrary raw `L²`.

The weighted H³ spectral state supplies a convenient generator domain.  The
already-defined map

    G ↦ Δ̂_L² G

lands in raw Fourier `L²`, with multiplier `-q / W₃` on the weighted state.
Because both heat evolution and the Laplacian are scalar Fourier multipliers,
they commute exactly on this H³ domain.

This file records that commutation first for one scalar coordinate and then
for the three-component velocity state.  No pointwise representative is
selected: equality is proved in the `L²` quotient using the existing a.e.
multiplier interfaces.

This is the algebraic input for the forthcoming integrated generator identity

    S(t) raw(G) - raw(G) = ν ∫₀ᵗ S(s) Δ̂_L²(G) ds,

which can then be applied to the endpoint Fourier `L²` integral equation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2HeatGeneratorDomain
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Heat evolution of the raw Fourier Laplacian equals the raw Fourier
Laplacian of the weighted heat evolution.  This is the scalar generator-domain
invariance statement. -/
theorem h3HeatFrequencyApplyNN_laplacianRawFourierL2
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (G : H3SpectralScalarState) :
    h3HeatFrequencyApplyNN ν hν t
        (h3SpectralScalarLaplacianRawFourierL2 G)
      =
    h3SpectralScalarLaplacianRawFourierL2
      (h3SpectralScalarHeatApplyNN ν hν t G) := by
  apply MeasureTheory.Lp.ext

  have hLeft :=
    h3HeatFrequencyApplyNN_coeFn
      ν hν t
      (h3SpectralScalarLaplacianRawFourierL2 G)

  have hLapG :=
    h3SpectralScalarLaplacianRawFourierL2_ae G

  have hRight :=
    h3SpectralScalarLaplacianRawFourierL2_ae
      (h3SpectralScalarHeatApplyNN ν hν t G)

  have hHeatG :
      ∀ᵐ ξ : H3FourierPoint3 ∂volume,
        h3SpectralScalarHeatApplyNN ν hν t G ξ
          =
        h3HeatFourierSymbol ν (t : ℝ) ξ * G ξ := by
    simpa only [h3SpectralScalarHeatApplyNN] using
      (h3HeatFrequencyApplyNN_coeFn ν hν t G)

  filter_upwards [hLeft, hLapG, hRight, hHeatG] with
      ξ hLeftξ hLapGξ hRightξ hHeatGξ

  rw [hLeftξ, hLapGξ, hRightξ, hHeatGξ]
  ring

/-- Coordinatewise raw Fourier Laplacian of a weighted H³ velocity state. -/
noncomputable def h3SpectralFinVectorLaplacianRawFourierL2
    (U : H3SpectralFinVectorState) :
    H3RawFourierL2FinVectorState :=
  fun i : Fin 3 =>
    h3SpectralScalarLaplacianRawFourierL2 (U i)

@[simp]
theorem h3SpectralFinVectorLaplacianRawFourierL2_apply
    (U : H3SpectralFinVectorState)
    (i : Fin 3) :
    h3SpectralFinVectorLaplacianRawFourierL2 U i
      =
    h3SpectralScalarLaplacianRawFourierL2 (U i) :=
  rfl

/-- The weighted H³ generator domain is invariant under heat evolution:
deweighted Laplacian and raw Fourier `L²` heat commute exactly. -/
theorem h3SpectralFinVectorLaplacianRawFourierL2_heatApplyNN
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (U : H3SpectralFinVectorState) :
    h3SpectralFinVectorLaplacianRawFourierL2
        (h3SpectralVelocityHeatApplyNN ν hν t U)
      =
    h3RawFourierL2HeatApplyNN ν hν t
      (h3SpectralFinVectorLaplacianRawFourierL2 U) := by
  funext i
  exact
    (h3HeatFrequencyApplyNN_laplacianRawFourierL2
      ν hν t (U i)).symm

/-- Equivalent orientation: applying the raw heat semigroup to generator data
is the same as taking the Laplacian after weighted heat evolution. -/
theorem h3RawFourierL2HeatApplyNN_laplacianRawFourierL2
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (U : H3SpectralFinVectorState) :
    h3RawFourierL2HeatApplyNN ν hν t
        (h3SpectralFinVectorLaplacianRawFourierL2 U)
      =
    h3SpectralFinVectorLaplacianRawFourierL2
      (h3SpectralVelocityHeatApplyNN ν hν t U) := by
  exact
    (h3SpectralFinVectorLaplacianRawFourierL2_heatApplyNN
      ν hν t U).symm

end

end Euclidean
end Bridge
end PrimeTensor
