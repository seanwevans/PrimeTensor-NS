import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.Laplacian.CLM
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Spectral.Heat.Generator

/-!
# Physical L² temporal admissibility: heat-generator representative in raw Fourier L²

The quotient-safe heat generator has now been packaged as a Bochner-integrable
raw Fourier `L²` path, and the weighted-H³-to-raw-`L²` Laplacian is available
as a continuous linear map.

For the differentiability step we still need one exact bridge to the scalar
heat-symbol calculus.  This file identifies the a.e. representative of

    ν • S(s) Δ̂_L² G

with the already-proved pointwise time-generator multiplier

    (∂ₛ m)(s,ξ) raw(G)(ξ).

The result remains an equality of `L²` representatives a.e.; no fixed
frequency is selected.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2HeatGeneratorRepresentative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The viscosity-scaled heat orbit of one quotient-safe Laplacian coordinate
has the exact heat time-generator multiplier as an a.e. representative. -/
theorem h3HeatGeneratorRawFourierL2_ae
    {ν s : ℝ}
    (hν : 0 ≤ ν)
    (hs : 0 ≤ s)
    (G : H3SpectralScalarState) :
    (((ν : ℝ) •
        h3HeatFrequencyApplyNN
          ν hν (NNReal.mk s hs)
          (h3SpectralScalarLaplacianRawFourierL2 G) :
        H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ =>
      h3HeatFourierTimeGeneratorSymbol ν s ξ *
        h3SpectralScalarRawFourierL2 G ξ) := by
  have hHeat :=
    h3HeatFrequencyApplyNN_coeFn
      ν hν (NNReal.mk s hs)
      (h3SpectralScalarLaplacianRawFourierL2 G)

  have hLap :=
    h3SpectralScalarLaplacianRawFourierL2_ae_eq_gradientSquare_mul_raw
      G

  have hSmul :=
    MeasureTheory.Lp.coeFn_smul
      (ν : ℝ)
      (h3HeatFrequencyApplyNN
        ν hν (NNReal.mk s hs)
        (h3SpectralScalarLaplacianRawFourierL2 G))

  filter_upwards [hHeat, hLap, hSmul] with
      ξ hHeatξ hLapξ hSmulξ

  simp only [Pi.smul_apply] at hSmulξ
  rw [hSmulξ, hHeatξ, hLapξ]
  rw [h3HeatFourierTimeGeneratorSymbol_eq]
  rw [Complex.real_smul]
  push_cast
  ring

/-- Coordinate form of the full vector heat-generator RHS on a nonnegative
elapsed slice. -/
theorem h3RawFourierL2HeatGeneratorRHSReal_apply_ae_of_nonneg
    {ν s : ℝ}
    (hν : 0 ≤ ν)
    (hs : 0 ≤ s)
    (U : H3SpectralFinVectorState)
    (i : Fin 3) :
    (((h3RawFourierL2HeatGeneratorRHSReal
          ν hν U s) i :
        H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ =>
      h3HeatFourierTimeGeneratorSymbol ν s ξ *
        h3SpectralScalarRawFourierL2 (U i) ξ) := by
  rw [
    h3RawFourierL2HeatGeneratorRHSReal_of_nonneg
      hν hs U
  ]

  exact
    h3HeatGeneratorRawFourierL2_ae
      hν hs (U i)

end

end Euclidean
end Bridge
end PrimeTensor
