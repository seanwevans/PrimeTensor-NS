import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.Heat.Generator.Orbit

/-!
# Physical L² temporal admissibility: Fourier L² heat generator integral

For the heat equation the time generator is `ν Δ`.  The preceding file
packages the quotient-safe raw Fourier `L²` orbit

    s ↦ S(s) Δ̂_L² U

and proves that it is strongly continuous and Bochner interval-integrable.

This file inserts the viscosity scalar and packages the resulting Bochner
integral

    ∫₀ᵗ ν • S(s) Δ̂_L² U ds.

The construction remains entirely in the raw Fourier `L²` quotient.  It is
the right-hand side of the forthcoming integrated heat-generator identity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2HeatGeneratorIntegral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Real-time quotient-safe heat-generator path, including the viscosity
scalar. -/
noncomputable def h3RawFourierL2HeatGeneratorRHSReal
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (U : H3SpectralFinVectorState)
    (s : ℝ) :
    H3RawFourierL2FinVectorState :=
  ν • h3RawFourierL2HeatGeneratorOrbitReal ν hν U s

/-- The viscosity-scaled generator path is strongly continuous. -/
theorem continuous_h3RawFourierL2HeatGeneratorRHSReal
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (U : H3SpectralFinVectorState) :
    Continuous
      (h3RawFourierL2HeatGeneratorRHSReal ν hν U) := by
  unfold h3RawFourierL2HeatGeneratorRHSReal

  have hScalar :
      Continuous (fun _ : ℝ => (ν : ℝ)) :=
    continuous_const

  have hOrbit :
      Continuous
        (h3RawFourierL2HeatGeneratorOrbitReal ν hν U) :=
    continuous_h3RawFourierL2HeatGeneratorOrbitReal
      ν hν U

  exact hScalar.smul hOrbit

/-- Hence the viscosity-scaled generator path is Bochner
interval-integrable on every finite interval. -/
theorem h3RawFourierL2HeatGeneratorRHSReal_intervalIntegrable
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (U : H3SpectralFinVectorState)
    (a b : ℝ) :
    IntervalIntegrable
      (h3RawFourierL2HeatGeneratorRHSReal ν hν U)
      volume
      a
      b := by
  apply ContinuousOn.intervalIntegrable
  exact
    (continuous_h3RawFourierL2HeatGeneratorRHSReal
      ν hν U).continuousOn

/-- Bochner integral of the quotient-safe heat generator from elapsed zero to
real time `t`. -/
noncomputable def h3RawFourierL2HeatGeneratorIntegral
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (U : H3SpectralFinVectorState)
    (t : ℝ) :
    H3RawFourierL2FinVectorState :=
  ∫ s in (0 : ℝ)..t,
    h3RawFourierL2HeatGeneratorRHSReal ν hν U s

@[simp]
theorem h3RawFourierL2HeatGeneratorIntegral_zero
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (U : H3SpectralFinVectorState) :
    h3RawFourierL2HeatGeneratorIntegral ν hν U 0
      =
    0 := by
  unfold h3RawFourierL2HeatGeneratorIntegral
  simp

/-- On a nonnegative elapsed interval, the integrand can be written directly
with the original nonnegative-time heat orbit. -/
theorem h3RawFourierL2HeatGeneratorRHSReal_of_nonneg
    {ν s : ℝ}
    (hν : 0 ≤ ν)
    (hs : 0 ≤ s)
    (U : H3SpectralFinVectorState) :
    h3RawFourierL2HeatGeneratorRHSReal ν hν U s
      =
    ν •
      h3RawFourierL2HeatGeneratorOrbitNN
        ν hν U (NNReal.mk s hs) := by
  unfold h3RawFourierL2HeatGeneratorRHSReal
  rw [
    h3RawFourierL2HeatGeneratorOrbitReal_of_nonneg
      hν hs U
  ]

end

end Euclidean
end Bridge
end PrimeTensor
