import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.FourierL2HeatGeneratorDomain

/-!
# Physical L² temporal admissibility: Fourier L² heat generator orbit

The quotient-safe heat semigroup now preserves the weighted H³ generator
domain and commutes there with the raw Fourier `L²` Laplacian.

Before proving the integrated generator identity, this file packages the
resulting generator orbit

    s ↦ S(s) Δ̂_L² U

as a strongly continuous raw Fourier `L²` path.  A real-time wrapper through
`Real.toNNReal` is then continuous on all of `ℝ`, hence Bochner
interval-integrable on every finite interval.

This isolates the analytic integrand needed by the next FTC step without
introducing fixed-frequency representatives.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2HeatGeneratorOrbit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Nonnegative-time raw Fourier `L²` orbit of the H³ generator datum. -/
noncomputable def h3RawFourierL2HeatGeneratorOrbitNN
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (U : H3SpectralFinVectorState)
    (s : ℝ≥0) :
    H3RawFourierL2FinVectorState :=
  h3RawFourierL2HeatApplyNN
    ν hν s
    (h3SpectralFinVectorLaplacianRawFourierL2 U)

/-- The generator orbit is strongly continuous for nonnegative time. -/
theorem continuous_h3RawFourierL2HeatGeneratorOrbitNN
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (U : H3SpectralFinVectorState) :
    Continuous
      (h3RawFourierL2HeatGeneratorOrbitNN ν hν U) := by
  exact
    continuous_h3RawFourierL2HeatApplyNN
      ν hν
      (h3SpectralFinVectorLaplacianRawFourierL2 U)

/-- The same generator orbit, extended to real time by clamping negative time
to zero. -/
noncomputable def h3RawFourierL2HeatGeneratorOrbitReal
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (U : H3SpectralFinVectorState)
    (s : ℝ) :
    H3RawFourierL2FinVectorState :=
  h3RawFourierL2HeatGeneratorOrbitNN
    ν hν U (Real.toNNReal s)

/-- The real-time generator orbit is strongly continuous. -/
theorem continuous_h3RawFourierL2HeatGeneratorOrbitReal
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (U : H3SpectralFinVectorState) :
    Continuous
      (h3RawFourierL2HeatGeneratorOrbitReal ν hν U) := by
  exact
    (continuous_h3RawFourierL2HeatGeneratorOrbitNN
      ν hν U).comp
      continuous_real_toNNReal

/-- Consequently the generator orbit is Bochner interval-integrable on every
finite real interval. -/
theorem h3RawFourierL2HeatGeneratorOrbitReal_intervalIntegrable
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (U : H3SpectralFinVectorState)
    (a b : ℝ) :
    IntervalIntegrable
      (h3RawFourierL2HeatGeneratorOrbitReal ν hν U)
      volume
      a
      b := by
  apply ContinuousOn.intervalIntegrable
  exact
    (continuous_h3RawFourierL2HeatGeneratorOrbitReal
      ν hν U).continuousOn

/-- On nonnegative real times the real wrapper is exactly the original
nonnegative-time orbit. -/
theorem h3RawFourierL2HeatGeneratorOrbitReal_of_nonneg
    {ν s : ℝ}
    (hν : 0 ≤ ν)
    (hs : 0 ≤ s)
    (U : H3SpectralFinVectorState) :
    h3RawFourierL2HeatGeneratorOrbitReal ν hν U s
      =
    h3RawFourierL2HeatGeneratorOrbitNN
      ν hν U (NNReal.mk s hs) := by
  unfold h3RawFourierL2HeatGeneratorOrbitReal
  rw [Real.toNNReal_of_nonneg hs]

/-- Generator-domain commutation identifies the orbit equally as the
deweighted Laplacian of the weighted heat evolution. -/
theorem h3RawFourierL2HeatGeneratorOrbitNN_eq_laplacian_heat
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (U : H3SpectralFinVectorState)
    (s : ℝ≥0) :
    h3RawFourierL2HeatGeneratorOrbitNN ν hν U s
      =
    h3SpectralFinVectorLaplacianRawFourierL2
      (h3SpectralVelocityHeatApplyNN ν hν s U) := by
  exact
    h3RawFourierL2HeatApplyNN_laplacianRawFourierL2
      ν hν s U

end

end Euclidean
end Bridge
end PrimeTensor
